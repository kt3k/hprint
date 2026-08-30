import Lean
import HPrint.Phrases

/-!
# Reading a proof out of Lean

hprint does not parse Lean itself: it hands the file to Lean's own frontend and
then reads the elaborator's `InfoTree`.  That gives every tactic its *real*
goal state — the hypotheses actually in scope and the goal actually remaining —
so the prose can state what is being assumed and what is left to prove instead
of guessing.
-/

open Lean Elab Meta

namespace HPrint

/-! ## Running the frontend -/

/-- The elaborated contents of one file. -/
structure Elaborated where
  input : String
  trees : List InfoTree
  /-- Diagnostics, paired with whether they are errors. -/
  messages : List (Bool × String)

/-- The errors, if any; both entry points report these before printing. -/
def Elaborated.errors (e : Elaborated) : List String :=
  e.messages.filterMap fun (isError, msg) => if isError then some msg else none

/-- Elaborate `path`, keeping the info trees the renderer needs. -/
def elaborateFile (path : System.FilePath) : IO Elaborated := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs ← s.commandState.messages.toList.mapM fun m => do
    pure (m.severity == .error, ← m.data.toString)
  pure { input, trees := s.commandState.infoState.trees.toList, messages := msgs }

/-! ## Tactic steps -/

/-- A tactic together with the goals it saw and the blocks nested inside it. -/
inductive Step where
  | mk (ctx : ContextInfo) (info : TacticInfo) (children : List Step)

/-- Last component of a name: `Nat.Prime` becomes `Prime`, `List` stays `List`. -/
def lastComponent (n : Name) : String :=
  match n.components.getLast? with
  | some c => c.toString
  | none => ""

/-- The source text a piece of syntax came from, trimmed. -/
def textAt (input : String) (stx : Syntax) : String :=
  match stx.getRange? with
  | some r => (input.extract r.start r.stop).trim
  | none => ""

namespace Step

def ctx : Step → ContextInfo | .mk c _ _ => c
def info : Step → TacticInfo | .mk _ i _ => i
def children : Step → List Step | .mk _ _ c => c
def stx (s : Step) : Syntax := s.info.stx
def kind (s : Step) : Name := s.info.stx.getKind

/-- Source range, used both for quoting and for spotting macro expansions. -/
def range (s : Step) : Option String.Range := s.stx.getRange?

/-- The exact Lean text of this tactic. -/
def source (s : Step) (input : String) : String := textAt input s.stx

/-- The case tag Lean gave this step's first goal, without opening `MetaM`. -/
def tag (s : Step) : String :=
  match s.info.goalsBefore.head?.bind (s.info.mctxBefore.findDecl? ·) with
  | some d => lastComponent d.userName
  | none => ""

end Step

/-- Kinds that only group other tactics; they never become a step of their own. -/
private def transparentKinds : List Name :=
  [ ``Lean.Parser.Term.byTactic, ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed,
    `null, `by, `Lean.cdotTk, ``Lean.Parser.Tactic.paren ]

/--
A node standing for a bare token rather than a tactic.

Macro expansions hang their output off whichever token they used as a source
reference, so the `rfl` that `rw` runs afterwards appears under a node of kind
`«]»`.  Such kinds are named after the token itself, so they start with
punctuation, while every real tactic kind starts with a letter.
-/
private def isTokenKind : Name → Bool
  | .str _ s => !s.isEmpty && !(s.front.isAlpha || s.front == '_')
  | _ => false

/--
A tactic the user actually wrote, rather than one a macro produced.

Expanding `have h : P := by tac` records a whole chain of `focus`, `case` and
`withAnnotateState` nodes; Lean marks every one of them synthetic, while the
`have` itself and the tactics inside the `by` block keep their original source
info.  That flag is what tells the two apart, since the synthetic nodes borrow
real source positions and so cannot be spotted by their range alone.
-/
private def isUserWritten (stx : Syntax) : Bool :=
  match stx.getHeadInfo with
  | .original .. => true
  | _ => false

/--
Turn an info tree into a tree of steps.

Three kinds of noise are removed: the grouping nodes above, the macro
expansions Lean records for a tactic, and the children covering exactly the
same source range as their parent, which are a tactic re-elaborated under a
different name.
-/
partial def collectSteps (t : InfoTree) (ctx? : Option ContextInfo := none) : List Step :=
  match t with
  | .context c t' => collectSteps t' (c.mergeIntoOuter? ctx?)
  | .hole _ => []
  | .node i cs =>
    let kids := cs.toList.flatMap (collectSteps · ctx?)
    match i, ctx? with
    | .ofTacticInfo ti, some ctx =>
      let kind := ti.stx.getKind
      if transparentKinds.contains kind || isTokenKind kind || !isUserWritten ti.stx then kids
      else
        let here : Step := .mk ctx ti []
        let kids := kids.filter fun k => k.range != here.range
        [.mk ctx ti kids]
    | _, _ => kids

/-! ## Goals as the reader should see them -/

structure HypView where
  name : String
  /-- Lean's own rendering of the type. -/
  type : String
  /-- The type read aloud, with quantifiers spelled out. -/
  prose : String
  /-- Head symbol of the type, for the noun dictionary. -/
  head : String
  isProp : Bool
  deriving Inhabited

structure GoalView where
  hyps : List HypView
  target : String
  targetProse : String
  targetIsFalse : Bool
  /-- Set when the goal asks for a witness, so `refine ⟨w, _⟩` can be read as one. -/
  targetIsExists : Bool
  deriving Inhabited

/-- Head symbol of a type, used to look up its noun. -/
private def headSymbol (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => lastComponent n
  | .sort l => if l.isZero then "Prop" else "Type"
  | _ => ""

private def ppStr (e : Expr) : MetaM String := do
  pure (toString (← ppExpr e))

/-- Number of leading binders the body actually depends on. -/
private def dependentPrefix : Expr → Nat
  | .forallE _ _ b _ => if b.hasLooseBVar 0 then 1 + dependentPrefix b else 0
  | _ => 0

/-- Number of leading binders the body does not depend on: an implication chain. -/
private def arrowPrefix : Expr → Nat
  | .forallE _ _ b _ => if b.hasLooseBVar 0 then 0 else 1 + arrowPrefix b
  | _ => 0

/-- One quantifier phrase: the variables that share a type, and that type. -/
private structure Subject where
  names : List String
  type : String
  head : String

/-- Group consecutive variables that share a type, so they read as one phrase. -/
private def subjects (items : List (String × String × String)) : List Subject :=
  (items.splitBy fun a b => a.2.1 == b.2.1).filterMap fun g =>
    g.head?.map fun (_, ty, head) => { names := g.map (·.1), type := ty, head }

mutual

/--
Read a proposition aloud: quantifiers and implications become words, everything
else stays in mathematical notation.
-/
partial def prose (ph : Phrases) (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.isForall then
    let n := dependentPrefix e
    if n > 0 then
      forallBoundedTelescope e (some n) fun xs body => do
        let items ← xs.toList.mapM fun x => do
          let d ← x.fvarId!.getDecl
          pure (d.userName.toString, ← ppStr d.type, headSymbol d.type)
        let phrases := (subjects items).map fun g =>
          ph.sSubject g.names ((ph.typeNoun g.head .plural).orElse fun _ => some g.type)
        pure (ph.sForall (ph.list phrases) (← prose ph body))
    else
      let m := arrowPrefix e
      forallBoundedTelescope e (some m) fun xs body => do
        let premises ← xs.toList.mapM fun x => do premise ph (← x.fvarId!.getType)
        pure (ph.sIf premises (← prose ph body))
  else match e.getAppFnArgs with
    | (``Exists, #[_, p]) =>
      lambdaBoundedTelescope p 1 fun xs body => do
        match xs[0]? with
        | some x =>
          let d ← x.fvarId!.getDecl
          let ty ← ppStr d.type
          let noun := (ph.typeNoun (headSymbol d.type) .article).getD ty
          pure (ph.sExists (ph.sSubject [d.userName.toString] (some noun)) (← prose ph body))
        | none => ppStr e
    | _ => ppStr e

/--
A premise inside an "if ..., then ..." sentence.  Quantifiers are worth
spelling out; a nested implication reads better in symbols.
-/
partial def premise (ph : Phrases) (e : Expr) : MetaM String := do
  if e.isForall && dependentPrefix e > 0 then prose ph e
  else match e.getAppFnArgs with
    | (``Exists, _) => prose ph e
    | _ => ppStr e

end

/-- The hypotheses of the current context, minus Lean's internal bookkeeping. -/
private def visibleDecls : MetaM (List LocalDecl) := do
  pure <| (← getLCtx).decls.toList.filterMap id |>.filter fun d => !d.isImplementationDetail

/-- Everything the renderer needs to know about one goal. -/
def goalView (ph : Phrases) (ctx : ContextInfo) (mctx : MetavarContext) (g : MVarId) :
    IO GoalView := do
  let ctx := { ctx with mctx }
  ctx.runMetaM {} do
    g.withContext do
      let decls ← visibleDecls
      let hyps ← decls.mapM fun d => do
        let ty ← instantiateMVars d.type
        pure {
          name := d.userName.toString
          type := ← ppStr ty
          prose := ← premise ph ty
          head := headSymbol ty
          isProp := ← Meta.isProp ty
          : HypView }
      let target ← instantiateMVars (← g.getType)
      pure {
        hyps
        target := ← ppStr target
        targetProse := ← prose ph target
        targetIsFalse := target.isConstOf ``False
        targetIsExists := target.getAppFn.isConstOf ``Exists
      }

/-- The goal a step was working on.  The others are not narrated here. -/
def beforeView (ph : Phrases) (s : Step) : IO (Option GoalView) :=
  s.info.goalsBefore.head?.mapM (goalView ph s.ctx s.info.mctxBefore)

/-- The goal a step left behind, if it left one. -/
def afterView (ph : Phrases) (s : Step) : IO (Option GoalView) :=
  s.info.goalsAfter.head?.mapM (goalView ph s.ctx s.info.mctxAfter)

/--
The theorem a proof opens with: the step's goal closed over its hypotheses.
Only ever needed once per declaration, so it is not part of `GoalView`.
-/
def statementOf (ph : Phrases) (s : Step) : IO (Option String) := do
  match s.info.goalsBefore.head? with
  | none => pure none
  | some g =>
    let ctx := { s.ctx with mctx := s.info.mctxBefore }
    ctx.runMetaM {} do
      g.withContext do
        let decls ← visibleDecls
        let target ← instantiateMVars (← g.getType)
        let closed ← mkForallFVars (decls.map (·.toExpr)).toArray target
        pure (some (← prose ph closed))

end HPrint
