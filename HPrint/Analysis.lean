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
  env : Environment
  trees : List InfoTree
  messages : List (Bool × String)

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
  pure {
    input
    env := s.commandState.env
    trees := s.commandState.infoState.trees.toList
    messages := msgs
  }

/-! ## Tactic steps -/

/-- A tactic together with the goals it saw and the blocks nested inside it. -/
inductive Step where
  | mk (ctx : ContextInfo) (info : TacticInfo) (children : List Step)

namespace Step

def ctx : Step → ContextInfo | .mk c _ _ => c
def info : Step → TacticInfo | .mk _ i _ => i
def children : Step → List Step | .mk _ _ c => c
def stx (s : Step) : Syntax := s.info.stx
def kind (s : Step) : Name := s.info.stx.getKind

/-- Source range, used both for quoting and for spotting macro expansions. -/
def range (s : Step) : Option (String.Pos × String.Pos) :=
  match s.stx.getPos?, s.stx.getTailPos? with
  | some a, some b => some (a, b)
  | _, _ => none

/-- The exact Lean text of this tactic. -/
def source (s : Step) (input : String) : String :=
  match s.range with
  | some (a, b) => (Substring.mk input a b).toString.trim
  | none => ""

end Step

/-- Kinds that only group other tactics; they never become a step of their own. -/
private def transparentKinds : List Name :=
  [ ``Lean.Parser.Term.byTactic, ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed,
    `null, `by, `Lean.cdotTk, ``Lean.Parser.Tactic.paren ]

/--
Turn an info tree into a tree of steps.

Two kinds of noise are removed: the grouping nodes above, and the macro
expansions Lean records for a tactic, which show up as children covering
exactly the same source range as their parent.
-/
partial def collectSteps (t : InfoTree) (ctx? : Option ContextInfo := none) : List Step :=
  match t with
  | .context c t' => collectSteps t' (c.mergeIntoOuter? ctx?)
  | .hole _ => []
  | .node i cs =>
    let kids := cs.toList.flatMap (collectSteps · ctx?)
    match i, ctx? with
    | .ofTacticInfo ti, some ctx =>
      if transparentKinds.contains ti.stx.getKind then kids
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
  /-- The `case` tag Lean gave this goal, e.g. `succ`, `inl`, `left`. -/
  tag : String
  hyps : List HypView
  target : String
  targetProse : String
  targetIsFalse : Bool
  /-- Set when the goal asks for a witness, so `refine ⟨w, _⟩` can be read as one. -/
  targetIsExists : Bool
  /-- The whole goal restated as a closed proposition, binders included. -/
  closed : String
  deriving Inhabited

/-- Last component of a name: `Nat.Prime` becomes `Prime`, `List` stays `List`. -/
private def lastComponent (n : Name) : String :=
  match n.components.getLast? with
  | some c => c.toString
  | none => ""

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

/-- Group consecutive variables that share a type, so they read as one phrase. -/
private def groupByType (items : List (String × String)) : List (List String × String) :=
  items.foldl (fun acc (name, ty) =>
    match acc.reverse with
    | (names, t) :: rest => if t == ty then ((names ++ [name], t) :: rest).reverse
                            else acc ++ [([name], ty)]
    | [] => [([name], ty)]) []

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
        let groups := groupByType (items.map fun (a, b, _) => (a, b))
        let subjects ← groups.mapM fun (names, ty) => do
          let head := (items.find? fun (_, t, _) => t == ty).map (·.2.2) |>.getD ""
          pure (ph.sSubject names (ph.typeNoun head .plural |>.orElse fun _ => some ty))
        pure (ph.sForall (ph.list subjects) (← prose ph body))
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

/-- Everything the renderer needs to know about one goal. -/
def goalView (ph : Phrases) (ctx : ContextInfo) (mctx : MetavarContext) (g : MVarId) :
    IO GoalView := do
  let ctx := { ctx with mctx }
  ctx.runMetaM {} do
    g.withContext do
      let decls := (← getLCtx).decls.toList.filterMap id
        |>.filter fun d => !d.isImplementationDetail
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
      let fvars := decls.map (·.toExpr) |>.toArray
      let closedTy ← mkForallFVars fvars target
      pure {
        tag := lastComponent (← g.getTag)
        hyps
        target := ← ppStr target
        targetProse := ← prose ph target
        targetIsFalse := target.isConstOf ``False
        targetIsExists := target.getAppFn.isConstOf ``Exists
        closed := ← prose ph closedTy
      }

/-- The goals a step saw before it ran. -/
def beforeViews (ph : Phrases) (s : Step) : IO (List GoalView) :=
  s.info.goalsBefore.mapM (goalView ph s.ctx s.info.mctxBefore ·)

/-- The goals a step left behind. -/
def afterViews (ph : Phrases) (s : Step) : IO (List GoalView) :=
  s.info.goalsAfter.mapM (goalView ph s.ctx s.info.mctxAfter ·)

end HPrint
