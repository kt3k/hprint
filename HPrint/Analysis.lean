module

public import Lean
import all HPrint.Phrases

open Lean Elab Meta

namespace HPrint

public structure Elaborated where
  input : String
  trees : List InfoTree
  messages : List (Bool × String)

public def Elaborated.errors (e : Elaborated) : List String :=
  e.messages.filterMap fun (isError, msg) => if isError then some msg else none

public def elaborate (input : String) (fileName : String := "<input>") : IO Elaborated := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs ← s.commandState.messages.toList.mapM fun m => do
    pure (m.severity == .error, ← m.data.toString)
  pure { input, trees := s.commandState.infoState.trees.toList, messages := msgs }

inductive Step where
  | mk (ctx : ContextInfo) (info : TacticInfo) (children : List Step)

def lastComponent (n : Name) : String :=
  match n.components.getLast? with
  | some c => c.toString
  | none => ""

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

def range (s : Step) : Option String.Range := s.stx.getRange?

def source (s : Step) (input : String) : String := textAt input s.stx

def tag (s : Step) : String :=
  match s.info.goalsBefore.head?.bind (s.info.mctxBefore.findDecl? ·) with
  | some d => lastComponent d.userName
  | none => ""

end Step

def transparentKinds : List Name :=
  [ ``Lean.Parser.Term.byTactic, ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed,
    `null, `by, `Lean.cdotTk, ``Lean.Parser.Tactic.paren ]

def isTokenKind : Name → Bool
  | .str _ s => !s.isEmpty && !(s.front.isAlpha || s.front == '_')
  | _ => false

def isUserWritten (stx : Syntax) : Bool :=
  match stx.getHeadInfo with
  | .original .. => true
  | _ => false

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

structure HypView where
  name : String
  type : String
  prose : String
  head : String
  isProp : Bool
  deriving Inhabited

structure GoalView where
  hyps : List HypView
  target : String
  targetProse : String
  targetIsFalse : Bool
  targetIsExists : Bool
  deriving Inhabited

def headSymbol (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => lastComponent n
  | .sort l => if l.isZero then "Prop" else "Type"
  | _ => ""

def ppStr (e : Expr) : MetaM String := do
  pure (toString (← ppExpr e))

def dependentPrefix : Expr → Nat
  | .forallE _ _ b _ => if b.hasLooseBVar 0 then 1 + dependentPrefix b else 0
  | _ => 0

def arrowPrefix : Expr → Nat
  | .forallE _ _ b _ => if b.hasLooseBVar 0 then 0 else 1 + arrowPrefix b
  | _ => 0

structure Subject where
  names : List String
  type : String
  head : String

def subjects (items : List (String × String × String)) : List Subject :=
  (items.splitBy fun a b => a.2.1 == b.2.1).filterMap fun g =>
    g.head?.map fun (_, ty, head) => { names := g.map (·.1), type := ty, head }

mutual

partial def prose (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.isForall then
    let n := dependentPrefix e
    if n > 0 then
      forallBoundedTelescope e (some n) fun xs body => do
        let items ← xs.toList.mapM fun x => do
          let d ← x.fvarId!.getDecl
          pure (d.userName.toString, ← ppStr d.type, headSymbol d.type)
        let phrases := (subjects items).map fun g =>
          Phrases.sSubject g.names ((Phrases.typeNoun g.head .plural).orElse fun _ => some g.type)
        pure (Phrases.sForall (Phrases.list phrases) (← prose body))
    else
      let m := arrowPrefix e
      forallBoundedTelescope e (some m) fun xs body => do
        let premises ← xs.toList.mapM fun x => do premise (← x.fvarId!.getType)
        pure (Phrases.sIf premises (← prose body))
  else match e.getAppFnArgs with
    | (``Exists, #[_, p]) =>
      lambdaBoundedTelescope p 1 fun xs body => do
        match xs[0]? with
        | some x =>
          let d ← x.fvarId!.getDecl
          let ty ← ppStr d.type
          let noun := (Phrases.typeNoun (headSymbol d.type) .article).getD ty
          pure (Phrases.sExists (Phrases.sSubject [d.userName.toString] (some noun)) (← prose body))
        | none => ppStr e
    | _ => ppStr e

partial def premise (e : Expr) : MetaM String := do
  if e.isForall && dependentPrefix e > 0 then prose e
  else match e.getAppFnArgs with
    | (``Exists, _) => prose e
    | _ => ppStr e

end

def visibleDecls : MetaM (List LocalDecl) := do
  pure <| (← getLCtx).decls.toList.filterMap id |>.filter fun d => !d.isImplementationDetail

def goalView (ctx : ContextInfo) (mctx : MetavarContext) (g : MVarId) :
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
          prose := ← premise ty
          head := headSymbol ty
          isProp := ← Meta.isProp ty
          : HypView }
      let target ← instantiateMVars (← g.getType)
      pure {
        hyps
        target := ← ppStr target
        targetProse := ← prose target
        targetIsFalse := target.isConstOf ``False
        targetIsExists := target.getAppFn.isConstOf ``Exists
      }

def beforeView (s : Step) : IO (Option GoalView) :=
  s.info.goalsBefore.head?.mapM (goalView s.ctx s.info.mctxBefore)

def afterView (s : Step) : IO (Option GoalView) :=
  s.info.goalsAfter.head?.mapM (goalView s.ctx s.info.mctxAfter)

def statementOf (s : Step) : IO (Option String) := do
  match s.info.goalsBefore.head? with
  | none => pure none
  | some g =>
    let ctx := { s.ctx with mctx := s.info.mctxBefore }
    ctx.runMetaM {} do
      g.withContext do
        let decls ← visibleDecls
        let target ← instantiateMVars (← g.getType)
        let closed ← mkForallFVars (decls.map (·.toExpr)).toArray target
        pure (some (← prose closed))

end HPrint
