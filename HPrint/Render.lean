module

public import HPrint.Analysis
import all HPrint.Analysis
import all HPrint.Phrases
import all HPrint.Doc

open Lean Elab

namespace HPrint

public structure Options where
  statement : Bool := true
  deriving Inhabited

structure Ctx where
  input : String
  restate : Bool

structure Sink where
  blocks : Array Block := #[]
  pending : Array String := #[]
  deriving Inhabited

namespace Sink

def say (k : Sink) (s : String) : Sink :=
  let s := s.trim
  if s.isEmpty then k else { k with pending := k.pending.push s }

def flush (k : Sink) : Sink :=
  if k.pending.isEmpty then k
  else { blocks := k.blocks.push (.para (String.intercalate Phrases.joiner k.pending.toList)),
         pending := #[] }

def block (k : Sink) (b : Block) : Sink :=
  let k := k.flush
  { k with blocks := k.blocks.push b }

def finish (k : Sink) : List Block := (k.flush).blocks.toList

end Sink

def tacticName (c : Ctx) (s : Step) : String :=
  (s.source c.input).takeWhile fun ch => !(ch == ' ' || ch == '\n' || ch == '[')

def tacticArgs (c : Ctx) (s : Step) : Option String :=
  let src := s.source c.input
  let rest := ((src.drop (tacticName c s).length).trim).replace "\n" " "
  if rest.isEmpty then none else some rest

def firstComponent (src : String) : Option String :=
  let s := src.trim
  if !(s.startsWith "⟨") then none else
    let stop := fun (acc : List Char × Nat × Bool) (ch : Char) =>
      let (cur, depth, stopped) := acc
      if stopped then acc
      else if ch == ',' && depth == 0 then (cur, depth, true)
      else if "⟨([".contains ch then (ch :: cur, depth + 1, false)
      else if "⟩)]".contains ch then (ch :: cur, depth - 1, false)
      else (ch :: cur, depth, false)
    let (cur, _, _) := (s.drop 1 |>.dropRight 1).toList.foldl stop ([], 0, false)
    let w := (String.mk cur.reverse).trim
    if w.isEmpty then none else some w

def prettyArgs (args : Option String) : Option String :=
  args.map fun a =>
    let a := a.trim
    if a.startsWith "[" && a.endsWith "]" then
      Phrases.list ((a.drop 1 |>.dropRight 1).splitOn "," |>.map (·.trim) |>.filter (!·.isEmpty))
    else a

def majorPremise (c : Ctx) (s : Step) : Option String :=
  let t := textAt c.input s.stx[1]
  if t.isEmpty then none else some t

def afterAssign (src : String) : Option String :=
  match src.splitOn ":=" with
  | _ :: rest@(_ :: _) =>
    let t := ((String.intercalate ":=" rest).trim).replace "\n" " "
    if t.isEmpty then none else some t
  | _ => none

def originOf (c : Ctx) (s : Step) (name : String) : Option String :=
  (afterAssign (s.source c.input)).orElse fun _ =>
    if name == "cases" || name == "rcases" || name == "obtain" then majorPremise c s else none

def isNew (old : List HypView) (h : HypView) : Bool :=
  !(old.any fun o => o.name == h.name && o.type == h.type)

def announce (hyps : List HypView) (k : Sink) : Sink :=
  let (props, objects) := hyps.partition (·.isProp)
  let groups := (objects.splitBy fun a b => a.type == b.type).filterMap fun g =>
    g.head?.map fun h =>
      { names := g.map (·.name), type := some h.type,
        noun := Phrases.typeNoun h.head (if g.length > 1 then .plural else .article) : FixGroup }
  let k := if groups.isEmpty then k else k.say (Phrases.fix groups)
  if props.isEmpty then k
  else k.say (Phrases.assume (props.map fun h => { name := some h.name, stmt := h.prose }))

def howKind (name : String) : HowKind :=
  if name == "rw" || name == "rewrite" || name == "erw" then .rewrite
  else if name.startsWith "simp" || name == "dsimp" then .simplify
  else if name == "unfold" || name == "delta" then .unfold
  else if name == "refine" || name == "apply" || name == "exact" then .apply
  else .other name

def transforms (kind : HowKind) : Bool :=
  match kind with
  | .rewrite | .simplify | .unfold => true
  | _ => false

def reasonFor (name : String) (args : Option String) : Option String :=
  (List.lookup name Phrases.reasons).orElse fun _ =>
    if name == "exact" || name == "apply" then args else none

def justification (c : Ctx) (s : Step) (name : String) : Option String :=
  if name == "have" || name == "suffices" || name == "replace" then
    (afterAssign (s.source c.input)).filter fun t => !t.startsWith "by"
  else none

partial def findAll (p : Syntax → Bool) (stx : Syntax) : List Syntax :=
  (if p stx then [stx] else []) ++ stx.getArgs.toList.flatMap (findAll p)

def sourceOf (c : Ctx) (stx : Syntax) : String :=
  (textAt c.input stx).replace "\n" " "

def relations : String := "↔≠≤≥⊆≡∣∈=<>"

def splitRelation (src : String) : String × String × String :=
  let rec go (cs : List Char) (seen : List Char) (depth : Nat) : Option (String × String × String) :=
    match cs with
    | [] => none
    | ch :: rest =>
      if depth == 0 && relations.contains ch then
        some (String.mk seen.reverse, ch.toString, String.mk rest)
      else
        let depth := if "(⟨[{".contains ch then depth + 1
          else if ")⟩]}".contains ch then depth - 1
          else depth
        go rest (ch :: seen) depth
  match go src.toList [] 0 with
  | some (l, op, r) => (l.trim, op, r.trim)
  | none => (src.trim, "", "")

def calcBlock (c : Ctx) (s : Step) (k : Sink) : Sink :=
  let steps := findAll (fun n =>
    n.isOfKind `Lean.calcFirstStep || n.isOfKind `Lean.calcStep) s.stx
  let lines := steps.map fun st =>
    let rel := sourceOf c st[0]
    let proof :=
      if st.isOfKind `Lean.calcStep then sourceOf c st[2]
      else if st[1].getNumArgs ≥ 2 then sourceOf c st[1][1] else ""
    let (lhs, op, rhs) := splitRelation rel
    { lhs := if lhs == "_" then "" else lhs
      op, rhs
      reason := if proof.isEmpty then none else some (Phrases.justification proof) : CalcLine }
  if lines.isEmpty then k.say (Phrases.verbatim (s.source c.input))
  else (k.say Phrases.computation).block (.calcBlock lines)

def witnessOf (c : Ctx) (s : Step) : Option String :=
  match tacticArgs c s with
  | some a => firstComponent a
  | none => none

def stateGoal (g : GoalView) (k : Sink) : Sink :=
  k.say (if g.targetIsFalse then Phrases.mustShowFalse else Phrases.mustShow g.targetProse)

inductive Nesting where
  | leaf
  | inline
  | subproof
  | branches (groups : List (String × List Step))

def groupByGoal (steps : List Step) : List (List Step) :=
  steps.splitBy fun a b => a.info.goalsBefore.head? == b.info.goalsBefore.head?

mutual

partial def classify (s : Step) (fresh : List HypView) (produced : Nat) :
    IO Nesting := do
  if s.children.isEmpty then return .leaf
  let parent := s.info.goalsBefore.head?
  if s.children.any fun ch => ch.info.goalsBefore.head? == parent then return .inline
  match s.children.head? with
  | none => return .leaf
  | some first =>
    if produced == 1 then
      if let some cg ← beforeView first then
        if fresh.any fun h => h.type == cg.target then return .subproof
    if s.children.any fun ch => ch.info.goalsBefore.head?.isNone then return .leaf
    let groups := (s.children.splitBy fun a b => a.tag == b.tag).filterMap fun g =>
      g.head?.map fun h => (h.tag, g)
    return .branches groups

partial def narrate (c : Ctx) (steps : List Step) (k : Sink) : IO Sink := do
  let mut k := k
  for s in steps do
    k ← narrateStep c s k
  pure k

partial def narrateStep (c : Ctx) (s : Step) (k : Sink) : IO Sink := do
  let name := tacticName c s
  let args := prettyArgs (tacticArgs c s)
  let kind := howKind name
  match ← beforeView s with
  | none => pure k
  | some g =>
    let produced := s.info.goalsAfter.length + 1 - s.info.goalsBefore.length
    let after? ← if produced == 0 then pure none else afterView s
    let fresh := ((after?.map (·.hyps)).getD []).filter (isNew g.hyps)
    if s.kind == `Lean.calcTactic then
      return calcBlock c s k
    if s.kind == `Lean.cdot then
      let body ← narrate c s.children (stateGoal g default)
      return k.block (.nested none (body.finish))
    match ← classify s fresh produced with
    | .inline =>
      let groups := groupByGoal s.children
      if groups.length ≤ 1 then narrate c s.children k
      else
        let parent := s.info.goalsBefore.head?
        let mut k := k
        for grp in groups do
          match grp.head? with
          | none => pure ()
          | some first =>
            if first.info.goalsBefore.head? == parent then
              k ← narrate c grp k
            else
              let head := match ← beforeView first with
                | some bg => stateGoal bg default
                | none => default
              let body ← narrate c grp head
              k := k.block (.nested none (body.finish))
        pure k
    | .subproof => narrateSideProof c s fresh k
    | .branches groups => narrateBranching c s g (name == "induction") groups k
    | .leaf =>
    if produced == 0 then
      match reasonFor name args with
      | some why => pure (k.say (Phrases.closedBy why))
      | none =>
        if transforms kind then pure (k.say (Phrases.closedByHow (Phrases.how kind args)))
        else pure (k.say (Phrases.closedBy s!"`{s.source c.input}`"))
    else if produced == 1 then
      match after? with
      | none => pure k
      | some a =>
        let (facts, objects) := fresh.partition (·.isProp)
        if !fresh.isEmpty && a.target == g.target then
          if !objects.isEmpty then
            pure (k.say (Phrases.obtainFrom (objects.map (·.name))
              (facts.map fun h => { name := some h.name, stmt := h.prose })
              (originOf c s name)))
          else
            let why := (reasonFor name args).orElse fun _ => justification c s name
            pure (facts.foldl (fun k h =>
              k.say (Phrases.weHave { name := some h.name, stmt := h.prose } why)) k)
        else if !fresh.isEmpty then
          pure (stateGoal a (announce fresh k))
        else if a.target != g.target then
          match (if g.targetIsExists && !a.targetIsExists then witnessOf c s else none) with
          | some w => pure ((k.say (Phrases.chooseWitness w)).say (Phrases.remainsToShow a.targetProse))
          | none => pure (k.say (Phrases.transformedBy (Phrases.how kind args) a.targetProse))
        else
          pure (k.say (Phrases.verbatim (s.source c.input)))
    else
      pure (k.say (Phrases.splitInto produced))

partial def narrateBranching (c : Ctx) (s : Step) (g : GoalView) (isInduction : Bool)
    (branches : List (String × List Step)) (k : Sink) : IO Sink := do
  let subject := (majorPremise c s).getD (s.source c.input)
  let noun := (g.hyps.find? fun h => h.name == subject).bind fun h => Phrases.typeNoun h.head .bare
  let mut k := k.say (if isInduction then Phrases.inductionOn subject noun else Phrases.caseAnalysis subject)
  for (tag, steps) in branches do
    match steps.head? with
    | none => pure ()
    | some first =>
      match ← beforeView first with
      | none => pure ()
      | some bg =>
        let fresh := bg.hyps.filter (isNew g.hyps)
        let (facts, objs) := fresh.partition (·.isProp)
        let mut body : Sink := default
        if !objs.isEmpty then body := announce objs body
        for h in facts do
          body := if isInduction then
              body.say (Phrases.inductionHypothesis { name := some h.name, stmt := h.prose })
            else body.say (Phrases.assume [{ name := some h.name, stmt := h.prose }])
        body := stateGoal bg body
        body ← narrate c steps body
        let label :=
          if tag.isEmpty then none
          else if isInduction then
            some (if facts.isEmpty then Phrases.baseCaseLabel tag else Phrases.stepCaseLabel tag)
          else some (Phrases.caseLabel tag)
        k := k.block (.nested label (body.finish))
  pure k

partial def narrateSideProof (c : Ctx) (s : Step) (fresh : List HypView) (k : Sink) :
    IO Sink := do
  let item : Named := match fresh.head? with
    | some h => { name := some h.name, stmt := h.prose }
    | none => { stmt := Phrases.anonymousFact }
  let k := k.say (Phrases.claim item)
  let body ← narrate c s.children default
  pure (k.block (.nested none (body.finish)))

end

def declKeyword (stx : Syntax) : String :=
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.example)).isSome then "example"
  else if (stx.find? (·.isOfKind ``Lean.Parser.Command.definition)).isSome then "def"
  else if (stx.find? (·.isOfKind ``Lean.Parser.Command.abbrev)).isSome then "abbrev"
  else "theorem"

def declName (stx : Syntax) : Option String :=
  (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).map fun d => d[0].getId.toString

def renderDeclaration (c : Ctx) (stx : Syntax) (steps : List Step) : IO (List Block) := do
  let mut k : Sink := default
  k := k.block (.heading (Phrases.headingTheorem (declKeyword stx) (declName stx)))
  match steps.head? with
  | none => pure (k.finish)
  | some first =>
    match ← beforeView first with
    | none => pure (k.finish)
    | some g =>
      if c.restate then
        if let some stmt ← statementOf first then
          k := k.block (.statement (stmt.capitalize ++ Phrases.period))
      k := k.block (.heading Phrases.headingProof)
      if !g.hyps.isEmpty then
        k := stateGoal g (announce g.hyps k)
      k ← narrate c steps k
      k := k.block (.qed Phrases.qed)
      pure (k.finish)

partial def declarationsOf (t : InfoTree) : List (Syntax × List Step) :=
  match t with
  | .context _ t' => declarationsOf t'
  | .hole _ => []
  | .node i cs =>
    match i with
    | .ofCommandInfo ci =>
      if ci.stx.isOfKind ``Lean.Parser.Command.declaration then
        [(ci.stx, cs.toList.flatMap (collectSteps · none))]
      else cs.toList.flatMap declarationsOf
    | _ => cs.toList.flatMap declarationsOf

def renderElaborated (e : Elaborated) (opts : Options := {}) : IO (List Block) := do
  let c : Ctx := { input := e.input, restate := opts.statement }
  let mut out : List Block := []
  for (stx, steps) in e.trees.flatMap declarationsOf do
    out := out ++ (← renderDeclaration c stx steps)
  pure out

public def hprint (e : Elaborated) (opts : Options := {}) : IO String := do
  pure (toText (← renderElaborated e opts))

public def hprintStr (input : String) (opts : Options := {}) (fileName : String := "<input>") :
    IO String := do
  hprint (← elaborate input fileName) opts

end HPrint
