import HPrint.Analysis
import HPrint.Doc

/-!
# Telling the proof back

The narration is driven by the *difference* between the goal state before and
after each tactic, not by a table of tactic names.  New hypotheses become "Let
n be a natural number" or "Assume P"; a changed target becomes "it remains to
show ..."; one goal becoming several becomes a case split.  A tactic's name is
consulted only to say *why* something holds ("by linear arithmetic").
-/

open Lean Elab

namespace HPrint

structure Options where
  lang : String := "en"
  /-- Restate the theorem before the proof. -/
  statement : Bool := true
  width : Nat := 76
  format : OutFormat := .text
  deriving Inhabited

private structure Ctx where
  ph : Phrases
  input : String
  /-- Whether to restate the theorem before its proof. -/
  restate : Bool

/-- Collects sentences into paragraphs so the output reads as prose. -/
private structure Sink where
  blocks : Array Block := #[]
  pending : Array String := #[]
  deriving Inhabited

namespace Sink

def say (k : Sink) (s : String) : Sink :=
  let s := s.trim
  if s.isEmpty then k else { k with pending := k.pending.push s }

def flush (k : Sink) (ph : Phrases) : Sink :=
  if k.pending.isEmpty then k
  else { blocks := k.blocks.push (.para (String.intercalate ph.joiner k.pending.toList)),
         pending := #[] }

def block (k : Sink) (ph : Phrases) (b : Block) : Sink :=
  let k := k.flush ph
  { k with blocks := k.blocks.push b }

def finish (k : Sink) (ph : Phrases) : List Block := (k.flush ph).blocks.toList

end Sink

/-! ## Reading the tactic itself -/

/-- The tactic's leading keyword, which is what the phrasebooks key on. -/
private def tacticName (c : Ctx) (s : Step) : String :=
  (s.source c.input).takeWhile fun ch => !(ch == ' ' || ch == '\n' || ch == '[')

/-- Everything after the leading keyword, as written. -/
private def tacticArgs (c : Ctx) (s : Step) : Option String :=
  let src := s.source c.input
  let rest := ((src.drop (tacticName c s).length).trim).replace "\n" " "
  if rest.isEmpty then none else some rest

/-- The first component of `⟨a, b⟩`: the witness, when there is one. -/
private def firstComponent (src : String) : Option String :=
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

/-- Turn `[a, b]` into a readable list, leaving anything else alone. -/
private def prettyArgs (ph : Phrases) (args : Option String) : Option String :=
  args.map fun a =>
    let a := a.trim
    if a.startsWith "[" && a.endsWith "]" then
      ph.list ((a.drop 1 |>.dropRight 1).splitOn "," |>.map (·.trim) |>.filter (!·.isEmpty))
    else a

/-- Source text of the tactic's first argument, e.g. `n` in `induction n with ...`. -/
private def majorPremise (c : Ctx) (s : Step) : Option String :=
  let t := textAt c.input s.stx[1]
  if t.isEmpty then none else some t

/-! ## Introducing hypotheses -/

/-- Whatever a tactic assigns after `:=`, as one line. -/
private def afterAssign (src : String) : Option String :=
  match src.splitOn ":=" with
  | _ :: rest@(_ :: _) =>
    let t := ((String.intercalate ":=" rest).trim).replace "\n" " "
    if t.isEmpty then none else some t
  | _ => none

/-- The term a fact was obtained from: the `h` of `obtain .. := h` or `cases h`. -/
private def originOf (c : Ctx) (s : Step) (name : String) : Option String :=
  (afterAssign (s.source c.input)).orElse fun _ =>
    if name == "cases" || name == "rcases" || name == "obtain" then majorPremise c s else none

private def isNew (old : List HypView) (h : HypView) : Bool :=
  !(old.any fun o => o.name == h.name && o.type == h.type)

/-- Emit "Let ... be ..." and "Assume ..." for a batch of new hypotheses. -/
private def announce (c : Ctx) (hyps : List HypView) (k : Sink) : Sink :=
  let ph := c.ph
  let (props, objects) := hyps.partition (·.isProp)
  let groups := (objects.splitBy fun a b => a.type == b.type).filterMap fun g =>
    g.head?.map fun h =>
      { names := g.map (·.name), type := some h.type,
        noun := ph.typeNoun h.head (if g.length > 1 then .plural else .article) : FixGroup }
  let k := if groups.isEmpty then k else k.say (ph.fix groups)
  if props.isEmpty then k
  else k.say (ph.assume (props.map fun h => { name := some h.name, stmt := h.prose }))

/--
What a tactic did, decided once here rather than in each phrasebook: the
categories are a fact about Lean, only their wording is a fact about English.
-/
private def howKind (name : String) : HowKind :=
  if name == "rw" || name == "rewrite" || name == "erw" then .rewrite
  else if name.startsWith "simp" || name == "dsimp" then .simplify
  else if name == "unfold" || name == "delta" then .unfold
  else if name == "refine" || name == "apply" || name == "exact" then .apply
  else .other name

/-- Tactics whose job is to reshape the goal rather than to justify it. -/
private def transforms (kind : HowKind) : Bool :=
  match kind with
  | .rewrite | .simplify | .unfold => true
  | _ => false

/--
Why a goal holds.  `exact`/`apply` justify themselves — their argument *is* the
reason — so that rule lives here with the rest of the tactic knowledge.
-/
private def reasonFor (ph : Phrases) (name : String) (args : Option String) : Option String :=
  (List.lookup name ph.reasons).orElse fun _ =>
    if name == "exact" || name == "apply" then args else none

/-- The justification written after `:=`, as in `have h : P := foo`. -/
private def justification (c : Ctx) (s : Step) (name : String) : Option String :=
  if name == "have" || name == "suffices" || name == "replace" then
    (afterAssign (s.source c.input)).filter fun t => !t.startsWith "by"
  else none

/-- Every node of `stx` satisfying `p`, outermost first. -/
private partial def findAll (p : Syntax → Bool) (stx : Syntax) : List Syntax :=
  (if p stx then [stx] else []) ++ stx.getArgs.toList.flatMap (findAll p)

private def sourceOf (c : Ctx) (stx : Syntax) : String :=
  (textAt c.input stx).replace "\n" " "

/-- Relation symbols a `calc` chain may be built from.  Each is one codepoint. -/
private def relations : String := "↔≠≤≥⊆≡∣∈=<>"

/-- Split `a ≤ b` into its two sides, ignoring anything inside brackets. -/
private def splitRelation (src : String) : String × String × String :=
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

/-- Lay a `calc` chain out as a displayed computation. -/
private def calcBlock (c : Ctx) (s : Step) (k : Sink) : Sink :=
  let ph := c.ph
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
      reason := if proof.isEmpty then none else some (ph.justification proof) : CalcLine }
  if lines.isEmpty then k.say (ph.verbatim (s.source c.input))
  else (k.say ph.computation).block ph (.calcBlock lines)

/-- The witness supplied by `refine ⟨w, ?_⟩`, `exact ⟨w, _⟩` or `use w`. -/
private def witnessOf (c : Ctx) (s : Step) : Option String :=
  match tacticArgs c s with
  | some a => firstComponent a
  | none => none

private def stateGoal (c : Ctx) (g : GoalView) (k : Sink) : Sink :=
  k.say (if g.targetIsFalse then c.ph.mustShowFalse else c.ph.mustShow g.targetProse)

/-! ## The walk -/

/--
What the children of a step are: a combinator carrying on with the same goal,
a side proof of a fact the step introduced, or the bodies of the branches the
step produced.
-/
private inductive Nesting where
  | leaf
  | inline
  | subproof
  | branches (groups : List (String × List Step))

/-- Group consecutive steps that work on the same goal. -/
private def groupByGoal (steps : List Step) : List (List Step) :=
  steps.splitBy fun a b => a.info.goalsBefore.head? == b.info.goalsBefore.head?

mutual

/--
Classify a step's children by the goals they work on.

Children that keep working on their parent's own goal belong to a combinator
(`first`, `all_goals`, `try`).  Children proving a goal whose statement is the
hypothesis their parent introduced are a side proof (`have h : P := by ...`).
Anything else is a branch body, grouped by the case tag Lean assigned it.
-/
private partial def classify (c : Ctx) (s : Step) (fresh : List HypView) (produced : Nat) :
    IO Nesting := do
  if s.children.isEmpty then return .leaf
  let parent := s.info.goalsBefore.head?
  if s.children.any fun ch => ch.info.goalsBefore.head? == parent then return .inline
  match s.children.head? with
  | none => return .leaf
  | some first =>
    if produced == 1 then
      if let some cg ← beforeView c.ph first then
        if fresh.any fun h => h.type == cg.target then return .subproof
    if s.children.any fun ch => ch.info.goalsBefore.head?.isNone then return .leaf
    let groups := (s.children.splitBy fun a b => a.tag == b.tag).filterMap fun g =>
      g.head?.map fun h => (h.tag, g)
    return .branches groups

private partial def narrate (c : Ctx) (steps : List Step) (k : Sink) : IO Sink := do
  let mut k := k
  for s in steps do
    k ← narrateStep c s k
  pure k

private partial def narrateStep (c : Ctx) (s : Step) (k : Sink) : IO Sink := do
  let ph := c.ph
  let name := tacticName c s
  let args := prettyArgs ph (tacticArgs c s)
  let kind := howKind name
  match ← beforeView ph s with
  | none => pure k
  | some g =>
    let produced := s.info.goalsAfter.length + 1 - s.info.goalsBefore.length
    let after? ← if produced == 0 then pure none else afterView ph s
    let fresh := ((after?.map (·.hyps)).getD []).filter (isNew g.hyps)
    if s.kind == `Lean.calcTactic then
      return calcBlock c s k
    if s.kind == `Lean.cdot then
      let body ← narrate c s.children (stateGoal c g default)
      return k.block ph (.nested none (body.finish ph))
    match ← classify c s fresh produced with
    | .inline =>
      -- A combinator such as `first`, `all_goals` or `<;>`: the children are
      -- the proof.  When they span several goals, give each one its own block
      -- so the reader can tell which claim is being settled.
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
              -- Still the goal we were given: `t` of `t <;> t'`.
              k ← narrate c grp k
            else
              let head := match ← beforeView ph first with
                | some bg => stateGoal c bg default
                | none => default
              let body ← narrate c grp head
              k := k.block ph (.nested none (body.finish ph))
        pure k
    | .subproof => narrateSideProof c s fresh k
    | .branches groups => narrateBranching c s g (name == "induction") groups k
    | .leaf =>
    if produced == 0 then
      match reasonFor ph name args with
      | some why => pure (k.say (ph.closedBy why))
      | none =>
        -- A transformer such as `rw` or `simp` that happened to finish the goal.
        if transforms kind then pure (k.say (ph.closedByHow (ph.how kind args)))
        else pure (k.say (ph.closedBy s!"`{s.source c.input}`"))
    else if produced == 1 then
      match after? with
      | none => pure k
      | some a =>
        let (facts, objects) := fresh.partition (·.isProp)
        if !fresh.isEmpty && a.target == g.target then
          -- Facts were obtained without changing what has to be shown.
          if !objects.isEmpty then
            pure (k.say (ph.obtainFrom (objects.map (·.name))
              (facts.map fun h => { name := some h.name, stmt := h.prose })
              (originOf c s name)))
          else
            let why := (reasonFor ph name args).orElse fun _ => justification c s name
            pure (facts.foldl (fun k h =>
              k.say (ph.weHave { name := some h.name, stmt := h.prose } why)) k)
        else if !fresh.isEmpty then
          pure (stateGoal c a (announce c fresh k))
        else if a.target != g.target then
          -- Supplying a witness for an existential reads as a choice, not a rewrite.
          match (if g.targetIsExists && !a.targetIsExists then witnessOf c s else none) with
          | some w => pure ((k.say (ph.chooseWitness w)).say (ph.remainsToShow a.targetProse))
          | none => pure (k.say (ph.transformedBy (ph.how kind args) a.targetProse))
        else
          pure (k.say (ph.verbatim (s.source c.input)))
    else
      pure (k.say (ph.splitInto produced))

private partial def narrateBranching (c : Ctx) (s : Step) (g : GoalView) (isInduction : Bool)
    (branches : List (String × List Step)) (k : Sink) : IO Sink := do
  let ph := c.ph
  let subject := (majorPremise c s).getD (s.source c.input)
  let noun := (g.hyps.find? fun h => h.name == subject).bind fun h => ph.typeNoun h.head .bare
  let mut k := k.say (if isInduction then ph.inductionOn subject noun else ph.caseAnalysis subject)
  for (tag, steps) in branches do
    match steps.head? with
    | none => pure ()
    | some first =>
      match ← beforeView ph first with
      | none => pure ()
      | some bg =>
        let fresh := bg.hyps.filter (isNew g.hyps)
        let (facts, objs) := fresh.partition (·.isProp)
        let mut body : Sink := default
        if !objs.isEmpty then body := announce c objs body
        for h in facts do
          body := if isInduction then
              body.say (ph.inductionHypothesis { name := some h.name, stmt := h.prose })
            else body.say (ph.assume [{ name := some h.name, stmt := h.prose }])
        body := stateGoal c bg body
        body ← narrate c steps body
        let label :=
          if tag.isEmpty then none
          else if isInduction then
            some (if facts.isEmpty then ph.baseCaseLabel tag else ph.stepCaseLabel tag)
          else some (ph.caseLabel tag)
        k := k.block ph (.nested label (body.finish ph))
  pure k

/-- A step that introduced a fact and whose children prove it, e.g. `have := by ...`. -/
private partial def narrateSideProof (c : Ctx) (s : Step) (fresh : List HypView) (k : Sink) :
    IO Sink := do
  let ph := c.ph
  let item : Named := match fresh.head? with
    | some h => { name := some h.name, stmt := h.prose }
    | none => { stmt := ph.anonymousFact }
  let k := k.say (ph.claim item)
  let body ← narrate c s.children default
  pure (k.block ph (.nested none (body.finish ph)))

end

/-! ## Declarations -/

private def declKeyword (stx : Syntax) : String :=
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.example)).isSome then "example"
  else if (stx.find? (·.isOfKind ``Lean.Parser.Command.definition)).isSome then "def"
  else if (stx.find? (·.isOfKind ``Lean.Parser.Command.abbrev)).isSome then "abbrev"
  else "theorem"

private def declName (stx : Syntax) : Option String :=
  (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).map fun d => d[0].getId.toString

/-- Render one declaration: heading, restated statement, proof, box. -/
private def renderDeclaration (c : Ctx) (stx : Syntax) (steps : List Step) : IO (List Block) := do
  let ph := c.ph
  let mut k : Sink := default
  k := k.block ph (.heading (ph.headingTheorem (declKeyword stx) (declName stx)))
  match steps.head? with
  | none => pure (k.finish ph)
  | some first =>
    match ← beforeView ph first with
    | none => pure (k.finish ph)
    | some g =>
      if c.restate then
        if let some stmt ← statementOf ph first then
          k := k.block ph (.statement (stmt.capitalize ++ ph.period))
      k := k.block ph (.heading ph.headingProof)
      if !g.hyps.isEmpty then
        k := stateGoal c g (announce c g.hyps k)
      k ← narrate c steps k
      k := k.block ph (.qed ph.qed)
      pure (k.finish ph)

/-- Find each declaration in a tree, together with the steps of its proof. -/
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

/-- Render every declaration of an elaborated file. -/
def renderElaborated (e : Elaborated) (opts : Options := {}) : IO (List Block) := do
  let c : Ctx := { ph := phrasesFor opts.lang, input := e.input, restate := opts.statement }
  let mut out : List Block := []
  for (stx, steps) in e.trees.flatMap declarationsOf do
    out := out ++ (← renderDeclaration c stx steps)
  pure out

/-- Elaborate `path` and print its proofs. -/
def printFile (path : System.FilePath) (opts : Options := {}) : IO String := do
  let e ← elaborateFile path
  let blocks ← renderElaborated e opts
  pure (renderBlocks opts.format opts.width blocks)

end HPrint
