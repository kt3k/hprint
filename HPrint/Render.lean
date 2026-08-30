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
  opts : Options

/-- Collects sentences into paragraphs so the output reads as prose. -/
private structure Sink where
  blocks : Array Block := #[]
  pending : Array String := #[]
  deriving Inhabited

namespace Sink

def say (k : Sink) (s : String) : Sink :=
  if s.trim.isEmpty then k else { k with pending := k.pending.push s.trim }

def flush (k : Sink) (ph : Phrases) : Sink :=
  if k.pending.isEmpty then k
  else { blocks := k.blocks.push (.para (String.intercalate ph.joiner k.pending.toList)),
         pending := #[] }

def block (k : Sink) (ph : Phrases) (b : Block) : Sink :=
  { k.flush ph with blocks := (k.flush ph).blocks.push b }

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

/-- Split on the top-level commas of `⟨a, b, c⟩`. -/
private def components (src : String) : List String :=
  let s := src.trim
  if !(s.startsWith "⟨") then [s] else
    let inner := (s.toList.drop 1).dropLast
    let step := fun (acc : List String × List Char × Nat) (ch : Char) =>
      let (done, cur, depth) := acc
      if ch == ',' && depth == 0 then (done ++ [String.mk cur.reverse], [], depth)
      else
        let depth :=
          if "⟨([".any (· == ch) then depth + 1
          else if "⟩)]".any (· == ch) then depth - 1
          else depth
        (done, ch :: cur, depth)
    let (done, cur, _) := inner.foldl step ([], [], 0)
    (done ++ [String.mk cur.reverse]).map (·.trim) |>.filter (!·.isEmpty)

/-- Turn `[a, b]` into a readable list, leaving anything else alone. -/
private def prettyArgs (ph : Phrases) (args : Option String) : Option String :=
  args.map fun a =>
    let a := a.trim
    if a.startsWith "[" && a.endsWith "]" then
      ph.list (((a.toList.drop 1).dropLast |> String.mk).splitOn "," |>.map (·.trim)
        |>.filter (!·.isEmpty))
    else a

/-- Source text of the tactic's first argument, e.g. `n` in `induction n with ...`. -/
private def majorPremise (c : Ctx) (s : Step) : Option String :=
  match s.stx[1].getPos?, s.stx[1].getTailPos? with
  | some a, some b =>
    let t := (Substring.mk c.input a b).toString.trim
    if t.isEmpty then none else some t
  | _, _ => none

/-! ## Introducing hypotheses -/

/-- The term a fact was obtained from: the `h` of `obtain .. := h` or `cases h`. -/
private def originOf (c : Ctx) (s : Step) (name : String) : Option String :=
  let src := s.source c.input
  match src.splitOn ":=" with
  | _ :: rest@(_ :: _) => some (String.intercalate ":=" rest).trim
  | _ => if name == "cases" || name == "rcases" || name == "obtain" then majorPremise c s
         else none

private def isNew (old : List HypView) (h : HypView) : Bool :=
  !(old.any fun o => o.name == h.name && o.type == h.type)

/-- Emit "Let ... be ..." and "Assume ..." for a batch of new hypotheses. -/
private def announce (c : Ctx) (hyps : List HypView) (k : Sink) : Sink :=
  let ph := c.ph
  let objects := hyps.filter fun h => !h.isProp
  let props := hyps.filter fun h => h.isProp
  let mk (h : HypView) (form : NounForm) : FixGroup :=
    { names := [h.name], type := some h.type, noun := ph.typeNoun h.head form }
  let groups := objects.foldl (fun (acc : List FixGroup) h =>
    match acc.reverse with
    | g :: rest =>
      if g.type == some h.type then
        ({ g with names := g.names ++ [h.name], noun := (mk h .plural).noun } :: rest).reverse
      else acc ++ [mk h .article]
    | [] => [mk h .article]) []
  let k := if groups.isEmpty then k else k.say (ph.fix groups)
  if props.isEmpty then k
  else k.say (ph.assume (props.map fun h => { name := some h.name, stmt := h.prose }))

/-- Tactics whose job is to reshape the goal rather than to justify it. -/
private def transforms (name : String) : Bool :=
  name == "rw" || name == "rewrite" || name == "erw" || name == "unfold" || name == "delta"
    || name.startsWith "simp" || name == "dsimp"

/-- The justification written after `:=`, as in `have h : P := foo`. -/
private def justification (c : Ctx) (s : Step) (name : String) : Option String :=
  if name == "have" || name == "suffices" || name == "replace" then
    match (s.source c.input).splitOn ":=" with
    | _ :: rest@(_ :: _) =>
      let t := (String.intercalate ":=" rest).trim.replace "\n" " "
      if t.isEmpty || t.startsWith "by" then none else some t
    | _ => none
  else none

/-- Every node of `stx` satisfying `p`, outermost first. -/
private partial def findAll (p : Syntax → Bool) (stx : Syntax) : List Syntax :=
  (if p stx then [stx] else []) ++ stx.getArgs.toList.flatMap (findAll p)

private def sourceOf (c : Ctx) (stx : Syntax) : String :=
  match stx.getPos?, stx.getTailPos? with
  | some a, some b => ((Substring.mk c.input a b).toString.trim).replace "\n" " "
  | _, _ => ""

/-- Relation symbols a `calc` chain may be built from, longest first. -/
private def relations : List String :=
  ["↔", "≠", "≤", "≥", "⊆", "≡", "∣", "∈", "=", "<", ">"]

/-- Split `a ≤ b` into its two sides, ignoring anything inside brackets. -/
private def splitRelation (src : String) : String × String × String :=
  let rec go (cs : List Char) (seen : List Char) (depth : Nat) : Option (String × String × String) :=
    match cs with
    | [] => none
    | ch :: rest =>
      let depth' :=
        if "(⟨[{".any (· == ch) then depth + 1
        else if ")⟩]}".any (· == ch) then depth - 1
        else depth
      let hit := if depth == 0 then relations.find? fun r => r.length == 1 && r.get 0 == ch
                 else none
      match hit with
      | some op => some (String.mk seen.reverse, op, String.mk rest)
      | none => go rest (ch :: seen) depth'
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
  | some a => (components a).head?
  | none => none

private def stateGoal (c : Ctx) (g : GoalView) (k : Sink) : Sink :=
  k.say (if g.targetIsFalse then c.ph.mustShowFalse else c.ph.mustShow g.targetProse)

/-! ## The walk -/

mutual

/--
Split a branching tactic's children into one group per branch.  A child that
works on a goal its parent never saw is the body of a branch; if every child
works on the parent's own goal there is no branching to report.
-/
private partial def branchesOf (s : Step) : IO (List (String × List Step)) := do
  if s.children.isEmpty then return []
  let parent := s.info.goalsBefore.head?
  let mut groups : List (String × List Step) := []
  for child in s.children do
    match child.info.goalsBefore.head? with
    | none => return []
    | some g =>
      if some g == parent then return []
      let tag ← child.ctx.runMetaM {} do pure (← g.getTag)
      let tag := (tag.components.getLast?.map (·.toString)).getD ""
      match groups.reverse with
      | (t, ss) :: rest =>
        if t == tag then groups := ((t, ss ++ [child]) :: rest).reverse
        else groups := groups ++ [(tag, [child])]
      | [] => groups := [(tag, [child])]
  pure groups

private partial def narrate (c : Ctx) (steps : List Step) (k : Sink) : IO Sink := do
  let mut k := k
  for s in steps do
    k ← narrateStep c s k
  pure k

private partial def narrateStep (c : Ctx) (s : Step) (k : Sink) : IO Sink := do
  let ph := c.ph
  let before ← beforeViews ph s
  let after ← afterViews ph s
  let name := tacticName c s
  let args := tacticArgs c s
  match before.head? with
  | none => pure k
  | some g =>
    let produced := after.length + 1 - before.length
    let newGoals := after.take produced
    let branches ← branchesOf s
    if s.kind == `Lean.calcTactic then
      pure (calcBlock c s k)
    else if !branches.isEmpty then
      narrateBranching c s g name branches k
    else if s.kind == `Lean.cdot then
      let body ← narrate c s.children (stateGoal c g default)
      pure (k.block ph (.nested none (body.finish ph)))
    else if !s.children.isEmpty then
      narrateHave c s g newGoals k
    else if produced == 0 then
      match ph.reason name (prettyArgs ph args) with
      | some why => pure (k.say (ph.closedBy why))
      | none =>
        -- A transformer such as `rw` or `simp` that happened to finish the goal.
        if transforms name then pure (k.say (ph.closedByHow (ph.how name (prettyArgs ph args))))
        else pure (k.say (ph.closedBy s!"`{s.source c.input}`"))
    else if produced == 1 then
      match newGoals.head? with
      | none => pure k
      | some a =>
        let fresh := a.hyps.filter (isNew g.hyps)
        let objects := fresh.filter fun h => !h.isProp
        let facts := fresh.filter fun h => h.isProp
        if !fresh.isEmpty && a.target == g.target then
          -- Facts were obtained without changing what has to be shown.
          if !objects.isEmpty then
            pure (k.say (ph.obtainFrom (objects.map (·.name))
              (facts.map fun h => { name := some h.name, stmt := h.prose })
              (originOf c s name)))
          else
            let why := (ph.reason name (prettyArgs ph args)).orElse fun _ =>
              justification c s name
            pure (facts.foldl (fun k h =>
              k.say (ph.weHave { name := some h.name, stmt := h.prose } why)) k)
        else if !fresh.isEmpty then
          pure (stateGoal c a (announce c fresh k))
        else if a.target != g.target then
          -- Supplying a witness for an existential reads as a choice, not a rewrite.
          match (if g.targetIsExists && !a.targetIsExists then witnessOf c s else none) with
          | some w => pure ((k.say (ph.chooseWitness [w])).say (ph.remainsToShow a.targetProse))
          | none => pure (k.say (ph.transformedBy (ph.how name (prettyArgs ph args))
              a.targetProse))
        else
          pure (k.say (ph.verbatim (s.source c.input)))
    else
      pure (k.say (ph.splitInto produced))

private partial def narrateBranching (c : Ctx) (s : Step) (g : GoalView) (name : String)
    (branches : List (String × List Step)) (k : Sink) : IO Sink := do
  let ph := c.ph
  let isInduction := name == "induction"
  let subject := (majorPremise c s).getD (s.source c.input)
  let noun := (g.hyps.find? fun h => h.name == subject).bind fun h => ph.typeNoun h.head .bare
  let mut k := k.say (if isInduction then ph.inductionOn subject noun else ph.caseAnalysis subject)
  for (tag, steps) in branches do
    match steps.head? with
    | none => pure ()
    | some first =>
      let bviews ← beforeViews ph first
      match bviews.head? with
      | none => pure ()
      | some bg =>
        let fresh := bg.hyps.filter (isNew g.hyps)
        let objs := fresh.filter fun h => !h.isProp
        let facts := fresh.filter fun h => h.isProp
        let mut body : Sink := default
        if !objs.isEmpty then body := announce c objs body
        for h in facts do
          body := if isInduction then
              body.say (ph.inductionHypothesis { name := some h.name, stmt := h.prose })
            else body.say (ph.assume [{ name := some h.name, stmt := h.prose }])
        body := stateGoal c bg body
        body ← narrate c steps body
        let label :=
          if isInduction then
            if facts.isEmpty then ph.baseCaseLabel tag else ph.stepCaseLabel tag
          else ph.caseLabel tag
        k := k.block ph (.nested (some label) (body.finish ph))
  pure k

private partial def narrateHave (c : Ctx) (s : Step) (g : GoalView) (newGoals : List GoalView)
    (k : Sink) : IO Sink := do
  let ph := c.ph
  let fresh := ((newGoals.head?.map (·.hyps)).getD []).filter (isNew g.hyps)
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

private def capitalize (s : String) : String :=
  match s.toList with
  | c :: rest => if c.isLower then String.mk (c.toUpper :: rest) else s
  | [] => s

/-- Render one declaration: heading, restated statement, proof, box. -/
private def renderDeclaration (c : Ctx) (stx : Syntax) (steps : List Step) : IO (List Block) := do
  let ph := c.ph
  let mut k : Sink := default
  k := k.block ph (.heading (ph.headingTheorem (declKeyword stx) (declName stx)))
  match steps.head? with
  | none => pure (k.finish ph)
  | some first =>
    let views ← beforeViews ph first
    match views.head? with
    | none => pure (k.finish ph)
    | some g =>
      if c.opts.statement then
        k := k.block ph (.statement (capitalize g.closed ++ ph.period))
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
  let c : Ctx := { ph := phrasesFor opts.lang, input := e.input, opts }
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
