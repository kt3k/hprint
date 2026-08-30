namespace HPrint

inductive NounForm where

  | article
  | bare
  | plural
  deriving Inhabited, DecidableEq

inductive HowKind where
  | rewrite
  | simplify
  | unfold
  | apply
  | other (name : String)
  deriving Inhabited

structure Named where
  name : Option String := none
  stmt : String
  deriving Inhabited

structure FixGroup where
  names : List String
  noun : Option String := none
  type : Option String := none
  deriving Inhabited

structure Phrases where

  joiner : String
  period : String
  list : List String → String
  headingTheorem : String → Option String → String
  headingProof : String
  qed : String
  fix : List FixGroup → String
  assume : List Named → String
  mustShow : String → String
  mustShowFalse : String
  remainsToShow : String → String
  weHave : Named → Option String → String
  claim : Named → String
  inductionOn : String → Option String → String
  caseAnalysis : String → String
  caseLabel : String → String
  baseCaseLabel : String → String
  stepCaseLabel : String → String
  inductionHypothesis : Named → String
  splitInto : Nat → String
  chooseWitness : String → String
  obtainFrom : List String → List Named → Option String → String
  closedBy : String → String
  closedByHow : String → String
  reasons : List (String × String)
  how : HowKind → Option String → String
  transformedBy : String → String → String
  computation : String
  justification : String → String
  verbatim : String → String
  typeNoun : String → NounForm → Option String
  sForall : String → String → String
  sIf : List String → String → String
  sExists : String → String → String
  sSubject : List String → Option String → String
  anonymousFact : String

private def joinEn (items : List String) : String :=
  match items with
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | _ => String.intercalate ", " items.dropLast ++ " and " ++ items.getLast!

private def labelEn (n : Named) : String :=
  match n.name with
  | some nm => s!"{n.stmt} (call this {nm})"
  | none => n.stmt

private def nounsEn : List (String × (String × String × String)) :=
  [ ("Nat", ("a natural number", "natural number", "natural numbers")),
    ("Int", ("an integer", "integer", "integers")),
    ("Rat", ("a rational number", "rational number", "rational numbers")),
    ("Real", ("a real number", "real number", "real numbers")),
    ("Complex", ("a complex number", "complex number", "complex numbers")),
    ("Bool", ("a boolean", "boolean", "booleans")),
    ("Prop", ("a proposition", "proposition", "propositions")),
    ("Type", ("a type", "type", "types")),
    ("Sort", ("a type", "type", "types")),
    ("List", ("a list", "list", "lists")),
    ("Array", ("an array", "array", "arrays")),
    ("Set", ("a set", "set", "sets")),
    ("Finset", ("a finite set", "finite set", "finite sets")),
    ("String", ("a string", "string", "strings")),
    ("Char", ("a character", "character", "characters")),
    ("Fin", ("a bounded natural number", "bounded natural number", "bounded natural numbers")) ]

private def reasonsEn : List (String × String) :=
  [ ("omega", "linear arithmetic"),
    ("decide", "a decision procedure"),
    ("native_decide", "a direct computation"),
    ("rfl", "reflexivity"),
    ("trivial", "triviality"),
    ("assumption", "one of our assumptions"),
    ("simp", "simplification"),
    ("simp_all", "simplification of everything in sight"),
    ("dsimp", "definitional simplification"),
    ("linarith", "linear arithmetic"),
    ("nlinarith", "nonlinear arithmetic"),
    ("positivity", "positivity of the expression"),
    ("ring", "expanding both sides as polynomials"),
    ("ring_nf", "normalising both sides as polynomials"),
    ("norm_num", "a numerical computation"),
    ("norm_cast", "normalising the coercions"),
    ("push_cast", "pushing the coercions inwards"),
    ("exact_mod_cast", "the same statement up to coercions"),
    ("tauto", "propositional reasoning"),
    ("contradiction", "the assumptions being contradictory"),
    ("aesop", "routine reasoning"),
    ("bv_decide", "a bit-vector decision procedure") ]

def en : Phrases where
  joiner := " "
  period := "."
  list := joinEn
  headingTheorem kw name :=
    let head :=
      if kw == "lemma" then "Lemma"
      else if kw == "example" then "Example"
      else if kw == "def" then "Definition"
      else "Theorem"
    match name with
    | some n => s!"{head} ({n})."
    | none => s!"{head}."
  headingProof := "Proof."
  qed := "∎"
  fix groups :=
    let parts := groups.map fun g =>
      match g.noun, g.type with
      | some n, _ => s!"{joinEn g.names} be {n}"
      | none, some t => s!"{joinEn g.names} : {t}"
      | none, none => joinEn g.names
    let named := groups.any fun g => g.noun.isSome || g.type.isSome
    if named then s!"Let {joinEn parts}." else s!"Fix {joinEn parts}."
  assume items :=
    if items.isEmpty then "" else s!"Assume {joinEn (items.map labelEn)}."
  mustShow stmt := s!"We must show that {stmt}."
  mustShowFalse := "We must derive a contradiction."
  remainsToShow stmt := s!"It remains to show that {stmt}."
  weHave item r :=
    match r with
    | some r => s!"By {r}, we have {labelEn item}."
    | none => s!"We have {labelEn item}."
  claim item := s!"We claim that {labelEn item}."
  inductionOn subject noun :=
    match noun with
    | some n => s!"We argue by induction on the {n} {subject}."
    | none => s!"We argue by induction on {subject}."
  caseAnalysis subject := s!"We distinguish cases according to {subject}."
  caseLabel d := s!"Case {d}."
  baseCaseLabel d := s!"Base case ({d})."
  stepCaseLabel d := s!"Inductive step ({d})."
  inductionHypothesis item :=
    match item.name with
    | some n => s!"By the induction hypothesis {n} we may assume that {item.stmt}."
    | none => s!"By the induction hypothesis we may assume that {item.stmt}."
  splitInto n :=
    if n == 2 then "We prove the two parts in turn."
    else s!"This leaves {n} things to prove."
  chooseWitness w := s!"Take {w} as the witness."
  obtainFrom objects facts source :=
    let from_ := match source with
      | some s => s!"From {s} we obtain "
      | none => "We obtain "
    if objects.isEmpty then s!"{from_}{joinEn (facts.map labelEn)}."
    else
      let such := if facts.isEmpty then ""
        else s!" such that {joinEn (facts.map (·.stmt))}"
      s!"{from_}{joinEn objects}{such}."
  closedBy r := s!"This holds by {r}."
  closedByHow how := s!"{how}, we are done."
  reasons := reasonsEn
  how kind args :=
    let with_ := match args with | some a => s!" {a}" | none => ""
    match kind with
    | .rewrite => s!"Rewriting with{with_}"
    | .simplify => "Simplifying"
    | .unfold => s!"Unfolding{with_}"
    | .apply => s!"By{with_}"
    | .other name => s!"By `{name}{with_}`"
  transformedBy how goal := s!"{how}, it remains to show that {goal}."
  computation := "We compute:"
  justification r := s!"by {r}"
  verbatim t := s!"In Lean: `{t}`."
  typeNoun head form :=
    match List.lookup head nounsEn with
    | some (a, b, p) => some (match form with | .article => a | .bare => b | .plural => p)
    | none => none
  sForall subject body := s!"for all {subject}, {body}"
  sIf premises concl := s!"if {joinEn premises}, then {concl}"
  sExists subject body := s!"there is {subject} such that {body}"
  sSubject names noun :=
    match noun with
    | some n => s!"{n} {joinEn names}"
    | none => joinEn names
  anonymousFact := "this"

end HPrint
