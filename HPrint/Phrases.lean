module



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

def joinEn (items : List String) : String :=
  match items with
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | _ => String.intercalate ", " items.dropLast ++ " and " ++ items.getLast!

def labelEn (n : Named) : String :=
  match n.name with
  | some nm => s!"{n.stmt} (call this {nm})"
  | none => n.stmt

def nounsEn : List (String × (String × String × String)) :=
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

def reasonsEn : List (String × String) :=
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

namespace Phrases

def joiner : String := " "
def period : String := "."
def list : List String → String := joinEn

def headingTheorem (kw : String) (name : Option String) : String :=
  let head :=
    if kw == "lemma" then "Lemma"
    else if kw == "example" then "Example"
    else if kw == "def" then "Definition"
    else "Theorem"
  match name with
  | some n => s!"{head} ({n})."
  | none => s!"{head}."

def headingProof : String := "Proof."
def qed : String := "∎"

def fix (groups : List FixGroup) : String :=
  let parts := groups.map fun g =>
    match g.noun, g.type with
    | some n, _ => s!"{joinEn g.names} be {n}"
    | none, some t => s!"{joinEn g.names} : {t}"
    | none, none => joinEn g.names
  let named := groups.any fun g => g.noun.isSome || g.type.isSome
  if named then s!"Let {joinEn parts}." else s!"Fix {joinEn parts}."

def assume (items : List Named) : String :=
  if items.isEmpty then "" else s!"Assume {joinEn (items.map labelEn)}."

def mustShow (stmt : String) : String := s!"We must show that {stmt}."
def mustShowFalse : String := "We must derive a contradiction."
def remainsToShow (stmt : String) : String := s!"It remains to show that {stmt}."

def weHave (item : Named) (reason : Option String) : String :=
  match reason with
  | some r => s!"By {r}, we have {labelEn item}."
  | none => s!"We have {labelEn item}."

def claim (item : Named) : String := s!"We claim that {labelEn item}."

def inductionOn (subject : String) (noun : Option String) : String :=
  match noun with
  | some n => s!"We argue by induction on the {n} {subject}."
  | none => s!"We argue by induction on {subject}."

def caseAnalysis (subject : String) : String :=
  s!"We distinguish cases according to {subject}."
def caseLabel (d : String) : String := s!"Case {d}."
def baseCaseLabel (d : String) : String := s!"Base case ({d})."
def stepCaseLabel (d : String) : String := s!"Inductive step ({d})."

def inductionHypothesis (item : Named) : String :=
  match item.name with
  | some n => s!"By the induction hypothesis {n} we may assume that {item.stmt}."
  | none => s!"By the induction hypothesis we may assume that {item.stmt}."

def splitInto (n : Nat) : String :=
  if n == 2 then "We prove the two parts in turn."
  else s!"This leaves {n} things to prove."

def chooseWitness (w : String) : String := s!"Take {w} as the witness."

def obtainFrom (objects : List String) (facts : List Named) (source : Option String) : String :=
  let from_ := match source with
    | some s => s!"From {s} we obtain "
    | none => "We obtain "
  if objects.isEmpty then s!"{from_}{joinEn (facts.map labelEn)}."
  else
    let such := if facts.isEmpty then ""
      else s!" such that {joinEn (facts.map (·.stmt))}"
    s!"{from_}{joinEn objects}{such}."

def closedBy (reason : String) : String := s!"This holds by {reason}."
def closedByHow (how : String) : String := s!"{how}, we are done."
def reasons : List (String × String) := reasonsEn

def how (kind : HowKind) (args : Option String) : String :=
  let with_ := match args with | some a => s!" {a}" | none => ""
  match kind with
  | .rewrite => s!"Rewriting with{with_}"
  | .simplify => "Simplifying"
  | .unfold => s!"Unfolding{with_}"
  | .apply => s!"By{with_}"
  | .other name => s!"By `{name}{with_}`"

def transformedBy (how goal : String) : String :=
  s!"{how}, it remains to show that {goal}."

def computation : String := "We compute:"
def justification (reason : String) : String := s!"by {reason}"
def verbatim (text : String) : String := s!"In Lean: `{text}`."

def typeNoun (head : String) (form : NounForm) : Option String :=
  match List.lookup head nounsEn with
  | some (a, b, p) => some (match form with | .article => a | .bare => b | .plural => p)
  | none => none

def sForall (subject body : String) : String := s!"for all {subject}, {body}"
def sIf (premises : List String) (concl : String) : String :=
  s!"if {joinEn premises}, then {concl}"
def sExists (subject body : String) : String := s!"there is {subject} such that {body}"
def sSubject (names : List String) (noun : Option String) : String :=
  match noun with
  | some n => s!"{n} {joinEn names}"
  | none => joinEn names

def anonymousFact : String := "this"

end Phrases

end HPrint
