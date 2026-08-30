/-!
# The vocabulary a proof is written in

The renderer never concatenates prose itself; it asks a `Phrases` for every
sentence.  Adding a language is therefore one value of this structure, not a
change to the proof-walking code.
-/

namespace HPrint

/-- Which grammatical form of a type noun a sentence needs. -/
inductive NounForm where
  /-- "a natural number" -/
  | article
  /-- "natural number" -/
  | bare
  /-- "natural numbers" -/
  | plural
  deriving Inhabited, DecidableEq

/-- A named statement: a hypothesis together with what it says. -/
structure Named where
  name : Option String := none
  stmt : String
  deriving Inhabited

/-- A group of objects introduced together: `n m : Nat`. -/
structure FixGroup where
  names : List String
  /-- A noun phrase for the type, when one is known. -/
  noun : Option String := none
  /-- The type as Lean prints it, used when no noun phrase is known. -/
  type : Option String := none
  deriving Inhabited

structure Phrases where
  id : String
  /-- Inserted between consecutive sentences of a paragraph. -/
  joiner : String
  /-- Sentence-final punctuation. -/
  period : String
  list : List String → String

  headingTheorem : String → Option String → String
  headingProof : String
  qed : String

  /-- "Let n and m be natural numbers." -/
  fix : List FixGroup → String
  /-- "Assume p ∧ q (call this h)." -/
  assume : List Named → String
  /-- "We must show that P." -/
  mustShow : String → String
  /-- Said instead of `mustShow` when the goal is `False`. -/
  mustShowFalse : String
  /-- "It remains to show that P." -/
  remainsToShow : String → String
  /-- "By h, we have P (call this k)." -/
  weHave : Named → Option String → String
  /-- "We claim that P (call this h)." -/
  claim : Named → String

  /-- "We argue by induction on the natural number n." -/
  inductionOn : String → Option String → String
  /-- "We distinguish cases according to the shape of h." -/
  caseAnalysis : String → String
  caseLabel : String → String
  baseCaseLabel : String → String
  stepCaseLabel : String → String
  /-- "By the induction hypothesis ih we may assume that P." -/
  inductionHypothesis : Named → String
  /-- "This leaves two things to prove." -/
  splitInto : Nat → String

  /-- "Take n + 1 as the witness." -/
  chooseWitness : List String → String
  /-- "From h we obtain k such that n = 2 * k." -/
  obtainFrom : List String → List Named → Option String → String

  /-- "This holds by linear arithmetic." -/
  closedBy : String → String
  /-- "Rewriting with h, we are done." -/
  closedByHow : String → String
  /--
  A reason phrase for a tactic that finished or transformed a goal, e.g.
  `omega` becomes "linear arithmetic".  `none` when we have nothing better
  to say than the tactic's own name.
  -/
  reason : String → Option String → Option String
  /-- How a tactic changed the goal: "Rewriting with h", "Simplifying". -/
  how : String → Option String → String
  /-- "Rewriting with h, it remains to show that P." -/
  transformedBy : String → String → String
  /-- Header for a displayed computation. -/
  computation : String
  /-- The justification written beside one line of a computation. -/
  justification : String → String
  /-- A step we could not interpret; the Lean text is quoted. -/
  verbatim : String → String
  done : String

  typeNoun : String → NounForm → Option String
  /-- "for all natural numbers n and m, <body>" -/
  sForall : String → String → String
  /-- "if A, B and C, then D" -/
  sIf : List String → String → String
  /-- "there is a natural number n such that <body>" -/
  sExists : String → String → String
  /-- "natural numbers n and m" -/
  sSubject : List String → Option String → String
  anonymousFact : String

/-! ## English -/

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
  id := "en"
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

  chooseWitness vs :=
    if vs.length == 1 then s!"Take {joinEn vs} as the witness."
    else s!"Take {joinEn vs} as the witnesses."

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
  reason name args :=
    match List.lookup name reasonsEn with
    | some r => some r
    | none =>
      if name == "exact" || name == "apply" then args
      else none
  how name args :=
    let with_ := match args with | some a => s!" {a}" | none => ""
    if name == "rw" || name == "rewrite" || name == "erw" then
      s!"Rewriting with{with_}"
    else if name.startsWith "simp" || name == "dsimp" then "Simplifying"
    else if name == "unfold" || name == "delta" then s!"Unfolding{with_}"
    else if name == "refine" || name == "apply" || name == "exact" then
      s!"By{with_}"
    else s!"By `{name}{with_}`"
  transformedBy how goal := s!"{how}, it remains to show that {goal}."
  computation := "We compute:"
  justification r := s!"by {r}"
  verbatim t := s!"In Lean: `{t}`."
  done := "This completes the argument."

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

/-! ## Japanese -/

private def joinJa (items : List String) : String :=
  match items with
  | [] => ""
  | [a] => a
  | _ => String.intercalate "、" items.dropLast ++ "、および " ++ items.getLast!

private def labelJa (n : Named) : String :=
  match n.name with
  | some nm => s!"{n.stmt}（これを {nm} とおく）"
  | none => n.stmt

private def isJapanese (c : Char) : Bool :=
  let v := c.toNat
  (0x3040 ≤ v && v ≤ 0x30FF) || (0x4E00 ≤ v && v ≤ 0x9FFF) || "）」』（「『、。".any (· == c)

/-- Latin formulas need a space before the following particle; Japanese text does not. -/
private def glue (s : String) : String :=
  match s.toList.getLast? with
  | some c => if isJapanese c then "" else " "
  | none => " "

/-- The same, for the space *before* an interpolated fragment. -/
private def glueBefore (s : String) : String :=
  match s.toList.head? with
  | some c => if isJapanese c then "" else " "
  | none => ""

/--
Turn a statement into something a `〜こと` clause can attach to, so that
"…が存在する" becomes "…が存在すること" while "n + 0 = n" is left alone.
-/
private def nominalize (s : String) : String :=
  if glue s == "" then s ++ "こと" else s

private def nounsJa : List (String × String) :=
  [ ("Nat", "自然数"), ("Int", "整数"), ("Rat", "有理数"), ("Real", "実数"),
    ("Complex", "複素数"), ("Bool", "真理値"), ("Prop", "命題"), ("Type", "型"),
    ("Sort", "型"), ("List", "リスト"), ("Array", "配列"), ("Set", "集合"),
    ("Finset", "有限集合"), ("String", "文字列"), ("Char", "文字"),
    ("Fin", "有界自然数") ]

private def reasonsJa : List (String × String) :=
  [ ("omega", "線形算術"), ("decide", "決定手続き"), ("native_decide", "直接計算"),
    ("rfl", "両辺が同一であること"), ("trivial", "自明であること"),
    ("assumption", "仮定そのもの"), ("simp", "簡約"), ("simp_all", "全体の簡約"),
    ("dsimp", "定義的簡約"), ("linarith", "線形算術"), ("nlinarith", "非線形算術"),
    ("positivity", "式の正値性"), ("ring", "両辺を多項式として展開すること"),
    ("ring_nf", "両辺の正規化"), ("norm_num", "数値計算"),
    ("norm_cast", "型強制の整理"), ("push_cast", "型強制を内側に押し込むこと"),
    ("exact_mod_cast", "型強制を除いて同一であること"), ("tauto", "命題論理の推論"),
    ("contradiction", "仮定の矛盾"), ("aesop", "定型的な推論"),
    ("bv_decide", "ビットベクトルの決定手続き") ]

def ja : Phrases where
  id := "ja"
  joiner := ""
  period := "。"
  list := joinJa

  headingTheorem kw name :=
    let head :=
      if kw == "lemma" then "補題"
      else if kw == "example" then "例"
      else if kw == "def" then "定義"
      else "定理"
    match name with
    | some n => s!"{head}（{n}）."
    | none => s!"{head}."
  headingProof := "証明."
  qed := "∎"

  fix groups :=
    let parts := groups.map fun g =>
      match g.noun, g.type with
      | some n, _ => s!"{String.intercalate "、" g.names} を{n}"
      | none, some t => s!"{String.intercalate "、" g.names} を {t} の要素"
      | none, none => String.intercalate "、" g.names
    let named := groups.any fun g => g.noun.isSome || g.type.isSome
    if named then s!"{joinJa parts}とする。" else s!"{joinJa parts} を任意にとる。"

  assume items :=
    if items.isEmpty then "" else
      let body := joinJa (items.map labelJa)
      s!"{body}{glue body}と仮定する。"

  mustShow stmt :=
    let n := nominalize stmt
    s!"示すべきことは {n}{glue n}である。"
  mustShowFalse := "矛盾を導けばよい。"
  remainsToShow stmt :=
    let n := nominalize stmt
    s!"残るは {n}{glue n}を示すことである。"

  weHave item r :=
    match r with
    | some r =>
      let l := labelJa item
      s!"{r}{glue r}により {l}{glue l}が成り立つ。"
    | none =>
      let l := labelJa item
      s!"{l}{glue l}が成り立つ。"
  claim item :=
    let l := labelJa item
    s!"ここで {l}{glue l}を示す。"

  inductionOn subject noun :=
    match noun with
    | some n => s!"{n} {subject} に関する帰納法で示す。"
    | none => s!"{subject} に関する帰納法で示す。"
  caseAnalysis subject := s!"{subject} で場合分けする。"
  caseLabel d := s!"場合 {d}."
  baseCaseLabel d := s!"基底の場合（{d}）."
  stepCaseLabel d := s!"帰納段階（{d}）."
  inductionHypothesis item :=
    let n := nominalize item.stmt
    let tail := s!"{n}{glue n}が使える。"
    match item.name with
    | some nm => s!"帰納法の仮定 {nm} により {tail}"
    | none => s!"帰納法の仮定により {tail}"
  splitInto n :=
    if n == 2 then "二つの主張を順に示す。" else s!"示すべきことが {n} つ残る。"

  chooseWitness vs := s!"{joinJa vs} を取ればよい。"

  obtainFrom objects facts source :=
    let from_ := match source with | some s => s!"{s} から " | none => ""
    if objects.isEmpty then s!"{from_}{joinJa (facts.map labelJa)} が得られる。"
    else
      let such := if facts.isEmpty then ""
        else s!"{joinJa (facts.map (·.stmt))} を満たす "
      s!"{from_}{such}{joinJa objects} が得られる。"

  closedBy r := s!"これは{glueBefore r}{r}{glue r}により成り立つ。"
  closedByHow how := s!"{how}、証明が終わる。"
  reason name args :=
    match List.lookup name reasonsJa with
    | some r => some r
    | none => if name == "exact" || name == "apply" then args else none
  how name args :=
    let with_ := match args with | some a => s!"{a} " | none => ""
    if name == "rw" || name == "rewrite" || name == "erw" then s!"{with_}により書き換えると"
    else if name.startsWith "simp" || name == "dsimp" then "簡約すると"
    else if name == "unfold" || name == "delta" then s!"{with_}の定義を展開すると"
    else if name == "refine" || name == "apply" || name == "exact" then s!"{with_}により"
    else s!"`{name} {with_}` により"
  transformedBy how goal :=
    let n := nominalize goal
    s!"{how}、残るは {n}{glue n}を示すことである。"
  computation := "次のように計算する:"
  justification r := s!"（{r} による）"
  verbatim t := s!"Lean では `{t}`。"
  done := "以上で証明が完了する。"

  typeNoun head _ := List.lookup head nounsJa
  sForall subject body := s!"任意の{subject} に対して {body}"
  sIf premises concl := s!"{joinJa premises} ならば {concl}"
  sExists subject body := s!"{body} を満たす {subject} が存在する"
  sSubject names noun :=
    match noun with
    | some n => s!"{n} {String.intercalate "、" names}"
    | none => String.intercalate "、" names
  anonymousFact := "これ"

def phrasesFor (lang : String) : Phrases :=
  if lang == "ja" then ja else en

end HPrint
