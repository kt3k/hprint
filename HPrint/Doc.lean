/-!
# Output documents

The renderer produces a tree of `Block`s; the writers here turn that tree into
plain text, Markdown or LaTeX.  Keeping them apart means the prose logic never
has to think about indentation or escaping.
-/

namespace HPrint

/-- One line of a displayed computation (`calc`). -/
structure CalcLine where
  /-- Empty on continuation lines, which line up under the previous result. -/
  lhs : String := ""
  op : String
  rhs : String
  reason : Option String := none
  deriving Inhabited, Repr

inductive Block where
  | heading (text : String)
  /-- The restated theorem, set off from the proof. -/
  | statement (text : String)
  | para (text : String)
  /-- An indented sub-proof: a case, a bullet, the proof of a `have`. -/
  | nested (title : Option String) (body : List Block)
  | calcBlock (lines : List CalcLine)
  /-- The end-of-proof marker. -/
  | qed (text : String)
  deriving Inhabited, Repr

/-! ## Widths and wrapping -/

/-- East Asian wide characters occupy two terminal columns. -/
def isWide (c : Char) : Bool :=
  let v := c.toNat
  (0x1100 ≤ v && v ≤ 0x115F) ||
  (0x2E80 ≤ v && v ≤ 0xA4CF) ||
  (0xAC00 ≤ v && v ≤ 0xD7A3) ||
  (0xF900 ≤ v && v ≤ 0xFAFF) ||
  (0xFE30 ≤ v && v ≤ 0xFE6F) ||
  (0xFF00 ≤ v && v ≤ 0xFF60) ||
  (0xFFE0 ≤ v && v ≤ 0xFFE6) ||
  (0x20000 ≤ v && v ≤ 0x3FFFD)

/-- Display width in terminal columns. -/
def dispWidth (s : String) : Nat :=
  s.foldl (fun n c => n + if isWide c then 2 else 1) 0

/-- Japanese punctuation that must not start a line. -/
def isClosing (c : Char) : Bool :=
  "。、）」』】〉》，．".any (· == c)

/--
Split `s` into pieces after which a line break is allowed: after a space, and
between wide characters, which is what wrapping Japanese prose needs.
-/
def segments (s : String) : List String :=
  let rec go (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] => if cur.isEmpty then acc.reverse else (String.mk cur.reverse :: acc).reverse
    | c :: rest =>
      let cur := c :: cur
      let breakable :=
        c == ' ' || (isWide c && !(rest.head?.map isClosing |>.getD true))
      if breakable then go rest [] (String.mk cur.reverse :: acc)
      else go rest cur acc
  go s.toList [] []

/-- Wrap `text` to at most `max` display columns. -/
def wrapText (text : String) (max : Nat) : List String :=
  let step := fun (acc : List String × String) (chunk : String) =>
    let (lines, cur) := acc
    if cur.isEmpty && chunk.trim.isEmpty then (lines, cur)
    else if dispWidth cur + dispWidth chunk > max && !cur.isEmpty then
      (cur.trimRight :: lines, chunk.trimLeft)
    else (lines, cur ++ chunk)
  let (lines, cur) := (segments text).foldl step ([], "")
  let lines := if cur.trim.isEmpty then lines else cur.trimRight :: lines
  match lines.reverse with
  | [] => [""]
  | ls => ls

/-! ## Writers -/

private def indent (n : Nat) : String := String.mk (List.replicate n ' ')

private def padTo (s : String) (n : Nat) : String :=
  s ++ indent (n - dispWidth s)

/-- Lay a computation out with its relation symbols aligned. -/
private def calcLines (ls : List CalcLine) (pad : String) : List String :=
  let lhsW := ls.foldl (fun n l => Nat.max n (dispWidth l.lhs)) 0
  let opW := ls.foldl (fun n l => Nat.max n (dispWidth l.op)) 0
  ls.map fun l =>
    let reason := match l.reason with | some r => "    " ++ r | none => ""
    (pad ++ padTo l.lhs lhsW ++ " " ++ padTo l.op opW ++ " " ++ l.rhs ++ reason).trimRight

private partial def textOf (bs : List Block) (depth width : Nat) : List String :=
  bs.flatMap fun b =>
    let pad := indent (2 * depth)
    match b with
    | .heading t => ["", pad ++ t]
    | .statement t => (wrapText t (width - 2 * depth - 2)).map (pad ++ "  " ++ ·) ++ [""]
    | .para t => (wrapText t (width - 2 * depth)).map (pad ++ ·)
    | .calcBlock ls => calcLines ls (pad ++ "  ")
    | .qed t => ["", pad ++ t]
    | .nested title body =>
      [""] ++ (match title with | some t => [pad ++ t] | none => [])
        ++ textOf body (depth + 1) width ++ [""]

private def squeeze (ls : List String) : List String :=
  ls.foldr (fun l acc =>
    match acc with
    | a :: _ => if l.isEmpty && a.isEmpty then acc else l :: acc
    | [] => if l.isEmpty then [] else [l]) []

def toText (bs : List Block) (width : Nat := 76) : String :=
  let ls := squeeze (textOf bs 0 width)
  let ls := match ls with | "" :: rest => rest | _ => ls
  String.intercalate "\n" ls ++ "\n"

private partial def markdownOf (bs : List Block) (depth : Nat) : List String :=
  bs.flatMap fun b =>
    let pad := indent (2 * depth)
    match b with
    | .heading t => ["", pad ++ "**" ++ t ++ "**", ""]
    | .statement t => [pad ++ "> " ++ t, ""]
    | .para t => [pad ++ t, ""]
    | .qed t => ["", pad ++ t, ""]
    | .calcBlock ls => [pad ++ "```"] ++ calcLines ls pad ++ [pad ++ "```", ""]
    | .nested title body =>
      (match title with | some t => [pad ++ "- **" ++ t ++ "**", ""] | none => [])
        ++ markdownOf body (depth + 1)

def toMarkdown (bs : List Block) : String :=
  let ls := squeeze (markdownOf bs 0)
  let ls := match ls with | "" :: rest => rest | _ => ls
  String.intercalate "\n" ls ++ "\n"

private def escapeTex (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '\\' => "\\textbackslash{}"
      | '&' => "\\&" | '%' => "\\%" | '$' => "\\$" | '#' => "\\#"
      | '_' => "\\_" | '{' => "\\{" | '}' => "\\}"
      | '~' => "\\textasciitilde{}" | '^' => "\\textasciicircum{}"
      | c => c.toString) ""

private partial def latexOf (bs : List Block) : List String :=
  match bs with
  | [] => []
  | .nested _ _ :: _ =>
    -- Consecutive cases belong in one list.
    let (cases, rest) := bs.span fun b => match b with | .nested _ _ => true | _ => false
    ["\\begin{itemize}"] ++ cases.flatMap (fun b =>
      match b with
      | .nested title body =>
        ["\\item " ++ (match title with | some t => "\\textbf{" ++ escapeTex t ++ "}" | none => "")]
          ++ latexOf body
      | _ => []) ++ ["\\end{itemize}"] ++ latexOf rest
  | b :: rest =>
    (match b with
     | .heading t => ["", "\\paragraph{" ++ escapeTex t ++ "}"]
     | .statement t => ["\\begin{quote}" ++ escapeTex t ++ "\\end{quote}"]
     | .para t => [escapeTex t, ""]
     | .qed _ => ["\\hfill$\\square$"]
     | .calcBlock ls =>
       ["\\begin{align*}"] ++ ls.map (fun l =>
         let reason := match l.reason with
           | some r => " && \\text{" ++ escapeTex r ++ "}"
           | none => ""
         "  " ++ escapeTex l.lhs ++ " &" ++ escapeTex l.op ++ " " ++ escapeTex l.rhs
           ++ reason ++ " \\\\") ++ ["\\end{align*}"]
     | .nested _ _ => []) ++ latexOf rest

def toLatex (bs : List Block) : String :=
  let ls := squeeze (latexOf bs)
  let ls := match ls with | "" :: rest => rest | _ => ls
  String.intercalate "\n" ls ++ "\n"

inductive OutFormat where
  | text | markdown | latex
  deriving Inhabited, DecidableEq

def renderBlocks (fmt : OutFormat) (width : Nat) (bs : List Block) : String :=
  match fmt with
  | .text => toText bs width
  | .markdown => toMarkdown bs
  | .latex => toLatex bs

end HPrint
