module



namespace HPrint

structure CalcLine where

  lhs : String := ""
  op : String
  rhs : String
  reason : Option String := none
  deriving Inhabited

inductive Block where
  | heading (text : String)
  | statement (text : String)
  | para (text : String)
  | nested (title : Option String) (body : List Block)
  | calcBlock (lines : List CalcLine)
  | qed (text : String)
  deriving Inhabited

def indent (n : Nat) : String := "".pushn ' ' n

def padTo (s : String) (n : Nat) : String :=
  s ++ indent (n - s.length)

def calcLines (ls : List CalcLine) (pad : String) : List String :=
  let lhsW := ls.foldl (fun n l => Nat.max n l.lhs.length) 0
  let opW := ls.foldl (fun n l => Nat.max n l.op.length) 0
  ls.map fun l =>
    let reason := match l.reason with | some r => "    " ++ r | none => ""
    (pad ++ padTo l.lhs lhsW ++ " " ++ padTo l.op opW ++ " " ++ l.rhs ++ reason).trimRight

partial def textOf (bs : List Block) (depth : Nat) : List String :=
  bs.flatMap fun b =>
    let pad := indent (2 * depth)
    match b with
    | .heading t => ["", pad ++ t]
    | .statement t => [pad ++ "  " ++ t, ""]
    | .para t => [pad ++ t]
    | .calcBlock ls => calcLines ls (pad ++ "  ")
    | .qed t => ["", pad ++ t]
    | .nested title body =>
      [""] ++ (match title with | some t => [pad ++ t] | none => [])
        ++ textOf body (depth + 1) ++ [""]

def squeeze (ls : List String) : List String :=
  ls.foldr (fun l acc =>
    match acc with
    | a :: _ => if l.isEmpty && a.isEmpty then acc else l :: acc
    | [] => if l.isEmpty then [] else [l]) []

def assemble (ls : List String) : String :=
  let ls := squeeze ls
  String.intercalate "\n" (match ls with | "" :: rest => rest | _ => ls) ++ "\n"

def toText (bs : List Block) : String := assemble (textOf bs 0)

end HPrint
