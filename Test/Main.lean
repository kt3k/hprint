import HPrint

open HPrint

private structure Report where
  passed : Nat := 0
  failed : Array String := #[]

private def Report.check (r : Report) (name : String) (ok : Bool) : Report :=
  if ok then { r with passed := r.passed + 1 } else { r with failed := r.failed.push name }

private def Report.eq [BEq α] [ToString α] (r : Report) (name : String) (actual expected : α) :
    Report :=
  r.check s!"{name}: got {actual}, expected {expected}" (actual == expected)

private def unitChecks : Report :=
  let r : Report := {}
  let r := r.eq "dispWidth latin" (dispWidth "abc") 3
  let r := r.eq "dispWidth wide" (dispWidth "自然数") 6
  let r := r.eq "wrap breaks on spaces" (wrapText "one two three four" 9)
      ["one two", "three", "four"]
  let jp := wrapText "自然数について帰納法で示す。" 10
  let r := r.check "wrap japanese respects width" (jp.all fun l => dispWidth l ≤ 10)
  let r := r.check "wrap japanese never orphans punctuation"
      (jp.all fun l => !((l.toList.head?.map isClosing).getD false))
  let sample : List Block :=
    [ .heading "Theorem.", .statement "Every n satisfies P n.", .para "Let n be a natural number.",
      .nested (some "Base case.") [.para "Immediate."],
      .calcBlock [{ lhs := "a", op := "=", rhs := "b", reason := some "by h" },
                  { op := "=", rhs := "c" }],
      .qed "∎" ]
  let text := toText sample 60
  let r := r.check "text indents nested blocks" ((text.splitOn "\n  Immediate.").length == 2)
  let r := r.check "text aligns calc" ((text.splitOn "  a = b    by h").length == 2)
  let md := toMarkdown sample
  let r := r.check "markdown bolds headings" ((md.splitOn "**Theorem.**").length == 2)
  let r := r.check "markdown quotes the statement"
      ((md.splitOn "> Every n satisfies P n.").length == 2)
  let tex := toLatex sample
  let r := r.check "latex escapes and boxes"
      ((tex.splitOn "\\hfill$\\square$").length == 2)
  let tex2 := toLatex [.nested (some "One.") [], .nested (some "Two.") []]
  let r := r.check "latex groups consecutive cases"
      ((tex2.splitOn "\\begin{itemize}").length == 2)
  r

private def goldenPath (base : String) : System.FilePath :=
  System.mkFilePath ["test", "golden", s!"{base}.txt"]

private def exampleFiles : IO (Array System.FilePath) := do
  let entries ← System.FilePath.readDir "examples"
  let files := entries.filterMap fun e =>
    if e.path.extension == some "lean" then some e.path else none
  pure (files.qsort fun a b => a.toString < b.toString)

private def goldenChecks (update : Bool) (r : Report) : IO Report := do
  let mut r := r
  for file in ← exampleFiles do
    let base := (file.fileStem).getD "?"
    let e ← elaborateFile file
    let errors := e.errors
    r := r.check s!"{base} elaborates without errors" errors.isEmpty
    for msg in errors do
      IO.eprintln s!"  {base}: {msg}"
    let blocks ← renderElaborated e { width := 76 }
    let actual := renderBlocks .text 76 blocks
    r := r.check s!"{base} produces a proof" ((actual.splitOn "∎").length ≥ 2)
    for line in actual.splitOn "\n" do
      if dispWidth line > 76 then
        r := r.check s!"{base} line too wide: {line}" false
    let path := goldenPath base
    if update then
      IO.FS.writeFile path actual
    else if ← path.pathExists then
      let expected ← IO.FS.readFile path
      if actual != expected then
        IO.eprintln s!"--- {path} differs; rerun with `lake test -- --update` to accept"
        IO.eprintln actual
        r := r.check s!"{base} matches golden output" false
      else r := r.check s!"{base} matches golden output" true
    else
      IO.eprintln s!"missing golden file {path}; run `lake test -- --update`"
      r := r.check s!"{base} has a golden file" false
  pure r

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let update := args.contains "--update"
  let r ← goldenChecks update unitChecks
  for f in r.failed do IO.eprintln s!"FAIL {f}"
  IO.println s!"{r.passed} passed, {r.failed.size} failed"
  pure (if r.failed.isEmpty then 0 else 1)
