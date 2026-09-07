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
  let sample : List Block :=
    [ .heading "Theorem.", .statement "Every n satisfies P n.", .para "Let n be a natural number.",
      .nested (some "Base case.") [.para "Immediate."],
      .calcBlock [{ lhs := "a", op := "=", rhs := "b", reason := some "by h" },
                  { op := "=", rhs := "c" }],
      .qed "∎" ]
  let text := toText sample
  let r := r.check "text indents nested blocks" ((text.splitOn "\n  Immediate.").length == 2)
  let r := r.check "text aligns calc" ((text.splitOn "  a = b    by h").length == 2)
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
    let e ← elaborate (← IO.FS.readFile file) file.toString
    let errors := e.errors
    r := r.check s!"{base} elaborates without errors" errors.isEmpty
    for msg in errors do
      IO.eprintln s!"  {base}: {msg}"
    let blocks ← renderElaborated e {}
    let actual := toText blocks
    r := r.check s!"{base} produces a proof" ((actual.splitOn "∎").length ≥ 2)
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
