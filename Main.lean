import HPrint

/-!
Command line entry point.

hprint elaborates the files it is given, so it needs to be able to find their
imports.  Run it inside a Lake project (`lake env hprint Foo.lean`) when the
proofs depend on a library.
-/

open HPrint

private def version := "0.1.0"

private def usage : String :=
s!"hprint {version} — print Lean 4 proofs the way a human would write them

USAGE:
  hprint [OPTIONS] FILE...

OPTIONS:
  -l, --lang <en|ja>                  Output language               (default: en)
  -f, --format <text|markdown|latex>  Output format                 (default: text)
  -w, --width <n>                     Line width for text output    (default: 76)
      --no-statement                  Omit the restated theorem
  -h, --help                          Show this help
  -V, --version                       Show the version

hprint runs Lean's own elaborator over each FILE, so a proof that uses a
library must be printed from inside that library's Lake project:

  lake env hprint MyProject/Basic.lean
"

private structure Args where
  files : List String := []
  opts : Options := {}
  help : Bool := false
  showVersion : Bool := false

private def parseArgs (argv : List String) : Except String Args :=
  go argv {}
where
  go : List String → Args → Except String Args
  | [], acc => .ok { acc with files := acc.files.reverse }
  | a :: rest, acc =>
    let needValue (k : String → Args → Except String Args) : Except String Args :=
      match rest with
      | v :: rest' => (k v acc).bind fun acc' => go rest' acc'
      | [] => .error s!"missing value for {a}"
    match a with
    | "-h" | "--help" => .ok { acc with help := true }
    | "-V" | "--version" => .ok { acc with showVersion := true }
    | "-l" | "--lang" => needValue fun v acc =>
        .ok { acc with opts := { acc.opts with lang := v } }
    | "-f" | "--format" => needValue fun v acc =>
        match v with
        | "text" => .ok { acc with opts := { acc.opts with format := .text } }
        | "markdown" => .ok { acc with opts := { acc.opts with format := .markdown } }
        | "latex" => .ok { acc with opts := { acc.opts with format := .latex } }
        | _ => .error s!"unknown format: {v} (expected text, markdown or latex)"
    | "-w" | "--width" => needValue fun v acc =>
        match v.toNat? with
        | some n => if n < 20 then .error s!"invalid width: {v}"
                    else .ok { acc with opts := { acc.opts with width := n } }
        | none => .error s!"invalid width: {v}"
    | "--no-statement" => go rest { acc with opts := { acc.opts with statement := false } }
    | _ =>
      if a.startsWith "-" && a != "-" then .error s!"unknown option: {a}"
      else go rest { acc with files := a :: acc.files }

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error e =>
    IO.eprintln s!"hprint: {e}"
    IO.eprintln "Try 'hprint --help'."
    pure 2
  | .ok args =>
    if args.help then IO.println usage; return 0
    if args.showVersion then IO.println version; return 0
    if args.files.isEmpty then
      IO.eprintln "hprint: no input files"
      IO.eprintln "Try 'hprint --help'."
      return 2
    Lean.initSearchPath (← Lean.findSysroot)
    let mut status : UInt32 := 0
    let mut first := true
    for file in args.files do
      unless first do IO.println ""
      first := false
      let e ← elaborateFile file
      -- Elaboration errors mean the goals we would narrate are not the real
      -- ones, so say so rather than printing a confident but wrong proof.
      for (isError, msg) in e.messages do
        if isError then
          IO.eprintln s!"hprint: {file}: {msg}"
          status := 1
      let blocks ← renderElaborated e args.opts
      IO.print (renderBlocks args.opts.format args.opts.width blocks)
    pure status
