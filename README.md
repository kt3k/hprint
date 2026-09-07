# hprint

A pretty printer for Lean 4 proofs that writes them out the way a person would
on paper.

Lean proofs are written for the elaborator: a stack of tactics, each one a
command. A proof in a textbook is written for a reader: sentences that fix
objects, state assumptions, name the goal, split into cases and finish with a
box. `hprint` reads the first and prints the second.

```lean
#eval do IO.print (← hprintStr (← IO.FS.readFile "examples/induction.lean"))
```

```
Theorem (zero_add').
  For all natural numbers n, 0 + n = n.

Proof.
Let n be a natural number. We must show that 0 + n = n. We argue by induction on the natural number n.

Base case (zero).
  We must show that 0 + 0 = 0. This holds by reflexivity.

Inductive step (succ).
  Let k be a natural number. By the induction hypothesis ih we may assume that 0 + k = k. We must show that 0 + (k + 1) = k + 1. Rewriting with Nat.add_succ and ih, we are done.

∎
```

Paragraphs are emitted as single lines; wrap them wherever you display them.

Every goal in that output is Lean's own. `hprint` does not parse Lean and does
not guess what a tactic did: it hands the file to Lean's frontend, elaborates
it, and reads the goal state the elaborator recorded before and after each
tactic. `0 + (k + 1) = k + 1` and the induction hypothesis `0 + k = k` are the
real ones, printed by Lean's pretty printer.

## Build

You need a Lean toolchain; [elan](https://github.com/leanprover/elan) will pick
up the pinned version from `lean-toolchain`.

```
lake build
```

## Use

`hprint` is a library, and it takes Lean source as a string.

```lean
import HPrint
open HPrint

#eval do IO.print (← hprintStr (← IO.FS.readFile "examples/induction.lean"))
```

Or take it in stages and stop wherever suits:

| Call | Gives you |
| --- | --- |
| `hprintStr : String → Options → String → IO String` | source in, proof out |
| `elaborate : String → String → IO Elaborated` | the source elaborated, with its info trees and diagnostics |
| `hprint : Elaborated → Options → IO String` | the proof, from something already elaborated |

`hprint` is the one to reach for when you already ran Lean's frontend yourself
and have an `Elaborated` in hand; `hprintStr` is that plus `elaborate`.

That, plus `Options` and `Elaborated`, is the whole public surface. Everything
else — the block tree, the writer, the wording, the step and goal views — is
internal, and the package uses Lean's module system to keep it that way: only
the entry points are marked `public`, and the modules reach each other's
internals with `import all`.

`Options` has one field, `statement`, which restates the theorem before its
proof; it defaults to `true`.

Because `hprint` elaborates its input, a proof that uses a library has to be
run from inside that library's Lake project, so that its imports resolve —
`lake env lean` for a script, or a `#eval` in a file of that project.
`Elaborated.errors` is non-empty when the source did not elaborate; the goals
narrated in that case are not the ones you meant.

## How it works

```
source ─▶ Lean frontend ─▶ InfoTree ─▶ steps ─▶ goal diff ─▶ blocks ─▶ text
```

`HPrint/Analysis.lean` runs `Lean.Elab.IO.processCommands` over the source and
turns the resulting `InfoTree` into a tree of steps: one per tactic, carrying
its syntax and its `goalsBefore` / `goalsAfter`.

Most of that tree is not the proof. `have h : P := by tac` elaborates into a
chain of `focus`, `case`, `withAnnotateState` and `paren` nodes, and `rw [h]`
hangs the `rfl` it runs afterwards off the closing `]`. Three rules cut it back
to what the user wrote: grouping kinds (`tacticSeq`, `by`) are transparent, so
are nodes Lean marked synthetic — macro output borrows real source positions,
so its range cannot give it away, but its `SourceInfo` can — and so are nodes
named after a bare token rather than a tactic. What survives is exactly the
tactics in the source.

`HPrint/Render.lean` then narrates by **diffing the goal state**, not by
switching on tactic names:

| What changed | What the reader is told |
| --- | --- |
| New hypotheses, goal changed | "Let n be a natural number. Assume 0 < n. We must show ..." |
| New hypotheses, goal unchanged | "From h we obtain k such that n = 2 * k." |
| One goal became several | one block per branch, labelled by Lean's own case tag |
| Goal replaced | "Rewriting with h, it remains to show ..." |
| Goal closed | "This holds by linear arithmetic." |

Nested tactics are classified the same way, by the goals their children work
on. Children carrying on with their parent's own goal belong to a combinator
(`first`, `all_goals`, `t <;> t'`), so the children are narrated and the
combinator itself is not mentioned. Children proving a goal whose statement is
the hypothesis their parent introduced are the side proof of a `have`. Anything
else is a branch body, and gets a block labelled with Lean's case tag.

A tactic's name is consulted only for *why* something holds — `omega` becomes
"linear arithmetic", `ring` becomes "expanding both sides as polynomials" — and
for a few shapes worth naming, such as supplying a witness to an existential or
laying a `calc` chain out as a displayed computation. That is why the renderer
stays small while covering tactics it has never heard of: an unknown tactic
still has a goal before and after it, and that is what gets described.

Every sentence comes from `HPrint/Phrases.lean`; the proof-walking code never
concatenates prose itself, so the wording is changed in one file without
touching the walk.

## Development

```
lake build
lake test                 # unit checks + golden output for every example
lake test -- --update     # accept new golden output after a deliberate change
```

The golden files in `test/golden/` hold the rendered form of every example, so
any change to the narration shows up as a diff you have to look at. The suite
also asserts that every example elaborates cleanly.

## Limitations

`hprint` reads a proof, it does not judge one. If the proof is convoluted, the
prose will be too: the narration follows the tactic script step by step and
does not reorganise it into the argument a person would have written.

Case labels use Lean's constructor tags (`zero`, `succ`, `inl`), not the
equations a textbook would write (`n = 0`, `n = k + 1`); the branch's actual
goal is stated immediately afterwards, which is what carries the meaning.

Tactics that change the goal in ways with no natural reading — and any tactic
whose effect on the state is invisible — fall back to quoting the Lean text.
Nothing is silently dropped.

## License

MIT
