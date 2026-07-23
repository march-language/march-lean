import MarchLean.Json
import MarchLean.Elab
import MarchLean.CapCheck
import MarchLean.Compare
import MarchLean.Linearity
import Lean.Data.Json

/-!
# `march-lean-check` (A2-reject)

Read march's `--emit-core-ast` `format_version` 3 envelope from stdin and
render A2's OWN independent accept/reject verdict on every in-fragment
file — via `CapCheck.checkCaps` (A3's declaration-level IO capability
checks, run first), `Compare.inferModule` (independent inference +
up-to-equivalence cross-check against march's `resolved_ty`), and the
independent linearity pass — WITHOUT reading march's own `verdict` field.
This lets the harness confirm march was right to reject: a reject-corpus
file that march correctly rejected, and that A2 also independently
rejects, now exits 1 (not the old A2 behavior of skipping the reject side
entirely).

`MarchLean.Json.parseVerdict` is still consulted, but ONLY as the
malformed-JSON / `format_version ≠ 3` gate (→ exit 3); its returned
verdict value is otherwise ignored.

Exit: 0=A2 accepts (capability check, inference, and linearity all pass,
types agree with `resolved_ty`), 1=A2 rejects (capability violation, or
inference/linearity found it ill-typed), 2=skip (out-of-fragment / no
module / unmodeled name), 3=internal error (malformed JSON / wrong
version), 4=A2 accepts but per-node types disagree with `resolved_ty`.
-/
open Lean (Json)

def run (input : String) : IO UInt32 := do
  match Json.parse input with
  | .error e => IO.eprintln s!"invalid JSON: {e}"; pure 3
  | .ok envelope =>
    -- Version/format gate ONLY: reuse parseVerdict for the malformed /
    -- format_version≠2 check (→ exit 3), but IGNORE march's verdict — A2
    -- renders its OWN verdict below (pure-independent).
    match MarchLean.Json.parseVerdict input with
    | .error msg => IO.eprintln msg; pure 3
    | .ok _ =>
      -- A parse-reject emits "module": null — no AST to judge ⇒ skip.
      match envelope.getObjVal? "module" with
      | .ok .null => IO.eprintln "skip: no module (parse failure)"; pure 2
      | _ =>
        match MarchLean.Elab.decodeModule envelope with
        | .error e => IO.eprintln s!"decode error: {e}"; pure 3
        | .ok m =>
          -- A3: capability checks run FIRST. They are purely
          -- declaration-level and need no inference, so a module whose body
          -- is out of fragment but whose `needs` manifest is malformed is
          -- still judgeable. Placing them after inference would forfeit
          -- exactly those files to the skip gate.
          --
          -- Note this can only ever produce a REJECT. A clean cap check
          -- never licenses an accept on its own: control falls through to
          -- the unchanged skip-gate → inference → linearity → cross-check
          -- path below.
          match MarchLean.CapCheck.checkCaps m with
          | .violation msg => IO.eprintln s!"reject (capability): {msg}"; pure 1
          | .ok =>
          let iv ← MarchLean.Compare.inferModule m
          match iv with
          | .skip r => IO.eprintln s!"skip: {r}"; pure 2
          | .reject r => IO.eprintln s!"reject (infer): {r}"; pure 1
          | _ =>  -- .accept or .typesDiffer: A2 says well-typed; check linearity
            match MarchLean.Linearity.checkLinearity m with
            | .skip r => IO.eprintln s!"skip: {r}"; pure 2
            | .reject r => IO.eprintln s!"reject (linearity): {r}"; pure 1
            | .ok =>
              match iv with
              | .typesDiffer r => IO.eprintln s!"accept, but types differ: {r}"; pure 4
              | _ => pure 0

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  run input
