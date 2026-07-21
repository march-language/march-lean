import MarchLean.Json
import MarchLean.Elab
import MarchLean.Check
import MarchLean.Linearity
import Lean.Data.Json

/-!
# `march-lean-check` (A1)

Read march's `--emit-core-ast` `format_version` 2 envelope from stdin and
independently re-check the accept verdict for the A1 fragment.

Exit: 0=accept, 1=reject (a real A1 disagreement), 2=skip (reject-side or
out-of-fragment), 3=internal error (malformed JSON / wrong version).
-/
open Lean (Json)

def run (input : String) : IO UInt32 := do
  match Json.parse input with
  | .error e => IO.eprintln s!"invalid JSON: {e}"; pure 3
  | .ok envelope =>
    -- version + verdict gate (reuses A0's parser, now requiring version 2)
    match MarchLean.Json.parseVerdict input with
    | .error msg => IO.eprintln msg; pure 3
    | .ok .reject => pure 2                     -- reject side: skip
    | .ok .accept =>
      match MarchLean.Elab.decodeModule envelope with
      | .error e => IO.eprintln s!"decode error: {e}"; pure 3
      | .ok m =>
        match MarchLean.Check.checkModule m with
        | .skip r => IO.eprintln s!"skip: {r}"; pure 2
        | .reject r => IO.eprintln s!"MISMATCH (types): {r}"; pure 1
        | .ok =>
          match MarchLean.Linearity.checkLinearity m with
          | .skip r => IO.eprintln s!"skip: {r}"; pure 2
          | .reject r => IO.eprintln s!"MISMATCH (linearity): {r}"; pure 1
          | .ok => pure 0

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  run input
