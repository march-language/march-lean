import MarchLean.Json

/-!
# `march-lean-check`

A0's executable entry point: read march's `--emit-core-ast` JSON envelope
from stdin, echo back its verdict as a process exit code.

Exit code contract (parent plan §5, do not deviate):
- `0` = accept
- `1` = reject
- `2` = skip (unmodeled construct) — **unreachable at A0**: this checker
  never inspects the AST, so it has no basis on which to produce a skip.
  Reserved for A1/A2.
- `3` = internal error (malformed JSON, missing/wrong `format_version`,
  missing/invalid `verdict`); the error message is written to stderr.
-/

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match MarchLean.Json.parseVerdict input with
  | .ok .accept => pure 0
  | .ok .reject => pure 1
  | .error msg => IO.eprintln msg *> pure 3
