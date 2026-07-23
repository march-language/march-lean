import Lean.Data.Json

/-!
# `MarchLean.Json`

A0's verdict-echo parser: reads march's `--emit-core-ast` JSON envelope

```json
{"format_version":3,"verdict":"accept"|"reject","diagnostics":[...],"module":{...}}
```

and extracts *only* `format_version` and `verdict`. This module intentionally
never inspects `"diagnostics"` or `"module"` — those matter for the A1
checker (see `MarchLean.Elab`'s `decodeModule`), not this module, which is
pure plumbing to prove the pipe works.

`format_version` must be exactly `3` — the emitter's real `--emit-core-ast`
output bumped from `1` to `2` when it started attaching
`resolved_ty`/`schemes`/`instantiations` HM-witness data, which `MarchLean.Elab`
depends on, and from `2` to `3` when it started attaching the `module_caps`
envelope table A3's `CapCheck` depends on; a `1`- or `2`-tagged envelope
predates that data and is rejected here.
-/

namespace MarchLean.Json

open Lean (Json)

/-- The two verdicts A0 can echo back. `skip`/`error` are not constructors
here because they are represented as `Except.error` (error) or are simply
unreachable at this milestone (skip — A0 never inspects the AST, so it has
no basis on which to produce one; that is reserved for later milestones). -/
inductive Verdict where
  | accept
  | reject
  deriving DecidableEq, Repr

/--
Parse march's `--emit-core-ast` JSON envelope and extract the verdict.

- Fails with `"invalid JSON: ..."` if `input` isn't valid JSON.
- Fails with `"missing format_version"` / `"unsupported format_version: ..."`
  if the `format_version` field is absent, not a number, or not equal to `3`.
- Fails with `"missing verdict"` / `"unexpected verdict: ..."` if the
  `verdict` field is absent, not a string, or not exactly `"accept"` or
  `"reject"`.
- Never looks up `"diagnostics"` or `"module"`.
-/
def parseVerdict (input : String) : Except String Verdict := do
  let json ← Json.parse input |>.mapError (fun e => s!"invalid JSON: {e}")
  let versionJson ← match json.getObjVal? "format_version" with
    | .ok v => pure v
    | .error _ => throw "missing format_version"
  let version ← match versionJson.getNat? with
    | .ok n => pure n
    | .error _ => throw s!"unsupported format_version: {versionJson.compress}"
  if version ≠ 3 then
    throw s!"unsupported format_version: {version}"
  let verdictJson ← match json.getObjVal? "verdict" with
    | .ok v => pure v
    | .error _ => throw "missing verdict"
  let verdictStr ← match verdictJson.getStr? with
    | .ok s => pure s
    | .error _ => throw s!"unexpected verdict: {verdictJson.compress}"
  match verdictStr with
  | "accept" => pure .accept
  | "reject" => pure .reject
  | other => throw s!"unexpected verdict: {other}"

end MarchLean.Json

-- Sanity checks (kept as executable documentation; not deleted — see task
-- report for rationale). `Except String Verdict` has no `Repr` instance of
-- its own, so each check renders manually via `repr`/string concatenation.
namespace MarchLean.Json.Test

open MarchLean.Json

def render : Except String Verdict → String
  | .ok v => s!"ok {reprStr v}"
  | .error e => s!"error {e}"

-- valid accept
#eval render <| parseVerdict "{\"format_version\":3,\"verdict\":\"accept\",\"diagnostics\":[],\"module\":{}}"
-- expected: "ok Verdict.accept" (equivalently `ok accept`)

-- valid reject
#eval render <| parseVerdict "{\"format_version\":3,\"verdict\":\"reject\",\"diagnostics\":[],\"module\":{}}"
-- expected: "ok Verdict.reject"

-- missing format_version
#eval render <| parseVerdict "{\"verdict\":\"accept\"}"
-- expected: "error missing format_version"

-- wrong format_version (the old v1 envelope shape is now rejected)
#eval render <| parseVerdict "{\"format_version\":1,\"verdict\":\"accept\"}"
-- expected: "error unsupported format_version: 1"

-- wrong format_version (the old v2 envelope shape, pre-module_caps, is now rejected)
#eval render <| parseVerdict "{\"format_version\":2,\"verdict\":\"accept\"}"
-- expected: "error unsupported format_version: 2"

-- malformed JSON
#eval render <| parseVerdict "not json"
-- expected: "error invalid JSON: ..." (parser-supplied message)

-- missing verdict field
#eval render <| parseVerdict "{\"format_version\":3}"
-- expected: "error missing verdict"

-- verdict has an unexpected string value
#eval render <| parseVerdict "{\"format_version\":3,\"verdict\":\"maybe\"}"
-- expected: "error unexpected verdict: maybe"

end MarchLean.Json.Test
