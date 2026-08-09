import MarchLean.Json
import MarchLean.Elab
import MarchLean.CapCheck
import MarchLean.Compare
import MarchLean.Linearity
import MarchLean.KindCoverage
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
    -- format_version≠3 check (→ exit 3), but IGNORE march's verdict — A2
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
          -- Note this can only ever produce a REJECT or a SKIP. A clean cap
          -- check never licenses an accept on its own: control falls through
          -- to the unchanged skip-gate → inference → linearity → cross-check
          -- path below.
          --
          -- `CapResult.skip` (today: a `cap no_panic` divisor whose
          -- non-zeroness needs a refinement type or Z3 — see
          -- `CapCheck.divisionVerdict`) is DEFERRED rather than returned
          -- here. A file the cap layer cannot judge may still be rejected by
          -- inference or linearity for an unrelated, fully-modelled reason,
          -- and march would reject it too; returning exit 2 immediately would
          -- forfeit those confirmations. So the skip is carried past both
          -- passes and only becomes exit 2 once nothing else has rendered a
          -- verdict — at which point it must beat the accept, since the
          -- unjudged division is exactly what an accept would be claiming.
          let capRes := MarchLean.CapCheck.checkCaps m
          match capRes with
          | .violation msg => IO.eprintln s!"reject (capability): {msg}"; pure 1
          | _ =>
          let iv ← MarchLean.Compare.inferModule m
          match iv with
          | .skip r => IO.eprintln s!"skip: {r}"; pure 2
          | .reject r => IO.eprintln s!"reject (infer): {r}"; pure 1
          | _ =>  -- .accept or .typesDiffer: A2 says well-typed; check linearity
            match MarchLean.Linearity.checkLinearity m with
            | .skip r => IO.eprintln s!"skip: {r}"; pure 2
            | .reject r => IO.eprintln s!"reject (linearity): {r}"; pure 1
            | .ok =>
              match capRes with
              | .skip r => IO.eprintln s!"skip (capability): {r}"; pure 2
              | _ =>
              match iv with
              | .typesDiffer r => IO.eprintln s!"accept, but types differ: {r}"; pure 4
              | _ => pure 0

/-- `--kind-coverage`: read march `"kind"` tag names from stdin, one per
line, and print one `KIND<TAB>CATEGORY<TAB>SITES` line each — what
`MarchLean.Elab`'s decoder actually does with a node bearing that tag,
derived by probing the live match arms (see `MarchLean.KindCoverage`).

This is a diagnostic mode of the SAME binary the conformance harness uses,
deliberately not a second executable: CI already builds and caches
`march-lean-check`, and a separate target would be one more thing that can
silently stop being built. It renders no verdict and reads no envelope. -/
def runKindCoverage (input : String) : IO UInt32 := do
  let kinds := (input.splitOn "\n").map (fun l => l.trimAscii.toString) |>.filter (· != "")
  if kinds.isEmpty then
    IO.eprintln "--kind-coverage: no kind names on stdin"
    return 3
  IO.println (MarchLean.KindCoverage.report kinds)
  return 0

def main (args : List String) : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match args with
  | [] => run input
  | ["--kind-coverage"] => runKindCoverage input
  | _ =>
    IO.eprintln "usage: march-lean-check [--kind-coverage] < INPUT"
    IO.eprintln "  (no args)        read a --emit-core-ast envelope, print a verdict via the exit code"
    IO.eprintln "  --kind-coverage  read march \"kind\" tag names, print decoder coverage as TSV"
    return 3

namespace MarchLean.Test
open MarchLean

/-- Finding M1 regression (end-to-end, over real emitter output). march scans
`param_tys @ ret_tys` for Check 1 (`typecheck.ml`'s `check_module_needs`), but
`CapCheck.capsInSignature` used to scan only params — so a module whose ONLY
capability defect is an uncovered RETURN-type `Cap(X)` was wrongly accepted by
the cap checker. This exercises the whole path — `Elab.decodeModule` (which
must surface `ret_ty` onto `Decl.dfn.retAnnot`) then `CapCheck.checkCaps` —
guarding BOTH the decoder threading and the return-cap union at once.

The envelope is `march --emit-core-ast` output (format_version 3) for

    mod Server do
      needs IO.Console
      fn get_net(cap : Cap(IO.Console)) : Cap(IO.Network) do cap_narrow(root_cap) end
    end

with the body trimmed to `0 : Int` (kept in fragment so the module stays fully
in fragment and the return-cap scan fires — see the gate in
`CapCheck.checkOneModule`) and spans normalised to `"f"`. march rejects it:
`Cap(IO.Network)` (the RETURN) is not covered by `needs IO.Console` (siblings);
the param `Cap(IO.Console)` IS covered, so the sole defect is the return cap.
Before the fix `checkCaps` returned `.ok`; now it must return a `.violation`. -/
def retCapEnvelope : String :=
  r#"{"diagnostics":[],"format_version":3,"instantiations":[],"module":{"decls":[{"kind":"DNeeds","paths":[[{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"IO"},{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Console"}]],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}},{"fn":{"attrs":[],"bounds":[],"clauses":[{"body":{"kind":"ELit","literal":{"kind":"LitInt","value":0},"resolved_ty":{"kind":"TCon","name":"Int","args":[]}},"guard":null,"params":[{"kind":"FPNamed","param":{"lin":{"kind":"Unrestricted"},"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"cap"},"ty":{"args":[{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"IO.Console"}}],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Cap"}}}}],"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"doc":null,"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"get_net"},"ret_ty":{"args":[{"args":[],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"IO.Network"}}],"kind":"TyCon","name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Cap"}},"vis":{"kind":"Public"}},"kind":"DFn","span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1}}],"name":{"span":{"end_col":2,"end_line":1,"file":"f","start_col":1,"start_line":1},"txt":"Server"}},"module_caps":[],"schemes":[],"verdict":"reject"}"#

#eval show IO Unit from do
  match Lean.Json.parse retCapEnvelope with
  | .error e => IO.println s!"parse failed: {e}"
  | .ok j    => match Elab.decodeModule j with
    | .error e => IO.println s!"decode failed: {e}"
    | .ok m    => IO.println s!"verdict={repr (CapCheck.checkCaps m)}"
  -- expect: verdict=(CapResult.violation "Check 1: `Cap(IO.Network)` ...")

/-- Enforced M1 guard: decoding the real envelope above and cap-checking it
MUST reject. Fails to build if the return-cap scan ever regresses — the decoder
dropping `ret_ty`, or `capsInReturnSignature` no longer being unioned in. -/
example :
    (match Lean.Json.parse retCapEnvelope with
     | .ok j => match Elab.decodeModule j with
                | .ok m => (CapCheck.checkCaps m).isViolation
                | .error _ => false
     | .error _ => false) = true := by native_decide

end MarchLean.Test
