import MarchLean.Syntax
import MarchLean.CapLattice

/-!
# Capability checks 1, 4, 5, 7 and 8

march's ERROR-level capability checks, ported from `typecheck.ml`'s
`check_module_needs`. Checks 1, 4 and 5 share the single subsumption relation
in `CapLattice`; Check 7 (realtime exclusion) and Check 8 (migrate-state
IO-freedom) are signature/body-shaped scans documented at their own
definitions below.

**Checks 1b and 1c are deliberately absent.** They are WARNING-only in march
(`core-march-types.md` §2.8.6), so a checker that rejected on them would
manufacture false MISMATCHes against a march that accepts. The cost is real
and inherited on purpose: for an ORDINARY (non-migrate) function, this
checker will not catch a function body calling a builtin that needs an
undeclared capability. Check 8 is the one exception carved out of that cost:
a `*_migrate_state` fn's body IS scanned (`bodyCallsIO`), because march's own
Check 8 scans it too (via `env.own_cap_closures`) — see that check's
docstring for the fidelity gaps that remain even there.
-/
namespace MarchLean.CapCheck
open MarchLean.Syntax
open MarchLean.CapLattice

inductive CapResult where
  | ok
  | violation (msg : String)
  deriving Repr, Inhabited

/-- Every capability named by a `Cap(X)` type anywhere inside a type.

**`Tagged` is deliberately NOT descended into**, mirroring march's own
extractor: `cap_paths_in_surface_ty` (`typecheck.ml`) has an explicit arm
`| Ast.TyCon (con, _) when con.txt = "Tagged" -> []` — an applied `Tagged(X,
T)` is a phantom/policy tag, not a capability position, so march skips its
arguments entirely rather than looking for `Cap(_)` inside `X`. Before this
arm existed, an applied `Tagged` decoded to `Ty.unsupported` here (see
`Elab.lean`'s `decodeSurfaceTy`), which this function's catch-all mapped to
`[]` — the same `[]` result, but by accident: once `Tagged` started decoding
to a real `Ty.con "Tagged" args` (to let Check 7 read the realtime marker),
the generic `.con _ args => args.flatMap capsInTy` arm below would have
started descending into `Tagged`'s payload and manufacturing false Check
1/Check 8 rejects on any `Cap(_)` nested there (e.g.
`Tagged(Cap(IO.Network), Realtime)`) even when march accepts, because march
never looks inside `Tagged` at all. This arm must stay ahead of the generic
`.con` arm below.

**The `Cap` arm requires its argument to be a NULLARY constructor**, mirroring
march exactly: `cap_paths_in_surface_ty` matches
`Ast.TyCon (con, [arg]) when con.txt = "Cap"` and then, inside that arm,
`| Ast.TyCon (name, []) -> [name.txt] | _ -> []` (`typecheck.ml:1617-1620`) —
a `Cap(_)` whose argument carries type arguments (e.g. `Cap(Foo(Int))`) is
NOT a capability path at all and march's whole `Cap` arm returns `[]` for it,
without falling through to generic recursion into the argument's own
sub-terms. The explicit `| .con "Cap" _ => []` arm below is required to match
that: without it, a non-nullary `Cap(_)` argument would fall through to the
generic `.con _ args => args.flatMap capsInTy` arm and this function would
wrongly recurse into the argument's payload (and could still surface a
`Cap(_)` nested further inside, e.g. `Cap(Foo(Cap(IO)))`, that march itself
never looks for). -/
partial def capsInTy : Ty → List String
  | .con "Tagged" _ => []
  | .con "Cap" [.con x []] => [x]
  | .con "Cap" _ => []
  | .con _ args => args.flatMap capsInTy
  | .arrow a b  => capsInTy a ++ capsInTy b
  | .tuple ts   => ts.flatMap capsInTy
  | .record fs  => fs.flatMap (fun (_, t) => capsInTy t)
  | .lin _ t    => capsInTy t
  | _           => []

/-- The caps a declaration's PARAMETER signature mentions. Only signatures
matter for Check 1 — body uses are Check 1b, which is warning-only and not
implemented. Return-type caps are handled separately by
`capsInReturnSignature` (they are gated differently — see `checkOneModule`). -/
def capsInSignature : Decl → List String
  | .dfn _ params _ _ =>
      params.flatMap (fun (_, _, annot) =>
        match annot with | some t => capsInTy t | none => [])
  | _ => []

/-- The caps a declaration's RETURN-type annotation mentions. march's Check 1
scans `param_tys @ ret_tys`, so a `Cap(X)` in return position counts exactly
like one in a parameter. Kept separate from `capsInSignature` because the two
call sites gate it differently: for **Check 1**, `checkOneModule` calls this
GATED on the enclosing module being fully in fragment (see its docstring for
why — march's self-declaration exemption can cover a return cap through
machinery this checker doesn't model). For **Check 8**, `checkOneModule`
calls this UNGATED — correctly so, since march's own Check 8 tests
`own_caps <> []` directly and is not subject to Check 1's self-declaration
exemption at all. -/
def capsInReturnSignature : Decl → List String
  | .dfn _ _ retAnnot _ =>
      match retAnnot with | some t => capsInTy t | none => []
  | _ => []

/-- The caps this module declares via `needs`. -/
def declaredNeeds (decls : List Decl) : List String :=
  decls.flatMap (fun d => match d with | .dneeds ps => ps | _ => [])

/-- IO-effectful builtin names — the subset of march's builtin→cap table
(`typecheck.ml:1498-1590`) whose cap begins `IO`. Copied verbatim from the
live table (Task 3 Step 1; extracted to `.superpowers/sdd/io-builtins.txt`),
NOT pinned by count. Any call to one of these inside a `*_migrate_state` body
is an IO effect (Check 8). -/
def ioBuiltins : List String :=
  [ "csv_next_row", "csv_open", "dir_exists", "dir_list", "dir_mkdir",
    "dir_mkdir_p", "dir_rm_rf", "dir_rmdir", "dns_resolve", "file_append",
    "file_copy", "file_delete", "file_exists", "file_open", "file_read",
    "file_read_chunk", "file_read_line", "file_rename", "file_stat",
    "file_write", "get_work_pool", "http_server_listen", "http_server_spawn_n",
    "http_server_wait", "print", "println", "process_argv", "process_cwd",
    "process_env", "process_exit", "process_kill_proc", "process_pid",
    "process_read_line", "process_set_env", "process_spawn_async",
    "process_spawn_lines", "process_spawn_sync", "process_wait_proc",
    "process_write", "random_bytes", "signal_raise_self", "signal_unwatch",
    "signal_watch", "stdlib_random_bytes", "task_spawn", "task_spawn_link",
    "task_spawn_steal", "task_spawn_with_cancel", "tcp_accept", "tcp_connect",
    "tcp_listen", "tcp_recv_all", "tcp_recv_chunk", "tcp_recv_chunked_frame",
    "tcp_recv_exact", "tcp_recv_http", "tcp_recv_http_headers", "tcp_send_all",
    "tls_accept", "tls_client_ctx", "tls_connect", "tls_negotiated_alpn",
    "tls_peer_cn", "tls_read", "tls_server_ctx", "tls_write", "unix_time",
    "unix_time_ms", "uuid_v4", "uuid_v7", "vault_drop", "vault_get",
    "vault_incr", "vault_keys", "vault_new", "vault_ns_drop", "vault_ns_get",
    "vault_ns_set", "vault_push_capped", "vault_put_new", "vault_set",
    "vault_set_ttl", "vault_size", "vault_update", "vault_whereis", "ws_recv",
    "ws_select", "ws_send" ]

/-- march's `is_migrate_fn_name` (`typecheck.ml:6780-6781`): the name ends in
the literal suffix `_migrate_state`. A SUFFIX test, not a substring test —
`"migrate_state_helper"` must NOT match. -/
def isMigrateFnName (n : String) : Bool := n.endsWith "_migrate_state"

example : isMigrateFnName "migrate_state_helper" = false := by native_decide
example : isMigrateFnName "counter_migrate_state" = true := by native_decide

/-- Does this term (a function body) directly call an IO builtin? A
structural walk: an `app` whose callee is a `var` in `ioBuiltins` is a hit;
otherwise recurse into every sub-term. This is a DIRECT-call scan only — it
does not follow calls into user functions. Total over every `Term`
constructor (`MarchLean/Syntax.lean`):
`lit`/`var`/`unsupported` are the only genuine leaves; every other
constructor recurses into all of its `Term`/`List Term`/`List (Pattern ×
Term)` children so an IO call nested arbitrarily deep (inside a `let`,
`match` arm, tuple, record, etc.) is still found.

**This walk is DELIBERATELY MORE TOTAL than march's own `calls_in_expr`
(`typecheck.ml:6737-6768`), and that is not a bug to fix here.** march's
version ends in a catch-all `| _ -> acc` and has no `ETuple`/record/list arm,
so a call nested inside a tuple/record/list literal is invisible to it. E.g.
`(println("hi"), old)` as a migrate body: march's Check 8 ACCEPTS (the
`println` inside the `ETuple` is never visited by `calls_in_expr`), while this
checker's exhaustive walk correctly finds it and REJECTS. Do not narrow
`bodyCallsIO` to match march's gap — that gap looks like a genuine march bug,
and surfacing exactly this kind of divergence is what this oracle is for. A
mismatch of this shape should be triaged as a **march finding**, not a
checker regression.

**Remaining Check-8 fidelity gaps (tracked here, not fixed):**
1. Direct-call only, as noted above — this scan does not follow
   `migrate_state → user fn → IO`. **This is NOT a one-sided gap: march does
   not follow it either.** `own_cap_closures` is written in exactly one
   place — `record_fn_caps` (`typecheck.ml:6847-6849`) — which merges
   `own_caps @ prior` for the SAME qualified function name; none of its three
   feeders (signature caps, `body_cap_uses` via `calls_in_expr`, extern caps)
   walks the call graph into a *different* function. Confirmed empirically:
   `fn helper(x : Int) : Int do println("side effect") x end` /
   `fn counter_migrate_state(old : Int) : Int do helper(old) end` is ACCEPTED
   by march (exit 0) despite `helper` performing IO. So
   `migrate → user fn → IO` is a SHARED BLIND SPOT, not a checker-only
   weakness: both march and this checker miss it, and — because
   `march-lean-check` is a differential oracle that can only ever surface
   *disagreements* between the two sides — no amount of corpus running will
   ever reveal this gap. That makes it strictly more important to record
   here than an ordinary one-sided fidelity gap would be. A future
   maintainer must NOT "close" this by adding transitive call-graph analysis
   to this checker: doing so would make this checker MORE precise than
   march and thereby *introduce* a fresh divergence (a false reject) rather
   than remove one. If transitive migrate-state checking is ever wanted,
   march itself must implement it first, and this checker should follow.
2. Extern migrate fns are not modelled: march also flags a `DExtern` fn whose
   name matches `is_migrate_fn_name` (`typecheck.ml:7226-7234`), attributing
   it `IO.Foreign` (plus `IO.Foreign.Blocking` under `blocking`) regardless of
   body. This checker has no representation of extern function bodies/caps
   for that case and does not check it.
3. A multi-clause fn (0 or 2+ clauses) whose name ends in `_migrate_state`
   decodes to `Decl.unsupported` (`Elab.lean`), never a `dfn` — it is
   therefore never seen by this scan at all and escapes Check 8 entirely.
   Safe in practice (the file is driven to skip downstream via the
   out-of-fragment gate before this would matter), but worth recording
   alongside the other two gaps above. march, by contrast, concatenates
   parameters across all clauses of a multi-clause fn
   (`typecheck.ml:7172-7178`, `:6853-6857`) and checks the merged signature. -/
partial def bodyCallsIO : Term → Bool
  | .lit _ _ => false
  | .var _ _ _ => false
  | .app (.var n _ _) args _ => ioBuiltins.contains n || args.any bodyCallsIO
  | .app fn args _ => bodyCallsIO fn || args.any bodyCallsIO
  | .lam _ body _ => bodyCallsIO body
  | .let_ _ _ _ rhs body _ => bodyCallsIO rhs || bodyCallsIO body
  | .letfn _ _ _ _ fnBody body _ => bodyCallsIO fnBody || bodyCallsIO body
  | .ite cond then_ else_ _ => bodyCallsIO cond || bodyCallsIO then_ || bodyCallsIO else_
  | .con _ args _ => args.any bodyCallsIO
  | .tuple elems _ => elems.any bodyCallsIO
  | .record fields _ => fields.any (fun (_, e) => bodyCallsIO e)
  | .field record _ _ _ => bodyCallsIO record
  | .match_ scrut arms _ => bodyCallsIO scrut || arms.any (fun (_, e) => bodyCallsIO e)
  -- LOAD-BEARING: this arm is safe returning `false` (rather than `true`,
  -- which would be the conservative choice) ONLY because
  -- `MarchLeanCheck.lean`'s `run` invokes `CapCheck.checkCaps` BEFORE the
  -- skip gate (decode → checkCaps → inferModule/skip-check → linearity). A
  -- body containing `Term.unsupported` also makes `Decl.hasUnsupported`
  -- true for its enclosing decl, which drives the file to exit 2 (skip)
  -- further down that same pipeline — so a migrate body with an
  -- out-of-fragment subterm never reaches exit 0 (accept) even though this
  -- arm itself reports "no IO here". If the driver is ever reordered so the
  -- skip gate runs before (or independently of) `checkCaps`, this arm
  -- becomes a false accept and must be revisited.
  | .unsupported _ => false

/-- Is `used` covered by any declared need? Reflexive and directional. -/
def covered (declared : List String) (used : String) : Bool :=
  declared.any (fun need => capSubsumes need used)

/-- Check one module (not recursing into nested modules — the caller does
that, since each module is checked against its OWN declared needs). -/
def checkOneModule (modName : String) (decls : List Decl)
    (moduleCaps : List (String × List String)) : CapResult :=
  let declared := declaredNeeds decls
  -- Check 1 — signature Cap(X) coverage over `param_tys @ ret_tys`
  -- (march's `check_module_needs`). Parameter caps are ALWAYS scanned.
  --
  -- RETURN caps are scanned only when this module is ENTIRELY in fragment. A
  -- module carrying an out-of-fragment declaration (e.g. a `proof cap`, which
  -- decodes to `Decl.unsupported`) may satisfy a return cap through machinery
  -- this checker does not model: march's self-declaration exemption lets a
  -- module's own `proof cap X` implicitly cover `Cap(Module.X)` returned by
  -- its public fns (accept/t62 — `Cap(Db.Migrated)` returned under `needs IO`,
  -- accepted). Rather than mis-reject such a return, defer — the file skips
  -- downstream via the out-of-fragment gate, exactly as it did before this
  -- scan existed. A fully-in-fragment module has only modeled IO caps and no
  -- such escape, so an uncovered return cap there is a real Check 1 violation
  -- (the M1 gap: e.g. `fn f(cap : Cap(IO.Console)) : Cap(IO.Network)` under
  -- `needs IO.Console`). Params are left unconditional so no existing
  -- signature-based reject changes.
  let retCaps :=
    if decls.any Decl.hasUnsupported then [] else decls.flatMap capsInReturnSignature
  let sigCaps := decls.flatMap capsInSignature ++ retCaps
  match sigCaps.find? (fun c => !covered declared c) with
  | some bad =>
      .violation s!"Check 1: `Cap({bad})` used in module `{modName}` but `{bad}` is not declared in `needs`"
  | none =>
  -- Check 5 — extern cap coverage
  let externCaps := decls.flatMap (fun d =>
    match d with | .dextern (some c) => [c] | _ => [])
  match externCaps.find? (fun c => !covered declared c) with
  | some bad =>
      .violation s!"Check 5: extern in module `{modName}` requires `Cap({bad})` but `{bad}` is not declared in `needs`"
  | none =>
  -- Check 4 — transitive `use` coverage
  let usedMods := decls.flatMap (fun d =>
    match d with | .duse p => [p] | _ => [])
  let unmet := usedMods.flatMap (fun m =>
    match moduleCaps.find? (fun (n, _) => n == m) with
    | some (_, reqs) => (reqs.filter (fun r => !covered declared r)).map (fun r => (m, r))
    | none => [])
  match unmet.head? with
  | some (m, r) =>
      .violation s!"Check 4: module `{modName}` imports `{m}` which requires `Cap({r})`, but `{r}` is not declared in `needs`"
  | none =>
  -- Check 7 — realtime exclusion (typecheck.ml:7162-7182). A fn whose
  -- PARAMETER signature carries BOTH a `Tagged(_, Realtime)` type and a
  -- `Cap(X)` with X ∈ {Alloc, IO, Panic} (the excluded roots — NOT other IO
  -- sub-caps like `IO.Network`) is rejected: realtime functions may not also
  -- hold allocation-, IO-, or panic-capable capabilities. Signature-level
  -- only (`dfn` param annotations) — this checker does not scan bodies
  -- (that is Check 1b, warning-only in march and deliberately not modelled;
  -- see the module docstring above). Also, as with Check 8 (see
  -- `bodyCallsIO`'s docstring), a multi-clause fn (0 or 2+ clauses) whose
  -- name would otherwise match decodes to `Decl.unsupported`, never a
  -- `dfn` — it is never seen by this scan and escapes Check 7 entirely;
  -- march instead concatenates params across all clauses
  -- (`typecheck.ml:7172-7178`, `:6853-6857`) before checking.
  --
  -- Both predicates below require their inner constructor to be NULLARY,
  -- matching march's own patterns exactly:
  -- `Ast.TyCon ({txt="Tagged";_}, [_; Ast.TyCon ({txt="Realtime";_}, [])])`
  -- and `Ast.TyCon ({txt="Cap";_}, [Ast.TyCon ({txt=("Alloc"|"IO"|"Panic");_},
  -- [])])` (`typecheck.ml:7163`, `:7167`). A `Tagged(_, Realtime(X))` or
  -- `Cap(IO(X))` with a non-nullary tag/cap name is NOT a match for march —
  -- matching on a wildcard arg list here would over-match and manufacture a
  -- false Check 7 reject on a program march accepts.
  let isRealtimeTagged : Ty → Bool
    | .con "Tagged" [_, .con "Realtime" []] => true
    | _ => false
  let isExcludedCap : Ty → Bool
    | .con "Cap" [.con r []] => r == "Alloc" || r == "IO" || r == "Panic"
    | _ => false
  let paramTysOf : Decl → List Ty
    | .dfn _ params _ _ => params.filterMap (fun (_, _, a) => a)
    | _ => []
  match decls.find? (fun d =>
      (paramTysOf d).any isRealtimeTagged && (paramTysOf d).any isExcludedCap) with
  | some (.dfn name params _ _) =>
      let excludedName :=
        match (params.filterMap (fun (_, _, a) => a)).find? isExcludedCap with
        | some (.con "Cap" [.con r []]) => r
        | _ => "?"
      .violation s!"Check 7: fn `{name}` in module `{modName}` takes a `Tagged(_, Realtime)` param and an excluded `Cap({excludedName})` param (Alloc|IO|Panic are excluded alongside a realtime tag)"
  | _ =>
  -- Check 8 — migrate-state IO-freedom (typecheck.ml:6771-6846). A fn whose
  -- name ends in `_migrate_state` must have EMPTY `own_caps`, where march's
  -- `own_caps` accumulates SIGNATURE caps + BODY caps + EXTERN caps
  -- (`typecheck.ml:6832-6849`, predicate at `:7210-7222`) — not body calls
  -- alone. We reject when the body directly calls an IO builtin OR the
  -- signature (param or return) mentions any `Cap(X)` at all — reusing
  -- `capsInSignature`/`capsInReturnSignature` rather than a new extractor,
  -- since ANY declared capability in a migrate fn's own signature makes
  -- `own_caps` non-empty regardless of what the body does. (The extern-caps
  -- third of march's `own_caps` is deliberately NOT modelled here — see the
  -- gap recorded in `bodyCallsIO`'s docstring.) Scoped to THIS module's own
  -- `dfn` decls only — an actor's handler body is out of fragment (decodes
  -- to `Decl.unsupported`, not a `dfn`), so it is never seen here regardless
  -- of what it calls.
  match decls.find? (fun d =>
      match d with
      | .dfn name _ _ body =>
          isMigrateFnName name &&
            (bodyCallsIO body
              || !(capsInSignature d).isEmpty
              || !(capsInReturnSignature d).isEmpty)
      | _ => false) with
  | some (.dfn name _ _ _) =>
      .violation s!"Check 8: fn `{name}` in module `{modName}` ends in `_migrate_state` but performs IO or its signature carries a capability"
  | _ => .ok

/-- Walk the whole module tree, checking each module against its own needs. -/
partial def checkDecls (moduleCaps : List (String × List String)) : List Decl → CapResult
  | [] => .ok
  | .dmod name inner :: rest =>
      match checkOneModule name inner moduleCaps with
      | .violation m => .violation m
      | .ok =>
        match checkDecls moduleCaps inner with   -- nested modules
        | .violation m => .violation m
        | .ok => checkDecls moduleCaps rest
  | _ :: rest => checkDecls moduleCaps rest

/-- Entry point. Also checks the top level as an implicit module, so a file
with `needs`/`Cap(X)` outside any `mod` block is still checked. -/
def checkCaps (m : Module) : CapResult :=
  match checkOneModule "<top-level>" m.decls m.moduleCaps with
  | .violation msg => .violation msg
  | .ok => checkDecls m.moduleCaps m.decls

end MarchLean.CapCheck

namespace MarchLean.CapCheck
open MarchLean.Syntax

/-- `mod Store do needs IO.FileRead; fn save(cap : Cap(IO.FileWrite), …) end`
— reject/t38: siblings do not cover each other. -/
def siblingViolation : Module := {
  decls := [Decl.dmod "Store" [
    Decl.dneeds ["IO.FileRead"],
    Decl.dfn "save" [("cap", Lin.unrestricted,
                      some (Ty.con "Cap" [Ty.con "IO.FileWrite" []]))]
             none (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps siblingViolation
  -- expect: violation — IO.FileWrite not covered by IO.FileRead

/-- accept/t46: the root `needs IO` covers `Cap(IO.Network)`. -/
def rootCovers : Module := {
  decls := [Decl.dmod "Server" [
    Decl.dneeds ["IO"],
    Decl.dfn "listen" [("cap", Lin.unrestricted,
                        some (Ty.con "Cap" [Ty.con "IO.Network" []]))]
             none (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rootCovers
  -- expect: ok

/-- reject/t39: `use Vault` where Vault needs IO.Mut, importer declares nothing. -/
def useUncovered : Module := {
  decls := [Decl.dmod "Main" [Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useUncovered
  -- expect: violation — Check 4, IO.Mut not covered

/-- accept/t49: same, but the importer declares `needs IO.Mut`. -/
def useCoveredExact : Module := {
  decls := [Decl.dmod "Main" [Decl.dneeds ["IO.Mut"], Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useCoveredExact
  -- expect: ok

/-- Check 4 uses the same subsumption: the root `needs IO` covers IO.Mut. -/
def useCoveredByRoot : Module := {
  decls := [Decl.dmod "Main" [Decl.dneeds ["IO"], Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useCoveredByRoot
  -- expect: ok

/-- Check 5: an extern declaring Cap(IO.Foreign) with no covering needs. -/
def externUncovered : Module := {
  decls := [Decl.dmod "F" [Decl.dextern (some "IO.Foreign")]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externUncovered
  -- expect: violation — Check 5

/-- Check 5 satisfied. -/
def externCovered : Module := {
  decls := [Decl.dmod "F" [Decl.dneeds ["IO.Foreign"], Decl.dextern (some "IO.Foreign")]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externCovered
  -- expect: ok

/-- A module with no caps at all is trivially fine — the overwhelmingly
common case, and it must not be flagged. -/
def noCapsAtAll : Module := {
  decls := [Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noCapsAtAll
  -- expect: ok

/-- True iff a `CapResult` is a violation — a `Bool` projection so the
`native_decide` guards below can pin the verdict at build time. (An end-to-end
guard that decodes real `march --emit-core-ast` output and cap-checks it lives
in `MarchLeanCheck.lean`, which already imports the decoder — this file's core
stays independent of `Elab`.) -/
def CapResult.isViolation : CapResult → Bool
  | .violation _ => true
  | .ok          => false

/-- Finding M1 regression, direct unit (no decode): a fully-in-fragment module
whose ONLY defect is an
uncovered RETURN cap is a Check 1 violation — the param `Cap(IO.Console)` is
covered by `needs IO.Console`, the return `Cap(IO.Network)` is not. -/
def retCapUncovered : Module := {
  decls := [Decl.dneeds ["IO.Console"],
    Decl.dfn "get_net"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []]))]
      (some (Ty.con "Cap" [Ty.con "IO.Network" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retCapUncovered  -- expect: violation (return IO.Network uncovered)
example : (checkCaps retCapUncovered).isViolation = true := by native_decide

/-- A covered RETURN cap must NOT be flagged: broad `needs IO` subsumes the
returned `Cap(IO.Network)` (the param here is a plain `Int`, isolating the
return path). -/
def retCapCovered : Module := {
  decls := [Decl.dneeds ["IO"],
    Decl.dfn "get_net"
      [("port", Lin.unrestricted, some (Ty.con "Int" []))]
      (some (Ty.con "Cap" [Ty.con "IO.Network" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retCapCovered  -- expect: ok
example : (checkCaps retCapCovered).isViolation = false := by native_decide

/-- Check 7 (reject/t41-shaped): a fn with BOTH a `Tagged(_, Realtime)` param
and a `Cap(IO)` param — one of the three excluded roots — is a violation. -/
def rtExcluded : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted, some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rtExcluded
  -- expect: violation — Check 7, `Cap(IO)` excluded alongside the realtime tag

/-- Check 7 requires BOTH conditions: a realtime-tagged param alongside a
NON-excluded cap (`IO.Network`, not a root `IO`/`Alloc`/`Panic`) must NOT be
flagged. -/
def rtSafe : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted, some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Network" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rtSafe
  -- expect: ok — IO.Network is not an excluded root

/-- Check 7's other half: an excluded cap with NO realtime-tagged param must
NOT be flagged (this is just an ordinary Check-1-covered `Cap(IO)` use). -/
def noRt : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noRt
  -- expect: ok

/-- The gate that keeps accept/t62 safe: a module carrying an out-of-fragment
declaration (here a bare `Decl.unsupported`, standing in for `proof cap
Migrated`) does NOT get its return caps scanned. march covers t62's returned
`Cap(Db.Migrated)` — under only `needs IO` — via the self-declaration
exemption this checker does not model, and ACCEPTS. So `checkCaps` must NOT
reject: it defers to the downstream out-of-fragment skip gate. Without the
gate, the uncovered `Db.Migrated` return would wrongly reject an accept file. -/
def retProofCapDeferred : Module := {
  decls := [Decl.unsupported,   -- e.g. `proof cap Migrated`
            Decl.dneeds ["IO"],
    Decl.dfn "run_migrations"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      (some (Ty.con "Cap" [Ty.con "Db.Migrated" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retProofCapDeferred  -- expect: ok (deferred, NOT rejected)
example : (checkCaps retProofCapDeferred).isViolation = false := by native_decide

/-- Check 8: a `*_migrate_state` fn whose body calls an IO builtin → violation. -/
def migrateDoesIO : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "counter_migrate_state" [("old", Lin.unrestricted, some (Ty.con "Int" []))] none
      (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                [Term.lit (Lit.str "x") (Ty.con "String" [])] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migrateDoesIO   -- expect: violation naming Check 8
example : (checkCaps migrateDoesIO).isViolation = true := by native_decide

/-- A `*_migrate_state` fn with an IO-free body → ok. -/
def migratePure : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "counter_migrate_state" [("old", Lin.unrestricted, some (Ty.con "Int" []))] none
      (Term.var "old" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migratePure   -- expect: ok
example : (checkCaps migratePure).isViolation = false := by native_decide

/-- A NON-migrate fn that calls `println` → ok (scan is gated on the name
suffix — Check 8 must not fire on ordinary functions). -/
def plainDoesIO : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "helper" [("old", Lin.unrestricted, some (Ty.con "Int" []))] none
      (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                [Term.lit (Lit.str "x") (Ty.con "String" [])] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps plainDoesIO   -- expect: ok
example : (checkCaps plainDoesIO).isViolation = false := by native_decide

/-- Finding 1 regression: a `*_migrate_state` fn whose BODY is IO-free but
whose SIGNATURE carries a `Cap(X)` param → violation. march's `own_caps`
(`typecheck.ml:6832-6849`) accumulates signature caps + body caps + extern
caps, not body calls alone — a migrate fn that merely ACCEPTS a capability
parameter (never calling anything with it) still has non-empty `own_caps` and
is rejected. Mirrors the false-accept demonstrated end-to-end:
`fn counter_migrate_state(c : Cap(IO.Console), old : Int) : Int do old end`. -/
def migrateSigCapUncalled : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "counter_migrate_state"
      [("c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []])),
       ("old", Lin.unrestricted, some (Ty.con "Int" []))]
      none
      (Term.var "old" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migrateSigCapUncalled   -- expect: violation naming Check 8
example : (checkCaps migrateSigCapUncalled).isViolation = true := by native_decide

/-- Finding 1's other half: a `*_migrate_state` fn whose RETURN annotation
(not a param) carries a `Cap(X)` → violation, exercising
`capsInReturnSignature` rather than `capsInSignature`. -/
def migrateRetCapUncalled : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "counter_migrate_state"
      [("old", Lin.unrestricted, some (Ty.con "Int" []))]
      (some (Ty.con "Cap" [Ty.con "IO.Console" []]))
      (Term.var "old" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migrateRetCapUncalled   -- expect: violation naming Check 8
example : (checkCaps migrateRetCapUncalled).isViolation = true := by native_decide

/-- Finding 3: no existing Check-8 fixture exercises any RECURSIVE arm of
`bodyCallsIO` — every one above uses a body that is a bare `var` or a
top-level `app`, so collapsing every recursive arm to a wildcard would still
pass all of them. This fixture buries the IO call two levels deep: inside a
`match` arm, which is itself the right-hand side of a `let` —
`let x = match old with | _ => println("hi") in x`. Must still be a
violation; see the accompanying teeth-check (temporarily stubbing the
`match_`/`let_` arms) recorded in the task report. -/
def migrateDoesIONested : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Console"],
    Decl.dfn "counter_migrate_state" [("old", Lin.unrestricted, some (Ty.con "Int" []))] none
      (Term.let_ "x" Lin.unrestricted none
        (Term.match_ (Term.var "old" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))
          [(Pattern.wild,
            Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                      [Term.lit (Lit.str "hi") (Ty.con "String" [])] (Ty.con "Unit" []))]
          (Ty.con "Unit" []))
        (Term.var "x" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
        (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migrateDoesIONested   -- expect: violation naming Check 8
example : (checkCaps migrateDoesIONested).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- Arity-fidelity re-review guards (a1-elaboration-checker-design review,
-- task 4): `isRealtimeTagged`, `isExcludedCap` and `capsInTy`'s `Cap` arm
-- each used to accept a wildcard where march requires a NULLARY
-- constructor, manufacturing a live false reject. Each guard below pins one
-- of those fixes so a future regression is caught at build time rather than
-- silently reopening a false-reject hole.

/-- Finding 1 pin: `isRealtimeTagged` must require the `Realtime` tag itself
to be NULLARY, mirroring march's
`Ast.TyCon ({txt="Realtime";_}, [])` (`typecheck.ml:7163`). A fn taking BOTH a
`Tagged(_, Realtime(Int))` (non-nullary tag — e.g. a user-defined
`type Realtime(a) = R(a)`) AND an excluded `Cap(IO)` param must NOT be a
Check 7 violation: march's own pattern does not match a parametrised
`Realtime`, so it does not treat this fn as realtime-tagged at all. Mirrors
the false-reject reproducer:
`fn step(_d : Tagged(Int, Realtime(Int)), _c : Cap(IO)) : Int do 1 end`
under a module defining `type Realtime(a) = R(a)`. -/
def rtTagNonNullarySafe : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted,
        some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" [Ty.con "Int" []]])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rtTagNonNullarySafe
  -- expect: ok — Realtime(Int) is not a nullary `Realtime` tag
example : (checkCaps rtTagNonNullarySafe).isViolation = false := by native_decide

/-- Finding 2 pin: `isExcludedCap` must require the excluded cap name itself
to be NULLARY, mirroring march's
`Ast.TyCon ({txt=("Alloc"|"IO"|"Panic");_}, [])` (`typecheck.ml:7167`). A fn
taking a genuinely realtime-tagged param (`Tagged(_, Realtime)`, nullary tag)
alongside `Cap(IO(Int))` — a user-defined generic `IO(a)` type, NOT the
nullary `IO` capability root — must NOT be a Check 7 violation: march's
pattern does not match a parametrised `IO`. Mirrors the false-reject
reproducer (accepted by march: `type Realtime = RT` / `type IO(a) = IOBox(a)`
/ `fn step(_d : Tagged(Int, Realtime), _c : Cap(IO(Int))) : Int do 1 end`). -/
def excludedCapNonNullarySafe : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted, some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" [Ty.con "Int" []]]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps excludedCapNonNullarySafe
  -- expect: ok — Cap(IO(Int)) is not the nullary `Cap(IO)` excluded root
example : (checkCaps excludedCapNonNullarySafe).isViolation = false := by native_decide

/-- Finding 3 pin: `capsInTy`'s `Cap` arm must require its argument to be a
NULLARY constructor, mirroring march's `cap_paths_in_surface_ty`
(`typecheck.ml:1617-1620`): `Cap(Foo(Int))` — a non-nullary argument — is not
a capability path at all and must extract to `[]`, not `["Foo"]`. Mirrors the
false-reject reproducer: `fn f(_c : Cap(Foo(Int))) : Int do 1 end` under a
module defining `type Foo(a) = F(a)`. -/
example : capsInTy (Ty.con "Cap" [Ty.con "Foo" [Ty.con "Int" []]]) = [] := by native_decide

/-- Finding 4 pin: `capsInTy` must NOT descend into an applied `Tagged`'s
payload at all — mirroring march's `cap_paths_in_surface_ty`, whose `Tagged`
arm returns `[]` unconditionally rather than falling through to generic
recursion. Direct unit on the extractor itself: a `Cap(IO.Network)` nested
inside `Tagged(_, Realtime)` must extract to `[]`, not `["IO.Network"]`. -/
example :
    capsInTy (Ty.con "Tagged" [Ty.con "Cap" [Ty.con "IO.Network" []], Ty.con "Realtime" []]) = []
  := by native_decide

/-- Finding 4 pin, `checkCaps`-level: a module declaring NO `needs` at all,
whose only `Cap(_)` mention is nested inside a `Tagged(_, Realtime)` param,
must be `ok` — if `capsInTy` were ever changed to descend into `Tagged`
again, this fixture's `Cap(IO.Network)` would surface as an uncovered Check 1
violation (there is no `needs` to cover it) and this guard would fail. -/
def tagPayloadCapIgnored : Module := {
  decls := [Decl.dmod "M" [
    Decl.dfn "f"
      [("_x", Lin.unrestricted,
        some (Ty.con "Tagged" [Ty.con "Cap" [Ty.con "IO.Network" []], Ty.con "Realtime" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps tagPayloadCapIgnored
  -- expect: ok — the nested Cap(IO.Network) is never extracted from inside Tagged
example : (checkCaps tagPayloadCapIgnored).isViolation = false := by native_decide

end MarchLean.CapCheck
