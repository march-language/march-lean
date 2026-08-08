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

/-- The cap layer's verdict on a whole file.

`skip` is NOT "ok" — it is the explicit "this checker cannot judge" answer,
and it exists because march reaches some of its own capability decisions
through machinery this solver-free oracle deliberately does not model (today:
`refinecheck/division_safety.ml`'s refined-parameter and Z3 channels — see
`divisionVerdict`'s docstring). A decision we RECONSTRUCT rather than model
must fail toward "cannot judge", never toward a confident accept or reject;
`ok` would be a false accept on a program march rejects, and `violation`
would be a false reject on one march accepts. `MarchLeanCheck.run` maps it to
exit 2, the same honest-skip channel the inference and linearity passes
already use. -/
inductive CapResult where
  | ok
  | violation (msg : String)
  | skip (reason : String)
  deriving Repr, Inhabited

/-- Combine two capability verdicts over disjoint parts of a file (two
modules, or one module's own check and its children's).

**A definite `violation` anywhere beats a `skip` anywhere**, and a `skip`
beats `ok`. march reports every error it finds and rejects the file if ANY
one of them fires, so a violation this checker is sure of stays a reject even
when some other module carried an unjudgeable divisor; conversely a `skip`
must not be swallowed by a sibling's clean `ok`, or the file would be
reported as accepted on the strength of a part we never judged. Leftmost wins
within a tier, so the reported message is the earliest one in decl order,
matching the previous short-circuiting behaviour. -/
def CapResult.andThen : CapResult → CapResult → CapResult
  | .violation m, _ => .violation m
  | _, .violation m => .violation m
  | .skip r, _      => .skip r
  | _, .skip r      => .skip r
  | .ok, .ok        => .ok

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

**The `Cap` MARKER ITSELF requires EXACTLY ONE type argument**, mirroring
march's `cap_paths_in_surface_ty`, which only recognizes the capability
position at all via the pattern `Ast.TyCon (con, [arg]) when con.txt = "Cap"`
(`typecheck.ml:1617`, one-element list) — march's OCaml match is
non-exhaustive here (`con` name aside, only the singleton-arg-list shape has
a `Cap`-specific arm at all) and any OTHER arity of `Cap` (0 args — the plain
user-ADT `Cap` from `type Cap = C(Int)`; 2+ args — e.g. `Cap(Cap(IO.Network),
Int)`) falls through to march's generic `| Ast.TyCon (_, args) ->
List.concat_map cap_paths_in_surface_ty args` catch-all, which DOES recurse
into every argument looking for capability paths nested inside them. A
regression in the previous commit collapsed this to `| .con "Cap" _ => []`
(matching Cap at ANY arity and always returning `[]`), which silently
swallowed any `Cap(_)` nested inside a non-unary `Cap(...)` application — a
live false accept (`fn f(_c : Cap(Cap(IO.Network), Int)) : Int`, which march
rejects for the uncovered `IO.Network` but the buggy checker accepted). The
`| .con "Cap" [_] => []` arm below is the arity-1-only guard: it only ever
fires for a single-argument `Cap(_)`, letting every other arity fall through
to the generic `.con _ args => args.flatMap capsInTy` arm below it, exactly
as march's own fallthrough does.

**Within that arity-1 arm, the argument must ALSO be a NULLARY constructor**
to extract a capability name at all, mirroring march's inner match on the
single argument: `| Ast.TyCon (name, []) -> [name.txt] | _ -> []`
(`typecheck.ml:1618-1619`) — a `Cap(_)` whose sole argument carries its OWN
type arguments (e.g. `Cap(Foo(Int))`) is NOT a capability path and march's
whole `Cap` arm returns `[]` for it, WITHOUT falling through to generic
recursion into that argument's own sub-terms (so a further-nested `Cap(_)`
inside it, e.g. `Cap(Foo(Cap(IO)))`, is never found — march itself never
looks for it there either). The explicit `| .con "Cap" [_] => []` arm (after
the nullary-match arm above it) is required for this: without it, a
non-nullary single argument would fall through to the generic
`.con _ args => args.flatMap capsInTy` arm and wrongly recurse into it. -/
partial def capsInTy : Ty → List String
  | .con "Tagged" _ => []
  | .con "Cap" [.con x []] => [x]
  | .con "Cap" [_] => []
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
why a residual gate is still needed even now that proof-cap self-declaration,
Finding I1, is modeled directly via `selfDeclaredCaps` rather than through
this gate). For **Check 8**, `checkOneModule` calls this UNGATED — correctly
so, since march's own Check 8 tests `own_caps <> []` directly and is not
subject to Check 1's self-declaration exemption at all. -/
def capsInReturnSignature : Decl → List String
  | .dfn _ _ retAnnot _ =>
      match retAnnot with | some t => capsInTy t | none => []
  | _ => []

/-- The caps this module declares via `needs`. -/
def declaredNeeds (decls : List Decl) : List String :=
  decls.flatMap (fun d => match d with | .dneeds ps => ps | _ => [])

/-- march's `has_foreign` (`typecheck.ml:9037-9042`, inside
`check_no_extern_module`), mirrored exactly: a `needs` path (here, one dotted
string like `"IO.Foreign"` or `"IO.Foreign.Blocking"` — `Elab.lean`'s `DNeeds`
decoder joins each path's segments with `"."`) counts toward `cap no_extern`
when its FIRST segment is literally `"IO"` and `"Foreign"` appears among the
REMAINING segments — `needs Foreign` alone (no `IO` prefix) or `needs
IO.NetForeign` (a different later segment) do NOT match, exactly as march's
`first.txt = "IO" && List.exists (fun p -> p.txt = "Foreign") rest` does not. -/
def hasForeignNeed (path : String) : Bool :=
  match path.splitOn "." with
  | first :: rest => first == "IO" && rest.contains "Foreign"
  | [] => false

/-- The bare names of proof caps this module declares DIRECTLY — a sibling
`Decl.dproofcap` in its OWN `decls` (not one declared inside a nested
`dmod`). Used only by `checkCaps` to build the top-level self-declaration
exemption (Finding I1) — see that function's docstring. -/
def declaredProofCapNames (decls : List Decl) : List String :=
  decls.flatMap (fun d => match d with | .dproofcap n => [n] | _ => [])

/-- march's builtin→cap table (`typecheck.ml:1497-…`, `builtin_cap_table`),
copied VERBATIM — every `(name, cap)` pair whose cap begins `IO`, `Alloc` or
`Panic` (A3 slice (c) Task 1 Step 1's extraction command against the live
`march` source), NOT pinned by count and NOT hand-typed. `ioBuiltins` below is
exactly this table's name projection, kept so Check 8's existing references
are unchanged. -/
def builtinCaps : List (String × String) :=
  [ ("println", "IO.Console"),
    ("print", "IO.Console"),
    ("file_exists", "IO.FileRead"),
    ("file_read", "IO.FileRead"),
    ("file_open", "IO.FileRead"),
    ("file_read_line", "IO.FileRead"),
    ("file_read_chunk", "IO.FileRead"),
    ("file_stat", "IO.FileRead"),
    ("dir_exists", "IO.FileRead"),
    ("dir_list", "IO.FileRead"),
    ("csv_open", "IO.FileRead"),
    ("csv_next_row", "IO.FileRead"),
    ("file_write", "IO.FileWrite"),
    ("file_append", "IO.FileWrite"),
    ("file_delete", "IO.FileWrite"),
    ("file_rename", "IO.FileWrite"),
    ("dir_mkdir", "IO.FileWrite"),
    ("dir_mkdir_p", "IO.FileWrite"),
    ("dir_rmdir", "IO.FileWrite"),
    ("dir_rm_rf", "IO.FileWrite"),
    ("file_copy", "IO.FileSystem"),
    ("tcp_connect", "IO.NetConnect"),
    ("tcp_send_all", "IO.NetConnect"),
    ("tcp_recv_all", "IO.NetConnect"),
    ("tcp_recv_exact", "IO.NetConnect"),
    ("tcp_recv_http", "IO.NetConnect"),
    ("tcp_recv_http_headers", "IO.NetConnect"),
    ("tcp_recv_chunk", "IO.NetConnect"),
    ("tcp_recv_chunked_frame", "IO.NetConnect"),
    ("ws_recv", "IO.WebSocket"),
    ("ws_send", "IO.WebSocket"),
    ("ws_select", "IO.WebSocket"),
    ("dns_resolve", "IO.Network"),
    ("tcp_listen", "IO.NetListen"),
    ("tcp_accept", "IO.NetListen"),
    ("http_server_listen", "IO.NetListen"),
    ("http_server_spawn_n", "IO.NetListen"),
    ("http_server_wait", "IO.NetListen"),
    ("process_env", "IO.Process"),
    ("process_set_env", "IO.Process"),
    ("process_cwd", "IO.Process"),
    ("process_argv", "IO.Process"),
    ("process_pid", "IO.Process"),
    ("process_exit", "IO.Process"),
    ("process_spawn_sync", "IO.Process"),
    ("process_spawn_lines", "IO.Process"),
    ("process_spawn_async", "IO.Process"),
    ("process_read_line", "IO.Process"),
    ("process_write", "IO.Process"),
    ("process_kill_proc", "IO.Process"),
    ("process_wait_proc", "IO.Process"),
    ("unix_time", "IO.Clock"),
    ("unix_time_ms", "IO.Clock"),
    ("uuid_v7", "IO.Clock"),
    ("random_bytes", "IO.Random"),
    ("stdlib_random_bytes", "IO.Random"),
    ("uuid_v4", "IO.Random"),
    ("signal_watch", "IO.Signal"),
    ("signal_unwatch", "IO.Signal"),
    ("signal_raise_self", "IO.Signal"),
    ("task_spawn", "IO.Spawn"),
    ("task_spawn_link", "IO.Spawn"),
    ("task_spawn_steal", "IO.Spawn"),
    ("task_spawn_with_cancel", "IO.Spawn"),
    ("get_work_pool", "IO.Spawn"),
    ("vault_new", "IO.Mut"),
    ("vault_set", "IO.Mut"),
    ("vault_set_ttl", "IO.Mut"),
    ("vault_get", "IO.Mut"),
    ("vault_drop", "IO.Mut"),
    ("vault_update", "IO.Mut"),
    ("vault_put_new", "IO.Mut"),
    ("vault_incr", "IO.Mut"),
    ("vault_push_capped", "IO.Mut"),
    ("vault_ns_set", "IO.Mut"),
    ("vault_ns_get", "IO.Mut"),
    ("vault_ns_drop", "IO.Mut"),
    ("vault_keys", "IO.Mut"),
    ("vault_whereis", "IO.Mut"),
    ("vault_size", "IO.Mut"),
    ("tls_client_ctx", "IO.NetConnect.TLS"),
    ("tls_server_ctx", "IO.NetConnect.TLS"),
    ("tls_connect", "IO.NetConnect.TLS"),
    ("tls_accept", "IO.NetConnect.TLS"),
    ("tls_read", "IO.NetConnect.TLS"),
    ("tls_write", "IO.NetConnect.TLS"),
    ("tls_negotiated_alpn", "IO.NetConnect.TLS"),
    ("tls_peer_cn", "IO.NetConnect.TLS") ]

/-- IO-effectful builtin names — the name projection of `builtinCaps`. Kept as
its own definition (rather than inlining `builtinCaps.map (·.1)` at every call
site) so Check 8's existing references (`bodyCallsIO`, `checkOneModule`) are
unchanged by this refactor. -/
def ioBuiltins : List String := builtinCaps.map (·.1)

/-- march's `is_migrate_fn_name` (`typecheck.ml:6780-6781`): the name ends in
the literal suffix `_migrate_state`. A SUFFIX test, not a substring test —
`"migrate_state_helper"` must NOT match. -/
def isMigrateFnName (n : String) : Bool := n.endsWith "_migrate_state"

example : isMigrateFnName "migrate_state_helper" = false := by native_decide
example : isMigrateFnName "counter_migrate_state" = true := by native_decide

/-- Does this term (a function body) directly apply a `var` whose name is in
`banned`? A structural walk: an `app` whose callee is a `var` in `banned` is a
hit; otherwise recurse into every sub-term. This is a DIRECT-call scan only —
it does not follow calls into user functions. Total over every `Term`
constructor (`MarchLean/Syntax.lean`):
`lit`/`var`/`unsupported` are the only genuine leaves; every other
constructor recurses into all of its `Term`/`List Term`/`List (Pattern ×
Term)` children so a banned call nested arbitrarily deep (inside a `let`,
`match` arm, tuple, record, etc.) is still found.

Generalised (A3 slice (c) Task 1) from the original `bodyCallsIO`, which
hardcoded `ioBuiltins` as the banned set — `bodyCallsIO` below is now a thin
specialisation (`bodyCalls ioBuiltins`) kept so Check 8's existing call site
is unchanged.

**This walk is DELIBERATELY MORE TOTAL than march's own `calls_in_expr`, and
that is not a bug to fix here.** march has TWO copies of `calls_in_expr`
(`typecheck.ml:6737-6768` and `typecheck.ml:~8834`); BOTH end in a catch-all
`| _ -> acc` with no `ETuple`/record/list/lambda arm, so a call nested inside
any of those is invisible to march. Filed upstream as **march#82** (see
`specs/march-findings.md`).

**SCOPE — this divergence affects FOUR checks, not just Check 8.** `bodyCalls`
is the shared scan behind:
  - Check 8 (migrate-state IO-freedom) — `bodyCallsIO`, via the first copy;
  - `cap pure`, `cap deterministic`, and `cap no_panic`'s explicit-panic scan
    — all via the second copy, which has the identical blind spot.
An earlier revision of this docstring discussed the divergence as though it
were Check-8-only. It is not, and that framing is exactly why the other three
went unexamined until the slice (c) whole-branch review. Confirmed divergent
shapes (march ACCEPTS, this checker REJECTS):
  `(println("hi"), 1)` under `cap pure`,
  `(unix_time(), 1)` under `cap deterministic`,
  `(panic("boom"), 1)` under `cap no_panic`,
  `(println("hi"), old)` as a migrate body under Check 8.

**Deliberate policy (decided 2026-07-30):** keep this walk total and let the
divergence stand. No corpus file currently exercises these shapes, so the
harness is green today; if march ever adds one, CI goes RED and that red is
the trigger to triage — NOT a signal that this checker regressed.

**Therefore: do NOT "fix" a red of this shape by narrowing `bodyCalls`.**
march is the side that is wrong here; the gap is a genuine march bug that
this oracle already surfaced and reported. Triage it as a **march finding**.
If march#82 is fixed upstream, this divergence disappears on its own and no
change is needed here.

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
2. Extern migrate fns (Finding I2 — CLOSED): march also flags a `DExtern` fn
   whose name matches `is_migrate_fn_name` (`typecheck.ml:6941-6950`,
   `:7226-7234`), attributing it `IO.Foreign` (plus `IO.Foreign.Blocking`
   under `blocking`) UNCONDITIONALLY — every extern fn in every extern block
   gets this, regardless of the block's own declared `ext_cap_ty` (verified
   directly against `march`: an extern block whose declared type isn't even
   `Cap`-shaped still rejects a migrate-named fn inside it). `checkOneModule`
   now checks this directly (below, right after the `dfn`-based scan above):
   ANY extern block listing a migrate-named fn is a violation, independent of
   this checker's own decoded `capTy` (which drives Check 5's separate
   `needs`-coverage obligation only). This checker doesn't distinguish
   `blocking` from non-blocking externs the way march's two-cap-vs-one-cap
   attribution does — but Check 8 only ever tests `own_caps <> []` (ANY
   non-empty list), never which specific caps are in it, so that distinction
   is irrelevant to the verdict here.
3. A multi-clause fn (0 or 2+ clauses) whose name ends in `_migrate_state`
   decodes to `Decl.unsupported` (`Elab.lean`), never a `dfn` — it is
   therefore never seen by this scan at all and escapes Check 8 entirely.
   Safe in practice (the file is driven to skip downstream via the
   out-of-fragment gate before this would matter), but worth recording
   alongside the other two gaps above. march, by contrast, concatenates
   parameters across all clauses of a multi-clause fn
   (`typecheck.ml:7172-7178`, `:6853-6857`) and checks the merged signature. -/
partial def bodyCalls (banned : List String) : Term → Bool
  | .lit _ _ => false
  | .var _ _ _ => false
  | .app (.var n _ _) args _ => banned.contains n || args.any (bodyCalls banned)
  | .app fn args _ => bodyCalls banned fn || args.any (bodyCalls banned)
  | .lam _ body _ => bodyCalls banned body
  | .let_ _ _ _ rhs body _ => bodyCalls banned rhs || bodyCalls banned body
  | .letfn _ _ _ _ fnBody body _ => bodyCalls banned fnBody || bodyCalls banned body
  | .ite c t e _ => bodyCalls banned c || bodyCalls banned t || bodyCalls banned e
  | .con _ args _ => args.any (bodyCalls banned)
  | .tuple elems _ => elems.any (bodyCalls banned)
  | .record fields _ => fields.any (fun (_, e) => bodyCalls banned e)
  | .field record _ _ _ => bodyCalls banned record
  -- A guard (A3 slice (c) Task 3) is scanned too — march's `calls_in_expr`
  -- (`typecheck.ml:6737-6768`) walks `branch_guard` alongside `branch_body`,
  -- so a banned call hiding in `Some(v) when println("leak") | ... -> body`
  -- must be found even though the guard, not the body, is where it lives.
  | .match_ scrut arms _ =>
      bodyCalls banned scrut ||
        arms.any (fun (_, g, e) => (g.map (bodyCalls banned)).getD false || bodyCalls banned e)
  -- `.opaque_` (`ECond`/`ERecordUpdate`/`EAtom`/`EAssert`/`EDbg`/`ELetFn`/
  -- `ELetQ`/`ESend`/`ESpawn`) RECURSES. Its own shape is unmodelled, but it
  -- carries the exact child-expression list march's `calls_in_expr` descends
  -- into for those kinds (`typecheck.ml:7734-7750`), and `calls_in_expr` is
  -- the shared body-walk behind `check_pure_module`,
  -- `check_deterministic_module`, `check_no_panic_module` and Check 8. A
  -- banned call inside `match do c -> println("leak") end` or
  -- `send(p, unix_time_ms())` must therefore be found HERE — before the skip
  -- gate — or the file exits 2 while march exits 1. Recursing costs nothing
  -- in false-reject exposure: it can only ever ADD a `true`, i.e. only ever
  -- turn a skip into a reject that march also renders.
  | .opaque_ children _ => children.any (bodyCalls banned)
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
  --
  -- **That ordering dependency is now DEEPER, not merely inherited.**
  -- `Term.opaque_` exists solely to exploit it: the constructor hard-codes
  -- `Term.hasUnsupported = true` (so the file still skips, so `Infer` and
  -- `Linearity` never judge a construct they have no rules for — the exact
  -- mechanism that produced the previous slice's false rejects) WHILE its
  -- children stay visible to this walk and its siblings (`bodyAllocates`,
  -- `divisionVerdict`, `matchesIn`, `termMentionsAny`). The whole value of
  -- the constructor is the window between `checkCaps` and the skip gate. If
  -- anyone reorders `MarchLeanCheck.run` so the skip gate precedes (or
  -- short-circuits) `checkCaps`, `Term.opaque_` stops detecting ANYTHING —
  -- it does not degrade to "conservative", it degrades to silent — and this
  -- arm becomes a false accept besides. Reorder the driver only by first
  -- deleting `Term.opaque_`.
  | .unsupported _ => false

/-- `bodyCallsIO`, kept as a thin specialisation of `bodyCalls` over
`ioBuiltins` so Check 8's existing call site (`checkOneModule`) is unchanged
by this refactor. -/
def bodyCallsIO (t : Term) : Bool := bodyCalls ioBuiltins t

/-- Does this term (a function body) allocate — construct a NON-EMPTY tuple,
record, non-nullary `con`, or `lam`? A sibling total walk to `bodyCalls`, for
the `no_alloc` behavioral cap (A3 slice (c)): `true` at `.tuple (_ :: _) _`
(a NON-EMPTY tuple — `no_alloc.ml:20`'s `ETuple ([], _) -> ()` explicitly
exempts the EMPTY tuple, i.e. unit `()`, from being an allocation; a bare
`.tuple [] _` is therefore `false`, matched FIRST so it is not shadowed by the
general non-empty arm), `.record _ _` (march's `ERecord` arm has no such
exemption — even an empty record literal `{}` always errors, unconditionally
of `fields`), `.con _ (_ :: _) _` (a NON-EMPTY arg list — a nullary
constructor, e.g. `None`, allocates nothing, mirroring march's `ECon (_, [],
_)` no-op arm), and `.lam _ _ _` (a closure allocation, unconditionally —
march's `ELam` arm has no exemption either); recurses into every other
constructor's children looking for a nested allocation; `.lit`/`.var`/
`.unsupported` are the only genuine leaves. Enumerates all 13 `Term`
constructors explicitly (14 pattern arms, since `.tuple` is split into an
empty and a non-empty case) — no catch-all — matching `bodyCalls`'s
exhaustiveness discipline. -/
partial def bodyAllocates : Term → Bool
  | .lit _ _ => false
  | .var _ _ _ => false
  | .app fn args _ => bodyAllocates fn || args.any bodyAllocates
  | .lam _ _ _ => true
  | .let_ _ _ _ rhs body _ => bodyAllocates rhs || bodyAllocates body
  | .letfn _ _ _ _ fnBody body _ => bodyAllocates fnBody || bodyAllocates body
  | .ite c t e _ => bodyAllocates c || bodyAllocates t || bodyAllocates e
  | .con _ [] _ => false
  | .con _ (_ :: _) _ => true
  | .tuple [] _ => false           -- unit `()` is not an allocation (no_alloc.ml:20)
  | .tuple (_ :: _) _ => true      -- non-empty tuple always allocates
  | .record _ _ => true
  | .field record _ _ _ => bodyAllocates record
  | .match_ scrut arms _ =>
      bodyAllocates scrut ||
        arms.any (fun (_, g, e) => (g.map bodyAllocates).getD false || bodyAllocates e)
  -- `.opaque_` RECURSES, and contributes NO allocation of its own. Verified
  -- against march's `no_alloc.ml` directly: its four allocating arms are
  -- `ETuple (_::_)`, `ERecord`, `ECon (_, _::_)` and `ELam` — none of the
  -- nine `opaque_` kinds is among them, and `check_expr` has an explicit
  -- recurse-only arm for every one (`ELetFn`, `ELetQ`, `ECond`, `ESpawn`,
  -- `EAssert`, `EDbg`, `ESend`, `ERecordUpdate`, `EAtom`;
  -- `no_alloc.ml:41-63`). Note in particular that march does NOT treat
  -- `ERecordUpdate` as an allocation even though it treats `ERecord` as one,
  -- so this arm must not answer `true` the way `.record` does.
  | .opaque_ children _ => children.any bodyAllocates
  | .unsupported _ => false

/-- Division operators march's own division-safety pass flags
(`refinecheck/division_safety.ml:25`, `div_ops`), copied VERBATIM. A division
site is an `app` whose callee is a `var` named here; per the emitted envelope
(verified directly against `reject/t123_cap_no_panic_shadowed_guard`'s
`--emit-core-ast` output for `10 / d`: `EApp{fn=EVar"/", args=[ELit 10,
EVar d]}`), the DIVISOR is the SECOND argument (`args[1]`, `lhs / rhs` with
`rhs` the divisor) — not the first. -/
def divOps : List String :=
  [ "/", "%", "int_div", "int_mod", "int_div_euclid", "int_mod_euclid" ]

/-- Names currently known to be bound to a literal `Int` value, from an
in-scope `let`. march's equivalent channel is `dctx.lets`
(`division_safety.ml:167`); this checker models this channel and the `path`
channel (`DivPath` below), but NOT the refined-parameter channel, as a plain
association list keyed on the bare variable name (see `divisionVerdict`'s
docstring for why the refinement channel is out of scope, and why a divisor
that would need it is a SKIP rather than an accept). -/
abbrev DivFacts := List (String × Int)

/-- Drop every fact about a name in `names`. march's `retire`
(`division_safety.ml:173`) exists precisely so a rebinding of a name can never
leave a STALE outer fact attributed to a fresh inner value — see
`divisionVerdict`'s docstring, and `reject/t123`'s own corpus comment, for the
runtime panic this omission caused in practice. Every binding-introducing
`Term` arm of `divisionVerdict` calls this BEFORE extending the facts with
anything the new binder itself provides. -/
def retireDivFacts (names : List String) (facts : DivFacts) : DivFacts :=
  facts.filter (fun (n, _) => !names.contains n)

/-- The bare names a `Pattern` binds (match/destructuring binders), so a match
arm can retire them from `DivFacts` before descending — mirrors march's
`Refine_check.pat_binders`. Total over every `Pattern` constructor
(`MarchLean/Syntax.lean`); `wild`/`lit`/`unsupported` bind nothing. -/
partial def patBinderNames : Pattern → List String
  | .wild => []
  | .var n _ => [n]
  | .con _ args => args.flatMap patBinderNames
  | .tuple elems => elems.flatMap patBinderNames
  | .lit _ => []
  | .record fields => fields.flatMap (fun (_, p) => patBinderNames p)
  | .as n p => n :: patBinderNames p
  | .or_ alts => alts.flatMap patBinderNames
  | .unsupported => []

/-- The literal `Int` value of a term, if it directly is one. -/
def intLitOf : Term → Option Int
  | .lit (.int n) _ => some n
  | _ => none

/-- The updated `DivFacts` after a `let name = rhs` binding: retire the old
`name` entry, then record a fresh one when — and only when — `rhs` is itself a
literal (march's `bind_let`, `division_safety.ml:183`). A non-literal `rhs`
retires and offers nothing in exchange, so a division by that name lands in
`divisorVerdict`'s "no tracked literal" arm — `DivVerdict.unknown`, i.e. a
SKIP, never a fabricated fact in either direction. (march's own `bind_let`
records EVERY `rhs`, literal or not, because it can hand a non-literal to
`smt_of` and Z3; this checker has no solver, so recording one would buy
nothing.) -/
def bindLetFacts (name : String) (rhs : Term) (facts : DivFacts) : DivFacts :=
  match intLitOf rhs with
  | some n => (name, n) :: retireDivFacts [name] facts
  | none => retireDivFacts [name] facts

/-- A guard condition in scope, paired with a `negated` flag — march's `dctx.path`
(`division_safety.ml`'s `dctx.path : (A.expr * bool) list`). `negated = true`
means we are on the ELSE side of the `if` that produced this entry, so the fact
actually in scope is `not cond`, not `cond` itself. Populated by
`divisionVerdict`'s `.ite` arm (the then-branch pushes `(cond, false)`, the
else-branch pushes `(cond, true)`) and by its `.match_` arm (an arm's BODY is
scanned with that arm's guard pushed as `(g, false)` — reaching the body means
the guard evaluated true), mirroring march's `EIf` and `EMatch` arms in
`iter_div_sites` (`division_safety.ml:234-251`). -/
abbrev DivPath := List (Term × Bool)

/-- Does `t` mention any name in `names` anywhere in its subtree? A DELIBERATELY
over-approximate structural walk (does not exclude occurrences under a nested
binder of the same name), mirroring march's `expr_mentions`
(`refine_check.ml:1696`) — `path_shadow`'s sole caller, which explains in its
own comment why over-approximating is the safe direction here: this function
is used only to DISCARD a path fact when the name it is about gets rebound, so
over-approximating loses information (silence) rather than inventing a false
proof. Total over every `Term` constructor, matching `bodyCalls`/
`bodyAllocates`'s exhaustiveness discipline. -/
partial def termMentionsAny (names : List String) : Term → Bool
  | .lit _ _ => false
  | .var n _ _ => names.contains n
  | .app fn args _ => termMentionsAny names fn || args.any (termMentionsAny names)
  | .lam _ body _ => termMentionsAny names body
  | .let_ _ _ _ rhs body _ => termMentionsAny names rhs || termMentionsAny names body
  | .letfn _ _ _ _ fnBody body _ => termMentionsAny names fnBody || termMentionsAny names body
  | .ite c t e _ => termMentionsAny names c || termMentionsAny names t || termMentionsAny names e
  | .con _ args _ => args.any (termMentionsAny names)
  | .tuple elems _ => elems.any (termMentionsAny names)
  | .record fields _ => fields.any (fun (_, e) => termMentionsAny names e)
  | .field record _ _ _ => termMentionsAny names record
  | .match_ scrut arms _ =>
      termMentionsAny names scrut ||
        arms.any (fun (_, g, e) => (g.map (termMentionsAny names)).getD false || termMentionsAny names e)
  -- `.opaque_` RECURSES. This walk is the DELIBERATELY over-approximate
  -- `expr_mentions`, whose only use is to DISCARD a path fact when a name it
  -- talks about is rebound; over-approximating loses information (a division
  -- goes unproven → skip) instead of inventing a proof. Recursing therefore
  -- moves strictly in the safe direction, and matches march, whose
  -- `expr_mentions` is itself total over `Ast.expr`. Leaving it at `false`
  -- would let a stale guard about an outer `d` survive a rebinding hidden in
  -- an `ELetQ`/`ELetFn` child and license a WRONG non-zero proof.
  | .opaque_ children _ => children.any (termMentionsAny names)
  | .unsupported _ => false

/-- Drop every path entry whose condition mentions a name in `names` — march's
`path_shadow` (`refine_check.ml:1747`), called from `divisionVerdict`'s binding
arms alongside `retireDivFacts` so a rebinding retires BOTH channels: a guard
about the outer `d` must not survive to describe an inner, rebound `d`. -/
def retireDivPath (names : List String) (path : DivPath) : DivPath :=
  if names.isEmpty then path else path.filter (fun (c, _) => !termMentionsAny names c)

/-- march's `path_proves_nonzero` (`division_safety.ml:290`), copied faithfully
— a NO-SOLVER syntactic scan of `path`'s guard conditions for a proof that
`var ≠ 0`. Handles exactly march's patterns: a direct `var != 0` / `0 != var`;
a negated `var == 0` (the else-branch of `if var == 0 do .. else .. end`,
where `negated = true` dualises `==` to `!=`); and the four one-sided
inequalities `var > n` / `var >= n` / `var < n` / `var <= n` (or their
literal-on-the-left mirror image, normalised via `flip`) whenever the literal
`n` pins `var` strictly to one side of zero. `dual` mirrors march's `dual`
(negating the comparison operator itself when `negated`); `flip` mirrors
march's `flip` (swapping `n op var` to `var (flip op) n` before `proves` is
applied); `proves` mirrors march's `proves`. No Z3, no refined-parameter
channel — this checker never models march's `Refine.discharge` fallback, only
the syntactic fast-path that runs ahead of it. -/
def pathProvesNonzero (var : String) (path : DivPath) : Bool :=
  let dual : String → Option String
    | "==" => some "!="
    | "!=" => some "=="
    | "<"  => some ">="
    | ">=" => some "<"
    | ">"  => some "<="
    | "<=" => some ">"
    | _    => none
  let flip : String → String
    | "<"  => ">"
    | ">"  => "<"
    | "<=" => ">="
    | ">=" => "<="
    | op   => op
  let proves : String → Int → Bool
    | "!=", n => n == 0
    | "==", n => n != 0
    | ">",  n => n ≥ 0
    | ">=", n => n ≥ 1
    | "<",  n => n ≤ 0
    | "<=", n => n ≤ -1
    | _, _    => false
  let isVar : Term → Bool
    | .var x _ _ => x == var
    | _          => false
  path.any (fun (cond, negated) =>
    match cond with
    | .app (.var op0 _ _) [a, b] _ =>
        -- Mirrors march's `match int_of b, int_of a with | Some n, _ when
        -- is_var a -> .. | _, Some n when is_var b -> ..`: the SECOND arm is
        -- tried whenever the first's guard fails, independent of whether
        -- `int_of b` matched at all — NOT a sequential if/else on `intLitOf b`
        -- alone, which would skip the second arm too eagerly.
        let normalized : Option (String × Int) :=
          match intLitOf b with
          | some n =>
              if isVar a then some (op0, n)
              else match intLitOf a with
                | some n2 => if isVar b then some (flip op0, n2) else none
                | none    => none
          | none =>
              match intLitOf a with
              | some n2 => if isVar b then some (flip op0, n2) else none
              | none    => none
        match normalized with
        | none => false
        | some (op, n) =>
            match (if negated then dual op else some op) with
            | none => false
            | some op' => proves op' n
    | _ => false)

/-- What this checker can say about ONE division site, or about a whole body
(the join of its sites). THREE-VALUED on purpose — see `divisorVerdict`.

`safe`    = provably NOT a division by zero (march accepts, and so do we).
`unknown` = march's answer depends on machinery this checker does not model
            (a refinement type, or a Z3 discharge). Neither an accept nor a
            reject may be manufactured from it: it becomes `CapResult.skip`.
`divZero` = march DEFINITELY rejects this divisor, with no solver involved and
            no fact in scope able to change the answer. Two disjoint shapes
            reach it: a divisor that provably IS zero (a literal `0`, or a name
            tracked to literal `0`), and a divisor march classifies as a
            complex expression — neither an `ELit` nor an `EVar` — which
            `check_clause`'s catch-all (`division_safety.ml:497-500`) errors on
            unconditionally. Named `divZero` rather than the obvious `unsafe`
            only because `unsafe` is a Lean declaration modifier and cannot
            name a constructor; read it as "march rejects this division". -/
inductive DivVerdict where
  | safe
  | unknown
  | divZero
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Join over sibling subterms / division sites: `divZero` (a definite reject
march would report) dominates `unknown`, which dominates `safe`. A body with
both a provable div-by-zero and an unresolvable divisor is a reject — march
errors on the first one regardless of what it later decides about the
second. -/
def DivVerdict.join : DivVerdict → DivVerdict → DivVerdict
  | .divZero, _   => .divZero
  | _, .divZero   => .divZero
  | .unknown, _  => .unknown
  | _, .unknown  => .unknown
  | .safe, .safe => .safe

/-- Join a list of verdicts (`safe` for the empty list). -/
def DivVerdict.joinAll (vs : List DivVerdict) : DivVerdict :=
  vs.foldl DivVerdict.join .safe

/-- This checker's verdict on ONE divisor expression — a faithful, SOLVER-FREE
partition of `division_safety.ml`'s decision into the part we can settle and
the part we cannot.

march's policy is **reject-unless-proven-non-zero**, and the default fires
with NO solver involved: `check_clause`'s callback (`:489-503`) errors on a
literal `0` and on ANY non-`ELit`/non-`EVar` divisor, and `check_var_divisor`
(`:345-478`) errors on a variable it cannot discharge. Only two of its arms
can reach machinery this checker has no analogue of:

* a divisor variable that IS an Int-**refined** parameter
  (`clause_refined_params`) — `syntactic_nonzero` on the refinement, then a
  `Refine.discharge` (Z3) query;
* a divisor variable bound by a `let` to a NON-literal right-hand side —
  reflected by `smt_of` and sent to Z3.

march's own dispatch on the divisor's SYNTACTIC SHAPE (`check_clause`,
`division_safety.ml:485-500`) is a clean four-way, and only the third arm
needs machinery we lack:

1. `A.ELit (A.LitInt 0, _)`     → unconditional `Err.error`.
2. `A.ELit (A.LitInt _, _)`     → unconditional `()`.
3. `A.EVar {txt = var_name; _}` → `check_var_divisor`: path proof, tracked
   `let` value, refinement + Z3 — the only arm with a solver in it.
4. `_` (anything else)          → unconditional `Err.error` (`:497-500`,
   "division by a complex expression"). NO solver, NO refinement escape, NO
   path escape: the divisor's shape alone decides it.

So the four-way boundary here is:

* **`divZero`** — a literal `0` (arm 1), a `var` whose tracked `let` value is
  literal `0` and whose path does not prove it non-zero
  (`check_var_divisor`'s `Some (ELit (LitInt 0))` arm), **or a complex
  divisor: any decoded node that is neither a `lit` nor a `var`** (arm 4).
  All three are unconditional `Err.error`s in march.
* **`safe`** — a non-zero literal (arm 2), a `var` proven non-zero by the
  enclosing path (`path_proves_nonzero`, which march consults on BOTH the
  refined and unrefined branch and which needs no solver), or a `var` whose
  tracked `let` value is a non-zero literal (`Some (ELit (LitInt _))` → `()`).
* **`unknown`** — what is left of arm 3 only: a `var` that is a bare
  parameter, a match/lambda binder, or a `let` bound to a non-literal. march
  rejects MOST of these outright, but this checker cannot tell them apart
  from the refined-parameter and Z3 sub-arms without modelling refinement
  types and an SMT solver, so it declines to judge. Plus `Term.unsupported`
  — see below.

**Why arm 4 is safe to mirror as a reject** (this was left at `unknown` when
the three-way boundary landed, on the grounds that "is this node an `EVar`?"
is a reconstruction). It is not a reconstruction: `Term.var` is produced by
`Elab.decodeTerm` from `"kind":"EVar"` and from nothing else, and
`dump/ast_json.ml:315` emits `"kind":"EVar"` from `Ast.EVar` and from nothing
else — the correspondence `Term.var ⟺ A.EVar` is a decoded fact, not an
inference. The same holds for `Term.lit ⟺ A.ELit`. Crucially, the AST march's
`Division_safety.check_module` inspects is the SAME `desugared` module
`--emit-core-ast` serialises (`bin/main.ml:1755/1764/1834`), so the shape we
decode is literally the shape `check_clause` matched on — post-desugar, not
surface syntax.

That last point is what makes the module-qualified case safe. `Consts.k`
PARSES as `EField (ECon "Consts", "k")`, but `Desugar.desugar_expr`'s `EField`
arm (`lib/desugar/desugar.ml:677-697`, `flatten_module_path`) rewrites a
module path into a single `EVar {txt = "Consts.k"}` before any of this runs.
march therefore reaches `check_var_divisor "Consts.k"`, where a guard
`if Consts.k != 0 do 10 / Consts.k` DISCHARGES (verified: exit 0) — and we
decode the same node to `Term.var "Consts.k"`, where `pathProvesNonzero`
discharges it identically. A genuine record field access (`r.d`, base not a
module path) stays `EField` on both sides and march rejects it even under the
same guard (verified: exit 1). There is no march-variable form that decodes
to a non-`var` node.

`Term.unsupported` is the ONE shape held back at `unknown`. Every march
`kind` that currently decodes to it (`ECond`/`EPipe`/`EAnnot`/`EHole`/
`EAtom`/`ESend`/`ESpawn`/`EResultRef`/`EDbg`/`ELetFn`/`ELetQ`/`EAssert`/
`ESigil`) does land in arm 4, so rejecting would be right today — but it is
also `decodeTerm`'s open catch-all for kinds that do not exist yet, and a
future march AST node need not stay in arm 4. Nothing is lost by holding it:
an `unsupported` node anywhere in a body already makes its `Decl` report
`hasUnsupported`, which sends the file to exit 2 on its own.

**Ordering matters and mirrors march exactly** (Finding C1): the path is
consulted BEFORE the `DivFacts` (`let`-to-literal) lookup, so a guard proving
the divisor non-zero wins outright even over a `let`-to-zero fact in the same
scope. -/
def divisorVerdict (facts : DivFacts) (path : DivPath) (divisor : Term) : DivVerdict :=
  match intLitOf divisor with
  | some n => if n == 0 then .divZero else .safe
  | none =>
    match divisor with
    | .var n _ _ =>
        if pathProvesNonzero n path then .safe
        else
          match facts.find? (fun (m, _) => m == n) with
          | some (_, v) => if v == 0 then .divZero else .safe
          -- A variable with no tracked literal: a parameter (refined or not),
          -- a pattern/lambda binder, or a `let` to a non-literal. march
          -- rejects all but the refined/Z3-discharged cases; we cannot tell
          -- which this is.
          | none => .unknown
    -- A COMPLEX divisor: neither an `ELit` nor an `EVar`, so march's
    -- `check_clause` catch-all (`division_safety.ml:497-500`) errors on it
    -- unconditionally — no solver, no refinement escape, no path escape.
    -- Enumerated one constructor at a time rather than left as `| _ =>`, so
    -- that a NEW `Term` constructor is a compile error here (a deliberate
    -- decision point) instead of silently inheriting a reject.
    --
    -- `.lit` reaches this arm only for a non-`Int` literal (`intLitOf`
    -- already consumed the `Int` case above); march's arms 1 and 2 match
    -- `A.ELit (A.LitInt _, _)` specifically, so a float/string/bool literal
    -- divisor falls into its catch-all too.
    | .lit _ _ | .app _ _ _ | .lam _ _ _ | .let_ _ _ _ _ _ _
    | .letfn _ _ _ _ _ _ _ | .ite _ _ _ _ | .con _ _ _ | .tuple _ _
    | .record _ _ | .field _ _ _ _ | .match_ _ _ _ => .divZero
    -- `.opaque_` as the DIVISOR ITSELF (`10 / dbg(x)`, `10 / :tag(x)`, ...)
    -- stays at "cannot judge", deliberately NOT joined into the `.divZero`
    -- row above. All nine kinds really do land in march's arm-4 catch-all
    -- today, so rejecting would be right — but this is a JUDGEMENT site, not
    -- a collector, and the whole point of this slice is that `opaque_`
    -- carries children WITHOUT modelling the node. Answering `unknown` keeps
    -- the file's verdict exactly what it was before `opaque_` existed (the
    -- enclosing decl's `hasUnsupported` sends it to exit 2 regardless), so
    -- the slice adds detection only where it can also justify it. Tightening
    -- this to `.divZero` is a separate, separately-verified change.
    | .opaque_ _ _ => .unknown
    -- `.unsupported` is `decodeTerm`'s open catch-all for march `kind`s this
    -- fragment does not decode — including ones that do not exist yet. Every
    -- kind it currently covers IS in march's arm 4, but a future one need not
    -- be, so this stays at "cannot judge"; the enclosing decl's
    -- `hasUnsupported` already drives such a file to skip anyway.
    | .unsupported _ => .unknown

/-- Division-safety scan for `cap no_panic` (`refinecheck/division_safety.ml`,
A3 slice (c) Task 2b, path-conditions fix Finding C1, three-way boundary
Finding 1) — the LITERAL-ZERO-WITH-SHADOWING-AND-PATH-CONDITIONS fragment, no
SMT. Walks a `dfn` body threading a `DivFacts` (the `let`-to-literal map) AND
a `DivPath` (the enclosing guard conditions, march's `dctx.path`), and JOINS
(`DivVerdict.join`) `divisorVerdict`'s answer over every division/modulo site
(`divOps`, divisor = SECOND argument) it reaches.

**Shadowing is the entire point of this checker** — `reject/t123`'s corpus
comment documents a real runtime panic (past `--check` with exit 0) from
exactly this omission. Every binder here — `let_` (a rebinding of `name`),
`lam`/`letfn` params, and match-arm binders — RETIRES (`retireDivFacts` AND
`retireDivPath`) the names it shadows from BOTH the incoming facts and the
incoming path BEFORE contributing anything of its own, so an outer `let d =
<lit>` (or an outer guard mentioning `d`) can never be misread as still
describing an inner, rebound `d`. This is exactly `reject/t123`'s shape: `if d
== 0 do 0 else let d = 0; 10 / d end` — the fact `not (d == 0)` (equivalently,
`d != 0`, from `pathProvesNonzero`'s dualisation of the else-branch) is about
the OUTER parameter, not the inner `let d = 0`, so the `else` branch's `let`
must retire whatever the outer scope believed about `d` — from BOTH channels
— before recording the fresh literal fact. `noPanicShadowedGuard` below still
pins this exact shape as a violation, now for the right reason: not because
path conditions are unmodelled, but because shadowing retires the outer path
fact before the inner zero fact is ever consulted.

**Path-condition tracking (Finding C1).** march's `check_var_divisor`
consults `path_proves_nonzero` BEFORE the `let`-value lookup — a guard proving
the divisor non-zero wins outright, even when a `let` in the SAME scope (not
retired by shadowing) would otherwise read as a zero fact. `divisorVerdict`
mirrors that ordering exactly. `divisionVerdict`'s `.ite` arm pushes `(cond,
false)` onto the path for the then-branch and `(cond, true)` (negated) for the
else-branch — march's `dctx.path` entries, with their `negated` flag, are
built the exact same way. `pathProvesNonzero` (defined above) is march's own
`path_proves_nonzero`, copied faithfully: `d != 0`, `0 != d`, a negated `d ==
0`, and the four one-sided inequalities (`d > 0`, `d >= 1`, `d < 0`, `d <=
-1`, or their literal-on-the-left mirror images) all prove non-zero; anything
else is silent (never a false proof — see `pathProvesNonzero`'s own
docstring). Prior to this fix, this checker modeled NO path-condition channel
at all and so FALSE-REJECTED a `let`-bound literal-zero divisor under a guard
that march itself accepts as proven non-zero (e.g. `let d = 0; if d != 0 do 10
/ d else 0 end`) — the worst class of divergence for a differential oracle,
since it cries wolf on a program march accepts.

**The unresolved-divisor case is a SKIP, not an accept (Finding 1).** This
paragraph used to claim refined-parameter and complex divisors were "out of
scope, permanently, without a solver" and that the gap "has not yet been
observed to surface on its own". Both clauses were WRONG. march's division
policy is REJECT-unless-proven-non-zero and its default fires with no solver
at all — `check_clause`'s catch-all errors on every non-`ELit`/non-`EVar`
divisor (`division_safety.ml:498-503`) and `check_var_divisor`'s `None` arm
errors on a variable with neither a proving path nor a tracked `let` value
(`:394-399`). Two plain, fully-in-fragment probes surface it directly:
`fn f(d : Int) : Int do 10 / d end` and
`fn f(a : Int, b : Int) : Int do 10 / (a + b) end`, both under `cap no_panic`
— march rejects both, and this checker used to ACCEPT both.

The fix is NOT to flip those to `violation`. march genuinely ACCEPTS a divisor
whose non-zeroness comes from a refinement type
(`fn f(d : {v : Int | v != 0}) : Int do 10 / d end`, verified against the
binary) or from a Z3 discharge, and blanket-rejecting would trade a false
accept for a FALSE REJECT — the worse error class for an oracle. Per the
governing rule stated at length in `matchExhaustive`'s docstring — *any march
decision this checker RECONSTRUCTS rather than models must fail conservative,
toward "cannot judge"* — an unresolved divisor answers `DivVerdict.unknown`,
which `checkOneModule` turns into `CapResult.skip` and `MarchLeanCheck` into
exit 2. Provable zero still rejects, provable non-zero still accepts; only the
middle changed, and it changed from a confident wrong answer to no answer.

Consequence for the ledger: `scripts/expected-skips.txt` gains every
`cap no_panic` file whose divisor is a bare parameter, a pattern/lambda
binder, or a `let` to a non-literal. That is the intended cost, and closing
it properly needs refinement-type decoding plus an SMT solver.

**The COMPLEX-divisor half of that bucket has since been tightened back to a
reject.** `10 / (a + b)` is not an unresolved `EVar` at all — it is march's
arm 4, `check_clause`'s catch-all (`division_safety.ml:497-500`), which errors
with no solver, no refinement escape and no path escape. The reason it was
originally left at `unknown` — that "is this decoded node an `EVar`?" is a
reconstruction — does not hold: `Term.var` decodes from `"kind":"EVar"` and
only from there, out of the very same post-desugar AST `check_clause` reads,
and module-qualified names (the one form that LOOKS complex but is a variable
to march) are already flattened to `EVar "M.k"` by desugar before either side
sees them. `divisorVerdict`'s docstring works the correspondence through in
full. So the boundary is now four-way: provable zero and complex both reject,
provable non-zero accepts, and only an undischarged `var` — where a
refinement type or a Z3 query really could go either way — declines. -/
partial def divisionVerdict (facts : DivFacts) (path : DivPath) : Term → DivVerdict
  | .lit _ _ => .safe
  | .var _ _ _ => .safe
  | .app fn args _ =>
      let here :=
        match fn with
        -- Exactly TWO arguments, mirroring march's own guard
        -- (`EApp (EVar op, [lhs; rhs], sp) when List.mem op div_ops`,
        -- `division_safety.ml:214`). An `args[1]?` lookup would also fire on a
        -- 3+-ary application of one of these names and hand march's `args[1]`
        -- a divisor march never looked at — harmless while the arm answered
        -- `unknown`, a false REJECT now that a complex divisor rejects.
        | .var op _ _ =>
            match args with
            | [_, divisor] => if divOps.contains op then divisorVerdict facts path divisor else .safe
            | _ => .safe
        | _ => .safe
      DivVerdict.joinAll
        (here :: divisionVerdict facts path fn :: args.map (divisionVerdict facts path))
  | .lam params body _ =>
      let names := params.map (·.1)
      divisionVerdict (retireDivFacts names facts) (retireDivPath names path) body
  | .let_ name _ _ rhs body _ =>
      (divisionVerdict facts path rhs).join
        (divisionVerdict (bindLetFacts name rhs facts) (retireDivPath [name] path) body)
  | .letfn name param _ _ fnBody body _ =>
      (divisionVerdict (retireDivFacts [name, param] facts) (retireDivPath [name, param] path) fnBody).join
        (divisionVerdict (retireDivFacts [name] facts) (retireDivPath [name] path) body)
  | .ite c t e _ =>
      DivVerdict.joinAll
        [ divisionVerdict facts path c
        , divisionVerdict facts ((c, false) :: path) t
        , divisionVerdict facts ((c, true) :: path) e ]
  | .con _ args _ => DivVerdict.joinAll (args.map (divisionVerdict facts path))
  | .tuple elems _ => DivVerdict.joinAll (elems.map (divisionVerdict facts path))
  | .record fields _ => DivVerdict.joinAll (fields.map (fun (_, e) => divisionVerdict facts path e))
  | .field record _ _ _ => divisionVerdict facts path record
  -- A guard runs in the pattern's own binder scope (its names are already
  -- bound by the time the guard is evaluated), so it is scanned with the SAME
  -- retired facts/path as the body, not the outer ones.
  --
  -- **A SUCCESSFUL guard is a proof available to that arm's BODY** — march's
  -- `EMatch` arm (`division_safety.ml:240-246`) scans the guard with the
  -- retired-only `ac`, then rebuilds `ac' = { ac with path = (g, false) ::
  -- ac.path }` and scans `arm.branch_body` with `ac'`. The flag is `false`
  -- (NOT negated): reaching an arm's body means the guard EVALUATED TRUE, so
  -- the fact in scope is `g` itself — exactly the `.ite` THEN-branch
  -- treatment, and the opposite of its else-branch `(cond, true)`. Omitting
  -- this push false-rejected `let d = 0; match x do Some(_) when d != 0 -> 10
  -- / d | _ -> 0 end`, which march accepts (`noPanicMatchGuardProvesNonzero`
  -- below pins it). Note the guard itself is still scanned WITHOUT its own
  -- condition on the path — a guard cannot assume itself.
  | .match_ scrut arms _ =>
      (divisionVerdict facts path scrut).join
        (DivVerdict.joinAll (arms.map (fun (p, g, e) =>
          let names := patBinderNames p
          let facts' := retireDivFacts names facts
          let path' := retireDivPath names path
          let bodyPath := match g with
            | some cond => (cond, false) :: path'
            | none      => path'
          ((g.map (divisionVerdict facts' path')).getD .safe).join
            (divisionVerdict facts' bodyPath e))))
  -- `.opaque_` RECURSES — but with BOTH channels EMPTIED, and that is the
  -- load-bearing part of this arm. march's `iter_div_sites`
  -- (`division_safety.ml:204-269`) walks all nine kinds too, but it walks
  -- them KNOWING their shape: `ELetFn`/`ELetQ` retire the names they bind
  -- (`under (n :: lam_param_names ps) body`, `under (pat_binders p) body`)
  -- and `ECond` pushes each arm's condition onto `path`. `Term.opaque_`
  -- records neither binders nor arm structure, so we cannot reproduce either.
  -- Carrying the OUTER facts/path in unchanged would be unsound in the
  -- false-REJECT direction: a stale `d = 0` fact surviving into an `ELetFn`
  -- body that rebinds `d` would manufacture a `divZero` march never renders.
  -- Emptying both channels is conservative on both sides — with no facts a
  -- `var` divisor answers `unknown` (skip, never a fabricated reject), and
  -- with no path nothing is fabricated as PROVEN non-zero either. What
  -- survives is exactly the two judgements march makes unconditionally, with
  -- no solver, no refinement escape and no path escape: a literal-zero
  -- divisor (arm 1) and a complex divisor (arm 4). So `10 / 0` hidden in a
  -- `cond` arm is now the reject march says it is, and nothing else moves.
  | .opaque_ children _ => DivVerdict.joinAll (children.map (divisionVerdict [] []))
  | .unsupported _ => .safe

/-- `no_panic`'s SECOND half (A3 slice (c) Task 3): a non-exhaustive `match`
lowers to a runtime "no matching clause" panic (`tir/lower_state.ml:48`), so
march's `check_no_panic_module` (`typecheck.ml:8879`) rejects any `match_`
whose GUARDLESS arms alone are non-exhaustive — attributed by span-containment
to the enclosing fn, recorded once by `check_exhaustiveness`
(`typecheck.ml:4546`) and promoted to an error here. This checker instead
walks each `dfn` body directly (`matchExhaustive` below, called from
`checkOneModule`).

Built-in ADT constructor sets, verbatim from march's `builtin_ctors`
(`typecheck.ml:2551-2566`; `Bool` is not registered there — `Bool` matches
lower to `if`, never a `match`). Each is registered under BOTH its bare name
("Some") and its type-qualified alias ("Option.Some") — `bareCtorName` below
normalises either spelling in a `Pattern.con` to the bare form before
comparing against these lists, mirroring that dual registration. -/
def builtinCtors : List (String × List String) :=
  [ ("Option", ["Some", "None"]), ("Result", ["Ok", "Err"]), ("List", ["Nil", "Cons"]) ]

/-- Strip a leading `Type.` qualifier from a constructor name (`"Option.Some"`
→ `"Some"`), mirroring `builtin_ctors`' dual bare/qualified registration — a
`Pattern.con` may spell either form and both must match the same ctor. Only
the LAST dot-segment is kept; a name with no dot passes through unchanged.
`(n.splitOn ".").reverse.head?` is never `none` — `String.splitOn` always
returns at least one segment (`[n]` itself when `"."` doesn't occur), so
there is no genuine `[]` case to fall back on; `getD n` is just how that
totality is expressed without an unreachable match arm (M2, review finding:
an earlier `| [] => n` branch here was dead code). -/
def bareCtorName (n : String) : String :=
  ((n.splitOn ".").reverse.head?).getD n

/-- The head type-constructor name of a resolved `Ty`, peeling a `Ty.lin`
wrapper first (a linear/affine-qualified scrutinee, e.g. `linear Option(Int)`,
still names `Option`). `none` for anything that isn't headed by a `Ty.con` at
all (a type variable, tuple, etc.) — such a scrutinee is never one of
`builtinCtors`/a decoded `DType` anyway, so `matchExhaustive` treats it as
unknown. -/
def headTypeName : Ty → Option String
  | .con name _ => some name
  | .lin _ t => headTypeName t
  | _ => none

/-- Every `(type name, ctor names)` pair from every `Decl.dtype` reachable in
`decls`, gathered across the WHOLE module tree (`flattenDecls`, not just this
one module's own siblings) — a `match` inside a nested module may scrutinize a
user ADT declared at an outer level or a sibling, and `matchExhaustive` needs
that type's full ctor set regardless of which module declared it. -/
def dtypeCtorSets (decls : List Decl) : List (String × List String) :=
  (flattenDecls decls).filterMap (fun d => match d with
    | .dtype name _ ctors => some (name, ctors.map (·.name))
    | _ => none)

/-- march's or-pattern enumeration cap, verbatim from `or_expansion_cap`
(`typecheck.ml:3958`) — see `orExpansionSize`'s docstring for how it's used.
Read from march's source, not guessed: hardcoding a *different* number here
would silently misplace the accept/reject boundary relative to march's own. -/
def orExpansionCap : Nat := 256

/-- How many `spat` rows `p` would expand to under march's `norm_pat_all`,
mirroring `or_expansion_size` (`typecheck.ml:3963-3974`) field-for-field:
`or_` sums its alternatives' sizes, `con`/`tuple`/`record` multiply their
sub-patterns' sizes (a nested or-pattern in a constructor argument or tuple
element/record field is a cross-product, e.g. `C(a|b, a|b)` is 4 shapes, not
2), and every other case (`wild`/`var`/`lit`/`unsupported`) is a single row.
Saturates at `orExpansionCap + 1` at every fold step, exactly like march's
`sat`, so a pathological pattern is capped instead of the `Nat` (or, in
OCaml, the row list) growing without bound. -/
partial def orExpansionSize : Pattern → Nat
  | .or_ alts =>
      let sat (n : Nat) := min n (orExpansionCap + 1)
      sat (alts.foldl (fun acc a => sat (acc + orExpansionSize a)) 0)
  | .as _ p => orExpansionSize p
  | .con _ args =>
      let sat (n : Nat) := min n (orExpansionCap + 1)
      sat (args.foldl (fun acc a => sat (acc * orExpansionSize a)) 1)
  | .tuple elems =>
      let sat (n : Nat) := min n (orExpansionCap + 1)
      sat (elems.foldl (fun acc a => sat (acc * orExpansionSize a)) 1)
  | .record fields =>
      let sat (n : Nat) := min n (orExpansionCap + 1)
      sat (fields.foldl (fun acc (_, a) => sat (acc * orExpansionSize a)) 1)
  | .wild | .var _ _ | .lit _ | .unsupported => 1

/-- True when `p`'s or-expansion exceeds march's cap, mirroring
`pat_or_expansion_capped` (`typecheck.ml:4007-4008`). Past this point march
abandons per-row enumeration (`norm_pat_rows`, `typecheck.ml:4021-4022`) and
falls back to the widening `norm_pat`, whose `PatOr` case is
`| Ast.PatOr _ -> SPWild` (`typecheck.ml:3948`) — i.e. an over-cap or-pattern
becomes a full catch-all row, unconditionally, not "enumerate what we can."
`isCatchAllPattern` below applies this at every `or_` node it actually
inspects (see FINDING B in the general-conservatism-rule paragraphs of
`matchExhaustive`'s docstring for why this is the right place, not a
recursive re-derivation of march's whole-arm cap check). -/
def patOrExpansionCapped (p : Pattern) : Bool := orExpansionSize p > orExpansionCap

/-- Is `p` a catch-all pattern for exhaustiveness purposes — `wild`/`var`
directly, through any depth of `Pattern.as` (C2), an `or_` with ANY
alternative that itself is a catch-all (review finding, regression fix), OR
an `or_` whose or-expansion exceeds march's cap (Finding B, this commit —
see `patOrExpansionCapped`)? march's `norm_pat_all` expands `PatOr` by
concatenating every alternative's own normal-form rows (`| Ast.PatOr (alts,
_) -> List.concat_map norm_pat_all alts`), and `PatWild` normalises to a
single `SPWild` row (`| Ast.PatWild _ -> [SPWild]`); so an or-pattern with a
wildcard/var alternative anywhere yields an `SPWild` row that alone covers
the whole column, making the arm exhaustive regardless of its other
alternatives. The widening fallback (`norm_pat`'s `| Ast.PatOr _ -> SPWild`)
agrees, AND fires unconditionally once the cap is exceeded, independent of
whether any alternative happens to be a wildcard — a 300-alternative
`Red | Red | … | Red` or-pattern (no wildcard anywhere) is still a catch-all
past the cap, because march stops enumerating its named constructors at all.
`Red | _`, `_ | Red`, and `Green | _` are therefore catch-alls (regardless of
size); `Red | Green` (only constructor alternatives, under the cap) is NOT —
it falls through to `patCoveredCtors` below, contributing exactly its named
constructors, not blanket coverage. -/
partial def isCatchAllPattern : Pattern → Bool
  | .wild | .var _ _ => true
  | .as _ p => isCatchAllPattern p
  | .or_ alts => alts.any isCatchAllPattern || patOrExpansionCapped (.or_ alts)
  | .con _ _ | .tuple _ | .lit _ | .record _ | .unsupported => false

/-- Is `p` one of the pattern forms `matchExhaustive` actually models for
coverage purposes — `wild`/`var`/`con`/`as`/`or_`, recursively through `as`
and `or_`'s own alternatives? `tuple`/`lit`/`record`/`unsupported` are NOT
modeled (this checker has no notion of what they cover), and per the
safety-net rule below their presence on a guardless arm must never be read
as "does not cover" — see `matchExhaustive`'s docstring. -/
partial def isModeledArmPattern : Pattern → Bool
  | .wild | .var _ _ | .con _ _ => true
  | .as _ p => isModeledArmPattern p
  | .or_ alts => alts.all isModeledArmPattern
  | .tuple _ | .lit _ | .record _ | .unsupported => false

/-- The (bare-normalised) constructor names `p` covers, peeling `Pattern.as`
first (C2) and, for `Pattern.or_`, unioning every alternative's own covered
set (C1) — march's `norm_pat_rows` expands a `PatOr` at every depth before
computing coverage (`typecheck.ml:3966`), so `Red | Green` must count as
covering BOTH `Red` and `Green`, not neither. Anything else that isn't a
`Pattern.con` (after peeling) covers nothing here — including `wild`/`var`,
which are handled separately by the catch-all shortcut, not by name-set
coverage. -/
partial def patCoveredCtors : Pattern → List String
  | .as _ p => patCoveredCtors p
  | .or_ alts => alts.flatMap patCoveredCtors
  | .con name _ => [bareCtorName name]
  | .wild | .var _ _ | .tuple _ | .lit _ | .record _ | .unsupported => []

/-- Is a `match_`'s arm list exhaustive over `scrutTy`, per march's
`check_exhaustiveness` restricted to the guardless-coverage fragment it falls
back to whenever any arm carries a `when` guard (`typecheck.ml:4546-4581`:
"compute exhaustiveness over the guardless branches only")? A GUARDED arm's
pattern contributes NOTHING to coverage — if every guard fails at runtime, a
guarded-only match still falls through and panics — so only `guard = none`
arms are ever consulted below, for both the wildcard/var catch-all shortcut
and the constructor-set coverage test.

- A guardless arm whose pattern is a catch-all per `isCatchAllPattern` —
  `Pattern.wild`/`Pattern.var` directly, through any depth of `Pattern.as`
  (C2: `Red as r` binds, doesn't catch-all; `x as y` does, because `x` alone
  would), or an `or_` with ANY wild/var alternative (`Red | _`, `_ | Red`;
  regression fix, mirrors `norm_pat_all`'s `PatOr`/`PatWild` handling) — is
  exhaustive regardless of the scrutinee type or any other arm. An `or_` of
  constructors only (`Red | Green`) is NOT a catch-all this way; it is judged
  by `patCoveredCtors` below instead.
- SAFETY NET (C1+C2, review finding): if any guardless arm's pattern is not
  one of the modeled forms `isModeledArmPattern` recognizes — i.e. it's (or
  recursively contains, through `as`/`or_`) an `unsupported`/`tuple`/`lit`/
  `record` — the match is conservatively treated as exhaustive. This mirrors
  the unknown-SCRUTINEE-TYPE carve-out two paragraphs below: both are "we do
  not model this," and only ONE direction of not-modeling is safe to invent —
  "cannot prove non-exhaustive ⇒ do not manufacture a reject." Before this
  net, an unmodelled PATTERN (e.g. an or-pattern with no `PatOr` decode, or an
  as-pattern nobody peeled) silently contributed nothing to coverage and was
  judged NOT a catch-all either, i.e. treated as "covers nothing" — the
  opposite, unsafe default from the type side, and the root cause of C1/C2's
  false rejects.
- Otherwise, collect the (bare-normalised, `Pattern.as`/`Pattern.or_`-aware)
  constructor names every guardless arm covers (`patCoveredCtors`) and test
  them against the scrutinee's full ctor set — from `userCtors` (a module
  tree's decoded `DType`s, see `dtypeCtorSets`) FIRST, then `builtinCtors`,
  by `scrutTy`'s head type name (C3, review finding: `List.find?` returns the
  FIRST hit, so a user type that shadows a built-in name — e.g. a local
  `type Result = Success(Int) | Failure(Int)` — must be judged against ITS
  OWN ctors, not `Result`'s built-in `{Ok, Err}`; see
  `accept/t82_local_type_exhaustive_shadows_stdlib_ctor`, which pins exactly
  this restriction-to-the-declaring-module's-own-ctors behavior) — BUT first,
  if `userCtors` contains MORE THAN ONE entry for `scrutTy`'s head name
  (FINDING A, this commit: two different modules each declaring their own
  `type Color = …`), the type is treated as unresolvable and the match is
  conservatively exhaustive — see the general-conservatism-rule paragraphs
  below for why picking either one would be unsound. If the scrutinee's type
  resolves to NEITHER (unknown to this checker entirely — no built-in, no
  decoded `DType`), the match is conservatively treated as exhaustive: an
  unknown-type match is out of this checker's fragment, and inventing a
  reject over it would be a false reject this differential oracle must never
  manufacture (see the module docstring's false-reject discipline).

**Known shallowness (Finding I1, documented not fixed):** coverage above
compares only TOP-LEVEL constructor names; a `Pattern.con`'s own argument
patterns are never inspected. march instead runs a full Maranget coverage
matrix over the whole arm column (`check_exhaustiveness`), so e.g.
`type Inner = A | B`, `type Outer = W(Inner)`, matching `W(A) -> ..` alone IS
flagged non-exhaustive by march but judged exhaustive here (a false accept —
`W`, the only ctor of `Outer`, is "covered" without looking at whether `A`
alone covers `Inner`). This is deliberately NOT implemented: no corpus
target in this fragment needs it, and it is a materially larger analysis
(a full pattern matrix, not a single constructor-name set). It would also
become reachable for `Option`/tuple-headed scrutinees the moment the
`Infer` builtin-ctor gap (`t59`'s pre-existing skip; see the `A3 slice (c),
Task 3` fixtures below) is ever closed and such matches stop being screened
out upstream.

**Known false-accept class (Finding I2, documented not fixed):** a
`Pattern.lit` arm list over a non-ADT scrutinee (`Int`/`String`/`Float`) has
no built-in/user ctor set to test against at all — but that mismatch is never
even reached: `Pattern.lit` is not one of `isModeledArmPattern`'s recognized
forms, so the SAFETY NET above fires FIRST on the unmodelled `.lit` pattern
and short-circuits to "exhaustive" before `headTypeName`/`scrutTy` are
consulted at all — this checker EXITS 0 on it either way. march, by
contrast, DOES exhaustiveness-check literal patterns against a scrutinee's
structure (`check_exhaustiveness`
handles `PatLit` rows) and rejects `match n do 0 -> 1; 1 -> 2 end` (no
catch-all) as non-exhaustive. This is therefore a live false-accept class,
not merely a "skip" as an earlier draft of this docstring implied — `Int`/
`String`/`Float` matches are otherwise fully in-fragment (they reach this
gate at all, rather than being screened out by `hasUnsupported` upstream),
so the unknown-type carve-out's conservatism here produces a genuine
divergence from march, not an out-of-fragment skip. Left unfixed
deliberately: narrowing the unknown-type rule to close this gap risks
reintroducing a false reject elsewhere (the exact failure mode C1/C2 already
demonstrated), which this differential oracle must never manufacture.

---

**THE GENERAL CONSERVATISM RULE (review finding, this commit — read this
before touching any input to the coverage test below):**

march's actual exhaustiveness decision, `find_missing_mc`, takes THREE
inputs: the arm patterns, the constructor universe to test them against, and
the or-expansion policy that governs how a `PatOr` is normalized. This
checker only ever sees the FIRST of those directly (the decoded `Pattern`
tree); the other two it must *reconstruct* from a flattened, already-decoded
tree with no access to march's `env` (module-scoped ctor resolution) or its
row-budget accounting. The pattern-shape SAFETY NET a few paragraphs up
protects only the first input — an arm pattern shape this checker doesn't
model. It has NO purchase over the other two, because they are not shapes
*within* the coverage test, they are INPUTS *to* it; an unmodelled pattern
shape and a mis-reconstructed universe or policy are different failure
classes that happen to demand the same remedy.

The rule: **any input this checker reconstructs rather than genuinely
models — now or later — MUST fail conservative.** On any doubt about what
march would actually use, treat the match as exhaustive; never manufacture a
reject from a guess. Concretely, as of this commit:

- **Constructor universe** (FINDING A). `dtypeCtorSets` keys every
  `Decl.dtype` reachable in the WHOLE flattened tree by BARE name, with no
  notion of march's module-scoped resolution — `ctors_for_type`'s
  `local_shadow` (`typecheck.ml:4027-4059`), which restricts the ctor
  universe to the CURRENT module's own type when a same-named type is ALSO
  declared elsewhere, using `ci_module` bookkeeping this checker has no
  analogue of. Before this commit, `(userCtors ++ builtinCtors).find?`
  silently took whichever `DType` came first in decl order — i.e. an
  arbitrary pick with no relationship to march's actual, module-scoped
  answer, and therefore a live false-reject site (order-dependent: swapping
  two sibling modules' declaration order flipped the verdict). Fix: when
  `scrutTy`'s head name matches MORE THAN ONE decoded `DType`, this checker
  cannot tell which one march would pick, so it picks none — the type is
  treated as unresolvable, i.e. exhaustive. This is deliberately NOT a full
  `ci_module` model (that would be the faithful fix); it is the safe
  under-approximation until one exists. The single-match case is unaffected
  — `userCtors` is still consulted before `builtinCtors` there (C3).
- **Or-expansion policy** (FINDING B). march abandons per-row or-pattern
  enumeration past `or_expansion_cap = 256` rows (`typecheck.ml:3958`,
  `orExpansionCap` above) and falls back to the widening `norm_pat`, whose
  `PatOr` case is unconditionally `SPWild` (`typecheck.ml:3948`) — i.e. march
  itself gives up and treats an over-cap or-pattern as a catch-all, full
  stop, regardless of which constructors it names. Before this commit, this
  checker enumerated every or-pattern unconditionally via `patCoveredCtors`
  and contributed only its named constructors — correct under the cap, but a
  false reject past it: a 300-alternative `Red | Red | … | Red` arm was
  judged to cover only `Red` (march judges it a catch-all past the cap) and
  the match was rejected as non-exhaustive on a type with `Green`/`Blue`
  also present, though march accepts it. Fix: `orExpansionSize` mirrors
  `or_expansion_size` field-for-field (including the cross-product over
  `con`/`tuple`/`record` sub-patterns, not just top-level alternative
  counting), and `isCatchAllPattern` treats an over-cap guardless `or_` as a
  catch-all — NOT as "enumerate what we can, ignore the rest," which would
  silently under-count coverage relative to what march actually decided and
  manufacture the exact false reject above.

A future contributor adding a THIRD reconstructed input to this function —
or anyone touching the two above — must give it the same treatment: when
this checker cannot be sure it has reconstructed march's answer correctly,
default to exhaustive. A reconstructed input we are not certain of is
exactly where this checker is most CONFIDENT and most likely WRONG; the
safety net's "unmodelled pattern shape ⇒ exhaustive" rule cannot save you
here, because there is no pattern shape to fail to recognize — the mistake
would be baked into a `Bool`/`List` this function computed with complete
confidence from an incomplete reconstruction. -/
def matchExhaustive (scrutTy : Ty) (userCtors : List (String × List String))
    (arms : List (Pattern × Option Term × Term)) : Bool :=
  let isCatchAll : Pattern × Option Term × Term → Bool := fun (p, g, _) =>
    g.isNone && isCatchAllPattern p
  if arms.any isCatchAll then true
  else if arms.any (fun (p, g, _) => g.isNone && !isModeledArmPattern p) then true
  else
    let covered : List String :=
      arms.flatMap (fun (p, g, _) => if g.isSome then [] else patCoveredCtors p)
    match headTypeName scrutTy with
    | none => true
    | some tyName =>
        -- FINDING A: more than one decoded `DType` sharing this bare name
        -- means we cannot reconstruct march's module-scoped pick — fail
        -- conservative (exhaustive) rather than guess via decl order. See
        -- the general-conservatism-rule paragraphs above.
        if 1 < (userCtors.filter (fun (n, _) => n == tyName)).length then true
        else
          match (userCtors ++ builtinCtors).find? (fun (n, _) => n == tyName) with
          | none => true
          | some (_, ctors) => ctors.all covered.contains

/-- Every `match_` node reachable anywhere inside `t` (not just at the top
level of a body — a non-exhaustive match nested inside a `let`/tuple/another
match's arm is exactly as much a runtime panic surface as a top-level one),
paired with its scrutinee type and arm list, ready for `matchExhaustive`.
Total over every `Term` constructor, matching `bodyCalls`/`bodyAllocates`'s
exhaustiveness-of-the-walk-itself discipline. -/
partial def matchesIn : Term → List (Ty × List (Pattern × Option Term × Term))
  | .lit _ _ => []
  | .var _ _ _ => []
  | .app fn args _ => matchesIn fn ++ args.flatMap matchesIn
  | .lam _ body _ => matchesIn body
  | .let_ _ _ _ rhs body _ => matchesIn rhs ++ matchesIn body
  | .letfn _ _ _ _ fnBody body _ => matchesIn fnBody ++ matchesIn body
  | .ite c t e _ => matchesIn c ++ matchesIn t ++ matchesIn e
  | .con _ args _ => args.flatMap matchesIn
  | .tuple elems _ => elems.flatMap matchesIn
  | .record fields _ => fields.flatMap (fun (_, e) => matchesIn e)
  | .field record _ _ _ => matchesIn record
  | .match_ scrut arms _ =>
      (scrut.ty, arms) :: (matchesIn scrut ++ arms.flatMap (fun (_, g, e) =>
        (g.map matchesIn).getD [] ++ matchesIn e))
  -- `.opaque_` RECURSES: a pure collector, and a non-exhaustive `match`
  -- nested inside a `cond` arm or a `let?` continuation is exactly as much a
  -- runtime-panic surface as a top-level one. march agrees — its
  -- exhaustiveness diagnostic is recorded by the typechecker's own total
  -- expression walk, which visits these nodes, and `check_no_panic_module`
  -- then promotes the recorded span to an error. `matchExhaustive` remains
  -- the judgement site and remains conservative (unsure ⇒ "exhaustive"), so
  -- adding nodes here cannot manufacture a reject on a match this checker
  -- cannot actually classify.
  | .opaque_ children _ => children.flatMap matchesIn
  | .unsupported _ => []

/-- Does `t` (a function body) contain any non-exhaustive `match_` at all,
anywhere within it? -/
def bodyHasNonExhaustiveMatch (userCtors : List (String × List String)) (t : Term) : Bool :=
  (matchesIn t).any (fun (scrutTy, arms) => !matchExhaustive scrutTy userCtors arms)

/-- Is `used` covered by any declared need? Reflexive and directional. -/
def covered (declared : List String) (used : String) : Bool :=
  declared.any (fun need => capSubsumes need used)

/-- Check one module (not recursing into nested modules — the caller does
that, since each module is checked against its OWN declared needs).
`selfDeclaredCaps` is the list of fully-qualified cap paths (e.g.
`"Db.Migrated"`) that Check 1 must treat as covered regardless of `needs`,
per Finding I1's self-declaration exemption — see `checkCaps`'s docstring for
why this is passed in ONLY at the top-level call and always `[]` for a
nested `dmod`. `inheritedCaps` is the subset of `inheritableBehavioralCaps`
(below) an ENCLOSING module has declared or itself inherited — Finding I3;
see this function's `pure`/`deterministic`/`no_extern`/`no_panic`-explicit-panic
gates below for how it is combined with this module's own `opts`. `userCtors`
is every `DType` ctor set reachable in the WHOLE module tree (`dtypeCtorSets
m.decls`, computed once in `checkCaps` and threaded unchanged through every
recursive call — see that function and `checkDecls`), consulted by the
`no_panic` exhaustiveness gate below for a user-ADT scrutinee. -/
def checkOneModule (modName : String) (decls : List Decl)
    (moduleCaps : List (String × List String))
    (selfDeclaredCaps : List String := [])
    (inheritedCaps : List String := [])
    (userCtors : List (String × List String) := []) : CapResult :=
  let declared := declaredNeeds decls
  -- Check 1 — signature Cap(X) coverage over `param_tys @ ret_tys`
  -- (march's `check_module_needs`). Parameter caps are ALWAYS scanned.
  --
  -- RETURN caps are scanned only when this module is ENTIRELY in fragment
  -- (excluding `Decl.dproofcap`, which is in-fragment but drives
  -- `selfDeclaredCaps` below rather than this gate — see Finding I1). A
  -- module carrying some OTHER out-of-fragment declaration may satisfy a
  -- return cap through machinery this checker still does not model at all
  -- (e.g. an actor/interface construct this fragment has no representation
  -- for whatsoever); rather than mis-reject such a return, defer — the file
  -- skips downstream via the out-of-fragment gate, exactly as it did before
  -- this scan existed. A fully-in-fragment module has only modeled IO/proof
  -- caps and no such escape, so an uncovered return cap there is a real
  -- Check 1 violation (the M1 gap: e.g. `fn f(cap : Cap(IO.Console)) :
  -- Cap(IO.Network)` under `needs IO.Console`). Params are left
  -- unconditional so no existing signature-based reject changes.
  let retCaps :=
    if decls.any Decl.hasUnsupported then [] else decls.flatMap capsInReturnSignature
  let sigCaps := decls.flatMap capsInSignature ++ retCaps
  -- Finding I1: a cap in `selfDeclaredCaps` is covered regardless of
  -- `needs` — march's self-declaration exemption (`typecheck.ml:6966-6970`)
  -- lets a proof cap's own declaring module use it in its own signatures
  -- (params OR returns, exactly like any other Check-1-scanned cap) without
  -- repeating `needs Module.X`. `accept/t62`'s returned `Cap(Db.Migrated)`
  -- under only `needs IO` is exactly this case, now covered here directly
  -- rather than via the return-cap defer-gate above.
  match sigCaps.find? (fun c => !covered declared c && !selfDeclaredCaps.contains c) with
  | some bad =>
      .violation s!"Check 1: `Cap({bad})` used in module `{modName}` but `{bad}` is not declared in `needs`"
  | none =>
  -- Check 5 — extern cap coverage
  let externCaps := decls.flatMap (fun d =>
    match d with | .dextern (some c) _ => [c] | _ => [])
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
  | _ =>
  -- Finding I2: EVERY extern block implies `Cap(IO.Foreign)` onto EVERY
  -- extern fn it contains, UNCONDITIONALLY of that block's own declared
  -- `ext_cap_ty` (`typecheck.ml:6941-6950`: `extern_cap_uses`'s `base =
  -- [("IO.Foreign", sp)]` and, per extern fn, `own = if ef_blocking then
  -- [...] else ["IO.Foreign"]` — both computed with no reference to
  -- `ext_cap_ty` at all; the comment there literally reads "any DExtern →
  -- needs IO.Foreign"). Verified empirically against `march --check`: an
  -- extern block whose `ext_cap_ty` isn't even `Cap`-shaped at all (e.g.
  -- `extern "libc" : Int do fn counter_migrate_state(...) ... end`, which
  -- this checker's own `Decl.dextern` decodes with `capTy = none`) STILL
  -- rejects a migrate-named fn inside it with the same "migrate_state must
  -- be IO-free" error. So this checker's `capTy` (which drives Check 5's
  -- SEPARATE `needs`-coverage obligation) must play NO role in Check 8 at
  -- all — an extern fn whose name matches `is_migrate_fn_name` is a
  -- violation whenever it sits in ANY extern block, `capTy` irrelevant (this
  -- closes gap 2 in `bodyCallsIO`'s docstring above).
  match decls.find? (fun d =>
      match d with
      | .dextern _ fnNames => fnNames.any isMigrateFnName
      | _ => false) with
  | some (.dextern _ fnNames) =>
      let name := (fnNames.filter isMigrateFnName).headD "?"
      .violation s!"Check 8: extern fn `{name}` in module `{modName}` ends in `_migrate_state` but every extern block implies `Cap(IO.Foreign)`"
  | _ =>
  -- A3 slice (c), Task 2 — the five behavioral capability checks. A module
  -- declares zero or more of these via a sibling `Decl.dopts [...]`; each
  -- scans only THIS module's own `dfn` bodies/decls — `checkDecls` recurses
  -- into a nested `dmod` separately, against that child's OWN `opts` PLUS
  -- whatever it inherits from here (`inheritedCaps`, threaded in by
  -- `checkDecls`'s recursive call — see Finding I3 below).
  --
  -- **Finding I3 — `pure`/`deterministic`/`no_extern`/`no_panic`'s
  -- explicit-panic half ARE inherited by nested modules; `no_alloc` and
  -- `no_panic`'s division-safety half are NOT.** march threads
  -- `pure_mod`/`deterministic_mod`/`no_extern_mod`/`no_panic_mod` on its `env`
  -- (`typecheck.ml:636-644`); a nested `DMod`'s own env is derived from the
  -- OUTER env via `{ env with local_fns = ...; current_module = ...;
  -- cap_qual_prefix = ... }` (`typecheck.ml:9336-9339`, no `_mod` field
  -- mentioned) and the four flags are set to `true` by `DOpts` handling
  -- (`:10182-10185`) but NEVER reset to `false` — so once set on an
  -- ancestor, a flag stays `true` all the way down, and `check_pure_module`
  -- /`check_deterministic_module`/`check_no_extern_module`/
  -- `check_no_panic_module` (its explicit-panic-call half) all run against
  -- `inner_env`'s (inherited) flags, not a re-derivation from the nested
  -- module's own `decls` (`:9484-9491`). Verified directly against `march`:
  -- `mod Outer do cap pure; needs IO.Console; mod Inner do needs IO.Console;
  -- fn g(c : Cap(IO.Console)) : () do println("io") end end; fn f() : Int do
  -- 1 end end` REJECTS (`Inner.g`'s `println` violates the INHERITED `pure`),
  -- even though `Inner` itself declares no `cap pure` at all. Same shape for
  -- `no_extern` and a nested `extern` block.
  --
  -- The exception is deliberate and empirically verified, not an oversight:
  -- `no_alloc` (`refinecheck/no_alloc.ml:71-81`) and the DIVISION-SAFETY half
  -- of `no_panic` (`refinecheck/division_safety.ml:522-533`, `check_decls`)
  -- are SEPARATE passes over the raw `Ast.decl` tree, outside march's
  -- `env`-threading entirely — each RE-DERIVES its own `no_alloc`/`no_panic`
  -- boolean by scanning `decls` (the CURRENT module's own decl list) for a
  -- `DOpts` sibling on every recursive `DMod` call, with no inherited
  -- parameter at all (`division_safety.ml`'s own comment: "A nested module
  -- re-derives its own `cap` directive: capabilities do not inherit
  -- inward"). Verified directly against `march`: a nested allocating fn under
  -- a `cap no_alloc` parent, and a nested `10 / 0` under a `cap no_panic`
  -- parent, BOTH still ACCEPT (exit 0) — the parent's cap does not reach
  -- them. So `inheritedCaps` below is consulted ONLY for the four inheritable
  -- gates; `no_alloc` and the division-safety `no_panic` gate stay scoped to
  -- this module's own `opts`, exactly as before.
  --
  -- **`dfn` ONLY — no `Decl.dlet` scan here.** march's own
  -- `check_pure_module`/`check_deterministic_module`/`check_no_panic_module`
  -- (`typecheck.ml`) all iterate `Ast.DFn` ONLY; a plain `Ast.DLet` (a real
  -- top-level `let x = ...` binding) is never scanned by any of the three, so
  -- scanning `Decl.dlet` bodies here would false-reject a
  -- `pure`/`deterministic`/`no_panic` module whose only "violation" is a
  -- side-effecting top-level `let` — a file march itself accepts (confirmed:
  -- `mod P do cap pure; let x = println("side effect") end` — march exit 0,
  -- a `dlet`-scanning checker exit 1). An earlier version of this file
  -- carried exactly that `Decl.dlet` scan, as a workaround for
  -- `Elab.decodeDecl`'s `DFn` arm folding a ZERO-PARAM `fn` clause to
  -- `Decl.dlet name body`, which hid 0-param fns (`reject/t42`'s `fail()`,
  -- `t46`'s `gen()`, `t47`'s `ts()`) from a `dfn`-only scan. That fold has
  -- since been fixed at the source (`Elab.lean`'s `DFn` arm now decodes a
  -- 0-param clause to `Decl.dfn name [] retTy body`, an empty-param `dfn`,
  -- not a `dlet`), so the workaround is no longer needed and has been
  -- removed: a 0-param fn is a real `dfn` again and this scan finds it
  -- without also catching genuine top-level `let`s march never looks at.
  let opts := decls.flatMap (fun d => match d with | .dopts o => o | _ => [])
  -- Finding I3: the EFFECTIVE set for the four inheritable gates
  -- (`pure`/`deterministic`/`no_extern`/`no_panic`-explicit-panic) is this
  -- module's own `opts` UNION whatever it inherits from an enclosing module
  -- — see the docstring above this block. `no_alloc` and the division-safety
  -- half of `no_panic` deliberately keep consulting `opts` alone, below.
  let effective := opts ++ inheritedCaps
  let dfns := decls.filterMap (fun d => match d with
    | .dfn name _ _ body => some (name, body)
    | _ => none)
  -- `pure` (typecheck.ml:8232): bans EVERY name in `builtinCaps` (the whole
  -- builtin→cap table, IO/Alloc/Panic alike) UNION the four extra names that
  -- are side-effecting but not in that table: `spawn`, `send`, `exit`,
  -- `read_byte`.
  let pureBanned := builtinCaps.map (·.1) ++ ["spawn", "send", "exit", "read_byte"]
  match if effective.contains "pure" then dfns.find? (fun (_, body) => bodyCalls pureBanned body) else none with
  | some (name, _) =>
      .violation s!"cap pure: fn `{name}` in module `{modName}` performs a side effect"
  | none =>
  -- `deterministic` (`:8297`, `is_nondeterministic_cap` `:8213`): bans ONLY
  -- the builtins whose cap is `IO.Clock` or `IO.Random` (6 names) — NOT the
  -- whole `builtinCaps` table, which would false-reject ordinary IO.
  let detBanned := (builtinCaps.filter (fun (_, c) => c == "IO.Clock" || c == "IO.Random")).map (·.1)
  match if effective.contains "deterministic" then dfns.find? (fun (_, body) => bodyCalls detBanned body) else none with
  | some (name, _) =>
      .violation s!"cap deterministic: fn `{name}` in module `{modName}` performs a non-deterministic operation"
  | none =>
  -- `no_extern` (`:9026`, `check_no_extern_module`) rejects on EITHER of two
  -- conditions (Finding C2 — the second arm was previously missing entirely):
  -- (1) the module's own decls contain a `Decl.dextern`, OR (2) the module
  -- declares a `needs` whose path's FIRST segment is `"IO"` and some LATER
  -- segment is `"Foreign"` (`needs IO.Foreign`, `needs IO.Foreign.Blocking`,
  -- …) — march's `has_foreign`, mirrored exactly by `hasForeignNeed` below.
  -- `declared` (bound at the top of this function from `declaredNeeds decls`)
  -- is exactly this module's own dotted `needs` paths, so arm (2) reuses it
  -- rather than re-scanning `decls`.
  if effective.contains "no_extern" &&
      (decls.any (fun d => match d with | .dextern _ _ => true | _ => false) ||
       declared.any hasForeignNeed) then
    .violation s!"cap no_extern: module `{modName}` contains an extern block or declares `needs IO.Foreign`"
  else
  -- `no_alloc` (`refinecheck/no_alloc.ml`): a `dfn` body constructs a
  -- tuple/record/non-nullary-con/lambda. NOT inherited (Finding I3's
  -- exception) — `opts` alone, never `effective`.
  match if opts.contains "no_alloc" then dfns.find? (fun (_, body) => bodyAllocates body) else none with
  | some (name, _) =>
      .violation s!"cap no_alloc: fn `{name}` in module `{modName}` allocates"
  | none =>
  -- `no_panic`, explicit-panic half (`:8108`) — a `dfn` body directly calls
  -- `panic`. Exhaustiveness (a further half of `no_panic`) is Task 3, not
  -- modelled here. INHERITED (Finding I3) — `check_no_panic_module` runs
  -- against the env-threaded, monotone `no_panic_mod` flag, so `effective`.
  --
  -- **Finding I4 (documented, NOT implemented): this bans only `"panic"`,
  -- one of march's ~26-name panic surface.** march's
  -- `panic_surface_all_direct` ∪ `panic_surface_stdlib` (`typecheck.ml:8784-
  -- 8804`) is `panic`/`panic_`/`todo_`/`unreachable_`/`unwrap`/`expect`/
  -- `head`/`tail`/`last` (9 direct names) UNION 17 qualified names —
  -- `List.nth`/`List.hd`/`List.tl`/`List.head`/`List.last`/`List.min_elt`/
  -- `List.max_elt`/`Option.unwrap`/`Option.expect`/`Result.unwrap`/
  -- `Result.expect`/`Result.unwrap_err`/`Array.get`/`Array.set`/
  -- `String.slice_bytes`/`String.nth`/`NativeArray.get`/`NativeArray.set`.
  -- Every one of those 25 OTHER names is currently unbound in this checker's
  -- modeled fragment (no qualified-call decoding, no stdlib call surface at
  -- all), so a file calling one of them skips downstream via the
  -- out-of-fragment gate rather than reaching this scan — no live divergence
  -- TODAY. If any of those 25 names ever enters the modeled fragment (e.g.
  -- qualified calls are decoded, or `unwrap`/`head`/etc. become recognised
  -- builtins) WITHOUT this ban set being widened to match, a `cap no_panic`
  -- module calling one becomes a FALSE ACCEPT here (march rejects, this
  -- checker doesn't) — the same shape of gap `divisionVerdict`'s docstring
  -- documents for its own solver-free scope boundary. Do NOT close this by
  -- guessing at the missing 25 names without re-deriving them from march's
  -- live source, the way `builtinCaps` above was extracted.
  --
  -- **march's transitive fixpoint (`typecheck.ml:8902-8934`) is also
  -- unmodelled, but BENIGN, not a gap to track.** march additionally flags a
  -- fn that calls a LOCAL fn which itself directly hits the panic surface
  -- (transitively, to a fixpoint). This checker's `dfns.find?` already finds
  -- the DIRECTLY-panicking callee itself (every top-level `dfn` in the
  -- module is scanned independently), so the module-level verdict this
  -- oracle reports (violation vs. ok) already agrees with march's even
  -- without following the call graph into the caller — only the SPECIFIC fn
  -- blamed in the message could differ, which this checker's whole-file
  -- accept/reject comparison never observes.
  match if effective.contains "no_panic" then dfns.find? (fun (_, body) => bodyCalls ["panic"] body) else none with
  | some (name, _) =>
      .violation s!"cap no_panic: fn `{name}` in module `{modName}` may panic (explicit panic)"
  | none =>
  -- `no_panic`, non-exhaustive-match half (A3 slice (c) Task 3;
  -- `matchExhaustive`'s docstring has the full march citation). Lives in the
  -- SAME march function (`check_no_panic_module`, called with the SAME
  -- `inner_env`) as the explicit-panic scan just above, so it is INHERITED
  -- exactly like that half — `effective`, not `opts` alone (contrast the
  -- division-safety half right below, which is a genuinely separate march
  -- pass, `refinecheck/division_safety.ml`, and does NOT inherit).
  match if effective.contains "no_panic" then
      dfns.find? (fun (_, body) => bodyHasNonExhaustiveMatch userCtors body)
    else none with
  | some (name, _) =>
      .violation s!"cap no_panic: fn `{name}` in module `{modName}` has a non-exhaustive match"
  | none =>
  -- `no_panic`, division-safety half (`refinecheck/division_safety.ml`, A3
  -- slice (c) Task 2b) — the literal-zero-with-shadowing-and-path-conditions
  -- fragment; see `divisionVerdict`'s docstring for the three-way boundary
  -- (Finding 1). NOT inherited (Finding I3's exception, same reasoning as
  -- `no_alloc` above) — `opts` alone, never `effective`.
  --
  -- THREE-WAY over `DivVerdict`, and the tiers are ordered: a fn whose
  -- division march DEFINITELY rejects (a provable div-by-zero, or a complex
  -- divisor — see `divisorVerdict`'s four-way boundary) makes the whole module
  -- a violation even if another fn carries an unresolvable divisor (march
  -- errors on the definite one regardless of what it later decides about the
  -- other); only when no fn is definitely unsafe does an unresolvable divisor
  -- downgrade the module to `skip`.
  let divVerdicts :=
    if opts.contains "no_panic" then
      dfns.map (fun (name, body) => (name, divisionVerdict [] [] body))
    else []
  match divVerdicts.find? (fun (_, v) => v == DivVerdict.divZero) with
  | some (name, _) =>
      .violation s!"cap no_panic: fn `{name}` in module `{modName}` may panic (divides by zero, or by a complex expression march rejects unconditionally)"
  | none =>
  match divVerdicts.find? (fun (_, v) => v == DivVerdict.unknown) with
  | some (name, _) =>
      .skip s!"cap no_panic: fn `{name}` in module `{modName}` divides by an expression this checker cannot resolve — march's policy is reject-unless-proven-non-zero, but a refinement type or a Z3 discharge may still prove it non-zero, so no verdict is rendered"
  | none => .ok

/-- The behavioral caps march inherits down into a nested `dmod` (Finding
I3) — the four whose march-side check reads an env-threaded, monotone flag
rather than re-deriving from the nested module's own `decls`. `no_alloc` and
`no_panic`'s division-safety half are deliberately absent from this list —
see `checkOneModule`'s docstring for the empirically-verified exception. -/
def inheritableBehavioralCaps : List String := ["pure", "deterministic", "no_extern", "no_panic"]

/-- Walk the whole module tree, checking each module against its own needs.
`inherited` is the subset of `inheritableBehavioralCaps` accumulated so far —
`[]` at the top level (`checkCaps` below).

**Inheritance into a nested `dmod` is POSITIONAL, not whole-list** (Finding
I3, refined). march sets `pure_mod`/`deterministic_mod`/`no_extern_mod`/
`no_panic_mod` on its `env` inside the SEQUENTIAL `check_decl` fold over a
module's decl list (`typecheck.ml`, the `Ast.DOpts` arm, `:10182-10185`); a
nested `Ast.DMod` is typechecked with whatever `env` that fold has reached AT
THAT POINT (`:9336-9339` derives the child env from the CURRENT outer env,
not from a pre-scan of the whole list). So a `cap` directive written AFTER a
nested `mod` in the source does NOT reach that nested module — only caps
declared BEFORE it do. Verified directly against `march`:
`mod Outer do needs IO.Console; mod Inner do needs IO.Console; fn g(c :
Cap(IO.Console)) : () do println("io") end end; cap pure; fn f() : Int do 1
end end` — ACCEPTS (`cap pure` comes after `mod Inner`, so `Inner.g`'s
`println` is never checked against it), even though the textually-identical
shape with `cap pure` moved BEFORE `mod Inner` REJECTS. Same for `no_extern`
and a nested `extern` block.

This function therefore folds `decls` in order, threading `inherited`
through EVERY decl (not just `dmod`s): a `Decl.dopts` adds its inheritable
caps to the running accumulator for the REST of this same list; a
`Decl.dmod` is checked, and its children recursed into, using only the
accumulator value reached so far (ancestors' caps, plus this list's own
`dopts` that appeared earlier) — never caps declared later in this list, and
never anything discovered inside a sibling's subtree. This makes inheritance
correctly transitive to a grandchild when positionally reachable, and keeps
it from leaking into siblings, exactly mirroring march's single sequential
fold.

This positional threading applies ONLY to what a nested `dmod` inherits.
Each module's OWN `dfn`s are still checked in `checkOneModule` against ALL of
that module's own `Decl.dopts` regardless of where they sit in its decl list
— march folds an ENTIRE module's decls (env included) before running that
module's own `check_pure_module`/etc., so a module's own `cap pure` declared
AFTER one of its own fns still governs that fn (verified: `mod P do fn f() :
Int do println("x"); 1 end; cap pure end` REJECTS). `checkOneModule`'s own
`opts` binding (order-insensitive flatMap over `decls`) already implements
that half unchanged; only this positional fold changes here.

`userCtors` (every `DType` ctor set in the WHOLE module tree, computed once by
`checkCaps`) is threaded through UNCHANGED at every level — unlike
`inherited`, it is not positional or scoped: a `match` anywhere may scrutinize
a user ADT declared anywhere else in the file, so every recursive
`checkOneModule` call gets the same complete table. -/
partial def checkDecls (moduleCaps : List (String × List String))
    (inherited : List String) (userCtors : List (String × List String)) :
    List Decl → CapResult
  | [] => .ok
  | .dopts o :: rest =>
      let inherited' := (inherited ++ o).filter inheritableBehavioralCaps.contains
      checkDecls moduleCaps inherited' userCtors rest
  | .dmod name inner :: rest =>
      -- `CapResult.andThen` keeps the old leftmost-violation behaviour while
      -- letting a `skip` from ANY module survive a clean sibling — see its
      -- docstring for the tier order (violation > skip > ok).
      (checkOneModule name inner moduleCaps (inheritedCaps := inherited) (userCtors := userCtors)).andThen
        ((checkDecls moduleCaps inherited userCtors inner).andThen   -- nested modules, same positional fold
          (checkDecls moduleCaps inherited userCtors rest))          -- siblings never see what `inner` declared
  | _ :: rest => checkDecls moduleCaps inherited userCtors rest

/-- Entry point. Also checks the top level as an implicit module, so a file
with `needs`/`Cap(X)` outside any `mod` block is still checked.

**Finding I1's self-declaration exemption is computed HERE, and passed ONLY
to this one top-level `checkOneModule` call — never to a nested `dmod`'s
check via `checkDecls`.** This asymmetry is deliberate and empirically
verified against march, not a simplification: march's own exemption
(`typecheck.ml:6966-6970`, `env.proof_caps`) checks `declaring_mod =
mod_name.txt` using whatever `env.proof_caps` the ENCLOSING scope's
env-threading happens to carry at the point `check_module_needs` runs for
that module — and for the FILE'S OWN entry module, that call
(`typecheck.ml:10167`) uses `final_env`, threaded through the ENTIRE
top-level decl list, so a proof cap the entry module declares directly IS
visible to its own check. For ANY nested `dmod`, by contrast, march's
`check_module_needs` call (`typecheck.ml:8650`) runs INSIDE that module's own
`DMod` arm using the OUTER `env` captured BEFORE that module's own decls were
folded — so a proof cap the NESTED module declares directly is NEVER visible
to its own check, regardless of matching bare names. Verified directly
against the `march` binary:
`mod Db do proof cap Migrated; fn consume(m : Cap(Db.Migrated)) : Int do 1 end end`
(entry module) — ACCEPTS; the identical shape one level down,
`mod Top do mod Db do proof cap Migrated; fn consume(m : Cap(Db.Migrated)) : Int do 1 end end end`
— REJECTS. So the exemption this checker models must be the SAME
asymmetry: computed once from `m.decls`/`m.entryName` (the file's own entry
module) and threaded only into the top-level `checkOneModule` call;
`checkDecls`'s recursive calls keep their default `[]`. -/
def checkCaps (m : Module) : CapResult :=
  let selfDeclaredCaps :=
    (declaredProofCapNames m.decls).map (fun n => s!"{m.entryName}.{n}")
  -- Every `DType` ctor set in the WHOLE file (A3 slice (c) Task 3), computed
  -- once here and threaded UNCHANGED into both the top-level call and every
  -- recursive `checkDecls`/`checkOneModule` call below — see `checkDecls`'s
  -- docstring for why this table, unlike `inherited`, is not positional.
  let userCtors := dtypeCtorSets m.decls
  (checkOneModule "<top-level>" m.decls m.moduleCaps selfDeclaredCaps (userCtors := userCtors)).andThen
    -- Finding I3: the top-level (entry) module is threaded through the SAME
    -- env-based, SEQUENTIAL `check_decl` fold march uses for a nested `dmod`,
    -- so a behavioral cap declared OUTSIDE any `mod` block (a top-level
    -- `Decl.dopts` sibling in `m.decls`) inherits into a nested `mod` exactly
    -- like a `cap pure` declared on any other enclosing module would — there
    -- is no asymmetry here the way Finding I1's self-declaration exemption
    -- has one. But per `checkDecls`'s docstring, that inheritance is
    -- POSITIONAL: only a top-level `cap` written BEFORE a nested `mod`
    -- reaches it. Starting the fold at `[]` and letting `checkDecls` itself
    -- accumulate `Decl.dopts` as it walks `m.decls` in order gets this right
    -- without any whole-list pre-collection here.
    (checkDecls m.moduleCaps [] userCtors m.decls)

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
  decls := [Decl.dmod "F" [Decl.dextern (some "IO.Foreign") []]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externUncovered
  -- expect: violation — Check 5

/-- Check 5 satisfied. -/
def externCovered : Module := {
  decls := [Decl.dmod "F" [Decl.dneeds ["IO.Foreign"], Decl.dextern (some "IO.Foreign") []]],
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
  | .skip _      => false
  | .ok          => false

/-- True iff a `CapResult` is the explicit "cannot judge" answer (exit 2).
Distinct from `!isViolation`: a `skip` is NOT an accept, and the fixtures
below that pin an unresolvable divisor need to say so positively — asserting
only `isViolation = false` would pass just as well if the checker regressed
to the old silent accept. -/
def CapResult.isSkip : CapResult → Bool
  | .skip _      => true
  | .violation _ => false
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

/-- The gate that still matters for a genuinely-unmodeled decl (NOT a proof
cap — Finding I1 now models those directly via `selfDeclaredCaps`, see the
three pins right below): a module carrying some OTHER out-of-fragment
declaration (here a bare `Decl.unsupported`, standing in for e.g. an actor or
interface this fragment has no representation for at all) does NOT get its
return caps scanned, since this checker has no way to know whether that
unmodeled construct covers the return some other way. `checkCaps` must NOT
reject here: it defers to the downstream out-of-fragment skip gate. Without
the gate, the uncovered `Vendor.Widget` return would wrongly reject a file
this checker cannot actually judge. -/
def retCapDeferredByOtherUnsupported : Module := {
  decls := [Decl.unsupported,   -- e.g. an actor/interface decl
            Decl.dneeds ["IO"],
    Decl.dfn "get_widget"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      (some (Ty.con "Cap" [Ty.con "Vendor.Widget" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retCapDeferredByOtherUnsupported  -- expect: ok (deferred, NOT rejected)
example : (checkCaps retCapDeferredByOtherUnsupported).isViolation = false := by native_decide

/-- Finding I1 pin (param case, the false-accept reproducer): a `proof cap`
declared directly in the FILE'S OWN entry module, used in a PARAMETER of a fn
in that same module, is self-covered — matching march's self-declaration
exemption for the one shape it actually reaches (see `checkCaps`'s
docstring). march ACCEPTS
`mod Db do proof cap Migrated; fn consume(m : Cap(Db.Migrated)) : Int do 1 end end`
even though `Db` declares no `needs Db.Migrated` (verified directly against
`march --check`); `entryName := "Db"` here stands in for the real decoder
populating it from the envelope's `module.name`. -/
def selfDeclaredParamOk : Module := {
  decls := [Decl.dproofcap "Migrated",
    Decl.dfn "consume"
      [("m", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "Db.Migrated" []]))]
      none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [], entryName := "Db" }
#eval checkCaps selfDeclaredParamOk  -- expect: ok
example : (checkCaps selfDeclaredParamOk).isViolation = false := by native_decide

/-- Finding I1 pin (return case): the same self-declaration exemption also
covers a RETURN-position use — this is `accept/t62`'s actual shape
(`Cap(Db.Migrated)` returned under only `needs IO`), now satisfied directly
via `selfDeclaredCaps` rather than by deferring through the out-of-fragment
gate (contrast `retCapDeferredByOtherUnsupported` above, which defers for an
UNRELATED reason and would no longer even apply here — `Decl.dproofcap` is
in-fragment). -/
def selfDeclaredReturnOk : Module := {
  decls := [Decl.dproofcap "Migrated", Decl.dneeds ["IO"],
    Decl.dfn "run_migrations"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      (some (Ty.con "Cap" [Ty.con "Db.Migrated" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [], entryName := "Db" }
#eval checkCaps selfDeclaredReturnOk  -- expect: ok
example : (checkCaps selfDeclaredReturnOk).isViolation = false := by native_decide

/-- Finding I1 pin (nested variant — must STILL reject): the identical
`proof cap` + param shape, but with the declaring module NESTED one level
inside another (`Top > Db`) instead of being the file's own entry module.
Verified directly against `march --check`: this shape REJECTS even though the
flat/entry-level shape above (`selfDeclaredParamOk`) ACCEPTS — see
`checkCaps`'s docstring for the env-threading reason march itself treats
these differently. `checkOneModule`'s recursive call for a nested `dmod`
always passes `selfDeclaredCaps := []` (its default), so `Db`'s own
`proof cap Migrated` never covers its own `Cap(Db.Migrated)` use here, and
Check 1 correctly fires. -/
def selfDeclaredNestedRejects : Module := {
  decls := [Decl.dmod "Top" [
    Decl.dmod "Db" [
      Decl.dproofcap "Migrated",
      Decl.dfn "consume"
        [("m", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "Db.Migrated" []]))]
        none
        (Term.lit (Lit.int 1) (Ty.con "Int" []))]]],
  schemes := [], insts := [], moduleCaps := [], entryName := "Top" }
#eval checkCaps selfDeclaredNestedRejects
  -- expect: violation — Check 1, Db.Migrated not self-covered when nested
example : (checkCaps selfDeclaredNestedRejects).isViolation = true := by native_decide

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
          [(Pattern.wild, none,
            Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                      [Term.lit (Lit.str "hi") (Ty.con "String" [])] (Ty.con "Unit" []))]
          (Ty.con "Unit" []))
        (Term.var "x" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
        (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps migrateDoesIONested   -- expect: violation naming Check 8
example : (checkCaps migrateDoesIONested).isViolation = true := by native_decide

/-- Finding I2 (the false-accept reproducer): an `extern` block that declares
a `Cap(X)` and contains a fn whose name matches `is_migrate_fn_name` is a
Check 8 violation, even though this checker has no representation of the
extern fn's own body — march attributes `IO.Foreign` onto every extern fn in
it (`typecheck.ml:6941-6950`), migrate-named or not. Mirrors
`mod Counter do needs IO.Foreign; extern "libc" : Cap(IO.Foreign) do
fn counter_migrate_state(old : Int) : Int end end`, which march rejects
(exit 1) but the pre-fix checker accepted (exit 0). -/
def externMigrateWithCapViolates : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Foreign"],
    Decl.dextern (some "IO.Foreign") ["counter_migrate_state"]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externMigrateWithCapViolates
  -- expect: violation naming Check 8
example : (checkCaps externMigrateWithCapViolates).isViolation = true := by native_decide

/-- Finding I2, "no declared cap" case — STILL a violation, verified against
`march` directly (NOT an accept, despite the task brief's working
assumption): march's `extern_cap_uses` attributes `IO.Foreign` onto every
extern fn UNCONDITIONALLY of `ext_cap_ty`'s shape (`typecheck.ml:6941-6950`'s
`base`/`own` are computed with no reference to `ext_cap_ty` at all — the
comment there literally reads "any DExtern → needs IO.Foreign"). Confirmed
empirically: `extern "libc" : Int do fn counter_migrate_state(old : Int) :
Int end` — `ext_cap_ty = Int`, not `Cap`-shaped at all, so this checker's own
`capTy` decodes to `none` — STILL rejects with march's "migrate_state must be
IO-free" (exit 1). So Check 8's extern arm must NOT be gated on `capTy`, and
this fixture (`capTy = none`) must still violate. -/
def externMigrateCapNoneStillViolates : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dextern none ["counter_migrate_state"]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externMigrateCapNoneStillViolates
  -- expect: violation naming Check 8 (NOT ok — capTy is irrelevant here)
example : (checkCaps externMigrateCapNoneStillViolates).isViolation = true := by native_decide

/-- Finding I2, the genuine negative case (must NOT over-fire): an extern
block whose fns DON'T match `is_migrate_fn_name` at all is never a Check 8
concern regardless of `capTy` — Check 8 only ever tests migrate-NAMED fns.
`needs IO.Foreign` here separately satisfies Check 5's own (unrelated)
coverage obligation for the declared `Cap(IO.Foreign)`. -/
def externCapNoMigrateSafe : Module := {
  decls := [Decl.dmod "Counter" [
    Decl.dneeds ["IO.Foreign"],
    Decl.dextern (some "IO.Foreign") ["read_byte"]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externCapNoMigrateSafe   -- expect: ok
example : (checkCaps externCapNoMigrateSafe).isViolation = false := by native_decide

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

/-- Finding C1 pin (regression in `6c6c2f0`, this re-review): `capsInTy`'s
`Cap` arm must be ARITY-1-ONLY, mirroring march's `cap_paths_in_surface_ty`,
whose `Cap`-specific arm only ever matches `Ast.TyCon (con, [arg])` — a
SINGLE type argument. `6c6c2f0` collapsed the fallthrough arm to
`| .con "Cap" _ => []`, which matches `Cap` at ANY arity (including 2) and
returns `[]` unconditionally — silently swallowing a `Cap(_)` nested inside a
non-unary `Cap(...)` application instead of falling through to generic
recursion the way march does. `Cap(Cap(IO.Network), Int)` — Cap applied to
TWO arguments, the first itself `Cap(IO.Network)` — must extract
`["IO.Network"]`, NOT `[]`: at arity 2, march's `Cap`-specific arm does not
match at all, so `Ast.TyCon (_, args) -> List.concat_map
cap_paths_in_surface_ty args` recurses into both arguments, and the first one
IS a capability path. Unlike the Finding-3 guard just above (which pins the
INNER argument's arity, already correct before `6c6c2f0`), this pins the
`Cap` MARKER's OWN arity — the dimension `6c6c2f0` broke. Mirrors the
false-accept reproducer: `fn f(_c : Cap(Cap(IO.Network), Int)) : Int do 1
end`, which march rejects (`Cap(IO.Network)` uncovered) but the regressed
checker silently accepted. -/
example :
    capsInTy (Ty.con "Cap" [Ty.con "Cap" [Ty.con "IO.Network" []], Ty.con "Int" []])
      = ["IO.Network"]
  := by native_decide

/-- Finding C1 pin, `checkCaps`-level: the same arity-2 `Cap(Cap(IO.Network),
Int)` shape, this time reaching `checkCaps` through a real (if minimal)
module with no `needs` at all — so the nested `IO.Network` capability, if
`capsInTy` ever regresses back to matching `Cap` at every arity, is uncovered
and must surface as a Check 1 violation, not silently vanish. -/
def capArityTwoViolation : Module := {
  decls := [Decl.dmod "M" [
    Decl.dfn "f"
      [("_c", Lin.unrestricted,
        some (Ty.con "Cap" [Ty.con "Cap" [Ty.con "IO.Network" []], Ty.con "Int" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps capArityTwoViolation
  -- expect: violation — Check 1, IO.Network uncovered (no `needs` at all)
example : (checkCaps capArityTwoViolation).isViolation = true := by native_decide

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

-- ---------------------------------------------------------------------
-- A3 slice (c), Task 1 (infrastructure): `builtinCaps` carries caps; the name
-- projection equals the old `ioBuiltins` set. The generalised walk
-- (`bodyCalls`) and its sibling (`bodyAllocates`) are total over every `Term`
-- constructor. This task adds NO new check.

-- builtinCaps carries caps; the name projection equals the old ioBuiltins set.
example : builtinCaps.any (fun (n, c) => n == "println" && c == "IO.Console") := by native_decide
example : builtinCaps.any (fun (n, c) => n == "unix_time_ms" && c == "IO.Clock") := by native_decide
-- generalised walk: bodyCalls finds a banned direct call (through a tuple).
example : bodyCalls ["println"]
  (Term.tuple [Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                        [Term.lit (Lit.str "x") (Ty.con "String" [])] (Ty.con "Unit" [])]
              (Ty.con "Unit" [])) = true := by native_decide
-- bodyAllocates: a NON-EMPTY tuple allocates; a bare literal does not; the
-- EMPTY tuple (unit `()`) is exempt (`no_alloc.ml:20`'s `ETuple ([], _) ->
-- ()`), matching march exactly — see the false-reject this closes at
-- `noAllocEmptyTupleOk` below.
example : bodyAllocates
  (Term.tuple [Term.lit (Lit.int 1) (Ty.con "Int" []), Term.lit (Lit.int 2) (Ty.con "Int" [])]
              (Ty.con "Unit" [])) = true := by native_decide
example : bodyAllocates (Term.tuple [] (Ty.con "Unit" [])) = false := by native_decide
example : bodyAllocates (Term.lit (Lit.int 1) (Ty.con "Int" [])) = false := by native_decide

-- ---------------------------------------------------------------------
-- A3 slice (c), Task 2: the five behavioral-cap checks — pure,
-- deterministic, no_extern, no_alloc, and no_panic's explicit-panic half.
-- A module declares a cap via a sibling `Decl.dopts [...]`.

/-- `pure`: a `dfn` body calling `println` (a plain `builtinCaps` name, not
one of the four extra pure-only bans) is a violation. -/
def purePrintln : Module := {
  decls := [Decl.dmod "P" [
    Decl.dopts ["pure"],
    Decl.dfn "f" []
      none
      (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                [Term.lit (Lit.str "x") (Ty.con "String" [])] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps purePrintln   -- expect: violation naming `pure`
example : (checkCaps purePrintln).isViolation = true := by native_decide

/-- `pure`: an arithmetic-only body (no builtin/side-effecting call at all) →
ok. -/
def pureArithmetic : Module := {
  decls := [Decl.dmod "P" [
    Decl.dopts ["pure"],
    Decl.dfn "f" []
      none
      (Term.app (Term.var "int_abs" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))
                [Term.lit (Lit.int (-1)) (Ty.con "Int" [])] (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps pureArithmetic   -- expect: ok
example : (checkCaps pureArithmetic).isViolation = false := by native_decide

/-- `deterministic`: a body calling `unix_time_ms` (`IO.Clock`) → violation. -/
def deterministicUnixTimeMs : Module := {
  decls := [Decl.dmod "D" [
    Decl.dopts ["deterministic"],
    Decl.dfn "f" []
      none
      (Term.app (Term.var "unix_time_ms" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))
                [] (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps deterministicUnixTimeMs   -- expect: violation naming `deterministic`
example : (checkCaps deterministicUnixTimeMs).isViolation = true := by native_decide

/-- `deterministic`: a body calling `int_abs` — an ordinary non-`IO.Clock`/
`IO.Random` builtin — must NOT be flagged (the ban set is the 6-name
Clock/Random subset, not the whole `builtinCaps` table). -/
def deterministicIntAbs : Module := {
  decls := [Decl.dmod "D" [
    Decl.dopts ["deterministic"],
    Decl.dfn "f" []
      none
      (Term.app (Term.var "int_abs" ⟨"f",0,0,0,0⟩ (Ty.con "Int" []))
                [Term.lit (Lit.int (-1)) (Ty.con "Int" [])] (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps deterministicIntAbs   -- expect: ok
example : (checkCaps deterministicIntAbs).isViolation = false := by native_decide

/-- `no_extern`: a module declaring `no_extern` with a `Decl.dextern` sibling
→ violation. -/
def noExternWithExtern : Module := {
  decls := [Decl.dmod "E" [
    Decl.dopts ["no_extern"],
    Decl.dextern none ["foreign_fn"]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternWithExtern   -- expect: violation naming `no_extern`
example : (checkCaps noExternWithExtern).isViolation = true := by native_decide

/-- `no_extern`: a module declaring `no_extern` with NO extern block at all →
ok. -/
def noExternWithoutExtern : Module := {
  decls := [Decl.dmod "E" [
    Decl.dopts ["no_extern"],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternWithoutExtern   -- expect: ok
example : (checkCaps noExternWithoutExtern).isViolation = false := by native_decide

/-- Finding C2 (the false-accept reproducer): a `no_extern` module declaring
`needs IO.Foreign` — no `Decl.dextern` at all — is STILL a violation. march's
`check_no_extern_module` has TWO arms; this checker previously implemented
only the `Decl.dextern` one. Mirrors
`mod NoFFI do cap no_extern; needs IO.Foreign; fn ping(host : String) : Int do
string_length(host) end end`, which march rejects (exit 1) but the pre-fix
checker accepted (exit 0). -/
def noExternWithForeignNeed : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO.Foreign"],
    Decl.dfn "ping" [("host", Lin.unrestricted, some (Ty.con "String" []))] none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternWithForeignNeed   -- expect: violation naming `no_extern`
example : (checkCaps noExternWithForeignNeed).isViolation = true := by native_decide

/-- Finding C2, a longer path under `IO.Foreign` also matches — `needs
IO.Foreign.Blocking` — mirroring march's `has_foreign`, which looks for
`"Foreign"` ANYWHERE among the path's segments after `"IO"`, not only as the
immediate second segment. -/
def noExternWithForeignBlockingNeed : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO.Foreign.Blocking"],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternWithForeignBlockingNeed   -- expect: violation naming `no_extern`
example : (checkCaps noExternWithForeignBlockingNeed).isViolation = true := by native_decide

/-- Finding C2, the negative case (must NOT over-fire): `needs IO.Network` —
`"IO"` first segment, but no `"Foreign"` segment at all — must NOT trip the
new arm. This is `accept/t56_cap_no_extern_ok`'s exact shape. -/
def noExternWithNonForeignIONeed : Module := {
  decls := [Decl.dmod "NoFFIService" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO.Network"],
    Decl.dfn "ping"
      [("_cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Network" []])),
       ("host", Lin.unrestricted, some (Ty.con "String" []))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternWithNonForeignIONeed   -- expect: ok
example : (checkCaps noExternWithNonForeignIONeed).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- Finding I3 pins: `pure`/`deterministic`/`no_extern`/`no_panic`-explicit-panic
-- ARE inherited by a nested `dmod`; `no_alloc` and `no_panic`-division-safety
-- are NOT. See `checkOneModule`'s docstring for the march-side justification.

/-- The false-accept reproducer: `Outer` declares `cap pure`; `Inner` (nested,
declaring no cap of its own) has a fn that performs IO. march REJECTS — the
inherited `pure` flag governs `Inner.g` too — but a checker that scans each
`dmod`'s own `opts` only would accept. Mirrors
`mod Outer do cap pure; needs IO.Console; mod Inner do needs IO.Console; fn
g(c : Cap(IO.Console)) : () do println("io") end end; fn f() : Int do 1 end
end`. -/
def pureInheritedIntoNestedModule : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dopts ["pure"],
    Decl.dneeds ["IO.Console"],
    Decl.dmod "Inner" [
      Decl.dneeds ["IO.Console"],
      Decl.dfn "g" [("c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []]))]
        none
        (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                  [Term.lit (Lit.str "io") (Ty.con "String" [])] (Ty.con "Unit" []))],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps pureInheritedIntoNestedModule   -- expect: violation naming `pure`
example : (checkCaps pureInheritedIntoNestedModule).isViolation = true := by native_decide

/-- Same shape for `no_extern`: `Outer` declares `cap no_extern`; a nested
`Inner` (no cap of its own) contains an `extern` block. march REJECTS. -/
def noExternInheritedIntoNestedModule : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dopts ["no_extern"],
    Decl.dmod "Inner" [
      Decl.dextern none ["foreign_fn"]]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noExternInheritedIntoNestedModule   -- expect: violation naming `no_extern`
example : (checkCaps noExternInheritedIntoNestedModule).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- Positional refinement of Finding I3: march sets its inheritable-cap flags
-- inside the SEQUENTIAL `check_decl` fold over a module's own decl list, so
-- a `cap` written AFTER a nested `mod` does NOT reach it — only one written
-- BEFORE it does. `checkDecls`'s docstring has the full march-side citation.

/-- The false-REJECT reproducer this fix closes: `cap pure` sits AFTER the
nested `Inner` module in `Outer`'s own decl list, so march's sequential fold
has not set `pure_mod` yet when it typechecks `Inner` — march ACCEPTS
(`Inner.g`'s `println` is never checked against `pure`), even though `Outer`
itself does declare `cap pure` (which still governs `Outer`'s OWN fn `f`,
checked separately below). A pre-collect-the-whole-list checker would
wrongly reject this. -/
def pureAfterNestedModuleNotInherited : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dneeds ["IO.Console"],
    Decl.dmod "Inner" [
      Decl.dneeds ["IO.Console"],
      Decl.dfn "g" [("c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []]))]
        none
        (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                  [Term.lit (Lit.str "io") (Ty.con "String" [])] (Ty.con "Unit" []))],
    Decl.dopts ["pure"],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps pureAfterNestedModuleNotInherited   -- expect: ok
example : (checkCaps pureAfterNestedModuleNotInherited).isViolation = false := by native_decide

/-- Same shape with `cap pure` moved BEFORE `mod Inner` (otherwise identical
decl list) — now positionally reachable, so march REJECTS. Paired with
`pureAfterNestedModuleNotInherited` above, this pins that inheritance is a
function of SOURCE ORDER, not merely "declared somewhere in the parent". -/
def pureBeforeNestedModuleInherited : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dneeds ["IO.Console"],
    Decl.dopts ["pure"],
    Decl.dmod "Inner" [
      Decl.dneeds ["IO.Console"],
      Decl.dfn "g" [("c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []]))]
        none
        (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                  [Term.lit (Lit.str "io") (Ty.con "String" [])] (Ty.con "Unit" []))],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps pureBeforeNestedModuleInherited   -- expect: violation naming `pure`
example : (checkCaps pureBeforeNestedModuleInherited).isViolation = true := by native_decide

/-- A module's OWN fns are still checked against ALL of its OWN `dopts`
regardless of position — only the CHILD-inheritance path became positional
above. `P`'s own fn `f` performs IO, and `cap pure` is declared AFTER `f` in
`P`'s decl list; march still rejects, because march folds an entire module's
own decls (env included) before running that module's own
`check_pure_module`. -/
def pureOwnFnOrderInsensitive : Module := {
  decls := [Decl.dmod "P" [
    Decl.dfn "f" [] none
      (Term.app (Term.var "println" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                [Term.lit (Lit.str "x") (Ty.con "String" [])] (Ty.con "Unit" [])),
    Decl.dopts ["pure"]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps pureOwnFnOrderInsensitive   -- expect: violation naming `pure`
example : (checkCaps pureOwnFnOrderInsensitive).isViolation = true := by native_decide

/-- The exception, half 1: `no_alloc` does NOT inherit. `Outer` declares `cap
no_alloc`; nested `Inner` (no cap of its own) allocates (a non-empty tuple).
march ACCEPTS — `no_alloc.ml`'s `check_decls` re-derives its own `no_alloc`
boolean from EACH module's own `decls`, with no inherited parameter at all. -/
def noAllocNotInheritedIntoNestedModule : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dopts ["no_alloc"],
    Decl.dmod "Inner" [
      Decl.dfn "f" [] none
        (Term.tuple [Term.lit (Lit.int 1) (Ty.con "Int" []), Term.lit (Lit.int 2) (Ty.con "Int" [])]
                    (Ty.con "Unit" []))]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noAllocNotInheritedIntoNestedModule   -- expect: ok
example : (checkCaps noAllocNotInheritedIntoNestedModule).isViolation = false := by native_decide

-- `noPanicDivisionNotInheritedIntoNestedModule` (Finding I3's other
-- exception half) is defined further below, alongside `divTerm`/`divIntTy`.

/-- `no_alloc`: a `dfn` returning a NON-EMPTY `Term.tuple` → violation. -/
def noAllocTuple : Module := {
  decls := [Decl.dmod "A" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none
      (Term.tuple [Term.lit (Lit.int 1) (Ty.con "Int" []), Term.lit (Lit.int 2) (Ty.con "Int" [])]
                  (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noAllocTuple   -- expect: violation naming `no_alloc`
example : (checkCaps noAllocTuple).isViolation = true := by native_decide

/-- `no_alloc`: a `dfn` returning the EMPTY tuple `()` (unit) → ok. Pins the
false-reject fix: `no_alloc.ml:20`'s `ETuple ([], _) -> ()` explicitly exempts
unit from being an allocation, so `bodyAllocates` must NOT flag it — prior to
this fix, `.tuple _ _ => true` flagged EVERY tuple including the empty one,
manufacturing a false reject on `mod NA do cap no_alloc fn f() : () do () end
end` (march accepts, march-lean-check rejected). -/
def noAllocEmptyTupleOk : Module := {
  decls := [Decl.dmod "A" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none (Term.tuple [] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noAllocEmptyTupleOk   -- expect: ok
example : (checkCaps noAllocEmptyTupleOk).isViolation = false := by native_decide

/-- `no_alloc`: a `dfn` returning a bare `int` literal → ok. -/
def noAllocArithmetic : Module := {
  decls := [Decl.dmod "A" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noAllocArithmetic   -- expect: ok
example : (checkCaps noAllocArithmetic).isViolation = false := by native_decide

/-- `no_panic`, panic half: a `dfn` body calling `panic` → violation. -/
def noPanicExplicitPanic : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" []
      none
      (Term.app (Term.var "panic" ⟨"f",0,0,0,0⟩ (Ty.con "Unit" []))
                [Term.lit (Lit.str "boom") (Ty.con "String" [])] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicExplicitPanic   -- expect: violation naming `no_panic`
example : (checkCaps noPanicExplicitPanic).isViolation = true := by native_decide

/-- `no_panic`, panic half: a `dfn` body with no `panic` call at all → ok
(exhaustiveness — the OTHER half of `no_panic` — is Task 3, not modelled
here). -/
def noPanicSafe : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicSafe   -- expect: ok
example : (checkCaps noPanicSafe).isViolation = false := by native_decide

-- `no_panic`, division-safety half (A3 slice (c) Task 2b) — see
-- `divisionVerdict`'s docstring for the literal-zero-with-shadowing scope.
def divIntTy : Ty := Ty.con "Int" []
def divSp : Span := ⟨"f", 0, 0, 0, 0⟩

/-- `lhs / rhs` at the exact shape march emits (`EApp{fn=EVar"/",
args=[lhs, rhs]}` — verified against `reject/t123`'s `--emit-core-ast`
output), so `rhs` is the divisor. -/
def divTerm (lhs rhs : Term) : Term :=
  Term.app (Term.var "/" divSp divIntTy) [lhs, rhs] divIntTy

/-- Finding I3's other exception half: `no_panic`'s DIVISION-SAFETY check does
NOT inherit (even though its explicit-panic half DOES — see
`pureInheritedIntoNestedModule`/`noExternInheritedIntoNestedModule` above for
the inherited side, and `noAllocNotInheritedIntoNestedModule` for the sibling
exception). `Outer` declares `cap no_panic`; nested `Inner` (no cap of its
own) divides by a literal zero. march ACCEPTS — `division_safety.ml`'s
`check_decls` re-derives its own `no_panic` boolean per module, exactly like
`no_alloc.ml`. -/
def noPanicDivisionNotInheritedIntoNestedModule : Module := {
  decls := [Decl.dmod "Outer" [
    Decl.dopts ["no_panic"],
    Decl.dmod "Inner" [
      Decl.dfn "f" [] none
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 0) divIntTy))]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivisionNotInheritedIntoNestedModule   -- expect: ok
example : (checkCaps noPanicDivisionNotInheritedIntoNestedModule).isViolation = false := by native_decide

/-- A bare `10 / 0` literal divisor → violation. -/
def noPanicDivLiteralZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 0) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivLiteralZero   -- expect: violation
example : (checkCaps noPanicDivLiteralZero).isViolation = true := by native_decide

/-- `let d = 0; 10 / d` → violation (a name tracked to literal `0`). -/
def noPanicDivLetZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivLetZero   -- expect: violation
example : (checkCaps noPanicDivLetZero).isViolation = true := by native_decide

/-- `reject/t123`'s exact shape: outer param `d`, `if d == 0 do 0 else let d =
0; 10 / d end` — the INNER shadowing `let` is what makes this unsafe. The `if`
guard's `d == 0` DOES get pushed onto the path for the else-branch (negated,
so `pathProvesNonzero` would read it as `d != 0`) — this checker now models
that channel (Finding C1) — but the fact is about the OUTER parameter `d`,
and the inner `let d = 0` RETIRES it (`retireDivPath`) before recording the
fresh literal-zero fact, exactly as it already retired the OUTER `DivFacts`
entry. So the guard plays no role here, but for the right reason now: not
because path conditions are unmodelled, but because shadowing correctly
discards a fact about a name that no longer refers to the same value. -/
def noPanicShadowedGuard : Module := {
  decls := [Decl.dmod "ShadowedGuard" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("d", Lin.unrestricted, some divIntTy)] none
      (Term.ite
        (Term.app (Term.var "==" divSp divIntTy)
          [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
        (Term.lit (Lit.int 0) divIntTy)
        (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicShadowedGuard   -- expect: violation
example : (checkCaps noPanicShadowedGuard).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- Finding C1 pins: a `let`-bound literal-zero divisor guarded (NOT shadowed
-- — the SAME `d` the guard is about) by a condition `pathProvesNonzero`
-- recognises must be `ok`, not a violation. Prior to this fix, `divisorVerdict`
-- consulted ONLY `DivFacts` and had no path channel at all, so all three of
-- these false-rejected (checker exit 1, march exit 0) — the worst class of
-- divergence for a differential oracle. Each mirrors one of march's
-- `path_proves_nonzero` patterns directly.

/-- `let d = 0; if d != 0 do 10 / d else 0 end` → ok (direct `!=` pattern). -/
def noPanicGuardedNotEqualSafe : Module := {
  decls := [Decl.dmod "Z" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.ite
          (Term.app (Term.var "!=" divSp divIntTy)
            [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          (Term.lit (Lit.int 0) divIntTy)
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicGuardedNotEqualSafe   -- expect: ok
example : (checkCaps noPanicGuardedNotEqualSafe).isViolation = false := by native_decide

/-- `let d = 0; if d == 0 do 0 else 10 / d end` → ok (negated `==`, dualised
to `!=` on the else-branch). -/
def noPanicGuardedNegatedEqualSafe : Module := {
  decls := [Decl.dmod "Z" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.ite
          (Term.app (Term.var "==" divSp divIntTy)
            [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
          (Term.lit (Lit.int 0) divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicGuardedNegatedEqualSafe   -- expect: ok
example : (checkCaps noPanicGuardedNegatedEqualSafe).isViolation = false := by native_decide

/-- `let d = 0; if d > 0 do 10 / d else 0 end` → ok (one-sided inequality
implies non-zero). -/
def noPanicGuardedGreaterThanSafe : Module := {
  decls := [Decl.dmod "Z" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.ite
          (Term.app (Term.var ">" divSp divIntTy)
            [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          (Term.lit (Lit.int 0) divIntTy)
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicGuardedGreaterThanSafe   -- expect: ok
example : (checkCaps noPanicGuardedGreaterThanSafe).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- Review Finding 3 pins: a MATCH-ARM guard is a proof available to that
-- arm's BODY, exactly like an `if`'s then-branch. march's `EMatch` case
-- (`division_safety.ml:240-246`) scans the guard with the retired-only `ac`
-- and then scans the body with `{ ac with path = (g, false) :: ac.path }`.
-- The three Finding C1 pins above cover only the `.ite` shape, so the
-- `.match_` push had no test at all and was in fact missing — a live FALSE
-- REJECT (confirmed against `march --check`, which accepts the first fixture
-- below and rejects the second).

/-- `let d = 0; match x do Some(_) when d != 0 -> 10 / d | _ -> 0 end` → ok.
The arm's guard `d != 0` is on the path for that arm's BODY, and the pattern
binds nothing that would retire the `d` it is about, so `pathProvesNonzero`
discharges the `let`-tracked zero — exactly as it does on an `if`'s
then-branch. march ACCEPTS this file. -/
def noPanicMatchGuardProvesNonzero : Module := {
  decls := [Decl.dmod "MG" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("x", Lin.unrestricted, none)] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.match_ (Term.var "x" divSp (Ty.con "Option" [divIntTy]))
          [(Pattern.con "Some" [Pattern.wild],
            some (Term.app (Term.var "!=" divSp divIntTy)
              [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy),
            divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy)),
           (Pattern.wild, none, Term.lit (Lit.int 0) divIntTy)]
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicMatchGuardProvesNonzero   -- expect: ok
example : (checkCaps noPanicMatchGuardProvesNonzero).isViolation = false := by native_decide

/-- Teeth for the pin above: the SAME shape with a guard that does NOT prove
`d != 0` (`d == 0`, which `pathProvesNonzero`'s `proves "==" 0` rejects)
stays a violation. The `.match_` push must put the guard on the path, not
license the arm body wholesale. march REJECTS this file. -/
def noPanicMatchGuardDoesNotProve : Module := {
  decls := [Decl.dmod "MG" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("x", Lin.unrestricted, none)] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.match_ (Term.var "x" divSp (Ty.con "Option" [divIntTy]))
          [(Pattern.con "Some" [Pattern.wild],
            some (Term.app (Term.var "==" divSp divIntTy)
              [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy),
            divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy)),
           (Pattern.wild, none, Term.lit (Lit.int 0) divIntTy)]
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicMatchGuardDoesNotProve   -- expect: violation
example : (checkCaps noPanicMatchGuardDoesNotProve).isViolation = true := by native_decide

/-- Teeth, second direction: the guard is scanned in its OWN scope WITHOUT
itself on the path (`a guard cannot assume itself`), mirroring march's
`Option.iter (iter_div_sites f ac) arm.branch_guard` running before `ac'` is
built. A division by the `let`-tracked zero INSIDE the guard expression is
therefore still a violation even though the guard would, if assumed, prove
its own divisor non-zero. -/
def noPanicMatchGuardSelfAssumption : Module := {
  decls := [Decl.dmod "MG" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("x", Lin.unrestricted, none)] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.match_ (Term.var "x" divSp (Ty.con "Option" [divIntTy]))
          [(Pattern.con "Some" [Pattern.wild],
            some (Term.app (Term.var "!=" divSp divIntTy)
              [divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy),
               Term.lit (Lit.int 0) divIntTy] divIntTy),
            Term.lit (Lit.int 1) divIntTy),
           (Pattern.wild, none, Term.lit (Lit.int 0) divIntTy)]
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicMatchGuardSelfAssumption   -- expect: violation
example : (checkCaps noPanicMatchGuardSelfAssumption).isViolation = true := by native_decide

/-- `let d = 5; 10 / d` → ok (a non-zero literal is trivially safe). -/
def noPanicDivLetNonZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 5) divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivLetNonZero   -- expect: ok
example : (checkCaps noPanicDivLetNonZero).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- Review Finding 1 pins: an UNRESOLVED divisor is a SKIP — not an accept
-- (which it silently was, a live FALSE ACCEPT on two plain in-fragment
-- programs) and not a reject (which would be a FALSE REJECT on the
-- refinement-typed programs march genuinely accepts). See
-- `divisorVerdict`/`divisionVerdict`'s docstrings. Verified against the
-- march binary for every shape below.

/-- `fn f(d : Int) : Int do 10 / d end` under `cap no_panic` → SKIP. march
REJECTS this (`check_var_divisor`'s `None` arm, `division_safety.ml:394-399`,
no solver involved) — but this checker cannot see whether `d` carries an Int
refinement, and `fn f(d : {v : Int | v != 0}) : Int do 10 / d end` is
textually the same division in a file march ACCEPTS (both verified against
the binary). So it declines to judge. Asserted with `isSkip`, not merely
`isViolation = false`, so a regression to the old silent accept fails here. -/
def noPanicDivUnresolvedParam : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("d", Lin.unrestricted, some divIntTy)] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivUnresolvedParam   -- expect: skip
example : (checkCaps noPanicDivUnresolvedParam).isSkip = true := by native_decide

-- ---------------------------------------------------------------------
-- Complex-divisor tightening: march's arm 4 (`check_clause`'s catch-all,
-- `division_safety.ml:497-500`) errors on ANY divisor that is neither an
-- `ELit` nor an `EVar` — no solver, no refinement escape, no path escape. The
-- shapes below were all SKIPS until the four-way boundary landed; each is
-- exit 1 from the march binary. See `divisorVerdict`'s docstring for why the
-- `Term.var ⟺ A.EVar` correspondence this relies on is a decoded fact rather
-- than a reconstruction.

/-- `fn f(a : Int, b : Int) : Int do 10 / (a + b) end` under `cap no_panic` →
VIOLATION. An `app` divisor is march's arm 4. (march binary: exit 1.) -/
def noPanicDivComplexExpr : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("a", Lin.unrestricted, some divIntTy),
                  ("b", Lin.unrestricted, some divIntTy)] none
      (divTerm (Term.lit (Lit.int 10) divIntTy)
        (Term.app (Term.var "+" divSp divIntTy)
          [Term.var "a" divSp divIntTy, Term.var "b" divSp divIntTy] divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivComplexExpr   -- expect: violation
example : (checkCaps noPanicDivComplexExpr).isViolation = true := by native_decide

/-- A CALL result as divisor — `10 / g(x)` — is the same arm 4 shape reached
through a non-operator callee. (march binary: exit 1.) -/
def noPanicDivCallResult : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("x", Lin.unrestricted, some divIntTy)] none
      (divTerm (Term.lit (Lit.int 10) divIntTy)
        (Term.app (Term.var "g" divSp divIntTy)
          [Term.var "x" divSp divIntTy] divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivCallResult   -- expect: violation
example : (checkCaps noPanicDivCallResult).isViolation = true := by native_decide

/-- A NESTED arithmetic divisor — `100 / (a * (b + 1))`. (march: exit 1.) -/
def noPanicDivNestedArith : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("a", Lin.unrestricted, some divIntTy),
                  ("b", Lin.unrestricted, some divIntTy)] none
      (divTerm (Term.lit (Lit.int 100) divIntTy)
        (Term.app (Term.var "*" divSp divIntTy)
          [Term.var "a" divSp divIntTy,
           Term.app (Term.var "+" divSp divIntTy)
             [Term.var "b" divSp divIntTy, Term.lit (Lit.int 1) divIntTy] divIntTy]
          divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivNestedArith   -- expect: violation
example : (checkCaps noPanicDivNestedArith).isViolation = true := by native_decide

/-- A genuine RECORD FIELD divisor — `if r.d != 0 do 10 / r.d else 0 end` — is
a VIOLATION even though a guard of exactly this shape discharges a plain
variable. `r.d`'s base is not a module path, so `Desugar`'s
`flatten_module_path` leaves it an `EField`, which is march's arm 4 and never
reaches `path_proves_nonzero` at all. Verified against the binary: exit 1,
where the module-qualified twin below is exit 0. This pair is the whole
correspondence argument in two fixtures. -/
def noPanicDivGuardedRecordField : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("r", Lin.unrestricted, none)] none
      (Term.ite
        (Term.app (Term.var "!=" divSp divIntTy)
          [Term.field (Term.var "r" divSp divIntTy) "d" divSp divIntTy,
           Term.lit (Lit.int 0) divIntTy] divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy)
          (Term.field (Term.var "r" divSp divIntTy) "d" divSp divIntTy))
        (Term.lit (Lit.int 0) divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivGuardedRecordField   -- expect: violation
example : (checkCaps noPanicDivGuardedRecordField).isViolation = true := by native_decide

/-- The FALSE-REJECT guard for the tightening: a MODULE-QUALIFIED divisor
`Consts.k` under `if Consts.k != 0`. march ACCEPTS this (verified: exit 0) —
`Desugar`'s `EField` arm (`desugar.ml:677-697`) flattens the module path to a
single `EVar {txt = "Consts.k"}` BEFORE `check_clause` runs, so march's arm 3
sees a variable and `path_proves_nonzero` discharges it. We decode the very
same node (`"kind":"EVar"`, `name.txt = "Consts.k"` — confirmed in the
`--emit-core-ast` output for this program) to `Term.var "Consts.k"`, so
`pathProvesNonzero` discharges it identically. If a future change ever
classified a dotted name as "complex", this pin fails instead of the harness
finding a false reject. -/
def noPanicDivGuardedQualifiedVar : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.ite
        (Term.app (Term.var "!=" divSp divIntTy)
          [Term.var "Consts.k" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "Consts.k" divSp divIntTy))
        (Term.lit (Lit.int 0) divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivGuardedQualifiedVar   -- expect: ok
example : (checkCaps noPanicDivGuardedQualifiedVar).isViolation = false := by native_decide
example : (checkCaps noPanicDivGuardedQualifiedVar).isSkip = false := by native_decide

/-- `Term.unsupported` as a divisor stays a SKIP, not a reject — the one shape
held back from the tightening (`divisorVerdict`'s docstring: it is
`decodeTerm`'s open catch-all for march `kind`s that may not exist yet). Such
a body already reports `hasUnsupported`, so the file skips downstream anyway;
what this pins is that `checkCaps` does not pre-empt that with a violation. -/
def noPanicDivUnsupportedDivisorSkips : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.unsupported divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivUnsupportedDivisorSkips   -- expect: skip
example : (checkCaps noPanicDivUnsupportedDivisorSkips).isSkip = true := by native_decide

/-- A division-operator NAME applied at an arity march's own guard
(`[lhs; rhs]`) does not match is NOT a division site. Pins the arity-exact
`args` match in `divisionVerdict`'s `.app` arm: with an `args[1]?` lookup the
complex second argument here would now false-reject. -/
def noPanicDivOpWrongArityIsNotADivSite : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("a", Lin.unrestricted, some divIntTy),
                  ("b", Lin.unrestricted, some divIntTy)] none
      (Term.app (Term.var "int_div" divSp divIntTy)
        [Term.lit (Lit.int 10) divIntTy,
         Term.app (Term.var "+" divSp divIntTy)
           [Term.var "a" divSp divIntTy, Term.var "b" divSp divIntTy] divIntTy,
         Term.lit (Lit.int 1) divIntTy] divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivOpWrongArityIsNotADivSite   -- expect: ok
example : (checkCaps noPanicDivOpWrongArityIsNotADivSite).isViolation = false := by native_decide

/-- `let d = a + b; 10 / d` → SKIP. march DOES track this `let` (its own
`bind_let` records every rhs, not just literals) and hands the rhs to
`smt_of`/Z3 — the one arm where a `let`-bound divisor can still be
discharged. No solver here, so no verdict. -/
def noPanicDivLetNonLiteral : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("a", Lin.unrestricted, some divIntTy),
                  ("b", Lin.unrestricted, some divIntTy)] none
      (Term.let_ "d" Lin.unrestricted none
        (Term.app (Term.var "+" divSp divIntTy)
          [Term.var "a" divSp divIntTy, Term.var "b" divSp divIntTy] divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivLetNonLiteral   -- expect: skip
example : (checkCaps noPanicDivLetNonLiteral).isSkip = true := by native_decide

/-- Tier order inside one module: a fn with a PROVABLE `10 / 0` and another
fn with an unresolvable divisor is a VIOLATION, not a skip. march errors on
the provable site regardless of what it decides about the other, so the
definite verdict must win (`checkOneModule`'s two-pass `divVerdicts` scan). -/
def noPanicDivProvableBeatsUnknown : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "g" [("d", Lin.unrestricted, some divIntTy)] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy)),
    Decl.dfn "f" [] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 0) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivProvableBeatsUnknown   -- expect: violation
example : (checkCaps noPanicDivProvableBeatsUnknown).isViolation = true := by native_decide

/-- Tier order ACROSS modules (`CapResult.andThen`): a skip in the FIRST
module must not swallow a definite violation in a later sibling — the file is
still a reject. This is the direction a naive early-return on the first
non-`ok` result would get wrong. -/
def noPanicDivSkipDoesNotMaskSibling : Module := {
  decls := [
    Decl.dmod "A" [
      Decl.dopts ["no_panic"],
      Decl.dfn "f" [("d", Lin.unrestricted, some divIntTy)] none
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))],
    Decl.dmod "B" [
      Decl.dopts ["no_panic"],
      Decl.dfn "g" [] none
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 0) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivSkipDoesNotMaskSibling   -- expect: violation
example : (checkCaps noPanicDivSkipDoesNotMaskSibling).isViolation = true := by native_decide

/-- The other direction of `CapResult.andThen`: a clean sibling must not
swallow a skip. `A` is unjudgeable, `B` is fine — the FILE is a skip. -/
def noPanicDivSkipSurvivesCleanSibling : Module := {
  decls := [
    Decl.dmod "A" [
      Decl.dopts ["no_panic"],
      Decl.dfn "f" [("d", Lin.unrestricted, some divIntTy)] none
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))],
    Decl.dmod "B" [
      Decl.dopts ["no_panic"],
      Decl.dfn "g" [] none
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 2) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivSkipSurvivesCleanSibling   -- expect: skip
example : (checkCaps noPanicDivSkipSurvivesCleanSibling).isSkip = true := by native_decide

/-- A bare `10 / 2` — a non-zero LITERAL divisor — stays a plain `ok`. The
three-way boundary must not drag the literal fast-path into `unknown`. -/
def noPanicDivLiteralNonZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 2) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivLiteralNonZero   -- expect: ok
example : (checkCaps noPanicDivLiteralNonZero).isViolation = false := by native_decide
example : (checkCaps noPanicDivLiteralNonZero).isSkip = false := by native_decide

/-- A guarded PARAMETER divisor — `fn f(d : Int) do if d != 0 do 10 / d else 0
end end` — stays a plain `ok`, not a skip: `path_proves_nonzero` is march's
own solver-free fast path and it applies to an unrefined parameter exactly as
it does to a `let`-bound one. march ACCEPTS this file. Without this pin the
three-way boundary could regress into skipping every parameter divisor. -/
def noPanicDivGuardedParam : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [("d", Lin.unrestricted, some divIntTy)] none
      (Term.ite
        (Term.app (Term.var "!=" divSp divIntTy)
          [Term.var "d" divSp divIntTy, Term.lit (Lit.int 0) divIntTy] divIntTy)
        (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
        (Term.lit (Lit.int 0) divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicDivGuardedParam   -- expect: ok
example : (checkCaps noPanicDivGuardedParam).isViolation = false := by native_decide
example : (checkCaps noPanicDivGuardedParam).isSkip = false := by native_decide

/-- A division by a literal `0` in a module WITHOUT `cap no_panic` → ok (the
check is gated on the cap, same as every other behavioral cap above). -/
def divUngatedWithoutCap : Module := {
  decls := [Decl.dmod "Plain" [
    Decl.dfn "f" [] none
      (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.lit (Lit.int 0) divIntTy))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps divUngatedWithoutCap   -- expect: ok (no `no_panic` opt)
example : (checkCaps divUngatedWithoutCap).isViolation = false := by native_decide

/-- Shadowing teeth, direction 1: `let d = 0; let d = 5; 10 / d` → ok — the
stale `d ↦ 0` fact from the first `let` must be RETIRED by the second, not
merged or left to leak through. -/
def noPanicShadowRetiresZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 5) divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicShadowRetiresZero   -- expect: ok
example : (checkCaps noPanicShadowRetiresZero).isViolation = false := by native_decide

/-- Shadowing teeth, direction 2 (the reverse of the above): `let d = 5; let d
= 0; 10 / d` → violation — the LATER binding's literal `0` must win, not the
earlier non-zero one. -/
def noPanicShadowInstallsZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 5) divIntTy)
        (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
          (divTerm (Term.lit (Lit.int 10) divIntTy) (Term.var "d" divSp divIntTy))
          divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noPanicShadowInstallsZero   -- expect: violation
example : (checkCaps noPanicShadowInstallsZero).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- A3 slice (c), Task 3: `no_panic`'s SECOND half — non-exhaustive matches.
-- See `matchExhaustive`'s docstring for the full march citation
-- (`typecheck.ml:4546-4581`, `check_exhaustiveness`'s guardless-only-coverage
-- fallback for a guarded match; `typecheck.ml:8955-8971`,
-- `check_no_panic_module`'s promotion of a recorded non-exhaustive span to an
-- error). Every fixture below is a direct false-reject probe: this task has
-- produced five false rejects already (see the module's `bodyCalls`
-- docstring for the general discipline), so each shape march ACCEPTS is
-- pinned here as `ok`, not just each shape it rejects.

private def optionIntTy : Ty := Ty.con "Option" [Ty.con "Int" []]
private def npSpan : Span := ⟨"f", 0, 0, 0, 0⟩

/-- `reject/t48`-equivalent: `Some(x) -> x` alone — no `None`, no guard, no
wildcard — is non-exhaustive → violation. -/
def npNonExhaustive : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
        Term.var "x" npSpan (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npNonExhaustive   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npNonExhaustive).isViolation = true := by native_decide

/-- `reject/t50`-equivalent: `Some(v) when v > 0 -> v | None -> 0` — the
GUARDED `Some` does not count toward coverage, so only `None` is guardlessly
covered → still non-exhaustive → violation. This is the shape that proves the
guard field is load-bearing (see the report's teeth-check). -/
def npGuardedNonExh : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "classify" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "v" Lin.unrestricted],
        some (Term.lit (Lit.bool true) (Ty.con "Bool" [])),
        Term.var "v" npSpan (Ty.con "Int" [])),
       (Pattern.con "None" [], none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npGuardedNonExh   -- expect: violation (guarded Some doesn't cover, None alone is non-exhaustive)
example : (checkCaps npGuardedNonExh).isViolation = true := by native_decide

/-- `accept/t59`-equivalent: same as `npGuardedNonExh`, plus a GUARDLESS
`Some(v)` arm — now the guardless arms (`Some`, `None`) cover `Option`'s full
ctor set → exhaustive → ok. -/
def npGuardless : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "classify" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "v" Lin.unrestricted],
        some (Term.lit (Lit.bool true) (Ty.con "Bool" [])),
        Term.var "v" npSpan (Ty.con "Int" [])),
       (Pattern.con "Some" [Pattern.var "v" Lin.unrestricted], none,
        Term.lit (Lit.int 0) (Ty.con "Int" [])),
       (Pattern.con "None" [], none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npGuardless   -- expect: ok
example : (checkCaps npGuardless).isViolation = false := by native_decide

/-- False-reject probe 1: a guardless wildcard arm is a catch-all regardless
of any other arm or the scrutinee type → ok. -/
def npWildcard : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
        Term.var "x" npSpan (Ty.con "Int" [])),
       (Pattern.wild, none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npWildcard   -- expect: ok
example : (checkCaps npWildcard).isViolation = false := by native_decide

/-- False-reject probe 2: a fully-covered `Option` (`Some` AND `None`, no
wildcard needed) → ok — ctor-set coverage alone is sufficient. -/
def npFullyCoveredOption : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
        Term.var "x" npSpan (Ty.con "Int" [])),
       (Pattern.con "None" [], none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npFullyCoveredOption   -- expect: ok
example : (checkCaps npFullyCoveredOption).isViolation = false := by native_decide

/-- A user ADT `Color = Red | Green | Blue` (`Decl.dtype`), reused by the next
two fixtures: one non-exhaustive (only `Red`/`Green` covered), one fully
covered. -/
def colorCtors : List CtorSig :=
  [ { name := "Red", argTys := [], resultTy := Ty.con "Color" [] },
    { name := "Green", argTys := [], resultTy := Ty.con "Color" [] },
    { name := "Blue", argTys := [], resultTy := Ty.con "Color" [] } ]
def colorDType : Decl := Decl.dtype "Color" [] colorCtors
def colorTy : Ty := Ty.con "Color" []

/-- False-reject probe 3 (negative half, must still REJECT): a user ADT match
covering only 2 of 3 ctors, no wildcard → non-exhaustive → violation. Proves
`userCtors` (from the decoded `DType`) actually drives coverage, not just the
built-in table. -/
def npUserAdtNonExhaustive : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Red" [], none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Green" [], none, Term.lit (Lit.int 1) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npUserAdtNonExhaustive   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npUserAdtNonExhaustive).isViolation = true := by native_decide

/-- False-reject probe 3 (positive half): the same user ADT, all 3 ctors
guardlessly covered → ok. -/
def npUserAdtFullyCovered : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Red" [], none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Green" [], none, Term.lit (Lit.int 1) (Ty.con "Int" [])),
         (Pattern.con "Blue" [], none, Term.lit (Lit.int 2) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npUserAdtFullyCovered   -- expect: ok
example : (checkCaps npUserAdtFullyCovered).isViolation = false := by native_decide

/-- False-reject probe 4: a match on a scrutinee type this checker cannot
resolve AT ALL — not `builtinCtors`, no decoded `DType` for it (no `Widget`
`Decl.dtype` anywhere in this module) — with only a partial, non-wildcard arm
list. Per `matchExhaustive`'s docstring, an unknown type is conservatively
exhaustive: inventing a reject here would be a false reject on a program this
checker cannot actually judge. -/
def npUnknownScrutineeOk : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("w", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "w" npSpan (Ty.con "Widget" []))
      [(Pattern.con "Sprocket" [], none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npUnknownScrutineeOk   -- expect: ok
example : (checkCaps npUnknownScrutineeOk).isViolation = false := by native_decide

/-- False-reject probe 5: a guarded arm PLUS a guardless WILDCARD catch-all
(distinct from `npGuardless`, whose guardless catch-all is a `Some(v)` ctor
arm, not a wildcard) → ok regardless of the guarded arm's coverage. -/
def npGuardedPlusGuardlessCatchAll : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "classify" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "v" Lin.unrestricted],
        some (Term.lit (Lit.bool true) (Ty.con "Bool" [])),
        Term.var "v" npSpan (Ty.con "Int" [])),
       (Pattern.wild, none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npGuardedPlusGuardlessCatchAll   -- expect: ok
example : (checkCaps npGuardedPlusGuardlessCatchAll).isViolation = false := by native_decide

/-- A non-exhaustive match NESTED inside a `let` (not the `dfn` body's own
top-level node) is still found — `bodyHasNonExhaustiveMatch`'s `matchesIn`
walk is total over every `Term` constructor, matching `bodyCalls`/
`bodyAllocates`'s discipline, not just a top-level scan. -/
def npNestedMatchNonExhaustive : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.let_ "_" Lin.unrestricted none
      (Term.match_ (Term.var "o" npSpan optionIntTy)
        [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
          Term.var "x" npSpan (Ty.con "Int" []))]
        (Ty.con "Int" []))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npNestedMatchNonExhaustive   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npNestedMatchNonExhaustive).isViolation = true := by native_decide

/-- Gating: the SAME non-exhaustive match, in a module WITHOUT `cap no_panic`
at all, must NOT be flagged — mirrors `divUngatedWithoutCap`. -/
def npNonExhaustiveUngated : Module := {
  decls := [Decl.dmod "Plain" [
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
        Term.var "x" npSpan (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npNonExhaustiveUngated   -- expect: ok (no `cap no_panic`)
example : (checkCaps npNonExhaustiveUngated).isViolation = false := by native_decide

/-- Finding I3, exhaustiveness half: like `pureInheritedIntoNestedModule`,
this half of `no_panic` lives in the SAME march function
(`check_no_panic_module`) and the SAME `inner_env` as the explicit-panic
scan, so it INHERITS into a nested `dmod` too. `Outer` declares `cap
no_panic`; nested `Inner` (no cap of its own) has a non-exhaustive match. -/
def npNonExhaustiveInheritedIntoNestedModule : Module := {
  decls := [Decl.dmod "Outer" [
  Decl.dopts ["no_panic"],
  Decl.dmod "Inner" [
    Decl.dfn "get" [("o", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "o" npSpan optionIntTy)
        [(Pattern.con "Some" [Pattern.var "x" Lin.unrestricted], none,
          Term.var "x" npSpan (Ty.con "Int" []))]
        (Ty.con "Int" []))]]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npNonExhaustiveInheritedIntoNestedModule   -- expect: violation naming no_panic
example : (checkCaps npNonExhaustiveInheritedIntoNestedModule).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- A3 slice (c) review findings C1 (or-patterns), C2 (as-patterns), C3
-- (user-type shadowing a built-in ctor set) — all three were FALSE REJECTS
-- (march accepts, this checker rejected) before the fixes above. See
-- `matchExhaustive`'s docstring for the full citations.

/-- C1: `Red | Green -> 0; Blue -> 2` over the `Color` user ADT — the
or-pattern's coverage is the UNION of its alternatives (`Red`, `Green`),
which together with the `Blue` arm covers the full ctor set → exhaustive →
ok. Before the fix, `Pattern.or_` didn't exist (decoded to `.unsupported`)
and contributed NOTHING to coverage, so this was a false reject. -/
def npOrPatternCoversAlternatives : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ [Pattern.con "Red" [], Pattern.con "Green" []], none,
          Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Blue" [], none, Term.lit (Lit.int 2) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternCoversAlternatives   -- expect: ok
example : (checkCaps npOrPatternCoversAlternatives).isViolation = false := by native_decide

/-- C1 negative half (must still REJECT): the SAME or-pattern arm, with no
`Blue` arm at all — `Red | Green` covers only 2 of `Color`'s 3 ctors → still
non-exhaustive → violation. Proves the or-pattern fix didn't blunt the check
into accepting everything. -/
def npOrPatternStillNonExhaustive : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ [Pattern.con "Red" [], Pattern.con "Green" []], none,
          Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternStillNonExhaustive   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npOrPatternStillNonExhaustive).isViolation = true := by native_decide

/-- C2: `Red as r -> 0; Green -> 1; Blue -> 2` — `isCatchAllPattern`/
`isModeledArmPattern`/`patCoveredCtors` each strip the `as` wrapper (via
their own `.as` recursion) before the coverage test, so `Red as r` counts as
covering `Red` exactly like a bare `Red` arm would → all 3 ctors covered →
ok. Before the fix, `matchExhaustive` never peeled `Pattern.as`, so
`Red as r`'s `.as` shape matched neither the catch-all test nor
`Pattern.con`, contributing nothing to coverage — a false reject. -/
def npAsPatternPeels : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.as "r" (Pattern.con "Red" []), none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Green" [], none, Term.lit (Lit.int 1) (Ty.con "Int" [])),
         (Pattern.con "Blue" [], none, Term.lit (Lit.int 2) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npAsPatternPeels   -- expect: ok
example : (checkCaps npAsPatternPeels).isViolation = false := by native_decide

/-- C2, catch-all half: `x as y -> ..` alone — peeling the `as` reaches a bare
`Pattern.var`, so this is a catch-all regardless of the scrutinee type →
exhaustive → ok, exactly as a plain `x -> ..` arm would be. -/
def npAsPatternCatchAll : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.as "y" (Pattern.var "x" Lin.unrestricted), none,
        Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npAsPatternCatchAll   -- expect: ok
example : (checkCaps npAsPatternCatchAll).isViolation = false := by native_decide

/-- C3: a user `type Result = Success(Int) | Failure(Int)` — same type NAME
as the built-in `Result` (`{Ok, Err}`), different ctors entirely. Matching
`Success`/`Failure` exhaustively must be judged against the USER's own ctor
set, not the built-in one: `(userCtors ++ builtinCtors).find?` finds the
user entry first → `{Success, Failure}` is the universe → both covered → ok.
Before the fix (`(builtinCtors ++ userCtors).find?`), the built-in `Result`
entry was found FIRST and this match was judged against `{Ok, Err}`, which
`Success`/`Failure` can never satisfy — a false reject. -/
def userResultCtors : List CtorSig :=
  [ { name := "Success", argTys := [Ty.con "Int" []], resultTy := Ty.con "Result" [] },
    { name := "Failure", argTys := [Ty.con "Int" []], resultTy := Ty.con "Result" [] } ]
def userResultDType : Decl := Decl.dtype "Result" [] userResultCtors
def userResultTy : Ty := Ty.con "Result" []
def npUserResultShadowsBuiltin : Module := {
  decls := [
  userResultDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("r", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "r" npSpan userResultTy)
        [(Pattern.con "Success" [Pattern.var "n" Lin.unrestricted], none,
          Term.var "n" npSpan (Ty.con "Int" [])),
         (Pattern.con "Failure" [Pattern.var "n" Lin.unrestricted], none,
          Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npUserResultShadowsBuiltin   -- expect: ok
example : (checkCaps npUserResultShadowsBuiltin).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- Regression fix: an or-pattern with a WILDCARD/VAR alternative
-- (`Red | _`, `_ | Red`) is a catch-all — `isCatchAllPattern`. Before this
-- fix, `isCatchAll` peeled only `Pattern.as` and never looked inside
-- `Pattern.or_`, and `isModeledArmPattern` reported `.or_ [.con _, .wild]`
-- as fully modeled (so the unmodelled-pattern safety net didn't fire
-- either); the arm was then scored only by `patCoveredCtors`, where the
-- `.wild` alternative contributes nothing to coverage — a false reject of
-- code march accepts (worse than the C1/C2 false rejects this task's
-- earlier fixes replaced, because these programs previously exited 2
-- (skip) and now produced a live MISMATCH). See `isCatchAllPattern`'s
-- docstring for the `norm_pat_all`/`norm_pat` citations.

/-- `Red | _ -> 0` alone, no other arm: the `.wild` alternative makes the
whole or-pattern a catch-all → exhaustive → ok, regardless of `Color` having
3 ctors and only 1 named here. -/
def npOrPatternWildAltCatchAll : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ [Pattern.con "Red" [], Pattern.wild], none,
          Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternWildAltCatchAll   -- expect: ok
example : (checkCaps npOrPatternWildAltCatchAll).isViolation = false := by native_decide

/-- `_ | Red -> 0` — same as above with the wildcard alternative FIRST
instead of last, pinning that `isCatchAllPattern`'s `alts.any` doesn't care
about alternative order. -/
def npOrPatternWildAltCatchAllLeading : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ [Pattern.wild, Pattern.con "Red" []], none,
          Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternWildAltCatchAllLeading   -- expect: ok
example : (checkCaps npOrPatternWildAltCatchAllLeading).isViolation = false := by native_decide

/-- `Red -> 1; Green | _ -> 0` — the exact 3-arm shape from the regression
report: a plain `Red` arm followed by an or-arm whose second alternative is
`.wild`. The or-arm alone is a catch-all, so the whole match is exhaustive →
ok, independent of the preceding `Red` arm. -/
def npOrPatternWildAltAfterConstructorArm : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Red" [], none, Term.lit (Lit.int 1) (Ty.con "Int" [])),
         (Pattern.or_ [Pattern.con "Green" [], Pattern.wild], none,
          Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternWildAltAfterConstructorArm   -- expect: ok
example : (checkCaps npOrPatternWildAltAfterConstructorArm).isViolation = false := by native_decide

/-- Negative half (must NOT over-apply the fix): `Red | Green -> 0` alone,
no `Blue` arm — an or-pattern of CONSTRUCTORS ONLY (no `.wild`/`.var`
alternative) must still contribute exactly its named constructors via
`patCoveredCtors`, not become a blanket catch-all. `Blue` is uncovered →
non-exhaustive → violation. (This is the same fixture as
`npOrPatternStillNonExhaustive` above, C1's negative half — restated here
under the regression-fix section for direct traceability: `isCatchAllPattern
(.or_ [.con "Red" [], .con "Green" []])` must be `false`.) -/
example : (checkCaps npOrPatternStillNonExhaustive).isViolation = true := by native_decide

/-- Negative half (guards still don't cover, even under an or-pattern):
`Red | Green when b -> 0` (guarded) plus `Blue -> 1` (guardless) — the
guarded or-arm contributes NOTHING to coverage (guard `g.isSome`, checked
before `isCatchAllPattern`/`patCoveredCtors` are even consulted for that
arm), so only `Blue` is guardlessly covered → `Red`/`Green` uncovered →
non-exhaustive → violation. Proves the regression fix didn't accidentally
let a guarded or-arm's wildcard alternative leak through the guard gate. -/
def npOrPatternGuardedDoesNotCover : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none), ("b", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ [Pattern.con "Red" [], Pattern.con "Green" []],
          some (Term.var "b" npSpan (Ty.con "Bool" [])),
          Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Blue" [], none, Term.lit (Lit.int 1) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternGuardedDoesNotCover   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npOrPatternGuardedDoesNotCover).isViolation = true := by native_decide

/-- C1+C2 safety net: a guardless `Pattern.tuple` arm (unmodelled by
`isModeledArmPattern`) is the ENTIRE arm list — no `Pattern.con`/wildcard at
all. `matchExhaustive` cannot prove this non-exhaustive through a pattern
form it doesn't model, so per the safety-net rule it is conservatively
judged exhaustive → ok, the same "cannot prove ⇒ do not manufacture a
reject" discipline already applied to unknown scrutinee TYPES. -/
def npUnmodelledPatternSafetyNet : Module := {
  decls := [Decl.dmod "G" [
  Decl.dopts ["no_panic"],
  Decl.dfn "get" [("o", Lin.unrestricted, none)] none
    (Term.match_ (Term.var "o" npSpan optionIntTy)
      [(Pattern.tuple [Pattern.wild, Pattern.wild], none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
      (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npUnmodelledPatternSafetyNet   -- expect: ok
example : (checkCaps npUnmodelledPatternSafetyNet).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- FINDING A (this commit, general-conservatism-rule review): a same-named
-- user type declared in TWO different modules is an ambiguous constructor
-- universe this checker cannot resolve the way march's `ci_module`-scoped
-- `local_shadow` does — see `matchExhaustive`'s docstring. Must be judged
-- exhaustive, not arbitrarily against whichever `DType` decl-order put
-- first.

/-- A second, differently-shaped `Color` declared in a SIBLING module from
`colorDType`'s (`Cyan`/`Magenta` instead of `Red`/`Green`/`Blue`). Together
they make `dtypeCtorSets` report TWO entries keyed `"Color"`. -/
def colorCtorsAmbiguous : List CtorSig :=
  [ { name := "Cyan", argTys := [], resultTy := Ty.con "Color" [] },
    { name := "Magenta", argTys := [], resultTy := Ty.con "Color" [] } ]
def colorDTypeAmbiguous : Decl := Decl.dtype "Color" [] colorCtorsAmbiguous

/-- Finding A: `mod A do type Color = Red|Green|Blue end; mod G do cap
no_panic; type Color = Cyan|Magenta; fn describe(c : Color) : Int do match c
do Cyan -> 0; Magenta -> 1 end end end` — `G`'s `Color` is fully covered by
its OWN two ctors, but `dtypeCtorSets` sees `A`'s three-ctor `Color` too
(same bare name, different module), so the universe is ambiguous → this
checker cannot tell which one march would pick → conservatively exhaustive →
ok. Before the fix, `(userCtors ++ builtinCtors).find?` took whichever
`Color` decl came first (decl order, not module scoping) — order-dependent
and a live false reject whenever `A`'s entry happened to land first. -/
def npAmbiguousTypeNameAcrossSiblingModules : Module := {
  decls := [
  Decl.dmod "A" [colorDType],
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    colorDTypeAmbiguous,
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Cyan" [], none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Magenta" [], none, Term.lit (Lit.int 1) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npAmbiguousTypeNameAcrossSiblingModules   -- expect: ok
example : (checkCaps npAmbiguousTypeNameAcrossSiblingModules).isViolation = false := by native_decide

/-- Same ambiguity, module ORDER SWAPPED (`G` before `A`) — must give the
SAME verdict (ok) as the fixture above, pinning that the fix isn't itself
order-dependent (it treats "more than one match" as ambiguous regardless of
which one `List.filter` would have found first). -/
def npAmbiguousTypeNameAcrossSiblingModulesSwapped : Module := {
  decls := [
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    colorDTypeAmbiguous,
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Cyan" [], none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Magenta" [], none, Term.lit (Lit.int 1) (Ty.con "Int" []))]
        (Ty.con "Int" []))],
  Decl.dmod "A" [colorDType]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npAmbiguousTypeNameAcrossSiblingModulesSwapped   -- expect: ok
example : (checkCaps npAmbiguousTypeNameAcrossSiblingModulesSwapped).isViolation = false := by native_decide

/-- Same ambiguity with the duplicate `Color` declared at the ENCLOSING
level instead of a sibling module — `dtypeCtorSets` gathers `Decl.dtype`
across the WHOLE flattened tree regardless of nesting depth, so an outer
`Color` and `G`'s own `Color` collide exactly like two siblings' would. -/
def npAmbiguousTypeNameEnclosingLevel : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    colorDTypeAmbiguous,
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.con "Cyan" [], none, Term.lit (Lit.int 0) (Ty.con "Int" [])),
         (Pattern.con "Magenta" [], none, Term.lit (Lit.int 1) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npAmbiguousTypeNameEnclosingLevel   -- expect: ok
example : (checkCaps npAmbiguousTypeNameEnclosingLevel).isViolation = false := by native_decide

/-- Negative half (must NOT over-apply the fix): a SINGLE `Color` declaration
(`colorDType` alone, as `npUserAdtFullyCovered` already exercises) must not
be treated as ambiguous just because the fix now filters `userCtors` by
name — restated here for direct traceability next to Finding A's other
fixtures. -/
example : (checkCaps npUserAdtFullyCovered).isViolation = false := by native_decide

/-- Negative half, C3 survival: `npUserResultShadowsBuiltin`'s user `Result`
(single `Decl.dtype`, shadowing the BUILT-IN `Result`, not another user
decl) must still resolve to the user's own ctors, not be treated as
ambiguous — `userCtors` alone has exactly one `"Result"` entry; `builtinCtors`
is a separate list never counted by the Finding A ambiguity filter. Restated
here for direct traceability; the underlying fixture/proof already exists
above. -/
example : (checkCaps npUserResultShadowsBuiltin).isViolation = false := by native_decide

-- ---------------------------------------------------------------------
-- FINDING B (this commit, general-conservatism-rule review): march's
-- `or_expansion_cap` (256 rows, `typecheck.ml:3958`) — past it, march
-- abandons per-row enumeration and widens the whole or-pattern to a
-- catch-all (`norm_pat`'s `PatOr -> SPWild`). This checker previously
-- enumerated unconditionally, so an over-cap or-pattern naming only SOME
-- of a type's constructors was judged non-exhaustive when march judges it
-- a full catch-all — a false reject. See `orExpansionSize`/
-- `patOrExpansionCapped`'s docstrings for the mirrored algorithm.

/-- `n` copies of a guardless `Red` alternative, for building or-patterns at
a specific or-expansion size (each `Pattern.con _ []` alternative has size 1,
so `n` alternatives sums to exactly `n`). -/
def manyRedAlts (n : Nat) : List Pattern := List.replicate n (Pattern.con "Red" [])

/-- Finding B, boundary exceeded: a single arm `Red | Red | … | Red -> 0`
with 300 alternatives (`orExpansionSize` sums to 300 > `orExpansionCap`
256) over the 3-ctor `Color` type, no `Green`/`Blue` arm at all. Past the
cap march treats the WHOLE or-pattern as a catch-all regardless of which
(or how few distinct) constructors it names → exhaustive → ok. Before the
fix, `patCoveredCtors` unconditionally contributed just `{Red}` and the
match was rejected as missing `Green`/`Blue` — a false reject of code march
accepts. -/
def npOrPatternOverCapCatchAll : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ (manyRedAlts 300), none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternOverCapCatchAll   -- expect: ok
example : (checkCaps npOrPatternOverCapCatchAll).isViolation = false := by native_decide

/-- Finding B, boundary NOT exceeded (must NOT over-apply the fix): the
identical shape with only 200 alternatives (`orExpansionSize` = 200 ≤ 256)
— still strictly UNDER march's cap, so no widening happens on either side;
`patCoveredCtors` still contributes only `{Red}`, `Green`/`Blue` remain
uncovered → still non-exhaustive → violation. Pins the exact boundary: this
fixture and the 300-alternative one above differ ONLY in count, and must
give OPPOSITE verdicts. -/
def npOrPatternUnderCapStillNonExhaustive : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.match_ (Term.var "c" npSpan colorTy)
        [(Pattern.or_ (manyRedAlts 200), none, Term.lit (Lit.int 0) (Ty.con "Int" []))]
        (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps npOrPatternUnderCapStillNonExhaustive   -- expect: violation naming no_panic (non-exhaustive)
example : (checkCaps npOrPatternUnderCapStillNonExhaustive).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- `Term.opaque_`: the nine unmodelled-but-child-carrying march kinds.
--
-- The 242-file conformance corpus CANNOT regression-test any of this: a
-- census found NO file combining a `cap` directive with a capability
-- violation inside any of these constructors. A green harness run is
-- therefore no evidence at all here, and these hand-built pins are the only
-- coverage. Each fixture reproduces the exact CHILD-LIST ARRANGEMENT
-- `Elab.decodeTerm` produces for that `kind` (see its docstring's table),
-- since that arrangement — not the node's shape, which is not modelled — is
-- the whole contract between the decoder and the cap layer.
--
-- Every violating shape below was verified end to end against the real
-- march binary: march rejects it naming the capability, and
-- `march --emit-core-ast | march-lean-check` now exits 1 (it exited 2
-- before `Term.opaque_`). Every non-violating counterpart was verified to be
-- ACCEPTED by march, and must NOT produce a violation here — a `violation`
-- on one of those would be a false reject, the worst error class this
-- oracle has.

def opqSp : Span := ⟨"o", 0, 0, 0, 0⟩
def opqUnitTy : Ty := Ty.con "Unit" []
def opqIntTy : Ty := Ty.con "Int" []

/-- `println("x")` — an `IO.Console` builtin, banned under `cap pure`. This is
the violation every `*Violating` fixture below hides inside an `opaque_`. -/
def opqBanned : Term :=
  Term.app (Term.var "println" opqSp opqUnitTy)
    [Term.lit (Lit.str "x") (Ty.con "String" [])] opqUnitTy

/-- An inert child: no call, no allocation, no division. -/
def opqInert : Term := Term.lit (Lit.int 1) opqIntTy

/-- `mod P do cap pure ... fn f() do <body> end end`. -/
def opqPureMod (body : Term) : Module := {
  decls := [Decl.dmod "P" [Decl.dopts ["pure"], Decl.dfn "f" [] none body]],
  schemes := [], insts := [], moduleCaps := [] }

/-- The invariant the whole design rests on: an `opaque_` node is out of
fragment REGARDLESS of its children, so `Compare.inferModule`'s whole-file
skip gate still fires and `Infer`/`Linearity` never judge it. If this ever
becomes `false`, every one of the nine fixtures below turns into a
false-reject risk. -/
example : (Term.opaque_ [] opqIntTy).hasUnsupported = true := by native_decide
example : (Term.opaque_ [opqInert] opqIntTy).hasUnsupported = true := by native_decide

/-- `ECond` — `match do c1 -> println("x") ... end`. Children are the arms
flattened as `cond, body, cond, body, ...`; BOTH halves are expressions and
march's `calls_in_expr` folds both. -/
def opqCondViolating : Module := opqPureMod
  (Term.opaque_ [Term.var "c1" opqSp (Ty.con "Bool" []), opqBanned,
                 Term.var "c2" opqSp (Ty.con "Bool" []), opqInert] opqIntTy)
#eval checkCaps opqCondViolating   -- expect: violation naming `pure`
example : (checkCaps opqCondViolating).isViolation = true := by native_decide

/-- `ECond` near-miss: same shape, no banned call anywhere. march ACCEPTS. -/
def opqCondClean : Module := opqPureMod
  (Term.opaque_ [Term.var "c1" opqSp (Ty.con "Bool" []), opqInert,
                 Term.var "c2" opqSp (Ty.con "Bool" []), opqInert] opqIntTy)
#eval checkCaps opqCondClean   -- expect: ok
example : (checkCaps opqCondClean).isViolation = false := by native_decide

/-- `ERecordUpdate` — `{ r with a: println("x") }`. Children are `base`
followed by each field's `value`; the field NAMES carry no expression. -/
def opqRecordUpdateViolating : Module := opqPureMod
  (Term.opaque_ [Term.var "r" opqSp opqIntTy, opqBanned] opqIntTy)
#eval checkCaps opqRecordUpdateViolating   -- expect: violation naming `pure`
example : (checkCaps opqRecordUpdateViolating).isViolation = true := by native_decide

def opqRecordUpdateClean : Module := opqPureMod
  (Term.opaque_ [Term.var "r" opqSp opqIntTy, opqInert] opqIntTy)
#eval checkCaps opqRecordUpdateClean   -- expect: ok
example : (checkCaps opqRecordUpdateClean).isViolation = false := by native_decide

/-- `EAtom` — `:tag(println("x"))`. Children are `args`; the atom itself is a
bare string in the envelope, not an expression. -/
def opqAtomViolating : Module := opqPureMod (Term.opaque_ [opqBanned] opqIntTy)
#eval checkCaps opqAtomViolating   -- expect: violation naming `pure`
example : (checkCaps opqAtomViolating).isViolation = true := by native_decide

def opqAtomClean : Module := opqPureMod (Term.opaque_ [opqInert] opqIntTy)
#eval checkCaps opqAtomClean   -- expect: ok
example : (checkCaps opqAtomClean).isViolation = false := by native_decide

/-- `EAssert` — `assert println("x") > 0`. One child, `expr`. -/
def opqAssertViolating : Module := opqPureMod
  (Term.opaque_ [Term.app (Term.var ">" opqSp (Ty.con "Bool" []))
                   [opqBanned, opqInert] (Ty.con "Bool" [])] opqUnitTy)
#eval checkCaps opqAssertViolating   -- expect: violation naming `pure`
example : (checkCaps opqAssertViolating).isViolation = true := by native_decide

def opqAssertClean : Module := opqPureMod
  (Term.opaque_ [Term.app (Term.var ">" opqSp (Ty.con "Bool" []))
                   [opqInert, opqInert] (Ty.con "Bool" [])] opqUnitTy)
#eval checkCaps opqAssertClean   -- expect: ok
example : (checkCaps opqAssertClean).isViolation = false := by native_decide

/-- `EDbg` — `dbg(println("x"))`. One child when `expr` is present. -/
def opqDbgViolating : Module := opqPureMod (Term.opaque_ [opqBanned] opqUnitTy)
#eval checkCaps opqDbgViolating   -- expect: violation naming `pure`
example : (checkCaps opqDbgViolating).isViolation = true := by native_decide

/-- `EDbg` with NO expression — bare `dbg()` emits `"expr": null`, which
decodes to an EMPTY child list (march's own `EDbg (None, _)` arm contributes
nothing). Nothing to find, and no decode error either. -/
def opqDbgNullaryClean : Module := opqPureMod (Term.opaque_ [] opqUnitTy)
#eval checkCaps opqDbgNullaryClean   -- expect: ok
example : (checkCaps opqDbgNullaryClean).isViolation = false := by native_decide

/-- `ELetFn` — a nested `fn g() do println("x") end` inside a block. The child
is `body` ONLY: `params` are `param_to_json` records (name/ty/lin) carrying no
expression, and march's `ELetFn` arm of `calls_in_expr` walks only `body`. -/
def opqLetFnViolating : Module := opqPureMod (Term.opaque_ [opqBanned] opqIntTy)
#eval checkCaps opqLetFnViolating   -- expect: violation naming `pure`
example : (checkCaps opqLetFnViolating).isViolation = true := by native_decide

def opqLetFnClean : Module := opqPureMod (Term.opaque_ [opqInert] opqIntTy)
#eval checkCaps opqLetFnClean   -- expect: ok
example : (checkCaps opqLetFnClean).isViolation = false := by native_decide

/-- `ELetQ` — `let? v = r` with the banned call in the CONTINUATION. Children
are `value` then `cont`; the pattern binds names but carries no expression.
The `cont` position is the one that matters: parser folding turns the rest of
the enclosing block into it, so most real code puts its work there. -/
def opqLetQViolating : Module := opqPureMod
  (Term.opaque_ [Term.var "r" opqSp opqIntTy, opqBanned] opqIntTy)
#eval checkCaps opqLetQViolating   -- expect: violation naming `pure`
example : (checkCaps opqLetQViolating).isViolation = true := by native_decide

def opqLetQClean : Module := opqPureMod
  (Term.opaque_ [Term.var "r" opqSp opqIntTy, opqInert] opqIntTy)
#eval checkCaps opqLetQClean   -- expect: ok
example : (checkCaps opqLetQClean).isViolation = false := by native_decide

/-- `ESend` — `send(p, println("x"))`. Children are `cap` then `msg`. -/
def opqSendViolating : Module := opqPureMod
  (Term.opaque_ [Term.var "p" opqSp opqIntTy, opqBanned] opqUnitTy)
#eval checkCaps opqSendViolating   -- expect: violation naming `pure`
example : (checkCaps opqSendViolating).isViolation = true := by native_decide

def opqSendClean : Module := opqPureMod
  (Term.opaque_ [Term.var "p" opqSp opqIntTy, opqInert] opqUnitTy)
#eval checkCaps opqSendClean   -- expect: ok
example : (checkCaps opqSendClean).isViolation = false := by native_decide

/-- `ESpawn` — `spawn(<expr>)`. One child, `actor`. march additionally
requires that child to be a bare actor name, so in WELL-TYPED code nothing can
hide there; the arm exists because `calls_in_expr` walks it anyway and because
`--emit-core-ast` still emits an AST for a program march rejects. -/
def opqSpawnViolating : Module := opqPureMod (Term.opaque_ [opqBanned] opqUnitTy)
#eval checkCaps opqSpawnViolating   -- expect: violation naming `pure`
example : (checkCaps opqSpawnViolating).isViolation = true := by native_decide

def opqSpawnClean : Module := opqPureMod
  (Term.opaque_ [Term.var "Counter" opqSp opqIntTy] opqUnitTy)
#eval checkCaps opqSpawnClean   -- expect: ok
example : (checkCaps opqSpawnClean).isViolation = false := by native_decide

/-- The other three cap-layer walks reach through `opaque_` too.

`no_panic` / `divisionVerdict`: a LITERAL-ZERO divisor hidden in an
`opaque_` child is a violation — march's arm 1 errors on it unconditionally,
with no solver, no refinement escape and no path escape, so the emptied
facts/path this arm recurses with cannot cost us the answer. -/
def opqNoPanicDivZeroInChild : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.opaque_ [divTerm (Term.lit (Lit.int 10) divIntTy)
                             (Term.lit (Lit.int 0) divIntTy)] divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoPanicDivZeroInChild   -- expect: violation naming no_panic
example : (checkCaps opqNoPanicDivZeroInChild).isViolation = true := by native_decide

/-- ...and a NON-zero literal divisor in the same position stays ok. -/
def opqNoPanicDivNonZeroInChild : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.opaque_ [divTerm (Term.lit (Lit.int 10) divIntTy)
                             (Term.lit (Lit.int 2) divIntTy)] divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoPanicDivNonZeroInChild   -- expect: ok
example : (checkCaps opqNoPanicDivNonZeroInChild).isViolation = false := by native_decide

/-- The emptied-channels choice, pinned. A `let d = 0` fact in scope OUTSIDE
an `opaque_` must NOT be carried into its children: `opaque_` records no
binders, so an `ELetFn`/`ELetQ` child that REBINDS `d` would be judged against
a stale fact and false-reject a program march accepts. `divisionVerdict`
recurses with empty facts AND empty path, so `10 / d` inside the child is an
undischarged variable — `DivVerdict.unknown`, i.e. a SKIP, never a reject. -/
def opqNoPanicStaleFactNotCarried : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (Term.let_ "d" Lin.unrestricted none (Term.lit (Lit.int 0) divIntTy)
        (Term.opaque_ [divTerm (Term.lit (Lit.int 10) divIntTy)
                               (Term.var "d" divSp divIntTy)] divIntTy)
        divIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoPanicStaleFactNotCarried   -- expect: skip, NOT violation
example : (checkCaps opqNoPanicStaleFactNotCarried).isViolation = false := by native_decide
example : (checkCaps opqNoPanicStaleFactNotCarried).isSkip = true := by native_decide

/-- `no_alloc` / `bodyAllocates`: an allocation NESTED in an `opaque_` child is
found (march's `no_alloc.ml` recurses into all nine kinds)... -/
def opqNoAllocTupleInChild : Module := {
  decls := [Decl.dmod "NA" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none
      (Term.opaque_ [Term.tuple [opqInert, opqInert] (Ty.tuple [opqIntTy, opqIntTy])]
        opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoAllocTupleInChild   -- expect: violation naming no_alloc
example : (checkCaps opqNoAllocTupleInChild).isViolation = true := by native_decide

/-- ...but the `opaque_` node itself allocates NOTHING. This matters most for
`ERecordUpdate`: march flags `ERecord` as an allocation and does NOT flag
`ERecordUpdate` (`no_alloc.ml:23` vs `:62`), so this arm must not copy
`.record`'s unconditional `true`. -/
def opqNoAllocNodeItselfIsNotAnAllocation : Module := {
  decls := [Decl.dmod "NA" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none
      (Term.opaque_ [Term.var "r" opqSp opqIntTy, opqInert] opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoAllocNodeItselfIsNotAnAllocation   -- expect: ok
example : (checkCaps opqNoAllocNodeItselfIsNotAnAllocation).isViolation = false := by native_decide

/-- `no_panic` / `matchesIn`: a non-exhaustive `match` nested inside an
`opaque_` child (e.g. inside a `cond` arm) is as much a runtime-panic surface
as a top-level one, and is reached. -/
def opqNoPanicNonExhaustiveMatchInChild : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (Term.opaque_
        [Term.match_ (Term.var "c" npSpan colorTy)
          [(Pattern.con "Red" [], none, Term.lit (Lit.int 0) opqIntTy)]
          opqIntTy]
        opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps opqNoPanicNonExhaustiveMatchInChild   -- expect: violation naming no_panic
example : (checkCaps opqNoPanicNonExhaustiveMatchInChild).isViolation = true := by native_decide

-- ---------------------------------------------------------------------
-- TRAILING `ELet` (a `do` block's last/only statement).
--
-- ROOT CAUSE these pin: `Elab.decodeTerm` had NO `"ELet"` arm. march's
-- emitter does not wrap a single-statement block in an `EBlock`, and
-- `decodeBlockStmts` hands an `EBlock`'s FINAL element straight back to
-- `decodeTerm` — so a trailing `let` hit the `| _ => Term.unsupported`
-- fallback and its right-hand side was DISCARDED before any walk below ever
-- saw it. Every cap walk went blind at once: `bodyCalls`, `bodyAllocates`,
-- `divisionVerdict` and `matchesIn`. march rejected
-- `fn f() : Unit do let q = println("leak") end`; we exited 2.
--
-- This was NOT an `opaque_` bug and NOT specific to the app-fn position that
-- surfaced it (`{ p with x: println("leak") }` applied to `()`): `bodyCalls`'s
-- generic `.app fn args` arm was always correct, it just never received a
-- term. The shapes below are what the FIXED decoder now emits, so they pin
-- the contract between decoder and cap layer, not the decoder's own dispatch
-- (that is pinned by the `#eval`s in `Elab`'s `Test` namespace).
--
-- Every violating fixture was verified end to end against the real march
-- binary (march exit 1 naming the cap; `--emit-core-ast | march-lean-check`
-- exited 2 before this fix and exits 1 after). Every clean counterpart was
-- verified ACCEPTED by march and must NOT produce a violation here.

/-- A trailing `let` has no continuation, so `decodeTerm`'s `ELet` arm makes
`Term.unsupported` the `let_`'s BODY. That is what keeps `hasUnsupported`
true (the file still skips, `Infer`/`Linearity` still never judge it) while
leaving the RHS on a real `let_` — so `divisionVerdict`'s fact/path
retirement still applies to the bound name, which `opaque_` could not offer.
If this ever becomes `false`, the trailing-let shape stops skipping and every
fixture below turns into a false-reject risk. -/
def trailingLet (rhs : Term) (ty : Ty) : Term :=
  Term.let_ "q" Lin.unrestricted none rhs (Term.unsupported ty) ty

example : (trailingLet opqInert opqIntTy).hasUnsupported = true := by native_decide

/-- The reported reproducer, exactly: `let q = { p with x: println("leak") }`
as a fn body, where march parses the record-update as the FN of a zero-arg
`EApp`. Two previously-fatal layers at once — the trailing `let` (which used
to drop everything) and the `opaque_` in app-fn position. -/
def letAppFnOpaqueViolating : Module := opqPureMod
  (trailingLet
    (Term.app
      (Term.opaque_ [Term.var "p" opqSp opqIntTy, opqBanned] opqIntTy) [] opqIntTy)
    opqIntTy)
#eval checkCaps letAppFnOpaqueViolating   -- expect: violation naming `pure`
example : (checkCaps letAppFnOpaqueViolating).isViolation = true := by native_decide

/-- Near-miss: same two layers, no banned call. march ACCEPTS — a violation
here would be a false reject. -/
def letAppFnOpaqueClean : Module := opqPureMod
  (trailingLet
    (Term.app
      (Term.opaque_ [Term.var "p" opqSp opqIntTy, opqInert] opqIntTy) [] opqIntTy)
    opqIntTy)
#eval checkCaps letAppFnOpaqueClean   -- expect: ok
example : (checkCaps letAppFnOpaqueClean).isViolation = false := by native_decide

/-- The general case, with no `opaque_` involved at all: a banned call sitting
DIRECTLY in a trailing let's RHS. This is the fixture that shows the bug was
never about the app-fn position. -/
def letTrailingBannedCall : Module := opqPureMod (trailingLet opqBanned opqUnitTy)
#eval checkCaps letTrailingBannedCall   -- expect: violation naming `pure`
example : (checkCaps letTrailingBannedCall).isViolation = true := by native_decide

/-- Sibling walk `bodyAllocates`: a non-empty tuple in a trailing let's RHS. -/
def letTrailingAllocates : Module := {
  decls := [Decl.dmod "NA" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none
      (trailingLet (Term.tuple [opqInert, opqInert] opqIntTy) opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps letTrailingAllocates   -- expect: violation naming no_alloc
example : (checkCaps letTrailingAllocates).isViolation = true := by native_decide

/-- Sibling walk `divisionVerdict`: `let q = 10 / 0` as the whole body. -/
def letTrailingDivZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (trailingLet
        (Term.app (Term.var "/" opqSp opqIntTy)
          [Term.lit (Lit.int 10) opqIntTy, Term.lit (Lit.int 0) opqIntTy] opqIntTy)
        opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps letTrailingDivZero   -- expect: violation naming no_panic
example : (checkCaps letTrailingDivZero).isViolation = true := by native_decide

/-- Near-miss for the above: `let q = 10 / 2`. march ACCEPTS. -/
def letTrailingDivNonZero : Module := {
  decls := [Decl.dmod "NP" [
    Decl.dopts ["no_panic"],
    Decl.dfn "f" [] none
      (trailingLet
        (Term.app (Term.var "/" opqSp opqIntTy)
          [Term.lit (Lit.int 10) opqIntTy, Term.lit (Lit.int 2) opqIntTy] opqIntTy)
        opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps letTrailingDivNonZero   -- expect: ok
example : (checkCaps letTrailingDivNonZero).isViolation = false := by native_decide

/-- Sibling walk `matchesIn`: a non-exhaustive `match` in a trailing let's
RHS. (An `Int` scrutinee would NOT pin this — `matchExhaustive` is
deliberately conservative there and answers "exhaustive"; only a user ADT
whose constructors it can enumerate exercises the walk.) -/
def letTrailingNonExhaustiveMatch : Module := {
  decls := [
  colorDType,
  Decl.dmod "G" [
    Decl.dopts ["no_panic"],
    Decl.dfn "describe" [("c", Lin.unrestricted, none)] none
      (trailingLet
        (Term.match_ (Term.var "c" npSpan colorTy)
          [(Pattern.con "Red" [], none, Term.lit (Lit.int 0) opqIntTy)]
          opqIntTy)
        opqIntTy)]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps letTrailingNonExhaustiveMatch   -- expect: violation naming no_panic
example : (checkCaps letTrailingNonExhaustiveMatch).isViolation = true := by native_decide

/-- SEPARATE SIBLING, same class: a NON-`PatVar`/`PatWild` `ELet` binder in
NON-tail position. `decodeBlockStmts` used to answer `Term.unsupported` for
the whole element, throwing away both the RHS and the entire remainder of the
block; it now answers `Term.opaque_ [rhs, rest]`. Verified against march:
`let (a, b) = (println("leak"), 1)` followed by `a` is a reject we skipped.
`opaque_` (not a synthetic `let_ "_"`) is the right carrier here because it
empties `divisionVerdict`'s channels, so a stale fact about a name the
destructuring pattern rebinds cannot manufacture a false reject. -/
def letDestructuringBinderViolating : Module := opqPureMod
  (Term.opaque_
    [Term.tuple [opqBanned, opqInert] opqIntTy, Term.var "a" opqSp opqIntTy]
    opqIntTy)
#eval checkCaps letDestructuringBinderViolating   -- expect: violation naming `pure`
example : (checkCaps letDestructuringBinderViolating).isViolation = true := by native_decide

/-- Near-miss for the above: `let (a, b) = (1, 2)` then `a`, under `cap pure`.
march ACCEPTS. (This fixture is `cap pure`, not `no_alloc` — the tuple IS an
allocation, so it would legitimately violate `no_alloc`.) -/
def letDestructuringBinderClean : Module := opqPureMod
  (Term.opaque_
    [Term.tuple [opqInert, opqInert] opqIntTy, Term.var "a" opqSp opqIntTy]
    opqIntTy)
#eval checkCaps letDestructuringBinderClean   -- expect: ok
example : (checkCaps letDestructuringBinderClean).isViolation = false := by native_decide

end MarchLean.CapCheck
