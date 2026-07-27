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

**This walk is DELIBERATELY MORE TOTAL than march's own `calls_in_expr`
(`typecheck.ml:6737-6768`), and that is not a bug to fix here.** march's
version ends in a catch-all `| _ -> acc` and has no `ETuple`/record/list arm,
so a call nested inside a tuple/record/list literal is invisible to it. E.g.
`(println("hi"), old)` as a migrate body: march's Check 8 ACCEPTS (the
`println` inside the `ETuple` is never visited by `calls_in_expr`), while this
checker's exhaustive walk correctly finds it and REJECTS. Do not narrow
`bodyCalls` to match march's gap — that gap looks like a genuine march bug,
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
  | .match_ scrut arms _ => bodyCalls banned scrut || arms.any (fun (_, e) => bodyCalls banned e)
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

/-- `bodyCallsIO`, kept as a thin specialisation of `bodyCalls` over
`ioBuiltins` so Check 8's existing call site (`checkOneModule`) is unchanged
by this refactor. -/
def bodyCallsIO (t : Term) : Bool := bodyCalls ioBuiltins t

/-- Does this term (a function body) allocate — construct a tuple, record,
non-nullary `con`, or `lam`? A sibling total walk to `bodyCalls`, for the
upcoming `no_alloc` behavioral cap (A3 slice (c)): `true` at `.tuple _ _`,
`.record _ _`, `.con _ (_ :: _) _` (a NON-EMPTY arg list — a nullary
constructor, e.g. `None`, allocates nothing, mirroring march's `no_alloc.ml`),
and `.lam _ _ _` (a closure allocation); recurses into every other
constructor's children looking for a nested allocation; `.lit`/`.var`/
`.unsupported` are the only genuine leaves. Enumerates all 13 `Term`
constructors explicitly — no catch-all — matching `bodyCalls`'s exhaustiveness
discipline. -/
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
  | .tuple _ _ => true
  | .record _ _ => true
  | .field record _ _ _ => bodyAllocates record
  | .match_ scrut arms _ => bodyAllocates scrut || arms.any (fun (_, e) => bodyAllocates e)
  | .unsupported _ => false

/-- Is `used` covered by any declared need? Reflexive and directional. -/
def covered (declared : List String) (used : String) : Bool :=
  declared.any (fun need => capSubsumes need used)

/-- Check one module (not recursing into nested modules — the caller does
that, since each module is checked against its OWN declared needs).
`selfDeclaredCaps` is the list of fully-qualified cap paths (e.g.
`"Db.Migrated"`) that Check 1 must treat as covered regardless of `needs`,
per Finding I1's self-declaration exemption — see `checkCaps`'s docstring for
why this is passed in ONLY at the top-level call and always `[]` for a
nested `dmod`. -/
def checkOneModule (modName : String) (decls : List Decl)
    (moduleCaps : List (String × List String))
    (selfDeclaredCaps : List String := []) : CapResult :=
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
  -- scans only THIS module's own `dfn`/`dlet` bodies/decls (never a nested
  -- `dmod`'s — `checkDecls` recurses into those separately, each against its
  -- own `dopts`, so a parent's declared caps never govern a child's
  -- functions).
  --
  -- **`Decl.dlet` bodies are scanned here too, alongside `Decl.dfn`.** march's
  -- own `check_pure_module`/`check_deterministic_module`/`check_no_panic_module`
  -- (`typecheck.ml`) all iterate `Ast.DFn` ONLY — a plain `Ast.DLet` is never
  -- scanned by any of the three. But `Elab.decodeDecl`'s `DFn` arm (Task 1
  -- infra, unchanged here — this file may only touch `CapCheck.lean`) collapses
  -- a ZERO-PARAM `fn` clause to `Decl.dlet name body` (`"0-param clause: a
  -- plain value binding"`), discarding the fact that it originated from an
  -- `Ast.DFn` in march's real AST rather than an `Ast.DLet`. march's own
  -- `--emit-core-ast` still tags a 0-param fn `"kind":"DFn"` — verified
  -- directly: `fn fail() : Int do panic("boom") end` emits `DFn`, not `DLet`
  -- — so a 0-param `cap no_panic`/`pure`/`deterministic` fn (e.g.
  -- `reject/t42`'s `fail()`, `t46`'s `gen()`, `t47`'s `ts()`) is a march-real
  -- `DFn` that this checker would otherwise silently drop from the scan
  -- entirely (falling through to a downstream skip on the unbound builtin
  -- name, never surfacing the capability violation at all). Scanning `dlet`
  -- bodies here recovers exactly those 0-param fns. The cost, since this
  -- checker cannot recover the lost DFn/DLet distinction from `Decl.dlet`
  -- alone: a genuine top-level `let x = ...` binding (a real `Ast.DLet`,
  -- which march's three checks never scan) sitting directly in a
  -- `pure`/`deterministic`/`no_panic` module and calling a banned name would
  -- be a FALSE REJECT here that march itself would accept. This is a
  -- one-sided fidelity gap in the conservative direction (reject when march
  -- accepts) rather than the unsound direction (accept when march rejects),
  -- and is not exercised by any fixture in this corpus (every `dlet` in the
  -- accept/reject fixtures below and in `specs/lang/types` is a folded
  -- 0-param `fn`, never a bare module-level `let`). A future fix belongs in
  -- `Elab.lean`'s decoder (e.g. a dedicated `Decl.dzerofn` constructor
  -- preserving the distinction), not here.
  let opts := decls.flatMap (fun d => match d with | .dopts o => o | _ => [])
  let dfns := decls.filterMap (fun d => match d with
    | .dfn name _ _ body => some (name, body)
    | .dlet name body => some (name, body)
    | _ => none)
  -- `pure` (typecheck.ml:8232): bans EVERY name in `builtinCaps` (the whole
  -- builtin→cap table, IO/Alloc/Panic alike) UNION the four extra names that
  -- are side-effecting but not in that table: `spawn`, `send`, `exit`,
  -- `read_byte`.
  let pureBanned := builtinCaps.map (·.1) ++ ["spawn", "send", "exit", "read_byte"]
  match if opts.contains "pure" then dfns.find? (fun (_, body) => bodyCalls pureBanned body) else none with
  | some (name, _) =>
      .violation s!"cap pure: fn `{name}` in module `{modName}` performs a side effect"
  | none =>
  -- `deterministic` (`:8297`, `is_nondeterministic_cap` `:8213`): bans ONLY
  -- the builtins whose cap is `IO.Clock` or `IO.Random` (6 names) — NOT the
  -- whole `builtinCaps` table, which would false-reject ordinary IO.
  let detBanned := (builtinCaps.filter (fun (_, c) => c == "IO.Clock" || c == "IO.Random")).map (·.1)
  match if opts.contains "deterministic" then dfns.find? (fun (_, body) => bodyCalls detBanned body) else none with
  | some (name, _) =>
      .violation s!"cap deterministic: fn `{name}` in module `{modName}` performs a non-deterministic operation"
  | none =>
  -- `no_extern` (`:8255`): the module's own decls contain a `Decl.dextern`.
  if opts.contains "no_extern" && decls.any (fun d => match d with | .dextern _ _ => true | _ => false) then
    .violation s!"cap no_extern: module `{modName}` contains an extern block"
  else
  -- `no_alloc` (`refinecheck/no_alloc.ml`): a `dfn` body constructs a
  -- tuple/record/non-nullary-con/lambda.
  match if opts.contains "no_alloc" then dfns.find? (fun (_, body) => bodyAllocates body) else none with
  | some (name, _) =>
      .violation s!"cap no_alloc: fn `{name}` in module `{modName}` allocates"
  | none =>
  -- `no_panic`, explicit-panic half only (`:8108`) — a `dfn` body directly
  -- calls `panic`. Exhaustiveness (the OTHER half of `no_panic`) is Task 3,
  -- not modelled here.
  match if opts.contains "no_panic" then dfns.find? (fun (_, body) => bodyCalls ["panic"] body) else none with
  | some (name, _) =>
      .violation s!"cap no_panic: fn `{name}` in module `{modName}` may panic (explicit panic)"
  | none => .ok

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
  match checkOneModule "<top-level>" m.decls m.moduleCaps selfDeclaredCaps with
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
          [(Pattern.wild,
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
-- bodyAllocates: a tuple allocates; a bare literal does not.
example : bodyAllocates (Term.tuple [] (Ty.con "Unit" [])) = true := by native_decide
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

/-- `no_alloc`: a `dfn` returning a `Term.tuple` → violation. -/
def noAllocTuple : Module := {
  decls := [Decl.dmod "A" [
    Decl.dopts ["no_alloc"],
    Decl.dfn "f" [] none (Term.tuple [] (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noAllocTuple   -- expect: violation naming `no_alloc`
example : (checkCaps noAllocTuple).isViolation = true := by native_decide

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

end MarchLean.CapCheck
