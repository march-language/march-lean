# A1 march-side: `format_version` 2 emitter — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Executes in the `march` repo** (NOT march-lean), on a fresh branch off
> `main` (main already has the A0 `--emit-core-ast` v1 emitter). Design doc:
> march-lean `specs/plans/2026-07-21-a1-elaboration-checker-design.md` — read
> §2 (the seam) and §3 before starting. This plan is the *producer*; the
> march-lean checker plan (`2026-07-21-a1-march-lean-checker.md`) is the
> *consumer* of the exact JSON shape defined here.

**Goal:** Upgrade `march --emit-core-ast` from `format_version` 1 to 2: annotate every AST node with its resolved type, and emit two HM witness tables (generalization schemes + instantiations), so an independent Lean checker can verify march's elaboration without re-running inference.

**Architecture:** A new internal-`ty` → JSON encoder (deep-`repr`, total over march's `ty`) lives in `lib/dump/ast_json.ml` (which already depends on `march_typecheck`). The typechecker records two witness tables into new `env` fields during checking, at the single `instantiate` chokepoint. `bin/main.ml`'s emit branch joins `type_map` onto the AST inline and appends the two tables to the envelope.

**Tech Stack:** OCaml, dune, Alcotest (existing test framework), march's own `Dump.json_*` combinators.

## Global Constraints

- **Verdict/exit contract unchanged** from A0: `--emit-core-ast` exits 0=accept, 1=reject; the envelope's `verdict` is computed by the exact same pipeline (`check_module_full` + refine/division/no-alloc/cap passes) — do NOT touch that logic.
- **No Mathlib / no new external dependency.** `march_dump` already depends on `march_typecheck`; add no new library deps.
- **The emitted `module` is `user_ast`** (`bin/main.ml`, `let user_ast = desugared` before stdlib/import injection) — the pre-import user subset. Do NOT switch it to the full `desugared`.
- **JSON numbers are real JSON numbers** (not quoted), per the existing A0 convention in `ast_json.ml`.
- **`format_version` is a JSON integer equal to `2`.**
- **The `ty → JSON` shape defined in Task 1 is a contract** the march-lean checker decodes verbatim. Any field-name change here is a breaking change there — keep them in sync.

---

## File Structure

- `lib/dump/ast_json.ml` — **modify**: add `resolved_ty_to_json` (internal-`ty` encoder) + `constraint_to_json`; thread `type_map` into `module_to_json`/`expr_to_json`/… to emit `resolved_ty` per node.
- `lib/typecheck/typecheck.ml` — **modify**: 2 new `env` fields (scheme + instantiation witness tables); populate them at `instantiate`; thread `?use_span` into `instantiate` and pass it at `EVar`/`EField` call sites.
- `bin/main.ml` — **modify**: bump `format_version` to `2`; call `module_to_json ~types`; serialize the two witness tables into the envelope; update the parse-failure short-circuit to v2 shape.
- `test/test_ty_json.ml` — **create**: focused unit tests for the `resolved_ty_to_json` encoder.
- `test/dune` — **modify**: register `test_ty_json`; the emit golden stanza needs no structural change.
- `test/emit_core_ast/fixtures/*.expected.json` — **regenerate**: 4 fixtures become v2.
- `test/test_emit_core_ast.ml` — **modify**: assert `resolved_ty` + witness fields present.

---

## Task 1: Internal-`ty` → JSON encoder

**Files:**
- Modify: `lib/dump/ast_json.ml` (add encoder functions near the existing `ty_to_json`, which encodes *surface* `Ast.ty` — this new one encodes *internal* `March_typecheck.Typecheck.ty`)
- Create: `test/test_ty_json.ml`
- Modify: `test/dune`

**Interfaces:**
- Produces: `Ast_json.resolved_ty_to_json : March_typecheck.Typecheck.ty -> string` and `Ast_json.constraint_to_json : March_typecheck.Typecheck.constraint_ -> string`. Both return a JSON-object string. Consumed by Task 3 (node annotation) and Task 4 (witness serialization).
- The JSON shape (contract with the march-lean checker):
  - `TCon(name,args)` → `{"kind":"TCon","name":<str>,"args":[<ty>...]}`
  - `TArrow(a,b)` → `{"kind":"TArrow","from":<ty>,"to":<ty>}`
  - `TTuple ts` → `{"kind":"TTuple","elems":[<ty>...]}`
  - `TRecord flds` → `{"kind":"TRecord","fields":[{"name":<str>,"ty":<ty>}...]}` (fields in stored/sorted order — do NOT re-sort)
  - `TVar` (after `repr`, always `Unbound(id,_)`) → `{"kind":"TVar","id":<int>}`
  - `TLin(l,t)` → `{"kind":"TLin","lin":"linear"|"affine"|"unrestricted","ty":<ty>}`
  - `TNat n` → `{"kind":"TNat","n":<int>}`
  - `TNatOp(op,a,b)` → `{"kind":"TNatOp","op":"add"|"mul","a":<ty>,"b":<ty>}`
  - `TChan _` → `{"kind":"unsupported","what":"session"}`
  - `TError` → `{"kind":"TError"}`
  - constraints: `CNum t`→`{"kind":"CNum","ty":<ty>}`, `COrd t`→`{"kind":"COrd","ty":<ty>}`, `CInterface(n,t)`→`{"kind":"CInterface","name":<str>,"ty":<ty>}`, `CADTBound(n,t)`→`{"kind":"CADTBound","name":<str>,"ty":<ty>}`, `CTNatBound t`→`{"kind":"CTNatBound","ty":<ty>}`

- [ ] **Step 1: Write the failing test**

Create `test/test_ty_json.ml`:

```ocaml
(* Unit tests for Ast_json.resolved_ty_to_json — the internal-ty -> JSON
   encoder used by --emit-core-ast v2. Constructs Typecheck.ty values
   directly and asserts the JSON shape (contract with the march-lean checker). *)
module T = March_typecheck.Typecheck
module J = March_dump.Ast_json

let check name expected actual =
  Alcotest.(check string) name expected actual

let test_tcon () =
  check "Int" {|{"kind":"TCon","name":"Int","args":[]}|}
    (J.resolved_ty_to_json (T.TCon ("Int", [])))

let test_tcon_args () =
  check "List(Int)"
    {|{"kind":"TCon","name":"List","args":[{"kind":"TCon","name":"Int","args":[]}]}|}
    (J.resolved_ty_to_json (T.TCon ("List", [ T.TCon ("Int", []) ])))

let test_tarrow () =
  check "Int -> Int"
    {|{"kind":"TArrow","from":{"kind":"TCon","name":"Int","args":[]},"to":{"kind":"TCon","name":"Int","args":[]}}|}
    (J.resolved_ty_to_json (T.TArrow (T.TCon ("Int", []), T.TCon ("Int", []))))

let test_tvar_unbound () =
  (* A raw unbound metavariable serializes to its id. *)
  check "tvar 7"
    {|{"kind":"TVar","id":7}|}
    (J.resolved_ty_to_json (T.TVar (ref (T.Unbound (7, 0)))))

let test_tvar_link_deep_repr () =
  (* A Link must be followed by deep-repr, not emitted as a var. *)
  let inner = T.TCon ("Bool", []) in
  check "linked -> Bool"
    {|{"kind":"TCon","name":"Bool","args":[]}|}
    (J.resolved_ty_to_json (T.TVar (ref (T.Link inner))))

let test_trecord_order_preserved () =
  check "record keeps stored order"
    {|{"kind":"TRecord","fields":[{"name":"b","ty":{"kind":"TCon","name":"Int","args":[]}},{"name":"a","ty":{"kind":"TCon","name":"Int","args":[]}}]}|}
    (J.resolved_ty_to_json
       (T.TRecord [ ("b", T.TCon ("Int", [])); ("a", T.TCon ("Int", [])) ]))

let test_tchan_unsupported () =
  check "session -> unsupported"
    {|{"kind":"unsupported","what":"session"}|}
    (J.resolved_ty_to_json (T.TChan (ref T.SEnd)))

let test_constraint_cnum () =
  check "CNum a"
    {|{"kind":"CNum","ty":{"kind":"TVar","id":3}}|}
    (J.constraint_to_json (T.CNum (T.TVar (ref (T.Unbound (3, 0))))))

let () =
  Alcotest.run "ty_json"
    [ ("encoder",
       [ Alcotest.test_case "tcon" `Quick test_tcon;
         Alcotest.test_case "tcon_args" `Quick test_tcon_args;
         Alcotest.test_case "tarrow" `Quick test_tarrow;
         Alcotest.test_case "tvar_unbound" `Quick test_tvar_unbound;
         Alcotest.test_case "tvar_link_deep_repr" `Quick test_tvar_link_deep_repr;
         Alcotest.test_case "trecord_order" `Quick test_trecord_order_preserved;
         Alcotest.test_case "tchan_unsupported" `Quick test_tchan_unsupported;
         Alcotest.test_case "constraint_cnum" `Quick test_constraint_cnum ]) ]
```

Register it in `test/dune` (add near the other `(test ...)` / `(executable ...)` stanzas — mirror the existing `test_ast_json` stanza's shape):

```lisp
(test
 (name test_ty_json)
 (modules test_ty_json)
 (libraries march_dump march_typecheck alcotest))
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cd /Users/80197052/code/march && eval $(opam env --switch=march) && dune build --root . @test/test_ty_json 2>&1 | head -30`
Expected: FAIL — compile error, `Unbound value J.resolved_ty_to_json` (the encoder doesn't exist yet).

- [ ] **Step 3: Implement the encoder**

In `lib/dump/ast_json.ml`, add (module alias at top if not present: `module T = March_typecheck.Typecheck`). Place these functions above `module_to_json`. Use the existing `Dump.json_obj`, `Dump.json_string`, `Dump.json_list`, and raw-int emission (integers are emitted verbatim as their `string_of_int`, matching this file's existing convention):

```ocaml
let lin_str : Ast.linearity -> string = function
  | Ast.Linear -> "linear"
  | Ast.Affine -> "affine"
  | Ast.Unrestricted -> "unrestricted"

let natop_str : Ast.nat_op -> string = function
  | Ast.NatAdd -> "add"
  | Ast.NatMul -> "mul"

(* Internal-ty -> JSON. Deep-repr at every level: resolve the head, then
   recurse (each recursive call re-reprs its argument). Total over T.ty.
   Contract: see test/test_ty_json.ml and the A1 design doc §2. *)
let rec resolved_ty_to_json (t : T.ty) : string =
  match T.repr t with
  | T.TCon (name, args) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TCon");
        ("name", Dump.json_string name);
        ("args", Dump.json_list (List.map resolved_ty_to_json args)) ]
  | T.TArrow (a, b) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TArrow");
        ("from", resolved_ty_to_json a);
        ("to", resolved_ty_to_json b) ]
  | T.TTuple ts ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TTuple");
        ("elems", Dump.json_list (List.map resolved_ty_to_json ts)) ]
  | T.TRecord flds ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TRecord");
        ("fields",
         Dump.json_list
           (List.map
              (fun (n, ft) ->
                Dump.json_obj
                  [ ("name", Dump.json_string n);
                    ("ty", resolved_ty_to_json ft) ])
              flds)) ]
  | T.TVar r ->
    (match !r with
     | T.Unbound (id, _) ->
       Dump.json_obj
         [ ("kind", Dump.json_string "TVar"); ("id", string_of_int id) ]
     | T.Link _ ->
       (* repr already follows links; unreachable, but stay total. *)
       resolved_ty_to_json (T.repr t))
  | T.TLin (l, inner) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TLin");
        ("lin", Dump.json_string (lin_str l));
        ("ty", resolved_ty_to_json inner) ]
  | T.TNat n ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TNat"); ("n", string_of_int n) ]
  | T.TNatOp (op, a, b) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "TNatOp");
        ("op", Dump.json_string (natop_str op));
        ("a", resolved_ty_to_json a);
        ("b", resolved_ty_to_json b) ]
  | T.TChan _ ->
    Dump.json_obj
      [ ("kind", Dump.json_string "unsupported");
        ("what", Dump.json_string "session") ]
  | T.TError -> Dump.json_obj [ ("kind", Dump.json_string "TError") ]
  | T.TRefine (base, _, _) ->
    (* repr strips TRefine, so this is unreachable; recurse defensively. *)
    resolved_ty_to_json base

let constraint_to_json : T.constraint_ -> string = function
  | T.CNum t ->
    Dump.json_obj [ ("kind", Dump.json_string "CNum"); ("ty", resolved_ty_to_json t) ]
  | T.COrd t ->
    Dump.json_obj [ ("kind", Dump.json_string "COrd"); ("ty", resolved_ty_to_json t) ]
  | T.CInterface (n, t) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "CInterface");
        ("name", Dump.json_string n);
        ("ty", resolved_ty_to_json t) ]
  | T.CADTBound (n, t) ->
    Dump.json_obj
      [ ("kind", Dump.json_string "CADTBound");
        ("name", Dump.json_string n);
        ("ty", resolved_ty_to_json t) ]
  | T.CTNatBound t ->
    Dump.json_obj [ ("kind", Dump.json_string "CTNatBound"); ("ty", resolved_ty_to_json t) ]
```

If `march_dump`'s `dune` `modules` list is explicit, no change is needed (both new functions live inside the existing `ast_json` module). Confirm `Dump.json_obj` emits keys in list order (it does — A0 relied on this).

- [ ] **Step 4: Run the test to verify it passes**

Run: `dune build --root . @test/test_ty_json 2>&1 | tail -20`
Expected: PASS — `Test Successful ... 8 tests run`.

- [ ] **Step 5: Commit**

```bash
cd /Users/80197052/code/march
git add lib/dump/ast_json.ml test/test_ty_json.ml test/dune
git commit -m "feat(dump): internal-ty -> JSON encoder for --emit-core-ast v2 (A1 Task 1)"
```

---

## Task 2: Record scheme + instantiation witnesses

**Files:**
- Modify: `lib/typecheck/typecheck.ml` (add 2 `env` fields; init in `make_env`; populate + thread `?use_span` at `instantiate`)

**Interfaces:**
- Consumes: nothing new.
- Produces: two fields on the `env` record, readable from the `env` value that `check_module_full` returns:
  - `scheme_witnesses : (int list, T.constraint_ list * T.ty) Hashtbl.t` — keyed by the scheme's quantified-id list; value is `(constraints, body)`.
  - `inst_witnesses : (Ast.span, int list * T.ty list) Hashtbl.t` — keyed by use-site span; value is `(ids, arg_types)` where `arg_types` are the freshly-substituted (post-solve, resolvable via `repr`) type arguments positionally aligned to `ids`.

- [ ] **Step 1: Write the failing test**

Add to a new `test/test_witnesses.ml` a test that checks a small polymorphic module through `check_module_full` and asserts a scheme + instantiation were recorded. (Building an `Ast.module_` by hand is verbose; instead parse a source string with the existing parser, matching how other typecheck tests bootstrap — search `test/` for a helper that parses+checks a source string, e.g. `Test_helpers` or `Parse.module_`. If a `parse_string`-style helper exists, reuse it; otherwise use `March_parser.Parser.module_` + lexer as `bin/main.ml` does.)

```ocaml
module T = March_typecheck.Typecheck

(* Parse a source string into an Ast.module_ the same way bin/main.ml does. *)
let parse_module (src : string) : March_ast.Ast.module_ =
  let lexbuf = Lexing.from_string src in
  March_parser.Parser.module_
    (March_parser.Token_filter.make March_lexer.Lexer.token) lexbuf

let test_scheme_and_instantiation_recorded () =
  (* `id` is generalized (a scheme), used at two types -> two instantiations. *)
  let m = parse_module
    "module M\n\
     let id = fn x -> x\n\
     let a = id(1)\n\
     let b = id(true)\n" in
  let (_errors, _type_map, env) = T.check_module_full m in
  Alcotest.(check bool) "at least one scheme recorded"
    true (Hashtbl.length env.T.scheme_witnesses >= 1);
  Alcotest.(check bool) "at least two instantiations recorded"
    true (Hashtbl.length env.T.inst_witnesses >= 2)

let () =
  Alcotest.run "witnesses"
    [ ("recording",
       [ Alcotest.test_case "scheme+inst" `Quick test_scheme_and_instantiation_recorded ]) ]
```

Register in `test/dune`:

```lisp
(test
 (name test_witnesses)
 (modules test_witnesses)
 (libraries march_typecheck march_ast march_parser march_lexer alcotest))
```

(Adjust library names to the actual parser/lexer library names — grep `test/dune` for how existing typecheck tests list them.)

- [ ] **Step 2: Run the test to verify it fails**

Run: `dune build --root . @test/test_witnesses 2>&1 | head -30`
Expected: FAIL — `Unbound record field scheme_witnesses`.

- [ ] **Step 3a: Add the two `env` fields**

Find the `env` record (`grep -n 'type env = {' lib/typecheck/typecheck.ml`). Add two fields:

```ocaml
  scheme_witnesses : (int list, constraint_ list * ty) Hashtbl.t;
  inst_witnesses   : (Ast.span, int list * ty list) Hashtbl.t;
```

Find `make_env` (the env constructor; `grep -n 'let make_env' lib/typecheck/typecheck.ml`) and initialize them alongside the existing `type_map` init:

```ocaml
  scheme_witnesses = Hashtbl.create 64;
  inst_witnesses   = Hashtbl.create 256;
```

(If `env` is constructed in more than one place — e.g. a `seed_env` path — initialize there too, or share via a helper. Grep for every `{ ... type_map = ...` record literal and add the two fields.)

- [ ] **Step 3b: Thread `?use_span` into `instantiate` and record witnesses**

Change `instantiate`'s signature from `let instantiate level env = function` to `let instantiate ?use_span level env = function`. In the `Poly (ids, cs, ty)` branch, after `subst` is built and `inst` is defined, record both witnesses. Insert immediately before the branch returns its instantiated type:

```ocaml
    (* A1 witnesses: record the scheme (deduped by ids) and, if this call
       site supplied a span, the instantiation's type-argument vector. The
       fresh vars in `subst` are ordinary unification vars; they resolve
       through repr after the module solves, so store them as-is and let the
       emitter deep-repr them at serialization time. *)
    Hashtbl.replace env.scheme_witnesses ids (cs, ty);
    (match use_span with
     | Some sp -> Hashtbl.replace env.inst_witnesses sp (ids, List.map snd subst)
     | None -> ());
```

Then update the `EVar` and `EField` inference call sites to pass the span. Find them: `grep -n 'instantiate ' lib/typecheck/typecheck.ml`. At the `EVar` site the variable's span is `name.span` (the same key `type_map`/`record_use` use); at `EField` use the field-access node's span. Change e.g. `instantiate env.level sch` to `instantiate ~use_span:name.span env.level sch`. Leave the interface/impl-checking `instantiate` sites (out-of-fragment) without a `use_span` — they simply won't record an instantiation, which is fine.

- [ ] **Step 4: Run the test to verify it passes**

Run: `dune build --root . @test/test_witnesses 2>&1 | tail -20`
Expected: PASS.

Then confirm no regression to the full suite:

Run: `dune build --root . @all 2>&1 | tail -5` — Expected: exit 0 (clean build; the new fields don't disturb existing record construction if every literal was updated).

- [ ] **Step 5: Commit**

```bash
git add lib/typecheck/typecheck.ml test/test_witnesses.ml test/dune
git commit -m "feat(typecheck): record HM scheme+instantiation witnesses (A1 Task 2)"
```

---

## Task 3: Emit `resolved_ty` per node

**Files:**
- Modify: `lib/dump/ast_json.ml` (thread `type_map` through `module_to_json` and the recursive node encoders; emit `resolved_ty`)

**Interfaces:**
- Consumes: `resolved_ty_to_json` (Task 1).
- Produces: `Ast_json.module_to_json : types:(Ast.span, March_typecheck.Typecheck.ty) Hashtbl.t -> Ast.module_ -> string` (was `module_to_json : Ast.module_ -> string`). Every expression node object gains `"resolved_ty": <ty>|null`. Consumed by Task 4 (`bin/main.ml`).

- [ ] **Step 1: Write the failing test**

Add to `test/test_emit_core_ast.ml` intent is covered by the golden test in Task 5; for a focused unit here, add to `test/test_ty_json.ml` a test that `module_to_json ~types` emits a `resolved_ty` key. Simplest: assert the substring appears for a trivial module. Append to `test/test_ty_json.ml`:

```ocaml
let test_module_emits_resolved_ty () =
  let m =
    let lexbuf = Lexing.from_string "module M\nlet a = 1\n" in
    March_parser.Parser.module_
      (March_parser.Token_filter.make March_lexer.Lexer.token) lexbuf
  in
  let (_e, type_map, _env) = March_typecheck.Typecheck.check_module_full m in
  let json = J.module_to_json ~types:type_map m in
  Alcotest.(check bool) "module JSON mentions resolved_ty"
    true (Astring_contains json "resolved_ty")
```

where `Astring_contains` is a tiny local helper (add at the top of the file, no new dep):

```ocaml
let astring_contains hay needle =
  let hl = String.length hay and nl = String.length needle in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i+1)) in
  nl = 0 || go 0
```

(rename the call to `astring_contains`.) Add the case to the runner list and add `march_parser march_lexer` to `test_ty_json`'s libraries in `test/dune`.

- [ ] **Step 2: Run the test to verify it fails**

Run: `dune build --root . @test/test_ty_json 2>&1 | head -30`
Expected: FAIL — either `module_to_json` doesn't take `~types` (arity error) or the output lacks `resolved_ty`.

- [ ] **Step 3: Thread `type_map` and emit `resolved_ty`**

In `lib/dump/ast_json.ml`: `module_to_json` currently walks `decl_to_json`/`expr_to_json`. Change the signature to take `~types` and thread it down. The mechanical change: add a labeled `~types` parameter to `module_to_json`, `decl_to_json`, `expr_to_json`, `pattern_to_json` (and any helper that emits an expr/param/binding). In `expr_to_json`, at the point each node's object field-list is built, append a `resolved_ty` entry computed from the node's span:

```ocaml
let resolved_ty_field ~types (sp : Ast.span) : string * string =
  match Hashtbl.find_opt types sp with
  | Some t -> ("resolved_ty", resolved_ty_to_json t)
  | None -> ("resolved_ty", "null")
```

For each expr constructor, obtain its span the same way the typechecker keys `type_map` — via `span_of_expr` if `march_ast` exposes it, otherwise the span already destructured in each arm (most arms bind a trailing `span`; `EVar`/`ECon` use `name.span`). Append `resolved_ty_field ~types sp` to that arm's `Dump.json_obj` list. Keep it last so existing keys are unchanged in position.

To minimize churn: if threading `~types` through every function is too invasive, use a file-local `let current_types : (Ast.span, T.ty) Hashtbl.t option ref = ref None` set at the top of `module_to_json` and read by `resolved_ty_field`. This is acceptable here (single-threaded CLI, one module per invocation). Prefer the explicit `~types` thread if the arm count is small; use the ref if it sprawls. Either way the *output contract* is identical.

Update `module_to_json`'s own signature and body to accept `~types`.

- [ ] **Step 4: Run the test to verify it passes**

Run: `dune build --root . @test/test_ty_json 2>&1 | tail -20`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/dump/ast_json.ml test/test_ty_json.ml test/dune
git commit -m "feat(dump): annotate emitted AST nodes with resolved_ty (A1 Task 3)"
```

---

## Task 4: Assemble the `format_version` 2 envelope

**Files:**
- Modify: `bin/main.ml` (the `--emit-core-ast` emit branch + the parse-failure short-circuit)

**Interfaces:**
- Consumes: `Ast_json.module_to_json ~types` (Task 3); `env.scheme_witnesses` / `env.inst_witnesses` (Task 2); `Ast_json.resolved_ty_to_json` / `constraint_to_json` (Task 1).
- Produces: the on-the-wire `format_version` 2 document (the contract the march-lean checker decodes).

- [ ] **Step 1: Write the failing test (manual, via the binary)**

This task's behavior is a whole-program output; verify by building and piping. First establish the *current* (v1) output to confirm the starting point:

Run: `cd /Users/80197052/code/march && eval $(opam env --switch=march) && dune build --root . bin/main.exe && echo 'module M
let a = 1' > /tmp/a1_smoke.march && ./_build/default/bin/main.exe --emit-core-ast /tmp/a1_smoke.march | python3 -m json.tool | head -5`
Expected (before change): shows `"format_version": 1`.

- [ ] **Step 2: Serialize the two witness tables + bump version**

In `bin/main.ml`, find the emit branch (`grep -n 'emit_core_ast_file <> None' bin/main.ml` — the one after `check_module_full`, currently building the v1 doc with `("format_version","1")` and `module_to_json user_ast`). Replace the module/version lines and add the two tables. `typecheck_env` is already bound at `let (errors, type_map, typecheck_env) = ... check_module_full desugared`:

```ocaml
    let module_json = March_dump.Ast_json.module_to_json ~types:type_map user_ast in
    let schemes_json =
      Hashtbl.fold
        (fun ids (cs, ty) acc ->
          March_dump.Dump.json_obj
            [ ("ids", March_dump.Dump.json_list (List.map string_of_int ids));
              ("constraints",
               March_dump.Dump.json_list (List.map March_dump.Ast_json.constraint_to_json cs));
              ("body", March_dump.Ast_json.resolved_ty_to_json ty) ]
          :: acc)
        typecheck_env.March_typecheck.Typecheck.scheme_witnesses []
    in
    let insts_json =
      Hashtbl.fold
        (fun (sp : March_ast.Ast.span) (ids, args) acc ->
          March_dump.Dump.json_obj
            [ ("use_span", March_dump.Ast_json.span_to_json sp);
              ("ids", March_dump.Dump.json_list (List.map string_of_int ids));
              ("args",
               March_dump.Dump.json_list (List.map March_dump.Ast_json.resolved_ty_to_json args)) ]
          :: acc)
        typecheck_env.March_typecheck.Typecheck.inst_witnesses []
    in
    let doc =
      March_dump.Dump.json_obj
        [ ("format_version", "2");
          ("verdict", March_dump.Dump.json_string verdict);
          ("diagnostics", diagnostics_json);
          ("module", module_json);
          ("schemes", March_dump.Dump.json_list schemes_json);
          ("instantiations", March_dump.Dump.json_list insts_json) ]
    in
    print_string doc;
    exit (if verdict = "accept" then 0 else 1)
```

Notes:
- Reuse the existing `verdict` and `diagnostics_json` bindings already in that branch (do not recompute the verdict).
- `span_to_json` must exist in `ast_json.ml`; the A0 code already emits spans on nodes, so a `span_to_json : Ast.span -> string` helper either exists (reuse it — grep `ast_json.ml` for how it renders a span) or extract the span-emitting code into one and call it here and from the node encoders. If A0 inlined span emission, add `let span_to_json (s : Ast.span) : string = ...` matching that exact shape and reuse it.

- [ ] **Step 3: Update the parse-failure short-circuit to v2**

Find `emit_core_ast_parse_failure` (`grep -n emit_core_ast_parse_failure bin/main.ml`). Bump its `("format_version","1")` to `"2"` and add empty witness tables so the envelope shape is uniform:

```ocaml
      let doc =
        March_dump.Dump.json_obj [
          ("format_version", "2");
          ("verdict", March_dump.Dump.json_string "reject");
          ("diagnostics",
           March_dump.Dump.json_list [March_errors.Errors.render_diagnostic_json diag]);
          ("module", "null");
          ("schemes", "[]");
          ("instantiations", "[]");
        ]
      in
```

- [ ] **Step 4: Verify the new output**

Run: `dune build --root . bin/main.exe && ./_build/default/bin/main.exe --emit-core-ast /tmp/a1_smoke.march | python3 -m json.tool | head -8`
Expected: `"format_version": 2`, and top-level `schemes` / `instantiations` keys present. Then a polymorphic check:

Run: `printf 'module M\nlet id = fn x -> x\nlet a = id(1)\n' > /tmp/a1_poly.march && ./_build/default/bin/main.exe --emit-core-ast /tmp/a1_poly.march | python3 -c 'import sys,json; d=json.load(sys.stdin); print("schemes",len(d["schemes"]),"insts",len(d["instantiations"]))'`
Expected: `schemes 1 insts 1` (or more). Confirm exit code: `echo $?` after an accept → `0`.

- [ ] **Step 5: Commit**

```bash
git add bin/main.ml lib/dump/ast_json.ml
git commit -m "feat(cli): emit format_version 2 envelope with witnesses (A1 Task 4)"
```

---

## Task 5: Regenerate golden fixtures for v2

**Files:**
- Modify: `test/emit_core_ast/fixtures/{t01_literals,t07_generic_option_two_types,t01_int_vs_string,t70_letq_type_annotation}.expected.json` (regenerate)
- Modify: `test/test_emit_core_ast.ml` (assert v2 fields)

**Interfaces:**
- Consumes: the built `bin/main.exe` v2 output.

- [ ] **Step 1: Confirm the golden test currently fails against v2**

Run: `dune build --root . @test/test_emit_core_ast 2>&1 | tail -30`
Expected: FAIL — the checked-in fixtures are v1 (`"format_version":1`, no `resolved_ty`/witnesses) but the binary now emits v2. This is the expected churn.

- [ ] **Step 2: Regenerate each fixture**

The fixtures must be generated with the corpus path **relative to the project root** and cwd = project root (so `span.file` stays portable — this is why the A0 fixtures are portable; preserve it). For each of the four, run from the march root:

```bash
cd /Users/80197052/code/march
for f in \
  "specs/lang/types/accept/t01_literals.march:t01_literals" \
  "specs/lang/types/accept/t07_generic_option_two_types.march:t07_generic_option_two_types" \
  "specs/lang/types/reject/t01_int_vs_string.march:t01_int_vs_string" \
  "specs/lang/types/reject/t70_letq_type_annotation.march:t70_letq_type_annotation" ; do
  src="${f%%:*}"; name="${f##*:}"
  ./_build/default/bin/main.exe --emit-core-ast "$src" > "test/emit_core_ast/fixtures/${name}.expected.json"
done
```

Then eyeball one to confirm it's v2 and well-formed:

Run: `python3 -m json.tool test/emit_core_ast/fixtures/t01_literals.expected.json | head -6`
Expected: `"format_version": 2` and a `resolved_ty` visible under `module`.

- [ ] **Step 3: Extend the golden test to assert v2 fields**

In `test/test_emit_core_ast.ml`, the existing test does a byte-for-byte compare against each fixture (that already re-pins everything). Add one lightweight structural assertion so a future accidental downgrade is caught explicitly — after the byte comparison for the `t01_literals` accept case, assert the produced output contains `"format_version":2` and `"resolved_ty"` and `"schemes"`. If the test's helper only exposes the compared string, add:

```ocaml
(* v2 sanity: the envelope must be version 2 and carry annotations+witnesses. *)
let assert_v2 (produced : string) =
  let has s =
    let hl = String.length produced and nl = String.length s in
    let rec go i = i + nl <= hl && (String.sub produced i nl = s || go (i+1)) in
    nl = 0 || go 0
  in
  Alcotest.(check bool) "format_version 2" true (has "\"format_version\":2" || has "\"format_version\": 2");
  Alcotest.(check bool) "has resolved_ty" true (has "resolved_ty");
  Alcotest.(check bool) "has schemes" true (has "schemes")
```

and call `assert_v2` on the produced output of at least the first accept case (wire it wherever the test already holds the produced string).

- [ ] **Step 4: Run the golden test to verify it passes**

Run: `dune build --root . @test/test_emit_core_ast 2>&1 | tail -20`
Expected: PASS (4/4 cases). Then full suite:

Run: `dune build --root . @runtest 2>&1 | tail -5`
Expected: exit 0, no regressions.

- [ ] **Step 5: Commit**

```bash
git add test/emit_core_ast/fixtures test/test_emit_core_ast.ml
git commit -m "test(emit-core-ast): regenerate golden fixtures for format_version 2 (A1 Task 5)"
```

---

## Done criteria (march side)

- `dune build --root . @runtest` is green.
- `--emit-core-ast` emits `format_version` 2 with per-node `resolved_ty`, a `schemes` table (each with `ids`/`constraints`/`body`), and an `instantiations` table (each with `use_span`/`ids`/`args`); a polymorphic program produces ≥1 of each.
- Exit codes unchanged (accept→0, reject→1); parse-failure still emits one valid v2 document with `"module":null`.
- After merge, the march-lean checker plan repins its CI to a `main` SHA containing this work.
