#!/usr/bin/env python3
"""Focused main-sync regressions; verdict mutations test oracle independence."""
import argparse
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--march-bin', required=True)
parser.add_argument('--march-lean-check-bin', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent / 'sync-probes'
# (March --check exit, independent checker exit). Skip is explicit, never success.
cases = {
    'let_annotation_bad': (1, 1),
    'let_annotation_ok': (0, 2),  # global value capability reach not yet modeled
    'linear_move_drop': (1, 1),
    'linear_move_use': (0, 0),
    'grant_missing': (1, 1),
    'grant_narrow': (1, 1),
    'grant_covered': (0, 0),
    'builtin_shadow': (0, 0),
    'needs_missing': (1, 1),
    'scoped_need': (0, 0),
    'local_cap_annotation': (0, 0),
    'affine_move': (0, 0),
    'console_shadow': (1, 2),  # March retains an injected console effect row
    'closure_no_grant': (1, 1),
    'closure_granted': (0, 0),
    'unreachable_effect': (0, 0),
    'grant_chain': (1, 1),
    'scope_inside': (0, 0),
    'scope_near_prefix': (1, 1),
    'scope_traversal_inside': (0, 0),
    'scope_traversal_escape': (1, 1),
    'scope_relative_use': (1, 1),
    'scope_union': (0, 0),
    'scope_unbounded': (0, 0),
    'scope_parent': (1, 1),
    'scope_root': (0, 0),
    'scope_computed': (0, 0),
    'scope_nested_outer': (0, 0),
    'scope_nested_inner': (1, 1),
    'scope_invalid_cap': (1, 1),
    'scope_relative_decl': (1, 1),

}
failures = []
for name, (march_exit, lean_exit) in cases.items():
    source = root / f'{name}.march'
    checked = subprocess.run([args.march_bin, '--check', str(source)], capture_output=True, timeout=120)
    emitted = subprocess.run([args.march_bin, '--emit-core-ast', str(source)], capture_output=True, timeout=120)
    envelope = json.loads(emitted.stdout)
    actual = subprocess.run([args.march_lean_check_bin], input=emitted.stdout, capture_output=True, timeout=30)
    # Changing the compiler's answer and removing its diagnostics must leave ours unchanged.
    envelope['verdict'] = 'reject' if envelope['verdict'] == 'accept' else 'accept'
    envelope['diagnostics'] = []
    flipped = subprocess.run([args.march_lean_check_bin], input=json.dumps(envelope).encode(), capture_output=True, timeout=30)
    ok = (
        checked.returncode == march_exit
        and actual.returncode == lean_exit
        and flipped.returncode == lean_exit
    )
    if name == 'grant_chain':
        ok = ok and 'call path: main → first → second → third' in actual.stderr.decode()
    print(f'{name}: march={checked.returncode} lean={actual.returncode} flipped={flipped.returncode} {"ok" if ok else "FAIL"}', flush=True)
    if not ok:
        failures.append(name)
        print(checked.stderr.decode(), actual.stderr.decode(), flipped.stderr.decode())
if failures:
    raise SystemExit(f'Failed: {", ".join(failures)}')
print(f'{len(cases)} sync probes passed (including verdict-independence mutations).')
