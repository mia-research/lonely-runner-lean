#!/usr/bin/env python3
"""Map every check_no_float hit to its enclosing function, and mark whether that
function is one PREREG_incomplete_shortscalar_v2 actually reuses (= signal path).

check_no_float.py is a blunt AST scan: it cannot tell `Fraction / int` (exact)
from `float / int` (lossy), and it flags display/reporting code equally.  A hit
is therefore a REVIEW FLAG, not a violation.  This resolves each one.
"""

import ast
import re
import sys

# functions v2's tooling inventory names as reused -> these are SIGNAL PATH
REUSED = {
    "eisenstein_lift_sextant_exact_v1.py": {"eis", "sextant", "N", "enorm"},
    "lift_sextant_rhombus_law_proof_v2.py": {"reduced_basis", "rdiv", "enorm"},
    "flap_density_glv_prereg_v1.py": {"mul_jac", "eps"},
    "ct_event_complete_v1.py": {"state", "state_vec", "Lift"},
    "glv_fundamental_domain_law_v1.py": {"om", "om2", "reduce_P"},
    "lift_sextant_law_proof_v1.py": set(),
    "norm_band_law_proof_v1.py": set(),
    "tdev_ceiling_exact_v1.py": set(),
}


def enclosing_defs(path):
    """line number -> (qualified function name) for every line in the file."""
    src = open(path).read()
    tree = ast.parse(src)
    owner = {}

    def walk(node, prefix=""):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                name = prefix + child.name
                lo = child.lineno
                hi = max(getattr(d, "lineno", lo)
                         for d in ast.walk(child)
                         if hasattr(d, "lineno"))
                for ln in range(lo, hi + 1):
                    owner[ln] = name
                walk(child, name + ".")
            else:
                walk(child, prefix)

    walk(tree)
    return owner


def main(logfile):
    cur = None
    results = {}
    owners = {}
    for line in open(logfile):
        m = re.match(r"FLOAT-RISK in (\S+):", line)
        if m:
            cur = m.group(1)
            results[cur] = []
            owners[cur] = enclosing_defs(cur)
            continue
        m = re.match(r"OK: (\S+)", line)
        if m:
            results[m.group(1)] = []
            continue
        m = re.match(r"\s+line (\d+): (.+)", line)
        if m and cur:
            results[cur].append((int(m.group(1)), m.group(2).strip()))

    print(f"{'file':<42} {'hits':>5}  {'in reused fn':>13}  verdict")
    print("-" * 92)
    total_sig = 0
    for f, hits in results.items():
        reused = REUSED.get(f, set())
        own = owners.get(f, {})
        sig = []
        for ln, what in hits:
            fn = own.get(ln, "<module>")
            base = fn.split(".")[0]
            if base in reused or fn in reused:
                sig.append((ln, what, fn))
        total_sig += len(sig)
        verdict = "CLEAN" if not hits else (
            f"REVIEW ({len(sig)} in signal path)" if sig
            else "hits are OUTSIDE reused fns")
        print(f"{f:<42} {len(hits):>5}  {len(sig):>13}  {verdict}")
        for ln, what, fn in sig:
            print(f"      -> line {ln} in {fn}(): {what}")

    print("-" * 92)
    print(f"TOTAL hits inside functions the spec reuses: {total_sig}")
    return 0 if total_sig == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1
                  else "CAL_check_no_float_v1.log"))
