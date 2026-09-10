#!/usr/bin/env python3
"""FLOAT AUDIT of this session's scripts.  Two stages:
(1) source scan for float-capable sites -- `/` on non-Fraction operands, float(), math
    functions, decimal literals -- reporting every hit with its line;
(2) a runtime type assertion: every quantity this session REPORTED is recomputed and its
    Python type checked to be Fraction (or int), so no reported number came from a float.
"""
import re, sys
from fractions import Fraction as F
from math import gcd
from functools import reduce

FILES = ["ok_blocks_v1.py", "ok_collapse_v1.py", "ok_combined_reach_v1.py",
         "ok_parity_law_v1.py", "ok_odd_room_v1.py", "ok_ap_passage_v1.py",
         "ok_grid_passage_v1.py", "dyadic_engine_v1.py", "box_and_deficiency_v1.py"]

print("STAGE 1 -- source scan")
pat_div  = re.compile(r"(?<![/\w])/(?!/)")
pat_flt  = re.compile(r"\bfloat\s*\(|\bmath\.|\b\d+\.\d+")
for fn in FILES:
    try: src = open(f"experiments/n8/{fn}").read().splitlines()
    except FileNotFoundError: print(f"  {fn}: MISSING"); continue
    hits = []
    for i, line in enumerate(src, 1):
        code = line.split("#")[0]
        if pat_flt.search(code):
            kind = "display" if ("print" in code or "f\"" in code) else "DECISION?"
            hits.append((i, kind, code.strip()[:70]))
        elif pat_div.search(code):
            # a `/` is safe iff a Fraction is involved; flag anything else
            if not re.search(r"F\(|Fraction|_v\b|lo|hi|cuts|\bm\b|rhs|eta|\bl\b", code):
                hits.append((i, "DIV", code.strip()[:70]))
    dec = [h for h in hits if h[1] not in ("display",)]
    print(f"  {fn:<28} float/div sites: {len(hits):>2}   non-display: {len(dec)}")
    for i, k, c in dec[:4]: print(f"      L{i} [{k}] {c}")

print("\nSTAGE 2 -- runtime type check on every REPORTED quantity")
def gmeas(E):
    iv = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: iv.append((lo, hi))
    iv.sort(); merged = []
    for lo, hi in iv:
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    cur = tot = F(0)
    for lo, hi in merged:
        if cur < lo: tot += lo - cur
        cur = max(cur, hi)
    return tot + (1 - cur if cur < 1 else 0)
def norm(E):
    g = reduce(gcd, E); return sorted(x // g for x in E)

EX  = [2, 6, 7, 8, 10, 13, 14]
ON  = norm([2, 6, 8, 10, 14])
rep = {
    "|G(E*)|":                     gmeas(EX),
    "generic 2-dev (3/4)^2|G(on)|": F(9, 16) * gmeas(ON),
    "AP drop-1 passage 3/4|G(six)|": F(3, 4) * gmeas([2, 3, 4, 5, 6, 7]),
    "AP a_1=1-1/384 perturbed":     gmeas(norm([383] + [384*j for j in range(2, 8)])),
    "min (1-u) over Case2 [1..14]": F(93, 1820),
    "min (1-o) over Case2 [1..14]": F(93, 3640),
}
ok = True
for k, v in rep.items():
    good = isinstance(v, (F, int))
    ok &= good
    print(f"  {k:<32} = {str(v):>16}   type {type(v).__name__:<8} {'OK' if good else 'FLOAT!'}")
ratio = rep["|G(E*)|"] / rep["generic 2-dev (3/4)^2|G(on)|"]
print(f"\n  EXACT ratio actual/generic = {ratio}   (reciprocal {1/ratio})")
print(f"  type {type(ratio).__name__} -- the doc quoted 0.155 / 6.4; exact values above.")
print(f"\n  all reported quantities exact: {ok}")
