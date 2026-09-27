"""The exceptions no single move rescues (lattice_exceptions_v1: 209 of 96,650).  Exact.  For each: L0, blockers per
numerator, the cascade's landing (e, K, t*), and whether two readings are = 0 mod 8 (the double collision of E103)."""
import ast
from fractions import Fraction as F
from collections import Counter
from lattice_exceptions_v1 import rows, blockers, L0_of
from lattice_vs_cascade_v1 import cascade, landing, clear_js
stuck = []
for (k, T, L0, Ds, e, K) in rows:
    ok = False
    for i, d in enumerate(T):
        for s in (-2, -1, 1, 2):
            d2 = d + s
            if d2 <= 0 or d2 in T: continue
            T2 = tuple(sorted(T[:i] + (d2,) + T[i + 1:]))
            if clear_js(T2, L0_of(T2)): ok = True; break
        if ok: break
    if not ok: stuck.append((T, L0, Ds, e, K))
c = Counter()
for T, L0, Ds, e, K in stuck:
    c[('L0', L0)] += 1
    c[('multiples of 8L0', sum(1 for d in T if d % (8 * L0) == 0 or d % (8 * L0) == 8 * L0 // 2 and False))] += 1
    c[('d_min', T[0])] += 1
    c[('multiples of 8', sum(1 for d in T if d % 8 == 0))] += 1
print("not rescued by one move:", len(stuck))
for k_, v in sorted(c.items(), key=str): print(" ", k_, v)
print("examples (readings, L0, D*, cascade e, K, t*):")
for T, L0, Ds, e, K in stuck[:30]: print("  ", T, L0, Ds, e, K, F(8 * K + 1, 8 * e))
