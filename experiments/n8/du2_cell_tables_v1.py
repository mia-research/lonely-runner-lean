r"""du2_cell_tables_v1 -- the full per-cell certificate for all 18 absent pairs.

For every cell [a,b) of the breakpoint decomposition of E_non, prints
  - the entry floors t_e = floor(e*a)  (equal to the exit floors, audited),
  - the union of bad(e,t_e) over E_non,
  - the uncovered set U = Z/8 minus that union   (requirement (ii): ALL of it).
A cell is safe iff U is non-empty.  Exact rationals; no midpoint is evaluated.
"""
from fractions import Fraction as F
from itertools import combinations
Z8 = frozenset(range(8)); UNITS = {1, 3, 5, 7}


def bad(e, t):
    return frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))


for A in [X for X in combinations(range(1, 8), 2) if set(X) & UNITS]:
    E = sorted(set(range(1, 8)) - set(A))
    pts = {F(0), F(1)}
    for e in E:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts)
    tot = F(0); nsafe = 0
    print(f"\n### absent {A}   E_non = {E}")
    print("| cell | " + " | ".join(f"t_{e}" for e in E) + " | covered | U | safe | length |")
    print("|---|" + "---|" * len(E) + "---|---|---|---|")
    for a, b in zip(p, p[1:]):
        ts = []
        cov = set()
        for e in E:
            v = e * a
            t = v.numerator // v.denominator
            vb = e * b
            tx = vb.numerator // vb.denominator - (1 if vb.denominator == 1 else 0)
            assert t == tx, (A, a, b, e, t, tx)
            k0 = t + 1
            assert not (F(k0, e) < b), ("interior breakpoint", A, a, b, e)
            ts.append(t)
            cov |= bad(e, t)
        U = Z8 - cov
        if U:
            tot += b - a; nsafe += 1
        print(f"| `[{a},{b})` | " + " | ".join(str(t) for t in ts) +
              f" | {sorted(cov)} | {sorted(U) if U else '-'} | "
              f"{'YES' if U else 'no'} | `{b-a}` |")
    print(f"\n**{nsafe} of {len(p)-1} cells safe; |S| = {tot} = {float(tot):.6f} "
          f"> 1/2; surplus {tot - F(1,2)}.**")
