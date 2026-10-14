"""
nonrep_safe_measure_v1  --  exact measure of the safe set of the FIVE base runners
for NON-representative speeds e_rho = 8 q_rho + rho.

S(e_1,e_3,e_5,e_7,e_rho0) = { x in [0,1) : union_rho bad(rho, floor(e_rho x)) != Z/8 }

Breakpoints of floor(e x) are at j/e, so S is a finite union of half-open rational
intervals.  Exact Fraction arithmetic; every decision is an exact comparison.
"""
from fractions import Fraction as F
import itertools, sys

FULL = frozenset(range(8))
BAD = {(rho, t): frozenset(r for r in range(8) if (rho * r + t) % 8 in (0, 7))
       for rho in range(1, 8) for t in range(8)}

def safe_measure(speeds, rhos, want_windows=False):
    pts = {F(0), F(1)}
    for e in speeds:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts)
    meas = F(0); wins = []
    for a, b in zip(p, p[1:]):
        mid = (a + b) / 2
        cov = set()
        for e, rho in zip(speeds, rhos):
            t = (e * mid.numerator) // (mid.denominator)   # floor(e*mid), exact int
            cov |= BAD[(rho, t % 8)]
        if cov != FULL:
            meas += b - a
            if want_windows:
                if wins and wins[-1][1] == a: wins[-1][1] = b
                else: wins.append([a, b])
    return (meas, wins) if want_windows else meas

if __name__ == "__main__":
    RHOS = (1, 3, 5, 7)
    QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for rho0 in (2, 4, 6):
        rhos = RHOS + (rho0,)
        rows = []
        for qs in itertools.product(range(QMAX + 1), repeat=5):
            speeds = tuple(8 * q + r for q, r in zip(qs, rhos))
            if len(set(speeds)) != 5:      # distinctness
                continue
            m = safe_measure(speeds, rhos)
            rows.append((m, speeds))
        rows.sort()
        print(f"=== rho0 = {rho0} :  {len(rows)} tuples with q in [0,{QMAX}] ===")
        print(f"  representative (q=0): |S| = {safe_measure(rhos, rhos)}")
        print(f"  MINIMUM |S| over the sweep = {rows[0][0]} = {float(rows[0][0]):.6f}"
              f"  at speeds {rows[0][1]}")
        print(f"  10 smallest:")
        for m, s in rows[:10]:
            flag = "  <= 1/2" if m <= F(1, 2) else ""
            print(f"      {str(m):>18} = {float(m):.6f}   {s}{flag}")
        n_le_half = sum(1 for m, s in rows if m <= F(1, 2))
        print(f"  tuples with |S| <= 1/2 : {n_le_half} of {len(rows)}")
        print(f"  MAXIMUM |S| = {rows[-1][0]} = {float(rows[-1][0]):.6f} at {rows[-1][1]}")
        print()
