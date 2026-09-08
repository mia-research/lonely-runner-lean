r"""
du2_nonrep_v1 -- n=8 DROPPED-UNIT leaf WITHOUT representativeness.

E_non = { e_rho = 8*q_rho + rho : rho in R_non }, one speed per present class,
q_rho >= 0 arbitrary (q = 0 for all rho is the representative case).
|E_div| = 2 still.  Question: does |S| > 1/2 survive?

Exact cell decomposition with boundary-exact floors (entry and exit, never a centre).
Reports the exact minimum of |S| over the sweep and every instance with |S| <= 1/2.
"""
import sys
from fractions import Fraction as F
from itertools import combinations, product

Z8 = frozenset(range(8))
UNITS = frozenset({1, 3, 5, 7})
BAD = {(e, t): frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))
       for e in range(8) for t in range(8)}


def safe_measure(Enon, want_windows=False, audit=False):
    pts = {F(0), F(1)}
    for e in Enon:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts)
    m = F(0)
    wins = []
    n_int = n_mis = n_sd = 0
    for a, b in zip(p, p[1:]):
        cov_in = set()
        cov_out = set()
        for e in Enon:
            va = e * a
            fe = va.numerator // va.denominator
            cov_in |= BAD[(e % 8, fe % 8)]
            if audit:
                k0 = fe + 1
                if F(k0, e) < b:
                    n_int += 1
                vb = e * b
                fx = vb.numerator // vb.denominator - (1 if vb.denominator == 1 else 0)
                if fe != fx:
                    n_mis += 1
                cov_out |= BAD[(e % 8, fx % 8)]
        if audit and cov_in != cov_out:
            n_sd += 1
        U = Z8 - cov_in
        if U:
            m += b - a
            if want_windows:
                wins.append((a, b, frozenset(U)))
    return m, wins, (n_int, n_mis, n_sd)


def main(Q):
    pairs = [A for A in combinations(range(1, 8), 2) if set(A) & UNITS]
    qs = list(range(Q + 1))
    best = None
    below = []
    tot = 0
    audit_tot = [0, 0, 0]
    per_pair_min = {}
    for A in pairs:
        R = sorted(set(range(1, 8)) - set(A))
        pmin = None
        for qv in product(qs, repeat=5):
            Enon = [8 * q + r for q, r in zip(qv, R)]
            if len(set(Enon)) < 5:
                continue
            tot += 1
            do_audit = (tot % 37 == 0)          # audit a sample exhaustively
            m, _, au = safe_measure(Enon, audit=do_audit)
            for i in range(3):
                audit_tot[i] += au[i]
            if pmin is None or m < pmin[0]:
                pmin = (m, tuple(Enon))
            if best is None or m < best[0]:
                best = (m, tuple(Enon), A)
            if m < F(1, 2):
                below.append((m, tuple(Enon), A))
        per_pair_min[A] = pmin
    print(f"sweep: q_rho in 0..{Q} for each of the 5 present classes; "
          f"{tot} admissible E_non")
    print(f"boundary audit on the sampled subset: interior={audit_tot[0]} "
          f"mismatch={audit_tot[1]} entry/exit-setdiff={audit_tot[2]}")
    print(f"\nglobal minimum |S| = {best[0]} = {float(best[0]):.6f}  at E_non = {list(best[1])}"
          f"  (absent {best[2]})")
    print(f"instances with |S| < 1/2 : {len(below)}")
    for m, E, A in sorted(below)[:40]:
        print(f"    |S| = {m} = {float(m):.6f}   E_non = {list(E)}   absent {A}")
    print("\nper-absent-pair minimum over the sweep:")
    for A in pairs:
        m, E = per_pair_min[A]
        print(f"   absent {str(A):>7}  min |S| = {str(m):>12} = {float(m):.6f}  at {list(E)}"
              f"   > 1/2 ? {m > F(1,2)}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
