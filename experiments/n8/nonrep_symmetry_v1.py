"""
nonrep_symmetry_v1  --  two exact symmetries of the covered set.

(S1) ODD SCALING.  For lambda odd, cov_{lambda*E}(x) = lambda * cov_E(lambda x).
     Hence S(lambda*E) = lambda^{-1} S(E) in R/Z, and |S(lambda E)| = |S(E)|.
(S2) REFLECTION.   cov_E(1-x) = -1 - cov_E(x).  Hence S is symmetric under x -> 1-x.

Proof of (S2) at the level of bad sets, verified here for every (rho,t):
     bad(rho, rho-1-t) = { -1-a : a in bad(rho,t) }.
Exact integer arithmetic.
"""
from fractions import Fraction as F
import itertools
from nonrep_safe_measure_v1 import safe_measure, BAD

FULL = frozenset(range(8))

# (S2) at the bad-set level
ok = True
for rho in range(1, 8):
    for t in range(8):
        lhs = BAD[(rho, (rho - 1 - t) % 8)]
        rhs = frozenset((-1 - a) % 8 for a in BAD[(rho, t)])
        if lhs != rhs:
            ok = False; print("FAIL", rho, t, sorted(lhs), sorted(rhs))
print(f"[S2] bad(rho, rho-1-t) == -1-bad(rho,t) for all 7*8 pairs : {'OK' if ok else 'FAIL'}")

# (S1) at the bad-set level:  bad(lambda*rho, t) == lambda * bad(rho, t)   (lambda odd)
ok = True
for lam in (1, 3, 5, 7):
    for rho in range(1, 8):
        for t in range(8):
            lhs = BAD[((lam * rho) % 8, t)]
            rhs = frozenset((lam * a) % 8 for a in BAD[(rho, t)])
            if lhs != rhs:
                ok = False; print("FAIL", lam, rho, t)
print(f"[S1] bad(lam*rho, t) == lam*bad(rho,t) for all lam odd, rho, t : {'OK' if ok else 'FAIL'}")

# (S1) at the measure level, on concrete tuples
print("\n[S1] measure invariance on concrete tuples (exact Fractions):")
tests = [(1,3,5,7,4), (1,3,5,7,2), (9,11,5,7,4), (1,19,5,7,26), (17,3,21,23,6)]
for sp in tests:
    base_rho = tuple(e % 8 for e in sp)
    m0 = safe_measure(sp, base_rho)
    line = [f"{sp} rho={base_rho} |S|={m0}"]
    for lam in (3, 5, 7):
        sp2 = tuple(lam * e for e in sp)
        rho2 = tuple(e % 8 for e in sp2)
        m2 = safe_measure(sp2, rho2)
        line.append(f"   lam={lam}: {sp2} rho={rho2} |S|={m2} {'EQ' if m2==m0 else 'DIFF'}")
    print("\n".join(line)); print()

# (S2) at the measure level: windows come in reflected pairs
print("[S2] window reflection check:")
for sp in tests:
    rho = tuple(e % 8 for e in sp)
    m, w = safe_measure(sp, rho, want_windows=True)
    wr = sorted([[1 - b, 1 - a] for a, b in w])
    print(f"   {sp}: {len(w)} windows, reflection-closed = {wr == sorted(w)}")
