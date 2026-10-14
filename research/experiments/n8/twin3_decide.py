"""twin3_decide.py -- the deterministic case machine.

For a chosen sub-window W = [alpha,beta) with a residue set V that is uncovered by
the five base runners throughout W, and a twin residue rho' with J = J(rho',V),
we must exhibit x in W with x not in A(c,J) and x not in B_m,  c = e' = 8q'+rho'.

LEMMA A (gap lemma).  If  ell >= 15/c  and  ell >= 7/(4m)  then W is not covered.
LEMMA B (small c).    mu(c) = longest component of W \\ A(c,J).  If 4*m*mu(c) > 1, done.
LEMMA C (small m).    lam(m) = longest component of W \\ B_m.  If c*lam(m) > kappa, done.

Whatever survives all three is enumerated and checked directly.
"""
from fractions import Fraction as F
from twin3_core import A_intervals, B_intervals, subtract, merge, total, J_set, bad
from twin3_window import safe_measure

def longest(iv):
    return max((b-a for a,b in iv), default=F(0))

def decide(rho0, rho2, alpha, beta, V, cmax_check=4000, mmax_check=4000, verbose=True):
    ell = beta - alpha
    J = J_set(rho2, V)
    kap = len(J)
    W = [(alpha,beta)]
    C1 = -(-15*ell.denominator // (15*0 + ell.numerator)) if False else None
    # smallest integer c with ell >= 15/c  <=>  c >= 15/ell
    from math import ceil
    C1 = ceil(F(15)/ell)          # c >= C1  satisfies Lemma A's first hypothesis
    M1 = ceil(F(7,4)/ell)         # m >= M1  satisfies Lemma A's second hypothesis
    if kap == 0:
        M0 = ceil(F(1,4)/ell)     # W subset B_m forces ell <= 1/(4m) i.e. m <= 1/(4 ell)
        res = []
        for m in range(1, M0+1):
            surv = subtract(W, B_intervals(m))
            if not surv: res.append(('m',m))
        return dict(ell=ell,J=J,kap=kap,C1=None,M1=None,mode='J-empty',
                    m_bound=M0, residual=res)
    # Lemma B residual: c < C1
    resB = []
    for c in range(rho2 if rho2>=8 else 8+rho2, C1, 8):
        mu = longest(subtract(W, A_intervals(c, J)))
        if mu == 0:
            mstop = None   # W entirely inside A: needs direct check for ALL m -> record
        else:
            mstop = int(F(1,4)/mu)      # done for m > 1/(4 mu); residual m <= floor(1/(4mu))
        resB.append((c, mu, mstop))
    # Lemma C residual: m < M1
    resC = []
    for m in range(1, M1):
        lam = longest(subtract(W, B_intervals(m)))
        if lam == 0:
            cstop = None
        else:
            cstop = int(F(kap)/lam)     # done for c > kappa/lam; residual c <= floor(kappa/lam)
        resC.append((m, lam, cstop))
    # assemble residual (c,m) pairs
    residual = set()
    for c, mu, mstop in resB:
        if mstop is None:
            raise RuntimeError(f"W fully inside A at c={c}: window choice fails")
        for m in range(1, mstop+1):
            residual.add((c,m))
    for m, lam, cstop in resC:
        if cstop is None:
            raise RuntimeError(f"W fully inside B_m at m={m}: window choice fails")
        c = 8 + rho2
        while c <= cstop:
            residual.add((c,m)); c += 8
    # direct check of every residual pair
    fails = []
    for c,m in sorted(residual):
        surv = subtract(W, merge(A_intervals(c,J) + B_intervals(m)))
        if not surv:
            fails.append((c,m))
    return dict(ell=ell, J=sorted(J), kap=kap, C1=C1, M1=M1, mode='gap',
                nresB=len(resB), nresC=len(resC),
                residual_size=len(residual), residual=sorted(residual), fails=fails)

CASES = [
    # (rho0, rho' list, alpha, beta, V, label)
    (2, [1,3,5,7], F(0),   F(1,7), frozenset({2,6}), "A"),
    (2, [2],       F(0),   F(1,5), frozenset({6}),   "B"),
    (4, [1,7,4],   F(2,7), F(2,5), frozenset({1,4}), "C"),
    (4, [3,5],     F(2,7), F(2,5), frozenset({1,4}), "D"),
    (6, [1,3,5,7], F(0),   F(1,7), frozenset({2,6}), "E"),
    (6, [6],       F(1,6), F(1,5), frozenset({4,6}), "F"),
]

if __name__ == "__main__":
    for rho0, rhos, a, b, V, lab in CASES:
        for rho2 in rhos:
            r = decide(rho0, rho2, a, b, V)
            print(f"[{lab}] rho0={rho0} rho'={rho2}  W=[{a},{b}) ell={r['ell']} V={sorted(V)} "
                  f"J={r['J'] if 'J' in r else ''} kappa={r['kap']}")
            if r['mode']=='J-empty':
                print(f"      J empty: W subset B_m forces m <= {r['m_bound']}; "
                      f"failures among those m: {r['residual']}")
            else:
                print(f"      C1={r['C1']} (c>=C1 ok)  M1={r['M1']} (m>=M1 ok)  "
                      f"residual pairs = {r['residual_size']}   direct-check failures = {len(r['fails'])}")
                if r['fails']: print("      FAILS:", r['fails'])
