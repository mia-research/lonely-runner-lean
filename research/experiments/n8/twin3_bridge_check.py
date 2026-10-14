"""twin3_bridge_check.py -- end-to-end control.

Takes the witness x produced by the window argument, converts it to b = x*L
(INTEGRALITY says this is an integer) and k = b + r*L for an uncovered residue r,
and verifies directly that  || e k / (8L) || >= 1/8  for every e in E.
This exercises the BRIDGE on the actual output of the proof; it is a control on
the reading of the setting, not part of the proof.
"""
from fractions import Fraction as F
from math import lcm
from twin3_core import bad, FULL, A_intervals, B_intervals, subtract, merge, J_set
from twin3_decide import decide, CASES

def dist_to_int(fr):
    n,d = fr.numerator, fr.denominator
    r = n % d
    return min(F(r,d), 1-F(r,d))

def check(E, x):
    L = lcm(*E)
    assert (x*L).denominator == 1, f"x={x} not integral in b-coords for L={L}"
    b = int(x*L)
    cov=set()
    for e in E: cov |= bad(e, (e*b)//L)
    U = FULL - cov
    if not U: return None
    out=[]
    for r in sorted(U):
        k = b + r*L
        N = 8*L
        mind = min(dist_to_int(F(e*k, N)) for e in E)
        out.append((r, k, mind, mind >= F(1,8), 0 < k < N))
    return b, L, out

TESTS = [
    ((1,3,4,5,7,11,32), F(2,7)),         # the tuple named in the warning
    ((1,3,4,5,7,11,24), F(2,7)),         # the global safe-measure minimiser
    ((1,2,3,5,7,8,18),  F(1,8)),
    ((1,3,5,6,7,13,8),  F(1,6)),
]
if __name__=="__main__":
    for E,x in TESTS:
        E=tuple(sorted(E))
        res = check(E,x)
        print(f"E={E}  x={x}")
        if res is None: print("   x NOT safe"); continue
        b,L,out = res
        print(f"   L={L}  b={b}")
        for r,k,mind,ok,inrange in out:
            print(f"      r={r} k={k}  min_e ||ek/(8L)|| = {mind} = {float(mind):.6f}  "
                  f">=1/8: {ok}   0<k<8L: {inrange}")
    # blanket run over every residual cell
    print("\nblanket bridge check over all residual cells:")
    tot=0; fail=0
    for rho0, rhos, a, bb, V, lab in CASES:
        for rho2 in rhos:
            r = decide(rho0,rho2,a,bb,V)
            J = J_set(rho2,V)
            pairs = [(None,m) for m in range(1,r['m_bound']+1)] if r['mode']=='J-empty' else r['residual']
            for c,m in pairs:
                cc = c if c is not None else 8+rho2
                E = tuple(sorted({1,3,5,7,rho0,cc,8*m}))
                surv = subtract([(a,bb)], merge(A_intervals(cc,J)+B_intervals(m)))
                if not surv: fail+=1; print("  no witness",E); continue
                x = surv[0][0]
                res = check(E,x)
                tot+=1
                if res is None: fail+=1; print("  UNSAFE",E,x); continue
                b_,L_,out = res
                if not any(ok and inr for _,_,_,ok,inr in out):
                    fail+=1; print("  BRIDGE FAIL",E,x,out)
    print(f"   cells={tot}  failures={fail}")
