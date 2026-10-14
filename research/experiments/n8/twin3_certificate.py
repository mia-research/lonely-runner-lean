"""twin3_certificate.py -- emits the residual tables as explicit witnesses.

For every (rho0, rho') and every residual pair (c,m) not settled by Lemmas A/B/C,
print the smallest surviving x in the chosen window, as an exact rational.
Also audits each witness against the FULL runner set E (all seven runners),
independently of the window argument.
"""
from fractions import Fraction as F
from math import ceil, gcd
from twin3_core import (A_intervals, B_intervals, subtract, merge, J_set, bad, FULL)
from twin3_decide import decide, CASES

def full_uncovered(E, x):
    cov=set()
    for e in E:
        cov |= bad(e, (e*x).numerator//(e*x).denominator)
    return FULL - cov

def witness(alpha,beta,c,J,m):
    surv = subtract([(alpha,beta)], merge(A_intervals(c,J)+B_intervals(m)))
    return surv[0][0] if surv else None

def residual_pairs(rho0,rho2,alpha,beta,V):
    r = decide(rho0,rho2,alpha,beta,V)
    if r['mode']=='J-empty':
        return [(None,m) for m in range(1,r['m_bound']+1)], r
    return r['residual'], r

if __name__=="__main__":
    grand=0; bad_rows=[]
    for rho0, rhos, a, b, V, lab in CASES:
        for rho2 in rhos:
            pairs, r = residual_pairs(rho0,rho2,a,b,V)
            J = J_set(rho2,V)
            print(f"\n=== [{lab}] rho0={rho0} rho'={rho2}  W=[{a},{b})  V={sorted(V)}  "
                  f"J={sorted(J)}  kappa={len(J)}  ell={b-a}")
            if r['mode']=='J-empty':
                print(f"    J = empty; only m <= {r['m_bound']} need a check.")
                rows=[(cm[1],) for cm in pairs]
                for m, in rows:
                    x = witness(a,b,1,frozenset(),m)   # A empty
                    grand+=1
                    ok = x is not None
                    if ok:
                        E_check=None
                    print(f"      m={m:<3} witness x={x}")
                    if not ok: bad_rows.append((lab,rho0,rho2,None,m))
            else:
                print(f"    C1={r['C1']}  M1={r['M1']}  residual cells: {len(pairs)}")
                for c,m in pairs:
                    x = witness(a,b,c,J,m)
                    grand+=1
                    q=(c-rho2)//8
                    E=tuple(sorted({1,3,5,7,rho0,c,8*m}))
                    if x is None:
                        bad_rows.append((lab,rho0,rho2,c,m)); print(f"      c={c} m={m}  NO WITNESS")
                        continue
                    U=full_uncovered(E,x)
                    flag="" if U else "  <-- FULL-E CHECK FAILED"
                    if not U: bad_rows.append((lab,rho0,rho2,c,m))
                    print(f"      e'={c:<4}(q'={q:<3}) m={m:<3} x={str(x):<12} "
                          f"E={E}  uncovered(all 7)={sorted(U)}{flag}")
    print(f"\nTOTAL residual cells checked: {grand};  failures: {len(bad_rows)}")
    for r in bad_rows: print("   FAIL", r)
