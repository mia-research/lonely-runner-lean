"""twin3_report_tables.py -- emits the markdown tables used in reports/n8_twin_case.md."""
from fractions import Fraction as F
from math import ceil
from twin3_core import A_intervals, B_intervals, subtract, merge, J_set, bad, FULL, uncovered_cells
from twin3_decide import CASES, decide

def longest(iv): return max((b-a for a,b in iv), default=F(0))
def wit(a,b,c,J,m):
    s=subtract([(a,b)], merge(A_intervals(c,J)+B_intervals(m)))
    return s[0][0] if s else None
def fu(E,x):
    cov=set()
    for e in E: cov|=bad(e,(e*x).numerator//(e*x).denominator)
    return sorted(FULL-cov)

print("## Table 1 - base-five uncovered sets\n")
for rho0 in (2,4,6):
    print(f"**rho0 = {rho0}**  (breakpoint denominators divide lcm(1,3,5,7,{rho0}))\n")
    print("| window | length | U (uncovered by {1,3,5,7,rho0}) |")
    print("|---|---|---|")
    for a,b,U in uncovered_cells([1,3,5,7,rho0]):
        print(f"| [{a}, {b}) | {b-a} | {sorted(U) if U else 'empty'} |")
    print()

print("\n## Table 2 - mu(c) and lam(m)\n")
for rho0, rhos, a, b, V, lab in CASES:
    for rho2 in rhos:
        J=J_set(rho2,V); kap=len(J); ell=b-a
        if kap==0: continue
        C1=ceil(F(15)/ell); M1=ceil(F(7,4)/ell)
        print(f"**[{lab}] rho0={rho0}, rho'={rho2}**  W=[{a},{b}), ell={ell}, J={sorted(J)}, "
              f"kappa={kap}, C1={C1}, M1={M1}\n")
        print("| c = e' | mu(c) | Lemma B settles m > | residual m |")
        print("|---|---|---|---|")
        for c in range(8+rho2, C1, 8):
            mu=longest(subtract([(a,b)], A_intervals(c,J)))
            k=int(F(1,4)/mu)
            print(f"| {c} | {mu} | {F(1,4)/mu} | {('1..'+str(k)) if k>=1 else 'none'} |")
        print()
        print("| m | lam(m) | Lemma C settles c > | residual c |")
        print("|---|---|---|---|")
        for m in range(1,M1):
            lam=longest(subtract([(a,b)], B_intervals(m)))
            k=int(F(kap)/lam)
            cs=[c for c in range(8+rho2, k+1, 8)]
            print(f"| {m} | {lam} | {F(kap)/lam} | {cs if cs else 'none'} |")
        print()

print("\n## Table 3 - residual cells with witnesses\n")
grand=0
for rho0, rhos, a, b, V, lab in CASES:
    for rho2 in rhos:
        r=decide(rho0,rho2,a,b,V); J=J_set(rho2,V)
        print(f"**[{lab}] rho0={rho0}, rho'={rho2}**")
        if r['mode']=='J-empty':
            print(f"J is empty, so the twin never kills W; W subset B_m forces m <= {r['m_bound']}.\n")
            print("| m | W minus B_m | witness x |")
            print("|---|---|---|")
            for m in range(1,r['m_bound']+1):
                s2=subtract([(a,b)],B_intervals(m)); grand+=1
                txt=" u ".join(f"[{u}, {v})" for u,v in s2) if s2 else "EMPTY"
                print(f"| {m} | {txt} | {s2[0][0] if s2 else 'NONE'} |")
            print()
        else:
            print(f"residual cells: {len(r['residual'])}\n")
            print("| e' | q' | m | witness x | E | uncovered by all 7 |")
            print("|---|---|---|---|---|---|")
            for c,m in r['residual']:
                x=wit(a,b,c,J,m); grand+=1
                E=tuple(sorted({1,3,5,7,rho0,c,8*m}))
                print(f"| {c} | {(c-rho2)//8} | {m} | {x} | {E} | {fu(E,x)} |")
            print()
print(f"\nTotal residual cells: {grand}")
