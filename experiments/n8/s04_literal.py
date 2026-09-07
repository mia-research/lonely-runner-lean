"""S04: distinguish the two fibre sets.
  B_lit  = [ceil(L/8), floor(7L/8)]                (the task's B_div, = runner-8 constraint)
  B_hon  = {b : floor(e b/L) mod 8 not in {0,7} for ALL e in E_div}
Report safe counts in each, inside the two windows and overall, and AUDIT the
assumed framework theorem (b in B_lit & safe  =>  x_0>=1)."""
import sys
from itertools import combinations
from math import gcd
from n8_fibre_core import L_of, split, safe, div_ok, witness_from_fibre, blocked_non

UNITS={1,3,5,7}
def unit_complete(En):
    R=set(e%8 for e in En); return UNITS<=R and len(R)==5

def report(E, verbose=True):
    L=L_of(E); Ed,En=split(E)
    lo,hi=-(-L//8),(7*L)//8
    W=[(-(-2*L//7),(2*L)//5), (-(-3*L//5),(5*L)//7)]
    inw=lambda b: any(a<=b<z for a,z in W)
    s_lit=s_lit_w=s_hon=s_hon_w=0
    thm_fail=[]
    ex_lit_w=ex_hon_w=ex_hon=None
    for b in range(lo,hi+1):
        if not safe(En,b,L): continue
        s_lit+=1
        if inw(b):
            s_lit_w+=1
            if ex_lit_w is None: ex_lit_w=b
        # audit assumed theorem on B_lit
        if witness_from_fibre(E,b) is None:
            thm_fail.append(b)
        if div_ok(Ed,b,L):
            s_hon+=1
            if ex_hon is None: ex_hon=b
            if inw(b):
                s_hon_w+=1
                if ex_hon_w is None: ex_hon_w=b
    r=dict(E=E,L=L,Ed=Ed,En=En,s_lit=s_lit,s_lit_w=s_lit_w,s_hon=s_hon,s_hon_w=s_hon_w,
           thm_fail=len(thm_fail),thm_fail_ex=thm_fail[:3],
           ex_lit_w=ex_lit_w,ex_hon_w=ex_hon_w,ex_hon=ex_hon)
    if verbose:
        print(f"E={E} L={L} E_div={Ed} R_non={sorted(set(e%8 for e in En))}")
        print(f"   safe in B_lit={s_lit}  of which in windows={s_lit_w}   (first {ex_lit_w})")
        print(f"   safe in B_hon={s_hon}  of which in windows={s_hon_w}   (first {ex_hon_w})")
        print(f"   assumed-theorem failures on B_lit (safe but NO witness): {r['thm_fail']} e.g. {r['thm_fail_ex']}")
    return r

if __name__=="__main__":
    cases=[(1,2,3,5,15,24,40),(1,3,4,5,15,24,40),(1,3,5,12,15,20,24),
           (1,3,9,12,15,45,360),(1,5,15,24,40,75,150),(3,9,12,15,40,45,360)]
    for E in cases:
        report(E); print()
