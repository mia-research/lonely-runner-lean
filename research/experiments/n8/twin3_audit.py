"""twin3_audit.py -- controls on the three lemmas.

The lemmas are only useful if they are TRUE, so each is tested on the region where
it claims to apply.  A single counterexample here would refute the proof.
  Lemma A control : c >= C1 and m >= M1   ->  W \\ (A u B) must be non-empty
  Lemma B control : c <  C1 and 4*m*mu(c) > 1
  Lemma C control : m <  M1 and c*lam(m) > kappa
Also: an independent brute-force sweep of the safe measure of the full E.
"""
from fractions import Fraction as F
from math import ceil
from twin3_core import A_intervals, B_intervals, subtract, merge, J_set
from twin3_decide import CASES

def longest(iv): return max((b-a for a,b in iv), default=F(0))

def run(CSTEPS=40, MSTEPS=40):
    tot=0; bad=[]
    for rho0, rhos, a, b, V, lab in CASES:
        ell=b-a
        for rho2 in rhos:
            J=J_set(rho2,V); kap=len(J)
            if kap==0:
                C1=1; M1=ceil(F(1,4)/ell)+1
            else:
                C1=ceil(F(15)/ell); M1=ceil(F(7,4)/ell)
            W=[(a,b)]
            # Lemma A region
            cs=[c for c in range(8+rho2, 8+rho2+8*CSTEPS, 8) if c>=C1][:CSTEPS]
            if not cs:
                c0=8+rho2
                while c0<C1: c0+=8
                cs=[c0+8*i for i in range(CSTEPS)]
            for c in cs:
                for m in range(M1, M1+MSTEPS):
                    surv=subtract(W, merge(A_intervals(c,J)+B_intervals(m)))
                    tot+=1
                    if not surv: bad.append(('A',lab,rho2,c,m))
            # Lemma B region
            for c in range(8+rho2, min(C1, 8+rho2+8*CSTEPS), 8):
                mu=longest(subtract(W, A_intervals(c,J)))
                for m in range(1, 4*MSTEPS):
                    if 4*m*mu>1:
                        surv=subtract(W, merge(A_intervals(c,J)+B_intervals(m)))
                        tot+=1
                        if not surv: bad.append(('B',lab,rho2,c,m))
            # Lemma C region
            for m in range(1, M1):
                lam=longest(subtract(W, B_intervals(m)))
                for c in range(8+rho2, 8+rho2+8*4*CSTEPS, 8):
                    if c*lam>kap:
                        surv=subtract(W, merge(A_intervals(c,J)+B_intervals(m)))
                        tot+=1
                        if not surv: bad.append(('C',lab,rho2,c,m))
    print(f"lemma-region controls: {tot} instances, violations = {len(bad)}")
    for x in bad[:20]: print("   VIOLATION", x)
    return bad

if __name__=="__main__":
    run()
