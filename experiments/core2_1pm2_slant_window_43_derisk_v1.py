#!/usr/bin/env python3
"""
Does the part-1 (1,-2)/(1,2) SLANT WINDOW survive the (43) cut in core2 (6p<q)?
==============================================================================
The part-1 exc_1_neg2_pentkill puts the cone points on the line Y = {3/2 - 2X}
(branch X in (1/4,3/4)), a 1/q-grid in X, and uses the slant window [Xlo,Xhi]
(width r(5s-4r)/(36qs)) inside P.  For core2 we additionally need the (43) cut
   Y <= 5/12 - p/(3q)   <=>   3/2 - 2X <= 5/12 - p/(3q)   <=>   X >= 13/24 + p/(6q).
So the P'-window is [max(Xlo, Xcut), Xhi] with Xcut = 13/24 + p/(6q).
Question: does it still contain a 1/q-grid point, i.e. is its width >= 1/q?

(1,-2) rigidity: 2r + p = 3q  (p,q odd).  (1,2) rigidity: 2r = 2q + p (p even),
line Y = {3/2 - 2X}? -- (1,2)'s line differs; here we focus on (1,-2) where the
slant-window formulas are known (exc_1_neg2_pentkill). For (1,2) we just brute the
generic odd-m P'-search restricted to the X-branch.

For (1,-2): Xlo = Nb/Db, Xhi = Na/Da with
   Da = 1/r + 2/p ;  Na = 5/(6r) + 4/(3p) - 1/(3s)
   Db = 2/(q-p) - 1/r ;  Nb = 1/(3s) - 5/(6r) + 7/(6(q-p))
We sweep core2 (q,p) with 2r+p=3q, p,q odd, 6p<q, gcd(r,q)=1, and completions
s in (r,3q].  Report: of completions where part-1 window has width>=1/q (hwb holds),
how many ALSO have the (43)-cut window width>=1/q; and overall whether SOME
grid point lands in the P'-window (allowing a different m than part-1's).
"""
import math

def frac(x): return x - math.floor(x)

def run_1neg2(qmax=80):
    tot=0; hwb_ok=0; cut_ok=0; cut_fail=[]; grid_ok=0; grid_fail=[]
    for q in range(7,qmax+1):
        if q%2==0: continue
        for p in range(1,q):
            if p%2==0: continue
            if math.gcd(p,q)!=1: continue
            if 6*p>=q: continue
            if (3*q-p)%2!=0: continue
            r=(3*q-p)//2
            if not (q<r and 2*r<3*q): continue
            if math.gcd(r,q)!=1: continue
            for s in range(r+1,3*q+1):
                tot+=1
                Da=1/r+2/p; Na=5/(6*r)+4/(3*p)-1/(3*s)
                Db=2/(q-p)-1/r; Nb=1/(3*s)-5/(6*r)+7/(6*(q-p))
                Xhi=Na/Da; Xlo=Nb/Db
                width=Xhi-Xlo
                hwb = width >= 1/q - 1e-12
                if hwb: hwb_ok+=1
                Xcut=13/24 + p/(6*q)
                Xlo2=max(Xlo,Xcut)
                w2=Xhi-Xlo2
                if w2 >= 1/q - 1e-12:
                    cut_ok+=1
                else:
                    if hwb: cut_fail.append((q,p,r,s,round(width,4),round(w2,4)))
                # actual grid points on the line in the P'-window (X = frac(r*m/(2q)), m odd)
                found=False
                for m in range(1,2*q,2):
                    X=frac(r*m/(2*q))
                    if not (0.25<X<0.75): continue
                    Y=frac(p*m/(2*q))
                    # must be the slant branch Y=3/2-2X (mod 1): check
                    if abs(Y-(1.5-2*X))>1e-9 and abs(Y-(1.5-2*X)+1)>1e-9 and abs(Y-(1.5-2*X)-1)>1e-9:
                        continue
                    if Xlo-1e-9 <= X <= Xhi+1e-9 and X >= Xcut-1e-9:
                        found=True; break
                if found: grid_ok+=1
                else: grid_fail.append((q,p,r,s))
    print(f"(1,-2): completions={tot}")
    print(f"  part-1 window width>=1/q (hwb): {hwb_ok}")
    print(f"  (43)-cut window width>=1/q:     {cut_ok}")
    print(f"  ACTUAL grid pt in P'-slant-window: {grid_ok}  (fail {len(grid_fail)})")
    if cut_fail:
        print(f"  hwb-ok but cut-window too narrow: {len(cut_fail)} (e.g. {cut_fail[:5]})")
    if grid_fail:
        print(f"  grid failures (e.g.): {grid_fail[:8]}")

run_1neg2()
