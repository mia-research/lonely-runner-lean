# Pairs with two consecutive failing cell ends: openers, residues, lengths, steps; check CRT compatibility of the two congruence classes.
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from one_multiple_cells_v1 import cells, disp
def opener(D,u):
    for d in D:
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: return d,int(v)//8
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    rows=[]
    for D in combinations(nonmult,k):
        C=cells(D)
        if len(C)<3: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue
            fails=[]
            for i in range(1,len(C)):
                u,w=C[i]; d,j=opener(D,u); r=(c*(8*j+1))%d
                if disp(x,u)<=w: break
                fails.append((i,d,j,r,w-u,disp(x,u)-u))
            if len(fails)>=2: rows.append((D,c,fails))
    print(f"k={k} N={N} C={Cmax}: pairs with >=2 consecutive failing ends: {len(rows)}")
    comp=0
    for D,c,fails in rows:
        (_,d1,j1,r1,l1,s1),(_,d2,j2,r2,l2,s2)=fails[0],fails[1]
        # c(8j+1) = r mod d  : residues of c mod d_i / gcd conditions; check whether a common c0 mod lcm exists
        a1=(8*j1+1); a2=(8*j2+1)
        sol=[cc for cc in range(1,d1*d2*8+1) if (cc*a1)%d1==r1 and (cc*a2)%d2==r2]
        comp+= 1 if sol else 0
        print("  D'=",D,"c=",c,"fails (cell,d,j,r,len,step):",[(f[0],f[1],f[2],f[3],str(f[4]),str(f[5])) for f in fails],"compatible c exist:",bool(sol),"smallest c:",sol[0] if sol else None)
    print(f"  compatible in {comp} of {len(rows)}",flush=True)
main(6,16,8); main(4,40,12)
