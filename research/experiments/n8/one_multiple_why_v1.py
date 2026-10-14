# For (D',c) whose FIRST cell [u,w] of D' dies under x = 8c: record x's state at u and the step against the cell length.
import sys
from fractions import Fraction as F
from math import floor
from itertools import combinations
from one_multiple_cells_v1 import cells, clear, disp
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    tot=0; dies=0
    cat={}; step_eq_open=0; frac0=0
    ex={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        m=min(D+(8,)) 
        u,w=C[0]
        for c in range(1,Cmax+1):
            x=8*c; tot+=1
            mm=min(min(D),x)
            if disp(x,u)<=w: continue
            dies+=1
            f=x*u-floor(x*u)
            Rint=(8*mm*u).denominator==1
            status='Z(frac<1/8)' if f<F(1,8) else 'E(frac>7/8)'
            step=disp(x,u)-u
            exact_open = (f==0)
            key=(status, 'R integer' if Rint else 'R non-integer', 'x on lap line' if f==0 else 'x off lap line')
            cat[key]=cat.get(key,0)+1
            if step==F(1,8*x): step_eq_open+=1
            ex.setdefault(key,(D,c,u,w,step))
    print(f"k={k} N={N} Cmax={Cmax} pairs={tot} first-cell-dies={dies}")
    for key,v in sorted(cat.items(),key=lambda z:-z[1]): print("  ",key,v,"example",ex[key])
    print("   step == 1/(8x) (x on a lap line):",step_eq_open,flush=True)
main(*map(int,sys.argv[1:4]))
