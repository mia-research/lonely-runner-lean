# Dominant class: first cell of D' at integer R, x = 8c exactly on a lap line there, first cell dies.
# Where does the first surviving cell sit, and is the survivor x's own opening or an undisplaced clear point?
import sys
from fractions import Fraction as F
from math import floor
from itertools import combinations
from one_multiple_cells_v1 import cells, clear, disp
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    tally={}; ex={}; mdiv=0; tot=0
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x); u0,w0=C[0]
            if disp(x,u0)<=w0: continue
            f=x*u0-floor(x*u0)
            if not ((8*mm*u0).denominator==1 and f==0): continue
            tot+=1
            for i,(u,w) in enumerate(C):
                p=disp(x,u)
                if p<=w: break
            R_u=8*mm*u; R_p=8*mm*p
            own_open = p>u
            key=(i, 'survivor=x own opening' if own_open else 'x clear at left end', 'left end R integer' if R_u.denominator==1 else 'left end R non-integer', 'R_u odd' if (R_u.denominator==1 and R_u%2==1) else 'R_u other')
            tally[key]=tally.get(key,0)+1; ex.setdefault(key,(D,c,R_u,R_p))
            if c%mm==0: mdiv+=1
    print(f"k={k} N={N} Cmax={Cmax} dominant-class pairs={tot}  (m divides c in {mdiv})")
    for key,v in sorted(tally.items(),key=lambda z:-z[1])[:8]: print("  ",key,v,"example (D',c,R_left,R_survivor)=",ex[key])
main(*map(int,sys.argv[1:4]))
