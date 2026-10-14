# Dominant class, survivor in cell 1: which reading d opens the left end, at which lap j, and does the D' cascade from the end of the
# first cell (move from just after w0) name the same opener?  Exact Fractions.
import sys
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
from one_multiple_cells_v1 import cells, clear, disp
from one_multiple_residue_v1 import opener
def blocked_after(d,t):
    # blocked on (t, t+eps)?  reading d at t: frac(d t) in [0,1/8) or in [7/8,1)
    f=d*t-floor(d*t); return f<F(1,8) or f>=F(7,8)
def nxt(d,t):
    j=floor(d*t+F(1,8)); return F(8*j+1,8*d)
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    tot=0; agree=0; dis=0; jt={}; cond={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if len(C)<2: continue
        u0,w0=C[0]; u1,w1=C[1]
        # D' move from just after the first cell: largest next opening among readings blocked just after w0
        bl=[d for d in D if blocked_after(d,w0)]
        mv=max((nxt(d,w0) for d in bl),default=None)
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue
            if not (disp(x,u1)<=w1): continue
            tot+=1
            op=opener(D,u1); d,j=op[0]
            jt[j]=jt.get(j,0)+1
            if mv==u1: agree+=1
            else: dis+=1
    print(f"k={k} N={N} Cmax={Cmax}: dominant-class survivors in cell 1 = {tot}; D' move from the end of the first cell lands at the left end of cell 1: {agree}, differs: {dis}; opener lap j counts: {dict(sorted(jt.items()))}",flush=True)
main(*map(int,sys.argv[1:4]))
