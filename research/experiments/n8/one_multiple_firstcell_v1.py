# Dominant class: is the first cell of D' (the integer-R grid instant) degenerate (a touch)? Compare its length with the step 1/(8x).
import sys
from fractions import Fraction as F
from math import floor
from itertools import combinations
from one_multiple_cells_v1 import cells, disp
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    tot=0; degen=0; pos=0; pos_ratio_ok=0; firstR={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            f=x*u0-floor(x*u0)
            if not ((8*mm*u0).denominator==1 and f==0): continue
            tot+=1
            if w0==u0: degen+=1
            else:
                pos+=1
                # length versus step
                assert w0-u0 < F(1,8*x)
            R=8*mm*u0; firstR[R]=firstR.get(R,0)+1
    print(f"k={k} dominant-class pairs={tot}: first cell degenerate (touch)={degen}, positive length={pos} (all shorter than 1/(8x), asserted); R of the first cell:",dict(sorted(firstR.items())),flush=True)
main(*map(int,sys.argv[1:4]))
