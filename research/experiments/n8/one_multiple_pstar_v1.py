import sys
from fractions import Fraction as F
from itertools import combinations
from one_multiple_cells_v1 import cells, disp
from math import floor
def opener(D,u):
    for d in D:
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: return d,int(v)//8
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    fail=0; viol=0; below=0; above=0; r0=0
    for D in combinations(nonmult,k):
        C=cells(D)
        if len(C)<2: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue
            for i in range(1,len(C)):
                u,w=C[i]; d,j=opener(D,u); r=(c*(8*j+1))%d
                if disp(x,u)<=w: break
                fail+=1
                if 8*r<d:
                    below+=1; 
                    if r>1: viol+=1
                    if r==0: r0+=1
                else:
                    above+=1
                    if d-r>2: viol+=1
    print(f"k={k} N={N} C={Cmax}: failing ends={fail} (below {below}, above {above}); r=0 among below: {r0}; violations of P*(below r<=1 or above d-r<=2): {viol}",flush=True)
for a in [(4,20,12),(5,18,8),(6,16,8)]: main(*a)
