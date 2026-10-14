# P* control: which residues are blocked at all for d <= N, and how the failing ends distribute by residue when d goes to 40.
import sys
from fractions import Fraction as F
from itertools import combinations
from one_multiple_cells_v1 import cells, disp
def opener(D,u):
    for d in D:
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: return d,int(v)//8
def main(k,N,Cmax,dmin_lo=1):
    nonmult=[d for d in range(1,N+1) if d%8]
    blocked_res={}   # (class) -> count over all examined ends
    fail=0; fail_by={}; ends=0; blocked_pass=0
    for D in combinations(nonmult,k):
        C=cells(D)
        if len(C)<2: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue
            for i in range(1,len(C)):
                u,w=C[i]; d,j=opener(D,u); r=(c*(8*j+1))%d; ends+=1
                if 8*r<d: key=('below r=%d'%r)
                elif 8*r>7*d: key=('above d-r=%d'%(d-r))
                else: key=None
                if disp(x,u)<=w:
                    if key: blocked_pass+=1
                    break
                fail+=1; fail_by[key]=fail_by.get(key,0)+1
    print(f"k={k} N={N} C={Cmax}: ends={ends} failing={fail} blocked-but-passing={blocked_pass}; failing by residue class: {dict(sorted(fail_by.items(),key=lambda z:-z[1]))}",flush=True)
for a in [(4,20,12),(4,32,12),(4,40,12)]: main(*a)
