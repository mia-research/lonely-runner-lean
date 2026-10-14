# Second stage of the one-multiple family: at the left end u of a later cell of D', u = (8j+1)/(8d) for a D' reading d (opener).
# Residue prediction: x u = c(8j+1)/d = K + r/d with r = c(8j+1) mod d.
#   8r in [d,7d]  -> x clear at u;  8r < d -> blocked, exit step (1/8 - r/d)/x;  8r > 7d -> blocked, exit step (9/8 - r/d)/x.
# Compare with the DispCell value disp x u; exact Fractions; deterministic populations.
import sys
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
from one_multiple_cells_v1 import cells, clear, disp
def opener(D,u):
    out=[]
    for d in D:
        # u = (8j+1)/(8d)  <=>  8 d u - 1 = 8 j
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: out.append((d,int(v)//8))
    return out
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    tot=0; noopen=0; mism=0; status={}; surv_idx={}; byrule={'clear':0,'short step fits':0}; opener_gcd={}
    exam={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue  # dominant class
            # walk later cells, apply the residue prediction at each left end
            for i in range(1,len(C)):
                u,w=C[i]; tot+=1
                op=opener(D,u)
                if not op: noopen+=1; continue
                d,j=op[0]
                r=(c*(8*j+1))%d
                if 8*r>=d and 8*r<=7*d: st='clear'; step=F(0)
                elif 8*r<d: st='below'; step=(F(1,8)-F(r,d))/x
                else: st='above'; step=(F(9,8)-F(r,d))/x
                actual=disp(x,u)-u
                if actual!=step: mism+=1
                fits = step<=w-u
                status[(st,fits)]=status.get((st,fits),0)+1
                g=gcd(8*j+1,d)
                opener_gcd[g]=opener_gcd.get(g,0)+1
                if fits:
                    surv_idx[i]=surv_idx.get(i,0)+1
                    exam.setdefault((st,i),(D,c,(d,j),r))
                    break
    print(f"k={k} N={N} Cmax={Cmax}: cell-ends examined={tot}, no D' opener found={noopen}, residue prediction differs from DispCell step={mism}")
    print("  (status of x at the left end by residue, step fits in cell):",dict(sorted(status.items())))
    print("  survivor cell index (dominant class):",dict(sorted(surv_idx.items())))
    print("  gcd(8j+1,d) of the opener over examined ends:",dict(sorted(opener_gcd.items())))
    for key,v in sorted(exam.items(),key=lambda z:(z[0][1],z[0][0]))[:6]: print("   example",key,v)
main(*map(int,sys.argv[1:4]))
