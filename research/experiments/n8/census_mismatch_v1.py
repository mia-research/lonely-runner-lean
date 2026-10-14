"""Resolve the 1,944 census cross-check mismatches.
Hypothesis: every killer the batch machine lists but our export does not has free parameter
x = kappa*M outside the admissible range 0 < x < M. If so, our export is right and the machine
over-counts -- and the 'always-free flank' classification our Lean emission rests on is sound."""
import ast, os, sys
from fractions import Fraction as F
from math import lcm
n=8; INV=F(1,n)
SRC=os.path.expanduser("~/ZCodeProject/lrc-n8/results/batch_machine_v1.out")
def fract(z): return z - (z.numerator//z.denominator)
def cd(z): return min(fract(z), 1-fract(z))
def clear(d,e,k): return cd(d*((F(k)+INV)/e)) >= INV
def pf(s):
    a,b=s.split('/') if '/' in s else (s,'1'); return F(int(a),int(b))
rows=[]
with open(SRC) as fh:
    for line in fh:
        line=line.strip()
        if not line.startswith("(("): continue
        try: rows.append(ast.literal_eval(line))
        except Exception: pass
print(f"machine rows parsed: {len(rows)}")
extra=0; outrange=0; inrange=[]
for cover,info in rows:
    pinned=sorted(F(b,c) for (c,b) in cover)
    M=1
    for p in pinned: M=lcm(M,p.denominator)
    diffs=sorted({int(p*M) for p in pinned} | {M})
    for ef,val in info.get("flanks",{}).items():
        if not (isinstance(val,tuple) and len(val)==4 and val[0]=='U'): continue
        e=int(pf(ef)*M)
        if e==0: continue
        P=1
        for d in diffs:
            r=F(d,e); P=lcm(P, (r-r.numerator//r.denominator).denominator)
        U=[k for k in range(P) if all(clear(F(d),F(e),k) for d in diffs)]
        ours=[]
        # recompute our killer set: on-lattice x in (0,M) blocking every k in U
        q=e//P if P and e%P==0 else 1
        for xnum in range(1,M):
            if all(not clear(F(xnum),F(e),k) for k in U) and U:
                ours.append(F(xnum,M))
        for kstr in val[3]:
            kap=pf(kstr)
            if kap not in ours:
                extra+=1
                x=kap*M
                if not (0 < x < M): outrange+=1
                else: inrange.append((cover,ef,kstr,x,M))
print(f"killers the machine lists that our recomputation does not: {extra}")
print(f"   of those, with free parameter x outside 0 < x < M: {outrange}")
print(f"   IN range (a genuine disagreement): {len(inrange)}")
for r in inrange[:6]: print(f"      {r}")
