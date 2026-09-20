"""The 257 census families with no ALWAYS-free flank. Why?
'No always-free flank' = every flank has some killer x. But if no single x kills EVERY flank,
then for each x some flank survives, and the family closes by a finite case split on x.
Compute, for each of the 257, the intersection of the killer sets over all flanks."""
import ast, os
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
        if line.startswith("(("):
            try: rows.append(ast.literal_eval(line))
            except Exception: pass
resid=[]; tot=0
for cover,info in rows:
    pinned=sorted(F(b,c) for (c,b) in cover)
    M=1
    for p in pinned: M=lcm(M,p.denominator)
    diffs=sorted({int(p*M) for p in pinned} | {M})
    tot+=1
    flankinfo=[]
    anyfree=False
    for ef,val in info.get("flanks",{}).items():
        if not (isinstance(val,tuple) and len(val)==4 and val[0]=='U'): continue
        e=int(pf(ef)*M)
        if e==0: continue
        P=1
        for d in diffs:
            r=F(d,e); P=lcm(P,(r-r.numerator//r.denominator).denominator)
        U=[k for k in range(P) if all(clear(F(d),F(e),k) for d in diffs)]
        if not U: continue                       # flank dead, not usable
        K={x for x in range(1,M) if all(not clear(F(x),F(e),k) for k in U)}
        flankinfo.append((ef,e,len(U),K))
        if not K: anyfree=True
    if not anyfree and flankinfo:
        inter=set(range(1,M))
        for _,_,_,K in flankinfo: inter &= K
        resid.append((cover,M,flankinfo,inter))
print(f"rows: {tot};  families with NO always-free flank: {len(resid)}")
bad=[r for r in resid if r[3]]
print(f"   of those, some x kills EVERY usable flank at once: {len(bad)}")
print(f"   => settled by a finite case split on x: {len(resid)-len(bad)}")
print()
if bad:
    print("   families where one x kills every flank (the genuine residual):")
    for cover,M,fi,inter in bad[:10]:
        print(f"      cover {cover}  M={M}  killing x in {sorted(inter)[:8]}")
        for ef,e,nu,K in fi: print(f"         flank {ef} (e={e}) |U|={nu} |K|={len(K)}")
