"""Redo, separating rows that HAVE a free parameter from those that do not.
An s = 6 cover pins 6 ratios; with M that is 7 differences and there is NO free x -- the machine
labels those 'SETTLED-all-x (no free param)'. Killer analysis applies only where x is free."""
import ast, os
from fractions import Fraction as F
from math import lcm
from collections import Counter
n=8; INV=F(1,n)
SRC=os.path.expanduser("~/ZCodeProject/lrc-n8/results/batch_machine_v1.out")
def fract(z): return z - (z.numerator//z.denominator)
def cd(z): return min(fract(z), 1-fract(z))
def clear(d,e,k): return cd(F(d)*((F(k)+INV)/F(e))) >= INV
def pf(s):
    a,b=s.split('/') if '/' in s else (s,'1'); return F(int(a),int(b))
rows=[]
with open(SRC) as fh:
    for line in fh:
        line=line.strip()
        if line.startswith("(("):
            try: rows.append(ast.literal_eval(line))
            except Exception: pass
print(f"rows: {len(rows)}")
print("  by cover size s:", dict(Counter(r[1].get('s') for r in rows)))
print("  by verdict:", dict(Counter(str(r[1].get('verdict'))[:34] for r in rows)))
free=[r for r in rows if 'no free param' not in str(r[1].get('verdict',''))]
print(f"\n  rows WITH a free parameter: {len(free)}")
noalways=0; killall=0; ex=[]
for cover,info in free:
    pinned=sorted(F(b,c) for (c,b) in cover)
    M=1
    for p in pinned: M=lcm(M,p.denominator)
    diffs=sorted({int(p*M) for p in pinned} | {M})
    fi=[]; anyfree=False
    for ef,val in info.get("flanks",{}).items():
        if not (isinstance(val,tuple) and len(val)==4 and val[0]=='U'): continue
        e=int(pf(ef)*M)
        if e==0: continue
        P=1
        for d in diffs:
            r=F(d,e); P=lcm(P,(r-r.numerator//r.denominator).denominator)
        U=[k for k in range(P) if all(clear(d,e,k) for d in diffs)]
        if not U: continue
        K={x for x in range(1,M) if all(not clear(x,e,k) for k in U)}
        fi.append((e,U,K))
        if not K: anyfree=True
    if not anyfree and fi:
        noalways+=1
        inter=set(range(1,M))
        for _,_,K in fi: inter &= K
        if inter:
            killall+=1
            if len(ex)<8: ex.append((cover,M,diffs,sorted(inter)))
print(f"     of those, NO always-free flank: {noalways}")
print(f"     of those, some x kills every usable pinned flank: {killall}")
for cover,M,diffs,xs in ex:
    print(f"        M={M} pinned+M={diffs} killing x={xs}  -> family {sorted(set(diffs)|set(xs[:1]))}")
