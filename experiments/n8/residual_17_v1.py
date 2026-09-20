"""The 17 families where some x kills every PINNED flank.
The family is {pinned} u {x}, so x is itself a difference -- and therefore itself a FLANK.
The pinned-flank analysis never looks at the flank at e = x. Does it clear?"""
import ast, os
from fractions import Fraction as F
from math import lcm
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
bad=[]
for cover,info in rows:
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
    if anyfree or not fi: continue
    inter=set(range(1,M))
    for _,_,K in fi: inter &= K
    if inter: bad.append((cover,M,diffs,fi,sorted(inter)))
print(f"families where some x kills every PINNED flank: {len(bad)}")
print()
print("for each, at each killing x, is the flank at e = x itself clear?")
allok=True
for cover,M,diffs,fi,xs in bad:
    for x in xs:
        full=sorted(set(diffs)|{x})
        # the flank at e = x: is there an opening k clearing every difference?
        ok=any(all(clear(d,x,k) for d in full) for k in range(0,8*x+8))
        if not ok: allok=False
        print(f"   M={M:3d} x={x:3d} diffs={full}   flank at e=x clears: {ok}")
print()
print(f"ALL 17 rescued by the flank at e = x: {allok}")
