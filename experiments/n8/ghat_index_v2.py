"""v2 -- v1 sampled randomly at denominator 1000 and found 0 shadowing configurations in 60,000,
so it discriminated nothing.  Shadowing needs EXACT rational coincidences.  Redone EXHAUSTIVELY
over small denominators, which is how the j=2 family was found.  Question: at j = 2..4, which
ghat = min(f,1-f) values support shadowing?"""
from fractions import Fraction as F
from math import floor, gcd, lcm
from itertools import combinations_with_replacement, product
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def ghat(f): return min(f,1-f)
FS=[F(p,q) for q in range(2,8) for p in range(1,q) if gcd(p,q)==1]
def shadow(ws):
    P=1
    for f,_ in ws: P=lcm(P,f.denominator)
    for k in range(0,8*P+1):
        if all(circd(F(k)*f+c)>=TH for f,c in ws): return False
    return True

for j in [2,3]:
    found={}
    tested=0
    for fs in combinations_with_replacement(FS,j):
        for As in product(range(8),repeat=j):
            ws=[(f,(F(A)+f)/8) for f,A in zip(fs,As)]
            tested+=1
            if shadow(ws):
                key=tuple(sorted(str(ghat(f)) for f in fs))
                found.setdefault(key,[]).append((tuple(str(f) for f in fs),As))
    print(f"=== j = {j}:  {tested} configurations tested exhaustively (denominators 2..7) ===")
    if not found:
        print("   no shadowing configuration")
    else:
        tot=sum(len(v) for v in found.values())
        print(f"   shadowing configurations: {tot}")
        for key in sorted(found, key=lambda t: -len(found[t])):
            print(f"      ghat multiset {key}: {len(found[key])} configs   e.g. f={found[key][0][0]} A={found[key][0][1]}")
    print()
