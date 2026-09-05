#!/usr/bin/env python3
"""
Definitive test of the q=53 X-histogram anomaly: split-half replication.
If real, χ²(X mod 53) is ~3σ in BOTH disjoint halves. If it's the survey maximum
(look-elsewhere), it won't replicate consistently. Exact perm p in each half.
Also: is 53 special, or is the top-modulus just wandering? Report the argmax
modulus in each half — a real mode keeps the SAME q; noise moves it.
"""
import csv, random
from fractions import Fraction
random.seed(999)

XS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        XS.append(int(r["X"],16))
random.shuffle(XS)
half=len(XS)//2
H1,H2=XS[:half],XS[half:]

def chi2(vals,q):
    h=[0]*q
    for v in vals: h[v%q]+=1
    exp=Fraction(len(vals),q)
    return sum((Fraction(x)-exp)**2 for x in h)*(exp**-1)
def perm_p(vals,q,obs,B=300):
    M=len(vals); exp=Fraction(M,q); ge=0
    for _ in range(B):
        h=[0]*q
        for _ in range(M): h[random.randrange(q)]+=1
        if sum((Fraction(x)-exp)**2 for x in h)*(exp**-1) >= obs: ge+=1
    return Fraction(ge+1,B+1)
def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"
def argmax_excess(vals):
    best=None
    for q in range(2,65):
        c=chi2(vals,q); ex=c-Fraction(q-1)     # excess over df
        if best is None or ex>best[1]: best=(q,ex)
    return best

for lab,H in [("half-1",H1),("half-2",H2)]:
    c=chi2(H,53)
    print(f"{lab} (M={len(H)}): q=53 χ²={frac3(c)}(df52) perm p={frac3(perm_p(H,53,c))}")
    q,ex=argmax_excess(H)
    print(f"         argmax-excess modulus in this half: q={q} (excess {frac3(ex)})")
