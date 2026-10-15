#!/usr/bin/env python3
"""Observation only. Write the cascade instant as T = c/q in lowest terms. Then each reading is (d·c mod q)/q: the
arrangement's residues mod q, multiplied by c, a unit of Z/q. Checked: identity per runner; q = 6b/g with b the final
flank and g = gcd(6k+1, b); and c mod 6, i.e. which of the order-6 ideal's two events (p = 1, 5) the fold lies over."""
from fractions import Fraction as F
from collections import Counter
from math import gcd
rows=[eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def walk(S):
    t=F(1,6*S[0]); fl=(S[0],0)
    while True:
        b=[d for d in S if cd(d*t)<F(1,6)]
        if not b: return t, fl
        o,d,N=max((F(6*round(d*t)+1,6*d),d,round(d*t)) for d in b); t=o; fl=(d,N)
idn=0; qok=0; cmod=Counter(); unit=0
for S in rows:
    T,(b,k)=walk(S); c,q=T.numerator,T.denominator
    idn+=all((d*T)%1==F((d*c)%q,q) for d in S)
    g=gcd(6*k+1,b); qok+= q==6*b//g and c==(6*k+1)//g
    unit+= gcd(c,q)==1; cmod[c%6]+=1
print(f"sets {len(rows)}; reading = (d c mod q)/q: {idn}; q = 6b/g and c = (6k+1)/g: {qok}; c a unit of Z/q: {unit}")
print("c mod 6 (the ideal event the fold lies over):",dict(cmod))
