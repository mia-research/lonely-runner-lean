#!/usr/bin/env python3
"""Observation only. At each primitive SixResidual set's cascade instant T (max <= 40), the readings frac(d T).
Question: is the state at T an unfolded slot picture of the order-6 ideal, or does it sit on the slot grid of another
ideal (readings all on k/q for one q)? For each set: the least common denominator q of the five readings, whether the
readings are pairwise distinct, and the slot picture on that grid. Also: per runner, the denominator of its reading."""
from fractions import Fraction as F
from collections import Counter
from math import lcm
rows=[eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def T(S):
    t=F(1,6*S[0])
    while True:
        b=[d for d in S if cd(d*t)<F(1,6)]
        if not b: return t
        t=max(F(6*round(d*t)+1,6*d) for d in b)
qset=Counter(); distinct=Counter(); qq=Counter(); ratioq=Counter(); ex={}
for S in rows:
    t=T(S); r=[(d*t)%1 for d in S]
    q=lcm(*[x.denominator for x in r]); qset[q]+=1
    distinct[(len(set(r))==5)]+=1
    # denominator of T itself versus q
    ratioq[(q==t.denominator)]+=1
    if q not in ex: ex[q]=(S,t,r)
print("sets:",len(rows))
print("readings all distinct:",dict(distinct))
print("q (common denominator of the five readings) equals the denominator of T:",dict(ratioq))
print("commonest q:",qset.most_common(15))
print("q <= 12:",{q:qset[q] for q in sorted(qset) if q<=12})
for q in sorted(ex)[:8]:
    S,t,r=ex[q]; print(f"  example q={q}: S={S} T={t} readings={[str(x) for x in r]}")
