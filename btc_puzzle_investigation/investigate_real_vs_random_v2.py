#!/usr/bin/env python3
"""
Do the 63 real keys' D-signatures differ from matched RANDOM integers anywhere?
Compare, real vs 200x matched-random (same bit-lengths): term count, D_1, D_2
distributions, and shared early-prefix rate. Exact counts + permutation p.
"""
import csv, random
from collections import Counter
rnd=random.Random(20260710)
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
rows=[(int(r["bits"]),int(r["private_key"],16)) for r in csv.DictReader(open("puzzles_verified.csv"))]
rows=[(P,d) for P,d in rows if P>=20]
Ps=[P for P,_ in rows]
real=[d_recursion(1<<P,d) for P,d in rows]

# matched-random pool: for each real P, many random keys of that P
def rand_sig(P):
    d=(1<<(P-1))+rnd.randrange(1<<(P-1)); return d_recursion(1<<P,d)
REP=200
randpool={P:[rand_sig(P) for _ in range(REP)] for P in set(Ps)}

def feat_termcount(sig): return len(sig)
def feat_d1(sig): return sig[1] if len(sig)>1 else 0
def feat_d2(sig): return sig[2] if len(sig)>2 else 0

def compare(fname, f):
    rv=[f(s) for s in real]
    # per-key percentile of real feature within its matched-random set -> uniform test
    ranks=[]
    for (P,_),s in zip(rows,real):
        pool=[f(x) for x in randpool[P]]
        lt=sum(1 for v in pool if v<f(s)); eq=sum(1 for v in pool if v==f(s))
        ranks.append((lt+eq/2)/len(pool))
    m=len(ranks); mean=sum(ranks)/m
    hi=sum(1 for r in ranks if r>0.5); lo=sum(1 for r in ranks if r<0.5)
    rc=Counter(rv); allrand=[f(x) for P in Ps for x in randpool[P]]
    ac=Counter(allrand)
    print(f"  {fname:11s}: real mean-rank={mean:.3f} (>0.5:{hi} <0.5:{lo})")
    print(f"    real most-common:   {rc.most_common(5)}")
    print(f"    random most-common: {[(v,round(c/ (len(Ps)*REP)*len(rows))) for v,c in ac.most_common(5)]}")

print(f"real keys P>=20: {len(rows)}   (matched-random {REP}x each)\n")
compare("term count", feat_termcount)
compare("D_1", feat_d1)
compare("D_2", feat_d2)

# shared early-prefix [D_1,D_2] rate: real vs random
def prefix(sig): return tuple(sig[1:3]) if len(sig)>2 else None
real_pref=[prefix(s) for s in real if prefix(s)]
dup_real=len(real_pref)-len(set(real_pref))
# random baseline: draw len(real_pref) random prefixes many times, count dups
dupd=[]
allrand_sigs=[x for P in Ps for x in randpool[P]]
for _ in range(300):
    samp=[prefix(x) for x in random.sample(allrand_sigs,len(real_pref)) if prefix(x)]
    dupd.append(len(samp)-len(set(samp)))
import statistics as st
ge=sum(1 for v in dupd if v>=dup_real)
print(f"\nshared [D_1,D_2] prefixes among real: {dup_real} duplicate(s); "
      f"random baseline mean={st.mean(dupd):.1f}; P(random>=real)={(ge+1)/301:.3f}")
# show which real keys share a prefix
c=Counter(real_pref)
shared=[(pfx,n) for pfx,n in c.items() if n>1]
print(f"  real shared prefixes: {shared if shared else 'none'}")
