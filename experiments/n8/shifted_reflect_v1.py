"""Two opposing patterns => two opposing reflection centres.

q -> c-q preserves the constraint at b iff c = L(b)+U(b) mod b.
   b mod 8 not in {0,1} : L+U = b   => c = 0  mod b
   b mod 8 in {0,1}     : L+U = b-1 => c = -1 mod b
Since b | m:  c = 0 works iff ALL moduli are good (the standard reflection, m-q);
              c = m-1 works iff ALL moduli are obstructed (since b | m gives c = -1 mod b).
Mixed profiles admit neither.  Test all three predictions.
"""
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])
def good(b): return b % 8 not in (0,1)

# 1. the L+U law
bad = [b for b in range(2,2000) if (I(b)[0]+I(b)[1]) != (b if good(b) else b-1)]
print(f"1. L(b)+U(b) = b when b mod 8 not in {{0,1}}, else b-1 : exceptions for b<2000 = {len(bad)}")

tot=0; cats={'all good':0,'all bad':0,'mixed':0}
acts={'all good':0,'all bad':0,'mixed':0}
even={'all good':0,'all bad':0,'mixed':0}
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c5 in combinations(ds,5):
        bs=sorted(c5); allb=bs+[m]
        S=set(q for q in range(m) if ok(q,m,bs))
        if not S: continue
        tot+=1
        ng=sum(1 for b in allb if good(b))
        cat='all good' if ng==len(allb) else ('all bad' if ng==0 else 'mixed')
        cats[cat]+=1
        cc = 0 if cat=='all good' else (m-1 if cat=='all bad' else None)
        if cc is not None:
            if {(cc-q)%m for q in S} == S: acts[cat]+=1
        if len(S)%2==0: even[cat]+=1
print(f"\n2. profiles {tot:,}")
for k in cats:
    n=cats[k]
    if not n: continue
    print(f"   {k:<9} {n:>7,}  reflection acts {acts[k]:>7,} ({100*acts[k]/n:6.2f}%)"
          f"   |S| even {100*even[k]/n:6.2f}%")
print(f"\n   prediction: 'all good' acts via c=0 (=m-q); 'all bad' acts via c=m-1; mixed neither.")
