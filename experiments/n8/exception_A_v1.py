"""A = no witness on both patterns, and A never contains modulus 2.  But A-profiles have MANY
witnesses (12-20), so scarcity is not the cause.  What distinguishes A?"""
from itertools import combinations
from collections import Counter
from math import gcd

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])

A=[]; rest=[]
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c in combinations(ds,5):
        bs=sorted(c); S=[q for q in range(m) if ok(q,m,bs)]
        if not S: continue
        inA = not any(any(q%b==I(b)[0] for b in bs+[m]) and any(q%b==I(b)[1] for b in bs+[m])
                      for q in S)
        (A if inA else rest).append((m,bs,S))

def prof(pop, lab):
    r8 = Counter(); parity = Counter(); minb = Counter(); nm = Counter()
    for m,bs,S in pop:
        for b in bs: r8[b % 8] += 1; parity['even' if b%2==0 else 'odd'] += 1
        minb[min(bs)] += 1
        nm[m % 8] += 1
    n = sum(r8.values())
    print(f"  {lab} ({len(pop):,} profiles)")
    print(f"     b mod 8 : " + " ".join(f"{k}:{100*v/n:4.1f}%" for k,v in sorted(r8.items())))
    t = sum(parity.values())
    print(f"     parity  : even {100*parity['even']/t:.1f}%  odd {100*parity['odd']/t:.1f}%")
    print(f"     min b   : " + " ".join(f"{k}:{100*v/len(pop):4.1f}%" for k,v in sorted(minb.items())[:6]))
    s = sum(nm.values())
    print(f"     m mod 8 : " + " ".join(f"{k}:{100*v/s:4.1f}%" for k,v in sorted(nm.items())))
prof(A, "A  (no both-pattern witness)")
print()
prof(rest, "rest")
print()
# the sharp test: does A require ALL moduli to have L != U and something else?
allev = sum(1 for m,bs,_ in A if all(b%2==0 for b in bs))
allev_r = sum(1 for m,bs,_ in rest if all(b%2==0 for b in bs))
print(f"  all moduli even: A {100*allev/len(A):.1f}%   rest {100*allev_r/len(rest):.1f}%")
min4 = sum(1 for m,bs,_ in A if min(bs) >= 4)
min4_r = sum(1 for m,bs,_ in rest if min(bs) >= 4)
print(f"  min modulus >= 4: A {100*min4/len(A):.1f}%   rest {100*min4_r/len(rest):.1f}%")
min3 = sum(1 for m,bs,_ in A if min(bs) >= 3)
min3_r = sum(1 for m,bs,_ in rest if min(bs) >= 3)
print(f"  min modulus >= 3: A {100*min3/len(A):.1f}%   rest {100*min3_r/len(rest):.1f}%")
