"""Target: |S| >= 2, i.e. the solution set is never a singleton.

If the reflection q -> m-q maps S to itself and has no fixed point in S, then |S| is EVEN,
so non-empty implies >= 2.  clear_reflect says the reflection acts when every modulus (and m)
has residue mod 8 outside {0,1}.  Fixed points of q -> m-q on Z/m: q = 0 and q = m/2.

Measure: where does the reflection act, is |S| even there, and what happens where it does not?
"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])

tot=0; acts=0; acts_even=0; noact=0; noact_even=0
minS = Counter(); singleton = []
fixed_in_S = 0
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c in combinations(ds,5):
        bs=sorted(c); S=set(q for q in range(m) if ok(q,m,bs))
        if not S: continue
        tot+=1; minS[len(S)]+=1
        if len(S)==1: singleton.append((m,bs,S))
        reflok = all(b % 8 not in (0,1) for b in bs+[m])
        closed = {(m-q)%m for q in S} == S
        fx = {q for q in S if (m-q)%m == q}
        if reflok:
            acts+=1
            if len(S)%2==0: acts_even+=1
            if fx: fixed_in_S += 1
        else:
            noact+=1
            if len(S)%2==0: noact_even+=1
print(f"divisor-closed profiles with a witness, m < 240 : {tot:,}")
print(f"  |S| distribution (smallest six): {dict(sorted(minS.items())[:6])}")
print(f"  singletons |S| = 1 : {len(singleton)}\n")
print(f"  reflection acts (all b,m mod 8 not in {{0,1}}) : {acts:,}")
print(f"     of those, |S| even : {acts_even:,}  ({100*acts_even/max(acts,1):.2f}%)")
print(f"     of those, a fixed point lies in S : {fixed_in_S:,}")
print(f"  reflection does NOT act : {noact:,}")
print(f"     of those, |S| even : {noact_even:,}  ({100*noact_even/max(noact,1):.2f}%)")
