"""The exceptional profiles: what is happening and why.

  A = no witness lies on BOTH patterns (some b with q%b=L(b) AND some b' with q%b'=U(b'))
  B = no witness has TWO tight constraints
Measured earlier as 2.99% and 1.615%.  (A previous 'distinct moduli' count conflated the two;
redone cleanly here.)

First observation to test: I(b) = [ceil((b-1)/8), floor((7b-1)/8)] is a SINGLE point only at b=2.
A modulus with L=U supplies both patterns at once -- so any profile containing b=2 cannot be in A.
"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])

degen = [b for b in range(2, 500) if I(b)[0] == I(b)[1]]
print(f"moduli with L(b) = U(b), b < 500 : {degen}\n")

A=[]; B=[]; tot=0
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c in combinations(ds,5):
        bs=sorted(c); S=[q for q in range(m) if ok(q,m,bs)]
        if not S: continue
        tot+=1
        inA = not any(any(q%b==I(b)[0] for b in bs+[m]) and any(q%b==I(b)[1] for b in bs+[m])
                      for q in S)
        inB = not any(sum(1 for b in bs+[m] if q%b in I(b)) >= 2 for q in S)
        if inA: A.append((m,bs,S))
        if inB: B.append((m,bs,S))
print(f"profiles {tot:,}   A (no both-pattern witness) {len(A):,} ({100*len(A)/tot:.2f}%)"
      f"   B (no doubly-tight witness) {len(B):,} ({100*len(B)/tot:.2f}%)")
print(f"  A and B overlap: {len(set((m,tuple(b)) for m,b,_ in A) & set((m,tuple(b)) for m,b,_ in B))}\n")

def feat(pop, lab):
    has2 = sum(1 for m,bs,_ in pop if 2 in bs)
    nsol = Counter(len(S) for _,_,S in pop)
    print(f"  {lab}: contains modulus 2 in {has2}/{len(pop)} ({100*has2/max(len(pop),1):.1f}%)")
    print(f"     witness-count distribution: {dict(sorted(nsol.items())[:6])}")
feat(A, "A")
feat(B, "B")
print()
print("PREDICTION: 2 in bs  =>  every witness is on both patterns  =>  profile NOT in A.")
bad = sum(1 for m,bs,_ in A if 2 in bs)
print(f"  profiles in A that DO contain modulus 2 : {bad}   (prediction says 0)")
