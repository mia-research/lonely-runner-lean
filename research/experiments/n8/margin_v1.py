"""SHRINK DEPTH. Shrink every clear interval by j on each side: [L+j, U-j].
Existence is 'depth >= 0 solvable'.  How much slack is there really?

If the minimum depth over all profiles is >= 1, existence has margin -- and a margin statement
is often easier to prove than bare non-emptiness, because it survives perturbation.
"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def solvable(m, bs, j):
    for q in range(m):
        if all(I(b)[0]+j <= q % b <= I(b)[1]-j for b in bs+[m]): return True
    return False
def depth(m, bs):
    j = 0
    while solvable(m, bs, j+1): j += 1
    return j

tot=0; d=Counter(); worst=None
for m in range(24, 200):
    ds=[d_ for d_ in range(2,m) if m%d_==0]
    if len(ds)<5: continue
    for c in combinations(ds,5):
        bs=sorted(c)
        if not solvable(m, bs, 0): continue
        tot+=1
        k = depth(m, bs)
        d[k]+=1
        if worst is None or k < worst[0]: worst=(k,m,bs)
print(f"divisor-closed profiles with a witness, m < 200 : {tot:,}\n")
print(f"  shrink depth (largest j with [L+j, U-j] still solvable):")
for k,v in sorted(d.items()):
    print(f"     j = {k:<3} {v:>8,}  ({100*v/tot:6.2f}%)")
print(f"\n  MINIMUM depth over all profiles : {worst[0]}   at m={worst[1]} b={worst[2]}")
print(f"  => existence holds with a margin of at least {worst[0]} residue(s) on every profile.")
