from math import gcd
from itertools import combinations
from functools import reduce
# Derivation to test:
#   d*A mod 8e in [e,7e]  with g=gcd(d,e), d'=d/g, c=e/g
#   <=>  (d'*A) mod 8c in [c,7c]          -- depends only on (c, d' mod 8c)
#   and A=8k+1, so the constraint on k has period c.
# Hence: witness at flank e  <=>  a CRT system {k mod c_d in A_d} has a solution.

def allowed(d,e):
    """allowed residues of k modulo c = e/gcd(d,e)"""
    g=gcd(d,e); dp=d//g; c=e//g
    return c, frozenset(k for k in range(c) if c <= (dp*(8*k+1)) % (8*c) <= 7*c)

def direct(ds,e):
    return [k for k in range(e) if all(e <= (d*(8*k+1)) % (8*e) <= 7*e for d in ds)]

def viaCRT(ds,e):
    cons=[allowed(d,e) for d in ds]
    return [k for k in range(e) if all((k % c) in A for c,A in cons)]

print("STEP 1  reduction  d*A mod 8e in [e,7e]  <=>  (d'A) mod 8c in [c,7c]")
bad=0; tot=0
for e in range(1,41):
    for d in range(1,121):
        for k in range(0,e):
            A=8*k+1
            lhs = e <= (d*A)%(8*e) <= 7*e
            g=gcd(d,e); c=e//g; dp=d//g
            rhs = c <= (dp*A)%(8*c) <= 7*c
            tot+=1
            if lhs!=rhs: bad+=1
print(f"  checked {tot} (d,e,k) triples; mismatches: {bad}")

print("\nSTEP 2  the witness set at a flank IS the CRT intersection")
bad=0; tot=0
import random
random.seed(11)
sets=[]
for _ in range(400):
    while True:
        c=tuple(sorted(random.sample(range(1,46),7)))
        g=reduce(gcd,c)
        if g==1: break
    sets.append(c)
for ds in sets:
    for e in ds:
        tot+=1
        if direct(ds,e)!=viaCRT(ds,e): bad+=1
print(f"  checked {tot} (set,flank) pairs; mismatches: {bad}")

print("\nSTEP 3  when the moduli c_d are PAIRWISE COPRIME, CRT makes the six")
print("        constraints independent: a witness exists iff every A_d is nonempty.")
pc_tot=pc_pred_ok=0; npc_tot=npc_pred_ok=0
for ds in sets:
    for e in ds:
        cons=[allowed(d,e) for d in ds]
        cs=[c for c,_ in cons if c>1]
        pairwise = all(gcd(x,y)==1 for x,y in combinations(cs,2))
        all_nonempty = all(len(A)>0 for _,A in cons)
        has = len(direct(ds,e))>0
        if pairwise:
            pc_tot+=1; pc_pred_ok += (all_nonempty==has)
        else:
            npc_tot+=1; npc_pred_ok += (all_nonempty==has)
print(f"  pairwise-coprime moduli : {pc_tot:5d} flanks, rule 'all A_d nonempty <=> witness' correct {pc_pred_ok}/{pc_tot}")
print(f"  NOT pairwise coprime    : {npc_tot:5d} flanks, same rule correct {npc_pred_ok}/{npc_tot}"
      f"  ({100*npc_pred_ok/max(npc_tot,1):.1f}%)")
