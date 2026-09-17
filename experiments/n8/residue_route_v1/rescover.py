# In residue form the question is a COVERING question.
#   At flank b, runner a blocks the openings u with  a*u mod n*b  in  [0,b) u (n*b-b, n*b).
#   The opening index enters as  u = n*k + 1,  so u runs over the residues  u = 1 mod n.
# Ask what the congruence u = 1 (mod n) actually buys: if u ranged over ALL residues
# mod n*b, would the seven blocked sets cover?
import random
n = 8
def blocked(a, b, u):
    r = (a*u) % (n*b)
    return r < b or r > (n-1)*b
rng = random.Random(21)
cong_free = allres_free = 0; tot = 0
cong_frac = []; allres_frac = []
for _ in range(20000):
    ds = sorted(rng.sample(range(1,60), 7)); b = rng.choice(ds); tot += 1
    U1 = [u for u in range(1, n*b, n)]                 # u = 1 mod n  (the real openings)
    UA = [u for u in range(1, n*b) if u % (n*b) != 0]  # all residues
    f1 = [u for u in U1 if not any(blocked(a,b,u) for a in ds)]
    fA = [u for u in UA if not any(blocked(a,b,u) for a in ds)]
    if f1: cong_free += 1
    if fA: allres_free += 1
    cong_frac.append(len(f1)/max(1,len(U1))); allres_frac.append(len(fA)/max(1,len(UA)))
print(f"flanks tested {tot}")
print(f"  free opening exists with u = 1 mod {n} : {cong_free} ({cong_free/tot:.3f})")
print(f"  free residue exists over ALL residues : {allres_free} ({allres_free/tot:.3f})")
print(f"  mean fraction free, u = 1 mod {n} : {sum(cong_frac)/tot:.4f}")
print(f"  mean fraction free, all residues  : {sum(allres_frac)/tot:.4f}")
print()
# The union-bound wall in residue form: each runner blocks 2b-1 of n*b residues.
print(f"blocked residues per runner : 2b-1 of {n}b, fraction -> 2/{n} = {2/n:.3f}")
print(f"seven runners, union bound  : 7 * 2/{n} = {7*2/n:.3f}  > 1, so the bound is vacuous")
