# Does the residue criterion make the ds-direction finite too?
#
# At flank b the verdict for runner a at opening k is
#     b <= a*(n k + 1) mod (n b) <= (n-1) b
# which depends on a only through  a mod (n b).  So the whole question AT FLANK b
# depends only on the residues of ds mod n*b -- a finite check over (ZMod (n b))^|ds|.
# Test that directly: perturb each runner by a multiple of n*b and confirm the verdict
# at flank b is unchanged, while a perturbation by anything else generally changes it.
import random
n = 8
def lonely_at(ds, b, k):
    m = n*k + 1
    return all(b <= (a*m) % (n*b) <= (n-1)*b for a in ds)
def flank_verdict(ds, b):          # the full k<b search AT THIS FLANK
    return tuple(lonely_at(ds,b,k) for k in range(b))

rng = random.Random(5)
same = diff = 0
for _ in range(40000):
    ds = sorted(rng.sample(range(1,60), 7))
    b  = rng.choice(ds)
    ds2 = [a + n*b*rng.randrange(-3,4) for a in ds]
    if flank_verdict(ds,b) == flank_verdict(ds2,b): same += 1
    else: diff += 1
print(f"[A] shift each runner by a multiple of n*b : verdict unchanged {same}, changed {diff}")

rng = random.Random(6)
same = diff = 0
for _ in range(40000):
    ds = sorted(rng.sample(range(1,60), 7))
    b  = rng.choice(ds)
    ds2 = [a + rng.randrange(1,n*b) for a in ds]      # NOT a multiple of n*b
    if flank_verdict(ds,b) == flank_verdict(ds2,b): same += 1
    else: diff += 1
print(f"[B] control, shift by a non-multiple       : verdict unchanged {same}, changed {diff}")

# Cost of the full finite search, and how the *number of openings that work* behaves.
rng = random.Random(7); costs=[]; wins=[]
for _ in range(20000):
    ds = sorted(rng.sample(range(1,120), 7))
    costs.append(sum(ds))
    w = sum(1 for b in ds for k in range(b) if lonely_at(ds,b,k))
    wins.append(w)
costs.sort(); wins.sort()
print(f"[C] openings to check  sum_b b : med {costs[len(costs)//2]}  max {costs[-1]}")
print(f"[D] lonely openings found      : min {wins[0]}  1% {wins[len(wins)//100]}  med {wins[len(wins)//2]}")
print(f"    sets with exactly one lonely opening: {sum(1 for w in wins if w==1)}")
