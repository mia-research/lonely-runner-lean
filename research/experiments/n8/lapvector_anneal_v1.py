"""Anneal integer 8-sets to minimise  min_i margin(V,i).
margin < 0 for any runner = counterexample to the first-interval claim.
The AP (1..8) sits at exactly 0, so the claim is tight and the search starts there.
"""
import random, sys
from fractions import Fraction as F
from lapvector_margin_v1 import margin
from lapvector_decide_v1 import diffs

SPAN = int(sys.argv[1]); ITERS = int(sys.argv[2]); SEED = int(sys.argv[3])
random.seed(SEED)

def score(V):
    return min(margin(sorted(diffs(V, i)))[0] for i in range(8))

def rand_set():
    return sorted(random.sample(range(0, SPAN+1), 8))

best_overall = None
for restart in range(40):
    V = sorted(range(8)) if restart == 0 else rand_set()
    s = score(V)
    T0 = F(1,50)
    for it in range(ITERS):
        T = T0 * F(ITERS - it, ITERS) + F(1,100000)
        W = list(V)
        j = random.randrange(8)
        W[j] += random.choice((-3,-2,-1,1,2,3))
        if W[j] < 0 or W[j] > SPAN or len(set(W)) < 8:
            continue
        W = sorted(W)
        s2 = score(W)
        if s2 <= s or random.random() < 0.02:
            V, s = W, s2
        if best_overall is None or s < best_overall[0]:
            best_overall = (s, tuple(V))
            if s < 0:
                print("COUNTEREXAMPLE", V, float(s)); sys.exit(0)
print("best min-margin found:", float(best_overall[0]), best_overall[0], best_overall[1])
