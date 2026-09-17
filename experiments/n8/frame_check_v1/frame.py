# Does the FORMAL statement compute the same thing as the CONJECTURE?
# Tested directly, not by reading the reduction.
#
# Conjecture, n=8: 8 runners, distinct constant speeds, circle of circumference 1.
#   For EACH runner k there is a time t with |pos_i(t) - pos_k(t)| >= 1/8 on the circle
#   for every i != k.
#
# Formal statement: ExistenceAt8 = for every Finset ds of <= 7 positive reals,
#   exists s > 0 with circDist(d*s) >= 1/8 for all d in ds.
import random
from fractions import Fraction as F
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)

def direct_lonely(vs, k, T):
    """Conjecture form: runner k's best min-distance to the OTHERS, over a grid of times."""
    best = F(0)
    for t in T:
        m = min(circ((vs[i]-vs[k])*t) for i in range(len(vs)) if i != k)
        if m > best: best = m
    return best

def formal_lonely(vs, k, T):
    """Formal form: build ds = {|v_i - v_k|} as a SET of positive reals, then min over ds."""
    ds = sorted({abs(vs[i]-vs[k]) for i in range(len(vs)) if i != k})
    assert all(d > 0 for d in ds) and len(ds) <= 7
    best = F(0)
    for t in T:
        m = min(circ(d*t) for d in ds)
        if m > best: best = m
    return best, ds

rng = random.Random(3)
mismatch = 0; trials = 0; cards = {}
worst = None
for _ in range(400):
    vs = sorted(random.Random(rng.random()).sample(range(1, 80), 8))
    # grid over a common period: all differences are integers, so period 1 in t suffices
    T = [F(a, 240) for a in range(1, 241)]
    for k in range(8):
        a = direct_lonely(vs, k, T)
        b, ds = formal_lonely(vs, k, T)
        trials += 1
        cards[len(ds)] = cards.get(len(ds), 0) + 1
        if a != b: mismatch += 1
        if worst is None or b < worst[0]: worst = (b, vs, k)
print(f"[A] (config, runner) pairs tested : {trials}")
print(f"    conjecture form vs formal form disagree : {mismatch}")
print(f"    difference-set sizes seen : {dict(sorted(cards.items()))}")
print(f"    smallest best-distance found : {float(worst[0]):.6f}  (>= 1/8 = 0.125 required)")

# [B] Is the cascade's starting bound 1/(8*m) principled -- can a lonely time lie BELOW it?
below = 0; checked = 0
rng2 = random.Random(9)
for _ in range(3000):
    ds = sorted(rng2.sample(range(1, 60), 7))
    m = min(ds); start = F(1, n*m)
    checked += 1
    # sample times strictly below the bound
    for j in range(1, 60):
        t = start * F(j, 60)
        if all(circ(F(d)*t) >= F(1,n) for d in ds): below += 1; break
print(f"[B] difference sets checked : {checked}; lonely instants found BELOW 1/(8*m) : {below}")
# and the bound itself: is the slowest runner exactly ON the boundary there?
ok = sum(1 for _ in range(1) )
vals = set()
for _ in range(3000):
    ds = sorted(rng2.sample(range(1, 60), 7)); m = min(ds)
    vals.add(circ(F(m) * F(1, n*m)))
print(f"    circDist(m * 1/(8m)) over 3000 sets : {sorted(float(v) for v in vals)}  (1/8 exactly = boundary)")
