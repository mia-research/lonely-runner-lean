"""Adversarial search: can an arrangement have NO free flank?

Flanks.lonely_iff_exists_flank is an iff, so an arrangement with no free flank is an
arrangement with NO lonely instant -- a counterexample to Existence at 8, and to LRC at 8.
Rosenfeld 2025 verified n=8 computationally, so none should exist; this is a check of OUR
reading of the obligation, not of the conjecture.  If this search found one, the flank
reading would be wrong, not LRC.

Integer arrangements only: ratios are rational, so one full period DECIDES each flank.
Hill-climbing with restarts on the objective 'number of free flanks' (minimise).
"""
import math, random
from fractions import Fraction

n = 8
TH = Fraction(1, n)

def circ_q(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def flank_free(ds, e, cap=400000):
    others = [d for d in ds if d != e]
    rs = [Fraction(d, e) for d in others]
    fr = [r - (r.numerator // r.denominator) for r in rs]
    per = 1
    for f in fr:
        per = per * f.denominator // math.gcd(per, f.denominator)
    if per > cap:
        return None
    for k in range(per):
        if all(circ_q(k * f + r / n) >= TH for f, r in zip(fr, rs)):
            return k
    return False                                   # decided: shadowed

def score(ds):
    """(#free flanks, total margin) - lower is 'more shadowed'. None if undecided."""
    free = 0
    for e in ds:
        r = flank_free(ds, e)
        if r is None:
            return None
        if r is not False:
            free += 1
    return free

random.seed(20260917)
best_overall = (99, None)
hist = {}
RESTARTS, STEPS, HI = 400, 160, 60
for _ in range(RESTARTS):
    ds = sorted(random.sample(range(1, HI + 1), 7))
    cur = score(ds)
    if cur is None:
        continue
    for _ in range(STEPS):
        i = random.randrange(7)
        cand = list(ds)
        cand[i] = random.randint(1, HI)
        if len(set(cand)) != 7 or min(cand) < 1:
            continue
        cand = sorted(cand)
        s = score(cand)
        if s is not None and s <= cur:
            ds, cur = cand, s
    hist[cur] = hist.get(cur, 0) + 1
    if cur < best_overall[0]:
        best_overall = (cur, tuple(ds))

print(f"hill-climb restarts               : {RESTARTS}  (7 integers from [1,{HI}], {STEPS} steps each)")
print(f"final free-flank counts reached   : {dict(sorted(hist.items()))}")
print(f"BEST (fewest free flanks) found   : {best_overall[0]}   {best_overall[1]}")
print()
if best_overall[0] == 0:
    print("*** ZERO free flanks found -- this would refute Existence at 8. VERIFY BY HAND. ***")
else:
    print(f"No arrangement with zero free flanks was reached. The search bottoms out at "
          f"{best_overall[0]}.")
    print("That is EVIDENCE about the search, not a proof: hill-climbing can miss an isolated")
    print("minimum, and this ranges over integers in a bounded window only.")
