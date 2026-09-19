"""The question the false claim hid: can an ARRANGEMENT realise, at one flank,
two half-movers on OPPOSITE parities plus a third mover of denominator >= 5?

Half-mover: d_j/e has fractional part 1/2, i.e. 2 d_j = (2w+1) e.
Blocks even k iff w mod 8 in {0,7}; odd k iff w mod 8 in {3,4}; neither otherwise.
"""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)
def whole(r): return r.numerator // r.denominator

def parity_blocked(w):
    if w % 8 in (0, 7): return 'even'
    if w % 8 in (3, 4): return 'odd'
    return None

rng = random.Random(20260919)
stats = Counter(); examples = []
tot_flanks = 0
for _ in range(30000):
    v = sorted(rng.sample(range(0, 600), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        for e in ds:
            if e == 0: continue
            ae = abs(e); ratios = [F(d, ae) for d in ds]
            if any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios): continue
            movers = [r for r in ratios if r.denominator != 1]
            tot_flanks += 1
            halves = [r for r in movers if frac(r) == F(1,2)]
            pars = [parity_blocked(whole(r)) for r in halves]
            opp = ('even' in pars) and ('odd' in pars)
            hi = [r for r in movers if frac(r).denominator >= 5]
            stats[('two halves opposite parity', opp)] += 1
            if opp:
                stats[('  ... and a denominator>=5 mover', bool(hi))] += 1
                if hi and len(examples) < 5:
                    examples.append((v, i, ae, [str(frac(r)) for r in movers]))
print(f"live flanks examined: {tot_flanks:,}\n")
a = stats[('two halves opposite parity', True)]
print(f"  flanks with two half-movers on OPPOSITE parities : {a:,}"
      f"  ({100*a/tot_flanks:.3f}%)")
b = stats[('  ... and a denominator>=5 mover', True)]
print(f"     of those, also carrying a denominator>=5 mover: {b:,}")
if examples:
    print(f"\n  EXISTS -- examples:")
    for v,i,e,fs in examples: print(f"     v={v} subject {i} flank e={e}  fracs {fs}")
else:
    print(f"\n  NOT FOUND in this sample -- a possible arrangement-level constraint.")
