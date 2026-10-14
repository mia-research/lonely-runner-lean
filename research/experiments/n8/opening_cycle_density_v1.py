"""k = 0 is a point on a cycle, not a beginning.

Flanks.circDist_periodic_of_int_flank: at a whole-number flank e the verdict is PERIODIC in k
with period e. So the openings are a CYCLE of length e, and "the first opening", "the bound",
"a later opening" all measure an arc from an arbitrary origin.

Everything this session measured was an arc: "k=0 settles 50.4%", "k<=2 settles 91.2%", the
census split 1,341 "at the bound" against 3,072 "later", "the required k is unbounded".

The question the structure poses is not how far to the first clear opening. It is HOW MUCH OF
THE CYCLE IS CLEAR. Existence at a flank is that set being non-empty; a lower bound on its
density would be a far stronger statement than a bound on the first hit.
"""
import random
from fractions import Fraction as F

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def clear_at(ds, e, k):
    return all(circd(d * (F(k) + F(1, 8)) / e) >= F(1, 8) for d in ds)

rng = random.Random(20260917)
rows = []
for _ in range(600):
    ds = sorted({F(x) for x in rng.sample(range(1, 60), 7)})
    for e in ds:
        P = int(e)                      # the period at a whole-number flank
        clear = [k for k in range(P) if clear_at(ds, e, k)]
        rows.append((len(ds), int(e), P, len(clear), clear[0] if clear else None))

nonempty = [r for r in rows if r[3] > 0]
empty    = [r for r in rows if r[3] == 0]
dens = sorted(r[3] / r[2] for r in nonempty)
print(f"(arrangement, flank) pairs        : {len(rows)}")
print(f"  cycles with NO clear opening    : {len(empty)}  ({100*len(empty)/len(rows):.1f}%)")
print(f"  cycles with at least one        : {len(nonempty)}")
print()
print("density of CLEAR openings on the cycle, where non-empty:")
print(f"  min {dens[0]:.4f}   10th {dens[len(dens)//10]:.4f}   median {dens[len(dens)//2]:.4f}"
      f"   90th {dens[9*len(dens)//10]:.4f}   max {dens[-1]:.4f}")
print()
print("the SAME data read as an arc from k = 0, which is how this session reported it:")
firsts = sorted(r[4] for r in nonempty)
print(f"  first clear opening: min {firsts[0]}  median {firsts[len(firsts)//2]}"
      f"  90th {firsts[9*len(firsts)//10]}  max {firsts[-1]}")
print()
print("Both describe the same cycles. The density is a property OF the cycle; the first hit")
print("is a property of the cycle AND of where you decided to start counting.")

print()
print("=" * 72)
print("WHAT THE REFRAMING CHANGES")
print()
print("  Read as an arc: 'the first clear opening is at median 3, and the required k is")
print("  UNBOUNDED -- a hill-climb reached 369'. That unboundedness is across arrangements")
print("  with different periods. WITHIN an arrangement k < P always, because the verdict")
print("  repeats. So 'k is unbounded' was measuring the origin, not the object.")
print()
print("  Read as a cycle: 5.5% of (arrangement, flank) cycles have NO clear opening -- the")
print("  flank is shadowed. Where a flank is free at all, roughly a FIFTH of its cycle is")
print("  clear (median 18.9%, 10th percentile 11.5%). The clear set is not a needle.")
print()
print("  These are the same 4,200 cycles. The density is a property OF the cycle; the first")
print("  hit is a property of the cycle AND of where counting began.")
print()
print("  The 5.5% are the same phenomenon as the d_min flank saturating below 100% measured")
print("  earlier (89.0% integer, 75.8% small-denominator): a shadowed flank is an EMPTY")
print("  cycle, not a distant first hit. No amount of searching further reaches it, which is")
print("  why widening the search never helped and choosing another flank always did.")
print()
print("  So the statement to aim at is not 'the first clear opening is near'. It is that the")
print("  clear sets of a runner's flanks are not ALL empty -- which is section 4.6's own open")
print("  item, 'not every flank of a runner can be shadowed at once', in cycle language.")
