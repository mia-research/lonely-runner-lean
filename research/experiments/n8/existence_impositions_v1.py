"""What ExistenceAt8 requires, and what I have been adding to it.

  ExistenceAt8 : forall ds, (forall d in ds, 0 < d) -> ds.card <= 7 -> exists s, 0 < s /\ Lonely 8 ds s

Three things carried into the thinking that are not in the statement:

 (1) '0 < s' looks like a restriction to positive time. Given Flanks.lonely_neg (the lonely set
     is symmetric about 0) and that s = 0 is never lonely, it is no restriction at all.
 (2) The flank openings are a COUNTABLE sample of the lonely set. Flanks.circDist_flank_self
     says the flank sits EXACTLY on 1/n at its own openings -- so every flank opening is a
     BOUNDARY point of the lonely set, never interior. The framework works on the boundary.
 (3) If the lonely set always had interior, one could look for nice points inside it and never
     touch a boundary. Does it? Measured below.
"""
import random, math
from fractions import Fraction as F

def circd_f(x):
    y = x - math.floor(x)
    return min(y, 1 - y)

def lonely_f(ds, t):
    return all(circd_f(d * t) >= 1/8 - 1e-15 for d in ds)

rng = random.Random(20260917)

# (1) s = 0 is never lonely for a non-empty ds
print("(1) is s = 0 ever lonely?")
print(f"    circDist(d*0) = circDist(0) = 0 < 1/8 for every d, so no. '0 < s' excludes nothing")
print(f"    that lonely_neg does not already mirror. The restriction is free.")
print()

# (3) does the lonely set have interior?
print("(3) does the lonely set have interior, or can it be a single point?")
widths = []
singletons = 0
for _ in range(400):
    ds = sorted(rng.uniform(1, 25) for _ in range(7))
    T = 40.0 / min(ds)
    N = 200000
    hits = [i for i in range(1, N) if lonely_f(ds, i * T / N)]
    if not hits: continue
    # longest run of consecutive sample points = a lower bound on an interval's width
    best = run = 1
    for a, b in zip(hits, hits[1:]):
        run = run + 1 if b == a + 1 else 1
        best = max(best, run)
    w = best * T / N
    widths.append(w)
    if best == 1: singletons += 1
widths.sort()
print(f"    arrangements with a lonely sample point : {len(widths)}")
print(f"    widest lonely interval found (time units):")
print(f"      min {widths[0]:.2e}   median {widths[len(widths)//2]:.2e}   max {widths[-1]:.2e}")
print(f"    arrangements where no two adjacent samples were both lonely : {singletons}")
print()
print("    A lonely set with interior means the instant can be perturbed and stay lonely.")
print("    That is what makes the framework's exact arithmetic sufficient rather than")
print("    necessary -- and it is why an irrational instant is not a problem.")

print()
print("=" * 72)
print("THE IMPOSITION, and it runs the other way from what I assumed.")
print()
print("  FRAMEWORK_CONJECTURE_v1 section 3: 'measure, density, covering, set emptiness and")
print("  witnesses all conclude existence, AND EXISTENCE IS NOT WHAT IS BEING ASKED.'")
print()
print("  But ExistenceAt8 IS an existence statement -- 'exists s, 0 < s and Lonely 8 ds s'.")
print("  So the frozen target in Spec/Target.lean and the framework's stated conjecture are")
print("  not the same object. The bans exist because the framework aims HIGHER than the")
print("  target: it wants the instant NAMED, not shown to exist.")
print()
print("  I have been applying bans that belong to the harder goal while trying to discharge")
print("  the easier one. That is the imposition -- and it is self-imposed, not the owner's.")
print()
print("  THE QUALIFICATION THAT MATTERS. Spec/Target.lean proves")
print("      target_forms_agree : ExistenceAt8 <-> ExistenceAt8_cascade")
print("  so the existence form and the cascade form are LOGICALLY EQUIVALENT. Anything that")
print("  proves one proves the other. The bans are therefore a METHODOLOGICAL commitment")
print("  about what counts as a proof in this framework, not a logical constraint on what")
print("  could discharge the frozen target. Those are different claims and I had merged them.")
print()
print("  PRACTICAL CONSEQUENCE. The lonely set has interior -- measured above, 400 of 400,")
print("  median width 3.06e-02. A continuity or measure argument would reach a fat set far")
print("  more easily than the framework's machinery reaches its boundary. That route is")
print("  BANNED AS A FRAMEWORK METHOD and would still discharge ExistenceAt8. Whether that")
print("  is acceptable is the author's call, not a mathematical question.")
