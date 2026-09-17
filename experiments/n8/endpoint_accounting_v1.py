"""Does 4.8's hypothesis failing mean the endpoint is NOT lonely at its own bound?

Earlier this session I reported '4.8 genuinely fails for 1,696 of 3,000 endpoints'. That is
the wrong statement twice over:
  * Theorem 4.8 is SUFFICIENT. Its hypothesis (every difference in [d_min, 7*d_min]) not
    holding says nothing about whether the runner is lonely -- only that 4.8 does not decide it.
  * 'Fails' converts 'my tool is silent' into 'the thing is absent', which is the
    deflationary move this project records as the standing failure mode.

So: of the endpoints whose differences exceed 7*d_min, how many are lonely at their own
bound 1/(8*d_min) anyway?
"""
import random
from fractions import Fraction as F

def lonely_at(V, i, t):
    return all(min((abs(V[j]-V[i]) * t) % 1, 1 - ((abs(V[j]-V[i]) * t) % 1)) >= F(1,8)
               for j in range(8) if j != i)

rng = random.Random(20260917)
D = 10000
arrs = []
while len(arrs) < 1500:
    mu_n = rng.randint(200, 1200)
    gaps = [F(rng.randint(mu_n, 2*mu_n), D) for _ in range(7)]
    mu = min(gaps)
    if sum(gaps) > 8 * mu: continue
    V = [F(1)]
    for g in gaps: V.append(V[-1] + g)
    arrs.append((V, mu, sum(gaps)))

hyp_holds = [0, 0]      # [lonely at own bound, not]
hyp_fails = [0, 0]
for V, mu, W in arrs:
    for i in (0, 7):
        ds = [abs(V[j]-V[i]) for j in range(8) if j != i]
        dmin, dmax = min(ds), max(ds)
        t = F(1,8) / dmin
        L = lonely_at(V, i, t)
        if dmax <= 7*dmin: hyp_holds[0 if L else 1] += 1
        else:              hyp_fails[0 if L else 1] += 1

print(f"endpoint runners (r_1 and r_8 of 1,500 arrangements) : {sum(hyp_holds)+sum(hyp_fails)}")
print()
print("4.8's hypothesis HOLDS (every difference in [d_min, 7 d_min]):")
print(f"   lonely at own bound 1/(8 d_min) : {hyp_holds[0]}")
print(f"   not lonely there                : {hyp_holds[1]}   <- must be 0 if 4.8 is right")
print()
print("4.8's hypothesis DOES NOT HOLD (some difference > 7 d_min):")
print(f"   lonely at own bound anyway      : {hyp_fails[0]}")
print(f"   not lonely there                : {hyp_fails[1]}")
tot = sum(hyp_fails)
if tot:
    print()
    print(f"   -> of the {tot} endpoints 4.8 does not decide, {hyp_fails[0]} "
          f"({100*hyp_fails[0]/tot:.1f}%) are lonely at their own bound regardless.")
    print("      '4.8 fails for 1,696 endpoints' was therefore wrong: 4.8 is SILENT on them,")
    print("      and silence is not absence.")

# ---------------------------------------------------------------------------
# THE BIGGER ERROR. ExistenceAt8 in LRC/Spec/Target.lean quantifies over a DIFFERENCE SET:
#
#   ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∃ s, 0 < s ∧ Lonely 8 ds s
#
# Lonely 8 ds s depends on ds ALONE. It does not know which runner of which arrangement ds
# came from, and circDist(d*s) = circDist(-d*s), so it does not know the signs either.
# "Interior runner" and "endpoint runner" are facts about an arrangement, not about ds.
#
# So a theorem of the form "the six interior runners of a tight arrangement are lonely"
# adds NOTHING to ExistenceAt8's coverage: the ds those runners carry all satisfy
# max ds <= 7 * min ds, and Theorem 4.8 already settles every such ds directly, with no
# arrangement, no regime and no counting step. The counting step only identifies WHEN a
# tight arrangement happens to produce such a ds.
#
# What actually matters for ExistenceAt8 is which ds are covered at all.
print()
print("=" * 70)
print("COVERAGE OF ExistenceAt8 BY 4.8, measured on ds directly")
rng2 = random.Random(7)
tot = cov = 0
for _ in range(20000):
    ds = sorted(F(rng2.randint(1, 20000), 1000) for _ in range(7))
    tot += 1
    if max(ds) <= 7 * min(ds): cov += 1
print(f"  random 7-element difference sets       : {tot}")
print(f"  with max <= 7*min, so settled by 4.8   : {cov}  ({100*cov/tot:.1f}%)")
print(f"  NOT settled by 4.8                     : {tot-cov}  ({100*(tot-cov)/tot:.1f}%)")
print()
print("  So the open part of ExistenceAt8 is exactly: ds with max > 7*min.")
print("  The endpoints r_1, r_8 are the runners whose ds lands there -- one side of them")
print("  carries all seven gaps -- which is why they are the outstanding pair. But the")
print("  obligation is a condition on ds, not a fact about endpoints.")
