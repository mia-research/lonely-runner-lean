"""Is 'the endpoints are the hard pair' a real structure, or an artefact of the regime?

Owner: r_1 being the slowest is a CONVENTION; the ordering can be reversed, and any runner
can sit at the r_1 position.

I claimed the runners whose difference set has max > 7*min -- the ds NOT settled by Theorem
4.8 -- are 'the endpoints r_1, r_8, because one side of them carries all seven gaps'. That
was measured only in the tight regime 7*mu < W <= 8*mu. Section 4.6 says the short gap
MIGRATES: 'Beyond W = 8*mu the short gap moves into the interior as runners cross.'

So: over general arrangements, which speed-ranks carry a ds with max > 7*min?
If it is spread across ranks, 'endpoints' is not the structure; it is the convention.
"""
import random
from fractions import Fraction as F

rng = random.Random(20260917)

def ranks_not_covered(V):
    out = []
    for i in range(8):
        ds = [abs(V[j]-V[i]) for j in range(8) if j != i]
        if max(ds) > 7 * min(ds):
            out.append(i)
    return out

for label, gen, N in [
    ("tight  7mu < W <= 8mu", None, 1500),
    ("general integer speeds", "int", 1500),
    ("general real speeds",    "real", 1500),
]:
    rank_hist = {i: 0 for i in range(8)}
    tot_arr = 0; tot_hard = 0
    made = 0
    while made < N:
        if gen is None:
            mu_n = rng.randint(200, 1200)
            gaps = [F(rng.randint(mu_n, 2*mu_n), 10000) for _ in range(7)]
            if sum(gaps) > 8 * min(gaps): continue
            V = [F(1)]
            for g in gaps: V.append(V[-1] + g)
        elif gen == "int":
            V = sorted(F(x) for x in rng.sample(range(1, 200), 8))
        else:
            cand = sorted({F(rng.randint(1, 100000), 1000) for _ in range(8)})
            if len(cand) != 8: continue
            V = cand
        made += 1; tot_arr += 1
        hard = ranks_not_covered(V)
        tot_hard += len(hard)
        for i in hard: rank_hist[i] += 1
    print(f"{label}:  {tot_arr} arrangements, {tot_hard} runners with max > 7*min")
    print("   by speed-rank r_1..r_8 : " + "  ".join(f"{rank_hist[i]:>5}" for i in range(8)))
    ends = rank_hist[0] + rank_hist[7]
    print(f"   at the two extremes    : {ends} / {tot_hard}  "
          f"({100*ends/max(tot_hard,1):.1f}%)")
    print()

print("READING.")
print("  Tight regime: 100% of the hard difference sets sit at the two extremes.")
print("  General arrangements: only ~21% do -- and if rank were irrelevant the figure")
print("  would be 25%, so the extremes are slightly UNDER-represented, not over. Ranks 2")
print("  and 7 carry the most (1190, 1202) against 898 and 927 at the extremes.")
print()
print("  So 'the endpoints r_1, r_8 are where the hard ds arise' is a fact about the TIGHT")
print("  regime only, and I stated it generally. Section 4.6 already says why: 'Beyond")
print("  W = 8*mu the short gap moves into the interior as runners cross.' Once it has")
print("  migrated, every rank carries hard sets and rank is exactly the convention the")
print("  owner called it.")
print()
print("  What survives: ExistenceAt8 depends on ds alone, so rank was never a property of")
print("  the object in the first place -- which is the same reason 'interior runner' could")
print("  not extend its coverage.")
