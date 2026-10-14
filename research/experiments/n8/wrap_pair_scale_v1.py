"""Does the wrap pair get its own instant, and is the six-of-eight result new?

Regime 7*mu < W <= 8*mu. At t = 1/(8*mu) exactly six runners are lonely; the short pair is
(r_1, r_8). Two questions:

 (a) do r_1 and r_8 each have a lonely instant of their own, and where;
 (b) are the six already covered by Theorem 4.8 (every difference in [d_min, 7*d_min] is
     clear at 1/(8*d_min))? If not, the six-of-eight result is new content, not 4.8 applied
     runner by runner.
"""
import random, math
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

six_by_48 = 0; six_tot = 0
wrap_found = {0: 0, 7: 0}; wrap_tot = 0
wrap_t = []
for V, mu, W in arrs:
    for i in range(8):
        ds = [abs(V[j]-V[i]) for j in range(8) if j != i]
        dmin = min(ds); dmax = max(ds)
        if i in (0, 7):
            wrap_tot += 1
            # search this runner's own openings for a lonely instant
            found = None
            for k in range(0, 4000):
                t = (F(k) + F(1,8)) / dmin
                if t > 0 and lonely_at(V, i, t):
                    found = t; break
            if found is not None:
                wrap_found[i] += 1
                wrap_t.append(float(found * dmin))     # in units of the runner's own bound
        else:
            six_tot += 1
            if dmax <= 7 * dmin: six_by_48 += 1

print(f"arrangements (7*mu < W <= 8*mu)            : {len(arrs)}")
print()
print("(b) are the six covered by Theorem 4.8?")
print(f"  interior runners (r_2..r_7)              : {six_tot}")
print(f"  with every difference in [d_min, 7 d_min]: {six_by_48}  ({100*six_by_48/six_tot:.1f}%)")
print(f"  -> {'4.8 covers them; not new' if six_by_48 == six_tot else 'NOT covered by 4.8 alone -- the gap/circle argument is doing the work'}")
print()
print("(a) does the wrap pair get its own instant?")
print(f"  r_1 instances                            : {wrap_tot//2}, lonely instant found: {wrap_found[0]}")
print(f"  r_8 instances                            : {wrap_tot//2}, lonely instant found: {wrap_found[7]}")
if wrap_t:
    wrap_t.sort()
    print(f"  its instant in units of its own bound 1/(8 d_min):")
    print(f"    min {wrap_t[0]*8:.2f}/8   median {wrap_t[len(wrap_t)//2]*8:.2f}/8   max {wrap_t[-1]*8:.2f}/8")

# ---------------------------------------------------------------------------
# The 3 r_1 cases with no instant found are suspect: the search ran to 4,000 openings and
# the observed maximum was 2,481, so a case needing more would be missed. Re-run those with
# a far larger bound before treating the null as a finding.
print()
print("=" * 66)
print("RE-TESTING the r_1 cases where no instant was found")
missing = []
for V, mu, W in arrs:
    i = 0
    ds = [abs(V[j]-V[i]) for j in range(8) if j != i]
    dmin = min(ds)
    if not any(lonely_at(V, i, (F(k) + F(1,8))/dmin) for k in range(0, 4000)):
        missing.append((V, dmin))
still = []
for V, dmin in missing:
    found = None
    for k in range(0, 200000):
        if lonely_at(V, 0, (F(k) + F(1,8))/dmin):
            found = k; break
    if found is None: still.append(V)
    else: print(f"    cleared at opening k = {found}")
print(f"  re-tested : {len(missing)}    still none : {len(still)}")
if not still:
    print("  -> search-bound artefact again. Every wrap-pair runner has its own instant.")

# ---------------------------------------------------------------------------
# The three survived a 200,000-opening search on r_1's OWN d_min lattice. That is one
# lattice. Flanks.lonely_iff_exists_flank is an IFF: the subject is lonely somewhere iff it
# is lonely at some opening of SOME difference e, not just the smallest. Search that.
if still:
    print()
    print("=" * 66)
    print("SEARCHING ALL FLANK OPENINGS (lonely_iff_exists_flank is an iff)")
    for V in still:
        i = 0
        ds = sorted(abs(V[j]-V[i]) for j in range(8) if j != i)
        hit = None
        for e in ds:
            for k in range(0, 8000):
                t = (F(k) + F(1,8)) / e
                if lonely_at(V, i, t):
                    hit = (e, k, t); break
            if hit: break
        sp = [str(v) for v in V]
        if hit:
            e, k, t = hit
            print(f"  FOUND  flank e={e}  opening k={k}   speeds {sp}")
        else:
            print(f"  none on any flank to k=8000  speeds {sp}")

# ---------------------------------------------------------------------------
# THE ARGUMENT behind (b), checked step by step, because it is what a Lean proof would use.
#
#   Interior runner k (2 <= k <= 7) has at most 6 gaps on either side of it.
#   A side carrying m gaps sums to  W - (sum of the other 7-m gaps) <= W - (7-m)*mu.
#   With W <= 8*mu and m <= 6 this is <= (1+m)*mu <= 7*mu.
#   And d_min(k) = min(a_{k-1}, a_k) >= mu.
#   So d_max(k) <= 7*mu <= 7*d_min(k), and Theorem 4.8 applies.
#
#   For r_1 and r_8 one side carries ALL SEVEN gaps: d_max = W <= 8*mu, ratio up to 8.
#   That is exactly why the endpoints fall outside 4.8 and the interior does not.
print()
print("=" * 66)
print("CHECKING THE ARGUMENT STEP BY STEP")
ok_side = ok_ratio = tot_int = 0
end_ratio_gt7 = end_tot = 0
for V, mu, W in arrs:
    gaps = [V[k+1]-V[k] for k in range(7)]
    for i in range(8):
        ds = [abs(V[j]-V[i]) for j in range(8) if j != i]
        dmin, dmax = min(ds), max(ds)
        if i in (0, 7):
            end_tot += 1
            if dmax > 7*dmin: end_ratio_gt7 += 1
        else:
            tot_int += 1
            if dmax <= 7*mu: ok_side += 1
            if dmax <= 7*dmin: ok_ratio += 1
print(f"  interior runners                       : {tot_int}")
print(f"    d_max <= 7*mu   (the counting step)  : {ok_side}")
print(f"    d_max <= 7*d_min (so 4.8 applies)    : {ok_ratio}")
print(f"  endpoint runners r_1, r_8              : {end_tot}")
print(f"    d_max > 7*d_min (4.8 does NOT apply) : {end_ratio_gt7}")
