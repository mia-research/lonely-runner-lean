# Discovery curve: how many distinct RESULTS (path signatures) appear as the sample grows, per family of arrangements.
# Results: full = ((setter rank, lap), ...); coarse = setter ranks only.  If the curve flattens, the family has a finite list of results.
import sys, random, math
from fractions import Fraction as F
from collections import Counter
sys.argv = [sys.argv[0]]
exec(open('result_classes_v1.py').read().split('fams = [')[0].replace("rnd = random.Random(319)", "rnd = random.Random(320)"))
def fam_int():
    while True:
        xs = sorted(rnd.sample(range(1, 41), 7))
        if xs[-1] > 7 * xs[0] or rnd.random() < 0.3: return [F(x) for x in xs]
def fam_rational():
    while True:
        xs = sorted({F(rnd.randint(1, 40), rnd.choice((1, 2, 3, 4, 5, 6, 7))) for _ in range(7)})
        if len(xs) == 7: return xs
def fam_scaled_ap():
    c = F(rnd.randint(1, 12)); xs = [c * k + F(rnd.randint(-30, 30), 100) * rnd.choice((0, 1)) for k in range(1, 8)]
    xs = sorted(xs); return xs if len(set(xs)) == 7 and xs[0] > 0 else fam_scaled_ap()
def fam_near_chain():
    # readings in a 9/7-ish chain: each next reading about (7/9..1) of the previous, around a slot band
    top = q(rnd.uniform(7.0, 9.5)); xs = [top]
    for _ in range(6): xs.append(xs[-1] * q(rnd.uniform(0.55, 0.95)))
    xs = sorted(xs); xs = [x / xs[0] for x in xs]; return xs if len(set(xs)) == 7 else fam_near_chain()
fams2 = [("random", fam_random), ("AP deformed", fam_ap_def), ("grid+laps", fam_grid_laps), ("clump", fam_clump),
         ("integers<=40", fam_int), ("rational", fam_rational), ("scaled AP", fam_scaled_ap), ("near-chain", fam_near_chain)]
print("%-14s %s" % ("family", "distinct coarse results after n = 100, 200, 400, 800, 1600 arrangements   |  full results at 1600  |  max moves"))
for name, f in fams2:
    seen = set(); seen_full = set(); out = []; mx = 0
    for n in range(1, 1601):
        sig, Rend, rhos = signature(f()); seen.add(tuple(s[0] for s in sig)); seen_full.add(sig); mx = max(mx, len(sig))
        if n in (100, 200, 400, 800, 1600): out.append(len(seen))
    print("%-14s %-48s | %4d | %d" % (name, out, len(seen_full), mx))
