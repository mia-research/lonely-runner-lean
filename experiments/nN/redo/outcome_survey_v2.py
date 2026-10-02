import sys, random, math, pickle
from fractions import Fraction as F
from collections import Counter, defaultdict
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(20261003)
def q(x): return F(round(x * 1000), 1000)
def fam_random():
    while True:
        s = rnd.choice((9, 20, 60, 200)); xs = sorted(q(math.exp(rnd.uniform(0, math.log(s)))) for _ in range(7)); xs[0] = F(1)
        if len(set(xs)) == 7: return xs
def fam_ap_def():
    xs = [F(k) for k in range(1, 8)]
    for m in rnd.sample(range(7), rnd.choice((1, 2, 3, 4))): xs[m] = max(F(11, 10), xs[m] + q(rnd.uniform(-1.5, 3.5)))
    xs = sorted(xs); return xs if len(set(xs)) == 7 else fam_ap_def()
def fam_grid_laps():
    res = list(range(1, 8)); rnd.shuffle(res)
    xs = sorted(F(r + 8 * rnd.randint(0, 3)) + q(rnd.uniform(-0.3, 0.3)) for r in res)
    return xs if len(set(xs)) == 7 and xs[0] > F(1, 2) else fam_grid_laps()
def fam_clump():
    c = rnd.choice((8, 16, 24, 40)); k = rnd.choice((3, 4, 5, 6))
    xs = sorted([q(rnd.uniform(1, 6)) for _ in range(7 - k)] + [F(c * j) + q(rnd.uniform(-1, 1)) for j in range(1, k + 1)])
    return xs if len(set(xs)) == 7 else fam_clump()
def fam_strip():   # readings in (7,9)+8Z strips plus a low one
    k = rnd.choice((2, 3, 4, 5, 6)); xs = [F(1)] + [q(rnd.uniform(1.2, 6.5)) for _ in range(6 - k)] + [q(8 * rnd.randint(1, 3) + rnd.uniform(-1.05, 1.05)) for _ in range(k)]
    xs = sorted(xs); return xs if len(set(xs)) == 7 and xs[0] > 0 else fam_strip()
fams = [("random", fam_random), ("AP deformed", fam_ap_def), ("grid+laps", fam_grid_laps), ("clump", fam_clump), ("strips", fam_strip)]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
rows = []
for name, f in fams:
    for _ in range(N):
        xs = f(); o = outcome(xs); o['fam'] = name; o['rho'] = xs; rows.append(o)
pickle.dump(rows, open('outcome_survey_v2.pkl', 'wb'))
print("arrangements", len(rows))
def tab(title, key, top=15):
    c = Counter(key(r) for r in rows); print("\n%s: %d classes" % (title, len(c)))
    for k, v in c.most_common(top): print("  ", k, v)
tab("lap vector at the landing", lambda r: r['lap'])
tab("opener (rank, lap)", lambda r: r['opener'])
tab("closer (rank, lap)", lambda r: r['closer'])
tab("(opener, closer)", lambda r: (r['opener'], r['closer']), 20)
tab("number of moves", lambda r: r['nmoves'], 30)
tab("landing R floor", lambda r: int(r['R']), 15)
tab("zero-width landing (tangent)", lambda r: r['width'] == 0)
