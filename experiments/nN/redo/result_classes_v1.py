# Group arrangements by the cascade's own RESULT: path signature = ((rank of setter among the sorted readings, lap), ...), plus where it lands.
# Families: random log-uniform, AP deformed, complete grids with extra laps + deviation, clump + outliers, the real B1 / C1 members.
# Exact Fractions (readings are rationals with denominator 1000).  rank 1 = smallest reading (d_min), rank 7 = fastest.
import sys, random, math
from fractions import Fraction as F
from collections import Counter, defaultdict
sys.argv = [sys.argv[0]]
exec(open('anatomy_members_v1.py').read().split('\nif __name__ == "__main__":')[0])
exec(open('redo/cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(319)
def q(x): return F(round(x * 1000), 1000)
def norm(rhos):
    rhos = sorted(rhos); m = rhos[0]; return [r / m for r in rhos]
def signature(rhos):
    rhos = norm(rhos); steps, Rend = path(rhos)
    sig = tuple((mv["setter"] + 1, mv["lap"]) for mv in steps)
    return sig, Rend, rhos
def fam_random():
    while True:
        xs = sorted(q(math.exp(rnd.uniform(0, math.log(rnd.choice((9, 20, 60)))))) for _ in range(7)); xs[0] = F(1)
        if len(set(xs)) == 7: return xs
def fam_ap_def():
    xs = [F(k) for k in range(1, 8)]
    for m in rnd.sample(range(7), rnd.choice((1, 2, 3))): xs[m] = max(F(11, 10), xs[m] + q(rnd.uniform(-1.5, 3.5)))
    xs = sorted(xs)
    return xs if len(set(xs)) == 7 else fam_ap_def()
def fam_grid_laps():
    res = list(range(1, 8)); rnd.shuffle(res)
    xs = sorted(F(r + 8 * rnd.randint(0, 3)) + q(rnd.uniform(-0.3, 0.3)) for r in res)
    return xs if len(set(xs)) == 7 and xs[0] > 0.5 else fam_grid_laps()
def fam_clump():
    c = rnd.choice((8, 16, 24, 40)); k = rnd.choice((4, 5, 6))
    clump = [F(c * j) + q(rnd.uniform(-1, 1)) for j in range(1, k + 1)]
    low = [q(rnd.uniform(1, 6)) for _ in range(7 - k)]
    xs = sorted(low + clump); return xs if len(set(xs)) == 7 else fam_clump()
fams = [("random", fam_random), ("AP deformed", fam_ap_def), ("grid+laps", fam_grid_laps), ("clump", fam_clump)]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
byclass = defaultdict(list); byfam = defaultdict(Counter)
for name, f in fams:
    for _ in range(N):
        sig, Rend, rhos = signature(f()); byclass[sig].append((name, float(Rend), [float(x) for x in rhos])); byfam[name][sig] += 1
for name, mem in (("B1", B), ("C1", C[:300])):
    for S in mem:
        sig, Rend, rhos = signature([F(x, 1) for x in S]); byclass[sig].append((name, float(Rend), [float(x) for x in rhos])); byfam[name][sig] += 1
tot = sum(len(v) for v in byclass.values())
print("arrangements:", tot, "; distinct results (path signatures):", len(byclass))
print("results by number of moves (0,1,2,...):", sorted(Counter(len(s) for s, v in byclass.items() for _ in v).items()))
for name in [n for n, _ in fams] + ["B1", "C1"]:
    c = byfam[name]; print("  family %-12s: %d arrangements, %d distinct results, the most common result covers %d" % (name, sum(c.values()), len(c), max(c.values())))
print()
top = sorted(byclass.items(), key=lambda kv: -len(kv[1]))[:22]
for sig, mem in top:
    box = [(min(m[2][k] for m in mem), max(m[2][k] for m in mem)) for k in range(7)]
    fams_ = Counter(m[0] for m in mem)
    print("result %-44s  n=%-4d families %s  R* in [%.3f, %.3f]" % ("".join("%d.%d " % s for s in sig) or "(none: R=1 lonely)", len(mem), dict(fams_), min(m[1] for m in mem), max(m[1] for m in mem)))
    print("      range of each sorted reading: " + " ".join("[%.2f,%.2f]" % b for b in box))
import pickle; pickle.dump(dict(byclass), open('result_classes_v1.pkl', 'wb'))
