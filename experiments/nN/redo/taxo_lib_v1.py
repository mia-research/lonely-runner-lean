# taxo_lib_v1.py -- shared definitions: generators (survey's five + added families), cascade labeller, independent condition labeller.
import random, math
from fractions import Fraction as F
_src = open('outcome_survey_v2.py').read().split('\nfams =')[0]
NS = {}
exec(_src.replace("rnd = random.Random(20261003)", "rnd = random.Random(0)"), NS)
outcome = NS['outcome']; q = NS['q']
CLASSES = ['K0', 'K0z', 'K1a', 'K1b', 'K1s1', 'K1s2', 'K1z', 'K2a', 'K2b', 'K2c', 'K2d', 'K2s1', 'K2s2', 'K2z']

# ---- added families (rnd = NS['rnd'], reseeded per chunk)
def fam_near8():      # 1 plus readings 8j +- u, u in (0,1.1), j in 1..4 (several laps), the rest low
    rnd = NS['rnd']; k = rnd.choice((3, 4, 5, 6)); xs = [F(1)]
    xs += [q(rnd.uniform(1.2, 6.8)) for _ in range(6 - k)]
    xs += [F(8 * rnd.randint(1, 4)) + q(rnd.uniform(-1.1, 1.1)) for _ in range(k)]
    xs = sorted(xs); return xs if len(set(xs)) == 7 and xs[0] == 1 else fam_near8()
def fam_ladder():     # geometric ladders rho_k = a^k, perturbed
    rnd = NS['rnd']; a = rnd.choice((F(6, 5), F(5, 4), F(4, 3), F(3, 2), F(2), F(5, 2), F(3)))
    xs = sorted(q(float(a ** k) * rnd.uniform(0.97, 1.03)) for k in range(7)); xs[0] = F(1)
    return xs if len(set(xs)) == 7 else fam_ladder()
def fam_integers():   # distinct integer readings (tangent cases 8j+-1 occur exactly)
    rnd = NS['rnd']; hi = rnd.choice((12, 20, 40, 70)); xs = sorted(F(x) for x in rnd.sample(range(2, hi + 1), 6)) ; return [F(1)] + xs
FAMS = [("random", NS['fam_random']), ("AP deformed", NS['fam_ap_def']), ("grid+laps", NS['fam_grid_laps']),
        ("clump", NS['fam_clump']), ("strips", NS['fam_strip']),
        ("near8", fam_near8), ("ladder", fam_ladder), ("integers", fam_integers)]

def is_strip(r): return any(abs(r - 8 * j) < 1 for j in range(1, int(r // 8) + 3))

def label_cascade(rho):
    """class from the cascade run (outcome_classes_v2.outcome); rho normalised, rho[0]==1"""
    o = outcome(rho); nm = o['nmoves']; w0 = (o['width'] == 0)
    if nm == 0: return ('K0z' if w0 else 'K0'), o
    s, j = o['opener']; c = o['closer']; many = nm >= 2; t = '2' if many else '1'
    if w0: return 'K' + t + 'z', o
    if c[0] == s: return 'K' + t + ('s1' if j == 1 else 's2'), o
    if not many: return 'K1' + ('a' if j == 1 else 'b'), o
    st = is_strip(rho[s - 1])
    return 'K2' + (('a' if j == 1 else 'b') if st else ('c' if j == 1 else 'd')), o

# ---- independent labeller: no cascade iteration; first-step inequalities + least clear point of {1} U exits
def zones_at(rho, R):
    out = []
    for y, r in enumerate(rho):
        x = R * r; j = int(x // 8)
        for jj in (j, j + 1):
            if 8 * jj - 1 < x < 8 * jj + 1: out.append((y, jj))
    return out
def label_conditions(rho):
    n = len(rho); Z1 = zones_at(rho, F(1))
    exits = lambda zs: [(F(8 * j + 1) / rho[y], y, j) for (y, j) in zs]
    if not Z1: nm = 0; Rstar = F(1); op = None
    else:
        R2 = max(exits(Z1))[0]; nm = 1 if not zones_at(rho, R2) else 2
        # least clear point >= 1 among {1} U {exits (8j+1)/rho_y >= 1}
        B = 8
        while True:
            cands = sorted(set(F(8 * j + 1) / rho[y] for y in range(n) for j in range(1, int(B * rho[y] / 8) + 2)
                               if 1 <= F(8 * j + 1) / rho[y] <= B))
            hit = [c for c in cands if not zones_at(rho, c)]
            if hit: Rstar = hit[0]; break
            B *= 4
        zs = [(y, int((Rstar * rho[y] - 1) / 8)) for y in range(n) if (Rstar * rho[y] - 1) % 8 == 0 and Rstar * rho[y] > 1]
        op = min(zs, key=lambda z: (F(8 * z[1] - 1) / rho[z[0]], -z[0]))   # variant B: zone with exit R*, smallest entry, then highest rank
    ent = []
    for y in range(n):
        j = 1
        while F(8 * j - 1) / rho[y] < Rstar: j += 1
        ent.append((F(8 * j - 1) / rho[y], y, j))
    e, cy, cj = min(ent); w0 = (e == Rstar)
    if nm == 0: return ('K0z' if w0 else 'K0'), Rstar
    s, j = op; t = str(nm if nm == 1 else 2)
    if w0: return 'K' + t + 'z', Rstar
    if cy == s: return 'K' + t + ('s1' if j == 1 else 's2'), Rstar
    if nm == 1: return 'K1' + ('a' if j == 1 else 'b'), Rstar
    st = is_strip(rho[s]); return 'K2' + (('a' if j == 1 else 'b') if st else ('c' if j == 1 else 'd')), Rstar
