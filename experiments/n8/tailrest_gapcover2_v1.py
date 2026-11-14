# tailrest_gapcover2_v1.py -- gap-column kills, widened populations, exact.
# (a) brute-force lap-tuple re-verification of the K2 CONFLICT verdicts on the remaining
#     recorded gap systems (3, 4, 6, 8); systems 0, 1, 7 already brute-forced (48/192/48
#     tuples, NOT NESTABLE).
# (b) the K6-nesting verdict on EVERY census-type witness (the 27 feasible-gap types'
#     exact witness vectors): the mission's "sampled skeletons". For each: regime, K6
#     components, exhaustive lap-tuple nesting feasibility over rho7 in (33,39) (the gap
#     window that contains all recorded gap witnesses; types with witness rho7 outside
#     any G_m are reported and skipped).
# Reuses the semantics of tailrest_gapcover_v1 (zones/K6/bands unchanged).
import sys, glob, re, pickle, random, itertools, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/n8')
DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'tailrest_gapcover2_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# tailrest_gapcover2_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))
t0 = time.time()

def zones_in_window(rho, lo=F(1), hi=F(7)):
    z = []; j = 1
    while True:
        a = F(8 * j - 1) / rho
        if a >= hi: break
        b = F(8 * j + 1) / rho
        if b > lo: z.append((a, b, j))
        j += 1
    return z

def k6_components(rho_sorted):
    cuts = []
    for rho in rho_sorted[:5]:
        for a, b, j in zones_in_window(rho):
            cuts.append((a, b))
    cuts.sort()
    comps = []; cur = F(1)
    for a, b in cuts:
        if a > cur:
            comps.append((cur, min(a, F(7))))
        cur = max(cur, b)
        if cur >= F(7): break
    if cur < F(7):
        comps.append((cur, F(7)))
    return comps

def bands_of(a, b, glo, ghi):
    res = []
    for j in range(1, 4000):
        lo = F(8 * j - 1) / a
        hi = F(8 * j + 1) / b
        if lo >= ghi: break
        if hi > glo:
            res.append((lo, hi, j))
    return res

def nest_bruteforce(rho_sorted, glo, ghi):
    comps = k6_components(rho_sorted)
    per = [bands_of(a, b, glo, ghi) for (a, b) in comps]
    if any(len(p) == 0 for p in per):
        return 'dead-component', comps, per, 0
    n = 1
    for p in per: n *= len(p)
    if n > 200000:
        return 'TOO-MANY', comps, per, n
    for tup in itertools.product(*per):
        lo = max(x[0] for x in tup); hi = min(x[1] for x in tup)
        l2, h2 = max(lo, glo), min(hi, ghi)
        if l2 < h2:
            return 'NESTABLE', comps, per, n
    return 'CONFLICT', comps, per, n

def regime(rho7):
    for m in range(1, 60):
        if F(8 * m - 1) < rho7 < F(8 * m + 1): return ('strip', m)
        if F(8 * m + 1) < rho7 < F(8 * m + 7): return ('gap', m)
    return (None, None)

# ---------- (a) the remaining recorded systems ----------
P('# === (a) brute-force re-verification, recorded systems 3, 4, 6, 8 ===')
near = [pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))]
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])
GLO, GHI = F(33), F(39)
ok = 0; tot = 0
for idx in (3, 4, 6, 8):
    rho = sorted(F(x) for x in near[idx])
    if not (GLO < rho[5] < GHI): continue
    v, comps, per, n = nest_bruteforce(rho, GLO, GHI)
    tot += 1; ok += (v in ('CONFLICT', 'dead-component'))
    P('  system %d: verdict %s | comps %d bands %s tuples %d' %
      (idx, v, len(comps), [len(p) for p in per], n))
P('(a) [T %d/%d]' % (ok, tot))

# ---------- (b) the census-type witnesses ----------
P('# === (b) K6-nesting on the 27 census-type witnesses (sampled skeletons) ===')
sys_argv_saved = sys.argv
src = open(DIR + 'frontier_type_search_v1.py').read().split('found = []; types_seen')[0]
sys.argv = ['x', '1', '15', '80', '1', '1']
exec(src)
sys.argv = sys_argv_saved
random.seed(1)
starts = []
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    starts.append([float(v) for v in m_.group(1).split(',')])
starts.append(pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb')))
types = {}
for it in range(6000):
    x0 = random.choice(starts); scale = random.choice([1e-3, 1e-2, 5e-2, 0.1])
    x = sorted(max(1.0001, v * (1 + scale * random.uniform(-1, 1))) for v in x0)
    ch = chain_of(x)
    if ch is not None: types.setdefault(ch, [F(v) for v in x])
import collections as _c
def links_of(chain):
    ls = []
    for k in range(len(chain) - 1):
        (p, jp), (q, jq) = chain[k], chain[k + 1]
        if p != q: ls.append((p, q, F(8 * jq - 1, 8 * jp + 1)))
    for i in range(5): ls.append((i, i + 1, F(1)))
    return ls
def maxc(ls):
    W = {}
    for p, q, w in ls:
        if (p, q) not in W or w > W[(p, q)]: W[(p, q)] = w
    best = F(0)
    for size in range(2, 7):
        for cyc in itertools.permutations(range(6), size):
            if cyc[0] != min(cyc) or (cyc[0], cyc[-1]) not in W: continue
            pr, okc = F(1), True
            for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                if (a, b) not in W: okc = False; break
                pr *= W[(a, b)]
            if okc and pr > best: best = pr
    return best
feas = {ch: rs for ch, rs in types.items() if maxc(links_of(ch)) < 1}
P('census types:', len(feas))
tally = _c.Counter()
gapverdicts = _c.Counter()
for ch, rs in sorted(feas.items(), key=lambda kv: len(kv[0])):
    reg, m = regime(rs[5])
    if reg != 'gap':
        tally[('skip', reg, m)] += 1
        continue
    glo, ghi = F(8 * m + 1), F(8 * m + 7)
    v, comps, per, n = nest_bruteforce(rs, glo, ghi)
    gapverdicts[v] += 1
    tally[(reg, m, v)] += 1
    P('  type len %d rho7=%.4f gap %d: %s (comps %d, tuples %d)'
      % (len(ch), float(rs[5]), m, v, len(comps), n))
P('(b) verdicts:', dict(gapverdicts))
for key in sorted(tally, key=str):
    P('   ', key, ':', tally[key])
P('done %.1fs' % (time.time() - t0))
out.close()
print('DONE')
