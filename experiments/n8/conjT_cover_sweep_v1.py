# conjT_cover_sweep_v1.py -- bounded synthetic sweep (floats steer, exact verdicts):
#  (S1) perturbations of the 9 recorded near-carve systems: is the whole-column (25,130)
#       K6-nesting kill population-wide under small perturbations of the smalls?
#  (S2) case-A structured grids (self-anchored unpinned): rho7 in C_4/C_5/C_6, smalls
#       strip-free, front via lap-1 or lap-2 bands: greedy covers? whole-column kill?
# All verdicts exact (Fractions on the float literals).
from fractions import Fraction as F
import pickle, re, sys, glob

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
from taillemma_lib_v1 import zones_of, greedy_chain

out = open(DIR + 'conjT_cover_sweep_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

def k6_components(rho_small):
    ivs = []
    for r in rho_small:
        for a, b, j in zones_of(r):
            a2, b2 = max(a, F(1)), min(b, F(7))
            if a2 < b2: ivs.append((a2, b2))
    ivs.sort()
    merged = []
    for a, b in ivs:
        if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a, b])
    comps, cur = [], F(1)
    for a, b in merged:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    if cur < F(7): comps.append((cur, F(7)))
    return comps

def feasible_set(a, b, rlo, rhi, jmax=900):
    ivs = []; j = 1
    while True:
        lo, hi = F(8 * j - 1, a), F(8 * j + 1, b)
        if lo >= rhi: break
        if hi > rlo and hi > lo: ivs.append((max(lo, rlo), min(hi, rhi)))
        j += 1
        if j > jmax: break
    ivs.sort(); merged = []
    for lo, hi in ivs:
        if lo >= hi: continue
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    return merged

def intersect(f1, f2):
    res = []
    for lo1, hi1 in f1:
        for lo2, hi2 in f2:
            lo, hi = max(lo1, lo2), min(hi1, hi2)
            if lo < hi: res.append((lo, hi))
    res.sort(); merged = []
    for lo, hi in res:
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    return merged

def column_kill(rho_small, rlo=F(25), rhi=F(130)):
    comps = k6_components(rho_small)
    cur = None
    for (a, b) in comps:
        fs = feasible_set(a, b, rlo, rhi)
        cur = fs if cur is None else intersect(cur, fs)
        if not cur: return True, len(comps)
    return (not cur), len(comps)

# ---- load the 9 recorded near systems ----
near = []
try:
    near.append(('near0', pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))))
except Exception:
    pass
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append((f.split('hi2_')[1].replace('.out', ''), [float(v) for v in m_.group(1).split(',')]))

P('# === S1. perturbations of the 9 recorded systems: whole-column (25,130) nesting verdict ===')
deltas = (0.001, 0.005, 0.01, 0.02)
n_tot = n_kill = 0
alive_rows = []
for name, v in near:
    base = sorted(float(x) for x in v)
    kills = 0; trials = 0
    for d in deltas:
        for sgn in (1, -1):
            pert = [base[i] * (1 + sgn * d) for i in range(5)] + [base[5]]
            # keep ordering valid
            if any(pert[i] >= pert[i + 1] for i in range(5)): continue
            rho = sorted(F(x) for x in pert)
            dead, ncomp = column_kill(rho[:5])
            trials += 1; kills += dead
            if not dead: alive_rows.append((name, d, sgn, [float(x) for x in rho[:5]]))
    n_tot += trials; n_kill += kills
    P('  %s: whole-column kill on %d/%d perturbations' % (name, kills, trials))
P('S1 TOTAL: %d/%d perturbed systems dead on the whole (25,130) column' % (n_kill, n_tot))
if alive_rows:
    P('  surviving perturbations (nesting bands still compatible):', len(alive_rows))
    for r in alive_rows[:5]:
        P('    %s d=%s sgn=%d smalls=%s' % (r[0], r[1], r[2], ['%.4f' % x for x in r[3]]))

# ---- S2: case-A structured grids ----
P('# === S2. case-A grids: rho7 in C_4/C_5/C_6, smalls strip-free (exact verdicts) ===')
mid_profiles = [
    [3.128139101571158, 3.722637992191327, 4.204281419315649],   # recorded-carve profile A
    [2.8690614936963414, 3.8828054084136983, 4.909405940454304], # recorded-carve profile B
    [3.1103692266836966, 3.726306232084355, 4.209767552275137],  # recorded-carve profile C
]
r7s = (31.4, 32.5, 39.5, 47.5)
fronts = {
    31.4: [(6.7, 6.8, 6.9), (14.35, 14.5, 14.8)],
    32.5: [(6.9, 6.95), (14.8, 14.9)],
    39.5: [(6.6, 6.75, 6.9), (14.3, 14.6, 14.9)],
    47.5: [(6.5, 6.7, 6.9), (14.2, 14.5, 14.9)],
}
n_tot2 = n_cov2 = n_kill2 = 0
best = (0.0, None)
for r7 in r7s:
    m = int((r7 + 1) // 8)
    win = (F(8 * m - 1), F(8 * m + 1))
    lo1 = 7 * r7 / (8 * m + 1); lo2 = 15 * r7 / (8 * m + 1)
    for lap1_r5 in fronts[r7][0]:
        for lap2_r6 in fronts[r7][1]:
            for mp in mid_profiles:
                row = mp + [lap1_r5, lap2_r6, r7]
                rho = sorted(F(x) for x in row)
                if any(F(8 * k - 1) < x < F(8 * k + 1) for x in rho[:5] for k in (1, 2)):
                    continue  # enforce case A
                if rho[3] >= rho[4] or rho[4] >= rho[5]: continue
                ch, cov = greedy_chain(rho)
                dead, ncomp = column_kill(rho[:5])
                # also strip-window feasibility (the anchor lap constraint included)
                comps = k6_components(rho[:5]); cur = None
                for (a, b) in comps:
                    fs = feasible_set(a, b, win[0], win[1])
                    cur = fs if cur is None else intersect(cur, fs)
                    if not cur: break
                n_tot2 += 1
                n_cov2 += bool(cov)
                n_kill2 += dead
                if ch:
                    z = {}
                    for i, r in enumerate(rho):
                        for a, b, j in zones_of(r): z[(i, j)] = (a, b)
                    cur2 = z[(ch[0][0], ch[0][1])][1]
                    for node in ch[1:]: cur2 = z[(node[0], node[1])][1]
                    if float(cur2) > best[0]:
                        best = (float(cur2), ([float(x) for x in rho], bool(cov), dead))
P('S2 TOTAL: %d case-A systems; greedy covers %d; whole-(25,130)-column kill %d; best reach %.5f'
  % (n_tot2, n_cov2, n_kill2, best[0]))
P('best row:', best[1])

out.close()
print('DONE')
