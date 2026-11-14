# conjT3_enum_v1.py -- (T-i): the nesting emptiness over (25,50) for ALL smalls-tuples
# with rho6 in (7,17].  Skeleton enumeration (cell partition) + per-skeleton exact
# column-kill tests + per-kill race certificates.
#
# Frames (all exact, Fractions; float literals steer the sampling only):
#   1 = rho1 < rho2 <= ... <= rho7; zone Z(rho,k) = ((8k-1)/rho, (8k+1)/rho); strips
#   C_j = (8j-1,8j+1); gaps G_m = (8m+1,8m+7).  A carve of [1,7] = covering of [1,7]
#   by the zones of rho2..rho7.
#   K6 = [1,7] \ zones(rho2..rho6), components [a_i,b_i] (closed).  EXACT EQUIVALENCE
#   (Lemma E below, re-validated as the instrument's negative control):
#     the tuple carves with tail rho7  <=>  rho7 in ^\cap_i \cup_j ((8j-1)/a_i,(8j+1)/b_i).
#   So (T-i) -- the K6 nesting-band intersection over (25,50) is empty for EVERY
#   smalls-tuple with rho6 in (7,17] -- is exactly "no carve with rho6 in (7,17],
#   rho7 in (25,50)" (the middle branch of Theorem S at the covering level).
#
# Parts:
#  P0 negative controls: 96 recorded carves (own rho7 feasible on own K6 in the own
#     strip window); 9 recorded near systems whole-column dead.
#  P1 the skeleton partition of {1 < rho2 <= ... <= rho6 <= 17, rho6 > 7}: cells
#     P=(1,7], S1=(7,9), G1=[9,15], S2=(15,17), E={17}; nondecreasing cell 5-tuples
#     with last cell != P (125 skeletons).  Per skeleton: deterministic probe grid
#     (cell-value Cartesian product, capped), exact whole-column verdicts over (25,50)
#     and (25,130), kill classification + race certificate of the first killing
#     component.
#  P2 per-strip blocks m in {4,5,6,7} (rho7 sampled in C_m): tuples consistent with
#     ordering + front-closure rho6 > 7 rho7/(8m+1) + front-existence (a small in the
#     lap-1 or lap-2 band of the anchor exit x0 = (8m+1)/rho7; lap >= 3 checked and
#     reported dead).  Exact verdicts per tuple; per-m [T n/N].
#  P3 race-certificate census: for every killed tuple, the killing component's
#     (rho_L,k_L;rho_R,k_R), q = rho_L/rho_R, phi* = (8k_L+1)/(8k_R-1), J (the largest
#     lap with a nonempty band), and the kill type:
#       COMP-DEAD-INF  (band union empty over [25,inf): (8J+1) rho_R <= 25(8k_R-1))
#       COMP-DEAD-50   (bands exist above 50; dead on (25,50) only)
#       INTERSECT-DIE  (component has (25,50) bands but the running intersection died)
#     plus K6 = empty detection (would be an ALIVE tuple: smalls alone cover [1,7]).
from fractions import Fraction as F
import pickle, glob, re, sys, time, random

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
from taillemma_lib_v1 import zones_of, greedy_chain

out = open(DIR + 'conjT3_enum_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# conjT3_enum_v1 -- exact (Fractions); started', time.strftime('%Y-%m-%d %H:%M:%S'))

PIN = F(49, 7)

def regime(rho):
    for m in range(1, 80):
        if F(8*m-1) < rho < F(8*m+1): return ('strip', m)
        if F(8*m+1) < rho < F(8*m+7): return ('gap', m)
    return (None, None)

def k6_components(rho_small):
    ivs = []
    for r in rho_small:
        for a, b, j in zones_of(r):
            a2, b2 = max(a, F(1)), min(b, F(7))
            if a2 < b2: ivs.append((a2, b2))
    ivs.sort(); merged = []
    for a, b in ivs:
        if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a, b])
    comps, cur = [], F(1)
    for a, b in merged:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    if cur < F(7): comps.append((cur, F(7)))
    return comps

def feasible_set(a, b, rlo, rhi, jmax=1200):
    ivs = []; j = 1
    while True:
        lo, hi = F(8*j-1, a), F(8*j+1, b)
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

def column_state(rho_small, rlo, rhi):
    """Run the whole-column instrument.  Returns (dead, killinfo).
    killinfo: None (alive) or dict(kind=..., idx=..., cert=...)."""
    comps = k6_components(rho_small)
    if not comps:
        return False, {'kind': 'K6-EMPTY', 'idx': None, 'cert': None}
    cur = None
    for i, (a, b) in enumerate(comps):
        fs = feasible_set(a, b, rlo, rhi)
        new = fs if cur is None else intersect(cur, fs)
        if not new:
            if not fs:
                kind = 'COMP-DEAD'
                cert = race_certificate(rho_small, a, b, rlo)
            else:
                kind = 'INTERSECT-DIE'
                cert = None
            return True, {'kind': kind, 'idx': i, 'cert': cert, 'ncomp': len(comps)}
        cur = new
    return False, None

def race_certificate(rho_small, a, b, rlo):
    """Identify the component's boundary zones (rho_L,k_L) at exit a, (rho_R,k_R) at
    entry b, and compute the exact race quantities.  Band j = ((8j-1)rho_L/(8k_L+1),
    (8j+1)rho_R/(8k_R-1)); nonempty iff rho_L/rho_R < Phi_j; Phi_j decreasing to
    phi* = (8k_L+1)/(8k_R-1); J = largest j with a nonempty band; dead over
    [rlo,inf) iff (8J+1) rho_R <= rlo (8k_R-1) (or J = 0: no bands at all)."""
    L = R = None
    for r in rho_small:
        for aa, bb, j in zones_of(r):
            if bb == a and L is None: L = (r, j)
            if aa == b and R is None: R = (r, j)
    if a == F(1): L = ('START', 0)
    if b == F(7): R = ('END', 0)
    if not (isinstance(L[0], F) and isinstance(R[0], F)):
        return {'L': L, 'R': R, 'note': 'boundary component (START/END)'}
    rL, kL = L; rR, kR = R
    q = rL / rR
    phi = F(8*kL+1, 8*kR-1)
    # largest j with (8j-1) q < (8j+1) phi  <=>  j < (q+phi)/(8(q-phi))   [q > phi since a<b]
    Jbound = (q + phi) / (8 * (q - phi))
    J = 0
    j = 1
    while F(8*j-1) * q < F(8*j+1) * phi:
        J = j; j += 1
        if j > 5000: break
    hi_J = F(8*J+1) * rR / F(8*kR-1) if J >= 1 else None
    dead_inf = (J == 0) or (F(8*J+1) * rR <= rlo * F(8*kR-1))
    return {'L': (str(rL), kL), 'R': (str(rR), kR), 'q': q, 'phi': phi,
            'J': J, 'Jbound_float': float(Jbound), 'hi_J': hi_J, 'dead_over_inf_from_rlo': dead_inf}

# ================= P0: negative controls =================
P('# === P0. negative controls (recorded population) ===')
vecs = {2: [], 3: []}
for k in (2, 3):
    for f in sorted(glob.glob(DIR + 'frontier_band_carve_v1_k%d_s*.pkl' % k)):
        vecs[k] += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_23_25_s*.pkl')):
    vecs[3] += pickle.load(open(f, 'rb'))
near = []
try:
    near.append(pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb')))
except Exception as e:
    P('polish load failed:', e)
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])

n_neg = 0; N96 = 0
for kk in (2, 3):
    for v in vecs[kk]:
        rho = sorted(F(x) for x in v); r7 = rho[5]
        rg, m = regime(r7)
        if rg != 'strip': continue
        N96 += 1
        comps = k6_components(rho[:5])
        cur = None
        for (a, b) in comps:
            fs = feasible_set(a, b, F(8*m-1), F(8*m+1))
            cur = fs if cur is None else intersect(cur, fs)
            if not cur: break
        n_neg += any(lo < r7 < hi for lo, hi in (cur or []))
P('NEG CONTROL: recorded carve own rho7 feasible on own K6 (own strip window): [T %d/%d]' % (n_neg, N96))

n_near = 0
for v in near:
    rho = sorted(F(x) for x in v)
    dead, _ = column_state(rho[:5], F(25), F(130))
    n_near += dead
P('near systems whole-column (25,130) dead: [T %d/%d]' % (n_near, len(near)))

# ================= P1: the skeleton partition =================
P('# === P1. skeleton enumeration (cell partition of (1,17], rho6 > 7) ===')
# cells partition (1,17]: P=(1,7], S1=(7,9), G1=[9,15], S2=(15,17), E={17}
CELLS = ['P', 'S1', 'G1', 'S2', 'E']
CELLVALS = {
    'P':  [F(12,10), F(25,10), F(4), F(69,10)],
    'S1': [F(72,10), F(88,10)],
    'G1': [F(9), F(11), F(149,10)],
    'S2': [F(151,10), F(169,10)],
    'E':  [F(17)],
}
def cell_of(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

skels = []
def gen(pref):
    if len(pref) == 5:
        if pref[-1] != 'P': skels.append(tuple(pref))
        return
    for c in CELLS:
        if pref and CELLS.index(c) < CELLS.index(pref[-1]): continue
        gen(pref + [c])
gen([])
P('skeleton count (nondecreasing cell 5-tuples, last != P):', len(skels))

random.seed(3)
def probe_tuples(cells, cap=60):
    vals = [CELLVALS[c] for c in cells]
    tot = 1
    for v in vals: tot *= len(v)
    combos = []
    if tot <= cap:
        import itertools
        combos = list(itertools.product(*vals))
    else:
        seen = set()
        while len(combos) < cap:
            t = tuple(random.choice(v) for v in vals)
            if t in seen: continue
            seen.add(t); combos.append(t)
    return combos

n_tup = 0; n_kill = 0; alive_rows = []
killtype_hist = {}; killidx_hist = {}; race_hist = {}
k6empty = 0
t00 = time.time()
for si, cells in enumerate(skels):
    for combo in probe_tuples(cells):
        smalls = sorted(combo)
        if len(set(smalls)) < 5: continue
        if not (smalls[0] > F(1) and smalls[-1] <= F(17) and smalls[-1] > F(7)): continue
        n_tup += 1
        dead, info = column_state(smalls, F(25), F(50))
        if dead:
            n_kill += 1
            killtype_hist[info['kind']] = killtype_hist.get(info['kind'], 0) + 1
            killidx_hist[info['idx']] = killidx_hist.get(info['idx'], 0) + 1
            cert = info.get('cert')
            if cert and 'J' in cert:
                race_hist[(cert['L'][1], cert['R'][1], cert['dead_over_inf_from_rlo'])] = \
                    race_hist.get((cert['L'][1], cert['R'][1], cert['dead_over_inf_from_rlo']), 0) + 1
        else:
            alive_rows.append((cells, [str(x) for x in smalls], info['kind']))
            if info['kind'] == 'K6-EMPTY': k6empty += 1
P('P1 TOTAL: %d skeletons, %d probed tuples, %d whole-(25,50)-column dead, %d ALIVE'
  % (len(skels), n_tup, n_kill, n_tup - n_kill))
P('kill-type histogram:', sorted(killtype_hist.items(), key=lambda t: str(t[0])))
P('killing-component index histogram:', sorted(killidx_hist.items(), key=lambda t: str(t[0])))
P('K6-EMPTY (smalls alone cover [1,7]) count:', k6empty)
P('race certificates (kL,kR,dead_over_[25,inf)) histogram:')
for k in sorted(race_hist.items(), key=lambda t: str(t[0])):
    P('   kL=%d kR=%d dead_inf=%s : %d' % (k[0][0], k[0][1], k[0][2], k[1]))
if alive_rows:
    P('ALIVE tuples (NESTING NOT EMPTY -- T-counterexample candidates):', len(alive_rows))
    for r in alive_rows[:10]:
        P('   cells=%s smalls=%s state=%s' % r)
P('P1 elapsed %.1fs' % (time.time() - t00))

# ================= P2: per-strip blocks =================
P('# === P2. per-strip blocks m in {4,5,6,7}: front-structured populations (exact) ===')
R7SAMP = {4: [F(313,10), F(319,10), F(326,10)],
          5: [F(393,10), F(399,10), F(406,10)],
          6: [F(473,10), F(479,10), F(486,10)],
          7: [F(553,10), F(559,10), F(566,10)]}
for m in (4, 5, 6, 7):
    n_m = 0; kill_m = 0; fc_viol = 0; front3 = 0; alive_m = []
    kd_hist = {}
    for r7 in R7SAMP[m]:
        x0 = (8*m+1) / r7
        fc = F(7) * r7 / F(8*m+1)
        for cells in skels:
            for combo in probe_tuples(cells, cap=24):
                smalls = sorted(combo)
                if len(set(smalls)) < 5: continue
                if not (smalls[0] > F(1) and smalls[-1] <= F(17) and smalls[-1] > F(7)): continue
                # consistency with a carve at this rho7: ordering (by construction),
                # front-closure rho6 > 7 rho7/(8m+1), front-existence at some lap f
                if smalls[-1] <= fc: fc_viol += 1; continue
                fr = [f for f in (1, 2, 3) for r in smalls if F(8*f-1) < x0*r < F(8*f+1)]
                if not fr: continue            # no front: not carve-consistent
                if max(fr) >= 3: front3 += 1
                n_m += 1
                dead, info = column_state(smalls, F(25), F(50))
                if dead:
                    kill_m += 1
                    kd_hist[info['kind']] = kd_hist.get(info['kind'], 0) + 1
                else:
                    alive_m.append((cells, r7, [str(x) for x in smalls], info['kind']))
    P('m=%d (C_m=(%d,%d), rho7 in {%s}): carve-consistent tuples %d, whole-(25,50)-column dead %d, ALIVE %d'
      % (m, 8*m-1, 8*m+1, ','.join(str(float(x)) for x in R7SAMP[m]), n_m, kill_m, len(alive_m)))
    P('   front-closure violations excluded: %d; front at lap >= 3 encountered: %d; kill types: %s'
      % (fc_viol, front3, sorted(kd_hist.items(), key=lambda t: str(t[0]))))
    for r in alive_m[:5]:
        P('   ALIVE:', r)
P('# note: m=7 block is auxiliary: C_7 = (55,57) is outside (25,50); the (25,50) column')
P('# test applies to the same smalls space, and E852 kills rho7 >= 50 at rho6 <= 17.')

out.close()
print('DONE')
