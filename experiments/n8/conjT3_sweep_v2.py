# conjT3_sweep_v2.py -- fixed rerun of conjT3_sweep_v1 (v1's S2 fill loop hangs on
# degenerate skeletons whose cell-value product is a single point, e.g. E,E,E,E,E:
# `while len(combos) < 40` never terminates; v1's S1 results are already banked in
# conjT3_sweep_v1.out and are NOT redone here).  v2 parts:
#  S2 per-skeleton table: all 125 skeletons, grid + bounded random fill: [T n/N] each.
#  S4 per-m front-structured dense blocks (m in {4,5,6}), case split A / B2 / B3 / B23.
#  S3 race closed-form check on every fresh COMP-DEAD certificate (v1 S1 already gave
#     5624/5624 matches; re-verified here on the S2/S4 populations).
# Exact verdicts (Fractions); float literals steer sampling only.
from fractions import Fraction as F
import sys, time, random, math
from decimal import Decimal, getcontext

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
from taillemma_lib_v1 import zones_of

out = open(DIR + 'conjT3_sweep_v2.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# conjT3_sweep_v2 -- exact (Fractions); started', time.strftime('%Y-%m-%d %H:%M:%S'))
getcontext().prec = 50

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

def race_cert(rho_small, a, b, rlo):
    L = R = None
    for r in rho_small:
        for aa, bb, j in zones_of(r):
            if bb == a and L is None: L = (r, j)
            if aa == b and R is None: R = (r, j)
    if a == F(1): L = ('START', 0)
    if b == F(7): R = ('END', 0)
    if not (isinstance(L[0], F) and isinstance(R[0], F)):
        return None
    rL, kL = L; rR, kR = R
    q = rL / rR
    phi = F(8*kL+1, 8*kR-1)
    J = 0; j = 1
    while F(8*j-1) * q < F(8*j+1) * phi:
        J = j; j += 1
        if j > 5000: break
    x = Decimal(q.numerator)/Decimal(q.denominator) - Decimal(phi.numerator)/Decimal(phi.denominator)
    y = Decimal(q.numerator)/Decimal(q.denominator) + Decimal(phi.numerator)/Decimal(phi.denominator)
    zb = y / (8 * x)
    Jc = int(math.ceil(zb)) - 1 if zb != zb.to_integral_value() else int(zb) - 1
    dead_inf = (J == 0) or (F(8*J+1) * rR <= rlo * F(8*kR-1))
    return {'kL': kL, 'kR': kR, 'q': q, 'phi': phi, 'J': J, 'J_closed': Jc,
            'cf_ok': (Jc == J), 'dead_inf': dead_inf}

def column_state(rho_small, rlo, rhi):
    comps = k6_components(rho_small)
    if not comps:
        return False, {'kind': 'K6-EMPTY', 'idx': None, 'cert': None}
    cur = None
    for i, (a, b) in enumerate(comps):
        fs = feasible_set(a, b, rlo, rhi)
        new = fs if cur is None else intersect(cur, fs)
        if not new:
            kind = 'COMP-DEAD' if not fs else 'INTERSECT-DIE'
            cert = race_cert(rho_small, a, b, rlo) if kind == 'COMP-DEAD' else None
            return True, {'kind': kind, 'idx': i, 'cert': cert, 'ncomp': len(comps)}
        cur = new
    return False, None

CELLS = ['P', 'S1', 'G1', 'S2', 'E']
CELLVALS = {
    'P':  [F(12,10), F(25,10), F(4), F(69,10)],
    'S1': [F(72,10), F(88,10)],
    'G1': [F(9), F(11), F(149,10)],
    'S2': [F(151,10), F(169,10)],
    'E':  [F(17)],
}
def sample_cell(c, u):
    if c == 'P':  return F(1) + F(6) * u
    if c == 'S1': return F(7) + F(2) * u
    if c == 'G1': return F(9) + F(6) * u
    if c == 'S2': return F(15) + F(2) * u
    return F(17)
def u_rand(rnd):
    return F(rnd.randrange(1, 10**6), 10**6)

rnd = random.Random(20261115)

# ---------- S2: per-skeleton table (bounded fill) ----------
P('# === S2. per-skeleton table (grid + bounded random fill, cap 40 attempts*5) ===')
import itertools
skels = []
def gen(pref):
    if len(pref) == 5:
        if pref[-1] != 'P': skels.append(tuple(pref))
        return
    for c in CELLS:
        if pref and CELLS.index(c) < CELLS.index(pref[-1]): continue
        gen(pref + [c])
gen([])
rows = []
tot_t = tot_k = 0; ncf = ncfok = ndi = 0
bad = []
t0 = time.time()
for cells in skels:
    combos = set(itertools.product(*[CELLVALS[c] for c in cells]))
    tries = 0
    while len(combos) < 40 and tries < 200:
        tries += 1
        combos.add(tuple(sample_cell(c, u_rand(rnd)) for c in cells))
    nk = 0; nt = 0
    for combo in combos:
        smalls = sorted(combo)
        if len(set(smalls)) < 5: continue
        nt += 1; tot_t += 1
        dead, info = column_state(smalls, F(25), F(50))
        if dead:
            nk += 1; tot_k += 1
            c = info.get('cert')
            if c: ncf += 1; ncfok += c['cf_ok']; ndi += c['dead_inf']
        else:
            bad.append((cells, [str(x) for x in smalls]))
    rows.append((cells, nt, nk))
P('S2: %d skeletons, %d tuples, %d dead; all-skeletons fully dead: %s'
  % (len(skels), tot_t, tot_k, all(nk == nt for _, nt, nk in rows)))
P('    COMP-DEAD certificates: %d, closed-form J matches: %d, dead over [25,inf): %d'
  % (ncf, ncfok, ndi))
part = [(c, nt, nk) for c, nt, nk in rows if nk < nt]
P('    skeletons with survivors: %s' % (part if part else 'NONE'))
for r in bad[:10]: P('    ALIVE:', r)
P('S2 elapsed %.1fs' % (time.time() - t0))

# ---------- S4: per-m front-structured dense blocks ----------
P('# === S4. per-m front-structured blocks (10 rho7 samples per strip m in {4,5,6}) ===')
for m in (4, 5, 6):
    r7s = [F(8*m-1,1) + F(k, 10) for k in (2, 5, 8, 12, 15, 18, 21, 24, 27, 30)]
    r7s = [x for x in r7s if x < F(8*m+1)]
    cnt = {'A': [0,0], 'B2': [0,0], 'B3': [0,0], 'B23': [0,0]}
    fc3 = 0; ncf4 = ncfok4 = ndi4 = 0
    alive4 = []
    for r7 in r7s:
        x0 = (8*m+1) / r7
        fcm = F(7) * r7 / F(8*m+1)
        for cells in skels:
            for _ in range(6):
                vals = [sample_cell(c, u_rand(rnd)) for c in cells]
                smalls = sorted(vals)
                if smalls[-1] > F(17) or smalls[-1] <= fcm: continue
                fr = [f for f in (1, 2, 3) for r in smalls if F(8*f-1) < x0*r < F(8*f+1)]
                if not fr: continue
                if max(fr) >= 3: fc3 += 1; continue
                hasS1 = any(c == 'S1' for c in cells); hasS2 = any(c == 'S2' for c in cells)
                key = 'B23' if (hasS1 and hasS2) else ('B2' if hasS1 else ('B3' if hasS2 else 'A'))
                cnt[key][0] += 1
                dead, info = column_state(smalls, F(25), F(50))
                if dead:
                    cnt[key][1] += 1
                    c = info.get('cert')
                    if c: ncf4 += 1; ncfok4 += c['cf_ok']; ndi4 += c['dead_inf']
                else:
                    alive4.append((cells, str(r7), [str(x) for x in smalls]))
    P('m=%d: front-structured tuples by case (tested, dead): A %s | B2 %s | B3 %s | B23 %s | front>=3 %d'
      % (m, cnt['A'], cnt['B2'], cnt['B3'], cnt['B23'], fc3))
    P('    certificates %d, closed-form ok %d, dead over [25,inf) %d, ALIVE %d'
      % (ncf4, ncfok4, ndi4, len(alive4)))
    for r in alive4[:5]: P('    ALIVE:', r)

out.close()
print('DONE')
