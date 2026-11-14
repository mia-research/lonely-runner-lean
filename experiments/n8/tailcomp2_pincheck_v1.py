# tailcomp2_pincheck_v1.py -- THE PIN-TRANSPORT LEMMA: exact two-regime verification.
# Part P: the comb case analysis, proved by exact interval arithmetic (Fractions only).
# Part T: validation [T n/N] against the recorded population (96 carves + 9 near-carves):
#   - the pin rho6 <= 49/7 on every recorded carve (the transport target);
#   - the end-pin structure: which zones cover R=7, is (rho6,6) among/unique, chain last node;
#   - the anchor (R=1 coverer) = the self-anchor (rho7,m);
#   - the two regimes (a) self-anchor/pinned vs (b) strip-1-anchored unpinned:
#     regime exclusivity, the E852 confinement of case (b) (rho6 <= 17, rho7 >= 50),
#     and the m >= 4 strip threshold for rho7 >= 25.
from fractions import Fraction as F
import pickle, glob, re, sys, time

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
out = open(DIR + 'tailcomp2_pincheck_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# tailcomp2_pincheck_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))

PIN = F(49, 7)          # 7
ENDLO = F(47, 7)        # 47/7 = lower edge of the lap-6 end window W_6

def regime(rho):
    """('strip', m) / ('gap', m) / (None,None), exact: strips C_j=(8j-1,8j+1), gaps (8j+1,8j+7)."""
    for m in range(1, 60):
        if F(8 * m - 1) < rho < F(8 * m + 1):
            return ('strip', m)
        if F(8 * m + 1) < rho < F(8 * m + 7):
            return ('gap', m)
    return (None, None)

def coverers_of_R(R, rho, jmax=400):
    """All laps j with R in Z(rho,j) = ((8j-1)/rho, (8j+1)/rho), exact: 8j-1 < R*rho < 8j+1."""
    X = R * rho
    res = []
    j = 1
    while F(8 * j - 1) < X:
        if F(8 * j - 1) < X < F(8 * j + 1):
            res.append(j)
        j += 1
        if j > jmax: break
    return res

# ---------------- P: the comb case analysis (exact) ----------------
P('# === P1. strips vs the pin window (exact) ===')
# (i) (1, 49/7] = (1,7] meets no strip C_j, j >= 1: lower edges 8j-1 >= 7, and C_1 open at 7.
meets = [j for j in range(1, 40) if F(8 * j - 1) < PIN and F(8 * j + 1) > F(1)]
P('(i) strips meeting (1, 49/7]:', meets, '-> EMPTY (pin: rho2..rho6 anchor nothing)' if not meets else 'FAILS')
# (ii) the two regime windows are disjoint: (47/7, 7) vs (7, 9).
P('(ii) ENDLO < PIN < 9:', ENDLO < PIN < F(9), '| (47/7,7) cap (7,9) disjoint: ',
  F(7) == PIN and ENDLO < F(7))
# (iii) rho7 >= 25 forces m >= 4 on a strip (C_3 = (23,25) open at 25) and gap m >= 3.
P('(iii) C_3 upper edge 8*3+1 = 25 exactly:', F(8 * 3 + 1) == F(25),
  '| so rho7 >= 25 in a strip => 8m-1 >= 31 => m >= 4 (exact)')
# (iv) case (b) inside the E852 hypotheses: rho6 in (7,9) => rho6 <= 17 and the strip-1
#      anchor reading exists; E852 [L/T] kills rho6 <= 17 with rho7 >= 50 => case (b) has rho7 < 50.
P('(iv) (7,9) subset (7,17]:', F(9) <= F(17), '| E852 hypothesis rho6<=17, rho7>=50: exact containment OK')
# (v) the end window W_k = ((8k-1)/7, (8k+1)/7) for k=1..8: which lie in (1,7] (reachable by
#     pinned readings) and which need readings > 7.
P('(v) end windows W_k (readings covering R=7 at lap k):')
for k in range(1, 9):
    lo, hi = F(8 * k - 1, 7), F(8 * k + 1, 7)
    tag = ''
    if hi <= F(7): tag = 'reachable under the pin (rho <= 7)'
    elif lo < F(7): tag = 'straddles 7'
    else: tag = 'needs a reading > 7 (strip 1 or above)'
    P('    W_%d = (%s, %s) = (%.4f, %.4f)  %s' % (k, lo, hi, float(lo), float(hi), tag))

P('# === P2. the two-regime transport statement (exact, per carve candidate) ===')
P('# (a) pinned (rho6 <= 49/7): anchor = {(rho7,m)} [self-anchor] or empty [gap => no carve].')
P('#     The pin is the HYPOTHESIS here; the transport TO the pin is the open direction:')
P('#     self-anchor + rho6 > 49/7 is exactly the unpinned residual (R3 self-anchored part).')
P('# (b) unpinned (rho6 > 49/7): a strip-1 reading exists (rho6 in (7,9) recorded structure);')
P('#     E852 => rho7 < 50; inside [25,50): gaps G_3,G_4,G_5 = R2, strips C_4..C_6 = R3.')

# ---------------- T: validation against the recorded population ----------------
P('# === T1. load the recorded population ===')
vecs = {2: [], 3: []}
for k in (2, 3):
    for f in sorted(glob.glob(DIR + 'frontier_band_carve_v1_k%d_s*.pkl' % k)):
        vecs[k] += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_23_25_s*.pkl')):
    vecs[3] += pickle.load(open(f, 'rb'))
near = [pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))]
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])
P('carves: strip2', len(vecs[2]), 'strip3', len(vecs[3]), '| near-carves:', len(near))

from taillemma_lib_v1 import greedy_chain

P('# === T2. the pin + end-pin + anchor on every recorded carve ===')
n_pin = n_endwin = n_anchor = n_cov = n_endnode = n_uniq7 = n_rho7cov7 = 0
minr6 = maxr6 = None
rows7 = {}
for k in (2, 3):
    for v in vecs[k]:
        rho = sorted(F(x) for x in v)          # rho[0..4] = rho2..rho6, rho[5] = rho7
        r6, r7 = rho[4], rho[5]
        ch, cov = greedy_chain(rho)
        pr = r6 <= PIN
        n_pin += pr
        minr6 = r6 if minr6 is None or r6 < minr6 else minr6
        maxr6 = r6 if maxr6 is None or r6 > maxr6 else maxr6
        n_endwin += ENDLO < r6 < PIN
        # anchor: coverers of R=1 over all readings (exact comb)
        anch = []
        for i, r in enumerate(rho):
            for j in coverers_of_R(F(1), r):
                anch.append((i + 2, j))
        reg, m = regime(r7)
        n_anchor += (anch == [(7, m)])
        # R=7 coverers over all readings (exact)
        c7 = []
        for i, r in enumerate(rho):
            for j in coverers_of_R(F(7), r):
                c7.append((i + 2, j))
        n_cov += bool(c7)
        n_uniq7 += (c7 == [(6, 6)])
        n_rho7cov7 += (7, m + 0) and any(i == 7 for i, j in c7)
        for t in c7:
            rows7.setdefault(t, 0); rows7[t] += 1
        # greedy chain end node
        n_endnode += bool(ch) and cov and (ch[-1][0] + 2, ch[-1][1]) == (6, 6)
N = len(vecs[2]) + len(vecs[3])
P('PIN  rho6 <= 49/7                : [T %d/%d]' % (n_pin, N))
P('ENDWIN rho6 in (47/7, 49/7)      : [T %d/%d]  (min rho6 = %s = %.6f, max = %s = %.6f)'
  % (n_endwin, N, minr6, float(minr6), maxr6, float(maxr6)))
P('ANCHOR coverer(R=1) = {(rho7,m)} : [T %d/%d]' % (n_anchor, N))
P('R=7 covered                      : [T %d/%d]' % (n_cov, N))
P('R=7 coverer UNIQUELY (rho6,6)    : [T %d/%d]' % (n_uniq7, N))
P('greedy chain last node (6,6)     : [T %d/%d]' % (n_endnode, N))
P('rho7 covers R=7 (some lap)       : %d/%d' % (n_rho7cov7, N))
P('all (reading,lap) covering R=7 over the population:', dict(sorted(rows7.items())))

P('# === T3. the near-carves: the two regimes in the wild ===')
for idx, v in enumerate(near):
    rho = sorted(F(x) for x in v)
    r6, r7 = rho[4], rho[5]
    ch, cov = greedy_chain(rho)
    reg, m = regime(r7)
    anch = []
    for i, r in enumerate(rho):
        for j in coverers_of_R(F(1), r):
            anch.append((i + 2, j))
    c7 = []
    for i, r in enumerate(rho):
        for j in coverers_of_R(F(7), r):
            c7.append((i + 2, j))
    P('  near %d: rho6=%.4f rho7=%.4f reg=%s pin=%s rho6in(7,9)=%s anchor=%s R7coverers=%s chainend=%s covers=%s'
      % (idx, float(r6), float(r7), (reg, m), r6 <= PIN, F(7) < r6 < F(9), anch,
         c7, (ch[-1][0] + 2, ch[-1][1]) if ch else None, cov))

P('# === T3b. per-carve cover status, chain start, and the front-pin lower bound (exact) ===')
# F1 (midbound2_mono lemma F1): zone 2 of the chain is a lap-1 zone of a reading
# rho_b > 7 rho7/(8m+1) (the front sliver); ordering gives rho6 >= rho_b. Two exact
# lower bounds on rho6: the sliver demand 7*rho7/(8m+1) and its strip floor f(m) = 7(8m-1)/(8m+1).
n_cov2 = n_start = n_sliver = n_floor = 0
for k in (2, 3):
    for v in vecs[k]:
        rho = sorted(F(x) for x in v)
        r6, r7 = rho[4], rho[5]
        ch, cov = greedy_chain(rho)
        reg, m = regime(r7)
        n_cov2 += cov
        n_start += bool(ch) and (ch[0][0] + 2, ch[0][1]) == (7, m)
        n_sliver += r6 > F(7) * r7 / F(8 * m + 1)
        n_floor += r6 > F(7) * F(8 * m - 1) / F(8 * m + 1)
P('covers=True (all recorded carves carve [1,7]) : [T %d/%d]' % (n_cov2, N))
P('greedy chain starts at the anchor (7,m)       : [T %d/%d]' % (n_start, N))
P('FRONT-PIN sliver rho6 > 7 rho7/(8m+1)         : [T %d/%d]' % (n_sliver, N))
P('FRONT-PIN floor  rho6 > f(m) = 7(8m-1)/(8m+1) : [T %d/%d]' % (n_floor, N))

P('# === T4. regime exclusivity + confinement, exact on the population ===')
# case (a) window and case (b) window are disjoint and neither contains the other's readings:
# every recorded carve sits in case (a) with rho6 in (47/7,7); every unpinned near-carve
# sits in case (b) with rho6 in (7,9); the pinned near-carves sit in case (a).
n_a = n_b = n_other = 0
for k in (2, 3):
    for v in vecs[k]:
        rho = sorted(F(x) for x in v); r6 = rho[4]
        if r6 <= PIN: n_a += 1
        elif F(7) < r6 < F(9): n_b += 1
        else: n_other += 1
for v in near:
    rho = sorted(F(x) for x in v); r6 = rho[4]
    if r6 <= PIN: n_a += 1
    elif F(7) < r6 < F(9): n_b += 1
    else: n_other += 1
P('population split: case (a) pinned %d | case (b) strip-1-anchored %d | other %d'
  % (n_a, n_b, n_other))
# the caps, exact re-derivation:
cap2 = F(73, 31) * F(49, 7)
cap3 = F(129, 15) * F(17, 23) * F(17, 31) * F(49, 7)
P('cap2 = (73/31)(49/7) =', cap2, '= 511/31:', cap2 == F(511, 31), '| < 17:', cap2 < F(17))
P('cap3 = (129/15)(17/23)(17/31)(49/7) =', cap3, '= 86989/3565:', cap3 == F(86989, 3565),
  '| < 25:', cap3 < F(25))
# rho7 >= 25 thresholds: strips 4..6 = (31,49); m>=7 => rho7 >= 55 >= 50 (E852 domain)
P('strip 7 lower edge 8*7-1 =', 8 * 7 - 1, '>= 50:', F(55) >= F(50),
  '| strips 4..6 = (31,49) subset [25,50):', F(31) >= F(25) and F(49) <= F(50))

out.close()
print('DONE')
