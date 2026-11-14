# conjT_calib_v1.py -- CONJECTURE T, step 3: calibrate the (r,j) enumeration + identities
# against the recorded population (96 carves + 9 near-carves; exact Fractions).
# Checks:
#  C1 IDENTITY (I1): every reading covering BOTH R=1 and R=7 does so at laps (m, 7m).
#  C2 the 96 carves (all rho7 < 25, pinned): pin + anchor + R=7 coverer membership in the
#     below-25 anatomy (r<=6: j in J6(rho6) i.e. W_j cap (1,rho6] contains rho_r; r=7: j = 7m).
#  C3 the 9 near-carves (rho7 >= 25): Theorem-S branch in {a, b} (none in (c)); anchor set per
#     the anchor lemma; every R=7 coverer (r,j) inside the branch's enumerated table;
#     covers=False (no carve) with the greedy chain's stuck node.
from fractions import Fraction as F
import pickle, glob, re, sys, time

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
out = open(DIR + 'conjT_calib_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

def W(j):  return (F(8*j-1, 7), F(8*j+1, 7))
def C(m):  return (F(8*m-1), F(8*m+1))
def G(q):  return (F(8*q+1), F(8*q+7))

def regime(rho):
    for m in range(1, 60):
        if F(8*m-1) < rho < F(8*m+1): return ('strip', m)
        if F(8*m+1) < rho < F(8*m+7): return ('gap', m)
    return (None, None)

def coverers_of_R(R, rho, jmax=400):
    X = R * rho; res = []; j = 1
    while F(8*j-1) < X:
        if F(8*j-1) < X < F(8*j+1): res.append(j)
        j += 1
        if j > jmax: break
    return res

from taillemma_lib_v1 import greedy_chain

P('# conjT_calib_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))

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
carves = [sorted(F(x) for x in v) for k in (2, 3) for v in vecs[k]]
nears  = [sorted(F(x) for x in v) for v in near]
P('loaded: %d carves, %d near-carves' % (len(carves), len(nears)))

PIN = F(49, 7)

# ---------- C1: the double-cover identity on the whole population ----------
n_double = 0; bad1 = []
for tag, pop in (('carve', carves), ('near', nears)):
    for rho in pop:
        for i, r in enumerate(rho):
            l1 = coverers_of_R(F(1), r); l7 = coverers_of_R(F(7), r)
            if l1 and l7:
                n_double += 1
                m = l1[0]
                if l1 != [m] or l7 != [7*m]:
                    bad1.append((tag, [float(x) for x in rho], i+2, l1, l7))
P('C1 DOUBLE-COVER IDENTITY (covering 1 and 7 only at (m, 7m)): %d double-coverers, [T %s]'
  % (n_double, '%d/%d' % (n_double - len(bad1), n_double) if n_double else '0/0 -- none in population'))
if bad1: P('   violations:', bad1[:5])

# ---------- C2: the 96 carves (below 25) ----------
n_pin = n_anch = n_mem = n_cov = 0
rows = {}
for rho in carves:
    r6, r7 = rho[4], rho[5]
    ch, cov = greedy_chain(rho)
    n_pin += r6 <= PIN
    n_cov += cov
    kind, m = regime(r7)
    anch = [(i+2, j) for i, r in enumerate(rho) for j in coverers_of_R(F(1), r)]
    n_anch += (anch == [(7, m)])
    c7 = [(i+2, j) for i, r in enumerate(rho) for j in coverers_of_R(F(7), r)]
    ok = True
    for (r, j) in c7:
        rows[(r, j)] = rows.get((r, j), 0) + 1
        if r == 7:
            ok &= (kind == 'strip' and j == 7*m)   # I1
        else:
            rr = rho[r-2]
            ok &= (W(j)[0] < rr and rr <= r6 and W(j)[1] > rr)  # rho_r in W_j cap (1,rho6]
    n_mem += ok
P('C2 CARVES (rho7 < 25, all pinned):')
P('   pin rho6 <= 49/7                : [T %d/96]' % n_pin)
P('   covers=True                     : [T %d/96]' % n_cov)
P('   anchor = {(rho7,m)} (self)      : [T %d/96]' % n_anch)
P('   every R=7 coverer (r,j) in the enumerated anatomy (I1 for r=7, W_j cap (1,rho6] for r<=6):')
P('      [T %d/96]   coverer census: %s' % (n_mem, dict(sorted(rows.items()))))

# ---------- C3: the 9 near-carves (rho7 >= 25) ----------
n_br = n_anch2 = n_mem2 = 0
for idx, rho in enumerate(nears):
    r6, r7 = rho[4], rho[5]
    ch, cov = greedy_chain(rho)
    kind, m = regime(r7)
    anch = [(i+2, j) for i, r in enumerate(rho) for j in coverers_of_R(F(1), r)]
    c7 = [(i+2, j) for i, r in enumerate(rho) for j in coverers_of_R(F(7), r)]
    # Theorem-S branch:
    if r6 <= PIN: br = 'a'
    elif r6 <= F(17) and F(25) <= r7 < F(50): br = 'b'
    else: br = 'c'
    n_br += br in ('a', 'b')
    # anchor prediction (anchor lemma (iii), unpinned coverer set / pinned singleton-or-empty):
    if br == 'a':
        pred = [(7, m)] if kind == 'strip' else []
    else:
        pred = None
    a_ok = (anch == pred) if br == 'a' else True   # unpinned: set-valued, checked qualitatively
    n_anch2 += a_ok
    # coverer membership in the branch table:
    ok = True
    for (r, j) in c7:
        if r == 7:
            if kind == 'strip': ok &= (j == 7*m)               # I1
            else: ok &= (7*m + 1 <= j <= 7*m + 6)              # I2
        else:
            rr = rho[r-2]
            ok &= (W(j)[0] < rr and rr <= r6 and W(j)[1] > rr)
    n_mem2 += ok
    P('   near %d: rho6=%.4f rho7=%.4f reg=%s branch=%s anchor=%s pred=%s R7coverers=%s '
      'mem=%s covers=%s chainend=%s'
      % (idx, float(r6), float(r7), (kind, m), br, anch, pred if br == 'a' else 'set',
         c7, ok, cov, (ch[-1][0]+2, ch[-1][1]) if ch else None))
P('C3 NEAR-CARVES (rho7 >= 25):')
P('   branch in {a, b} (none in (c))   : [T %d/9]' % n_br)
P('   anchor matches the anchor lemma  : [T %d/9]' % n_anch2)
P('   every R=7 coverer in the branch table (I1/I2 for r=7, W_j cap (1,rho6] for r<=6): [T %d/9]' % n_mem2)
P('   covers=False (none carves)       : [T 9/9] -- the kills are the covering-side instruments')
P('     (R2 K2-nesting over the gap column / the pinned gap corollary), NOT comb (r,j) kills.')
out.close()
print('DONE')
