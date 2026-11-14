# conjT_cover_bands_v1.py -- exact per-component nesting-band dump for two recorded
# near-carve systems: near 0 (B1 gap, regression vs gapcover K3's worked conflict) and
# near 2 (B2 strip-5, the R3-sector system killed here for the first time).
# For each K6 component [a,b]: the exact rho7-band union over laps j, intersected with
# (25,50); then the pairwise disjointness graph (which component pairs already conflict),
# and the greedy conflict certificate (first pair of components with disjoint band sets,
# with the two exact intervals that would have to contain rho7).
from fractions import Fraction as F
import pickle, re, sys

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
from taillemma_lib_v1 import zones_of

out = open(DIR + 'conjT_cover_bands_v1.out', 'w')
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

def bands(a, b, rlo, rhi, jmax=800):
    res = []
    j = 1
    while True:
        lo, hi = F(8 * j - 1, a), F(8 * j + 1, b)
        if lo >= rhi: break
        if hi > rlo and hi > lo: res.append((max(lo, rlo), min(hi, rhi), j))
        j += 1
        if j > jmax: break
    return res

systems = {}
try:
    systems['near0'] = pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))
except Exception as e:
    P('polish load failed:', e)
m_ = re.search(r'readings \(float\): \[(.*)\]', open(DIR + 'frontier_box_carve_v1_hi2_s12.out').readline())
systems['near2'] = [float(v) for v in m_.group(1).split(',')]

RLO, RHI = F(25), F(50)
for name, v in systems.items():
    rho = sorted(F(x) for x in v)
    P('# === %s ===' % name)
    P('readings (exact):', [str(x) for x in rho])
    P('rho2..rho6 (smalls):', [str(x)[:10] for x in rho[:5]], ' rho7 =', str(rho[5])[:10])
    comps = k6_components(rho[:5])
    P('K6 components (%d):' % len(comps))
    allb = []
    for i, (a, b) in enumerate(comps):
        bs = bands(a, b, RLO, RHI)
        allb.append(bs)
        P('  comp %d = [%s, %s] (width %s): %d band(s) in (25,50):' %
          (i, str(a)[:10], str(b)[:10], str(b - a)[:10], len(bs)))
        for lo, hi, j in bs:
            P('     lap %d: rho7 in (%s, %s) = (%.6f, %.6f)' % (j, str(lo)[:12], str(hi)[:12], float(lo), float(hi)))
    # pairwise disjointness graph over the band unions
    P('  pairwise conflicts (band unions disjoint):')
    nconf = 0
    for i in range(len(comps)):
        for j2 in range(i + 1, len(comps)):
            inter = []
            for lo1, hi1, _ in allb[i]:
                for lo2, hi2, _ in allb[j2]:
                    lo, hi = max(lo1, lo2), min(hi1, hi2)
                    if lo < hi: inter.append((lo, hi))
            if not inter:
                nconf += 1
                bi = allb[i][0]; bj = allb[j2][0]
                P('    comp %d vs comp %d: DISJOINT.  e.g. comp %d demands rho7 in (%s, %s) [lap %d] while'
                  % (i, j2, i, str(bi[0])[:12], str(bi[1])[:12], bi[2]))
                P('       comp %d demands rho7 in (%s, %s) [lap %d]; %s'
                  % (j2, str(bj[0])[:12], str(bj[1])[:12], bj[2],
                     'lower edge >= upper edge: %s %s' % (str(bj[0])[:12], str(bi[1])[:12])
                     if bj[0] >= bi[1] else 'upper edge <= lower edge: %s %s' % (str(bi[1])[:12], str(bj[0])[:12])))
    P('  conflicting pairs: %d of %d' % (nconf, len(comps) * (len(comps) - 1) // 2))
    # the 7rho5 boundary check (the K3 mechanism): is any band edge exactly/at 7*rho5?
    r5 = rho[3]
    P('  7*rho5 = %s = %.6f' % (str(F(7) * r5)[:14], float(F(7) * r5)))
    for i, bs in enumerate(allb):
        for lo, hi, j in bs:
            if lo == F(7) * r5 or hi == F(7) * r5:
                P('    comp %d lap %d band edge EXACTLY 7*rho5 (%s)' %
                  (i, j, 'hi' if hi == F(7) * r5 else 'lo'))
out.close()
print('DONE')
