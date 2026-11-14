# conjT3_closedform_v1.py -- exact validation of the race closed form
#     J = max(0, ceil((q+phi*)/(8(q-phi*))) - 1),   q = rho_L/rho_R, phi* = (8k_L+1)/(8k_R-1),
# against the loop J = max{j : q < Phi_j} on the interior K6 components of the sweep
# populations.  Supersedes the Decimal-based checks inside conjT3_sweep_v1/v2:
#   - v1 (float-snapped ceil): 5624/5624 matched;
#   - v2 (Decimal prec-50 ceil): 14 apparent mismatches, ALL diagnosed as Decimal
#     intermediate-rounding flips at exactly-integral zb (e.g. q = 17/9, phi* = 5/3,
#     zb = 2 exactly; Decimal gave 2.000...0002 -> ceil 3 -> Jc = 2 != J = 1);
# here the ceiling is computed in EXACT rational arithmetic (Fraction), which is the
# form the Lean certificate must use.  Residual mismatches are expected ONLY where the
# loop's safety cap (j <= 5000) truncates: q -> phi*+ gives zb -> infinity (the
# near-tangency slivers, the record's tie-plane/tangency class) and the true J is huge.
from fractions import Fraction as F
import sys, random, time
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/n8')
from taillemma_lib_v1 import zones_of

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'conjT3_closedform_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()
P('# conjT3_closedform_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))

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

def J_closed_exact(q, phi):
    zb = F(q + phi, 8 * (q - phi))
    p, Q = zb.numerator, zb.denominator
    return max(0, (p + Q - 1) // Q - 1)

def race_check(rho_small, a, b):
    L = R = None
    for r in rho_small:
        for aa, bb, j in zones_of(r):
            if bb == a and L is None: L = (r, j)
            if aa == b and R is None: R = (r, j)
    if a == F(1) or b == F(7) or L is None or R is None: return None
    rL, kL = L; rR, kR = R
    q = rL / rR; phi = F(8*kL+1, 8*kR-1)
    J = 0; j = 1
    while F(8*j-1) * q < F(8*j+1) * phi:
        J = j; j += 1
        if j > 5000: break
    return (J, J_closed_exact(q, phi), q, phi, kL, kR)

CELLS = ['P','S1','G1','S2','E']
CELLVALS = {'P':[F(12,10),F(25,10),F(4),F(69,10)],'S1':[F(72,10),F(88,10)],
            'G1':[F(9),F(11),F(149,10)],'S2':[F(151,10),F(169,10)],'E':[F(17)]}
import itertools
skels = []
def gen(pref):
    if len(pref)==5:
        if pref[-1]!='P': skels.append(tuple(pref))
        return
    for c in CELLS:
        if pref and CELLS.index(c)<CELLS.index(pref[-1]): continue
        gen(pref+[c])
gen([])
rnd = random.Random(20261116)
tot = 0; mis = 0; capped = 0; capex = []
for cells in skels:
    combos = set(itertools.product(*[CELLVALS[c] for c in cells]))
    tries = 0
    while len(combos) < 40 and tries < 200:
        tries += 1
        combos.add(tuple(F(1)+F(6)*F(rnd.randrange(1,10**6),10**6) if c=='P' else
                         F(7)+F(2)*F(rnd.randrange(1,10**6),10**6) if c=='S1' else
                         F(9)+F(6)*F(rnd.randrange(1,10**6),10**6) if c=='G1' else
                         F(15)+F(2)*F(rnd.randrange(1,10**6),10**6) if c=='S2' else F(17) for c in cells))
    for combo in combos:
        smalls = sorted(combo)
        if len(set(smalls))<5: continue
        for (a,b) in (k6_components(smalls)[1:-1] if len(k6_components(smalls))>2 else []):
            rc = race_check(smalls, a, b)
            if rc is None: continue
            tot += 1
            J, Jc, q, phi, kL, kR = rc
            if J != Jc:
                mis += 1
                if J == 5000:
                    capped += 1
                    if len(capex) < 5: capex.append((str(q), str(phi), Jc, kL, kR))
P('EXACT closed-form check (Fraction ceiling): %d interior components checked' % tot)
P('  mismatches: %d, of which loop-cap (J_loop = 5000, true J > 5000): %d' % (mis, capped))
P('  unexplained mismatches: %d' % (mis - capped))
for s in capex: P('  cap example (q, phi*, J_true, kL, kR):', s)
out.close()
print('DONE')
