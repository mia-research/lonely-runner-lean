# tie_pair_v1.py -- pair-law avoidance: exact rule, tests. Exact Fractions throughout (random draws are rational with fixed denominators; seeds fixed).
# RULE (proved in tie_structure_v1.md section 5): a window contains an instant of {8k+1,8k+7} and an instant of {8k+3,8k+5} (k=0,1,2, same period)
#   <=> for some x in X = {1,5,9,13,17,21}, every reading rho_y lies in I(x) = union_{m>=0} [(8m+1)/x, (8m+7)/(x+2)]   (the window then contains [x,x+2]).
import sys, pickle, glob, random, itertools, time
from fractions import Fraction as F
from collections import Counter
from math import comb
exec(open('win_lib_v1.py').read())
X = (1, 5, 9, 13, 17, 21)
def inI(x, r):
    m = (x * r - 1) // 8           # largest m with 8m+1 <= x r  (floor of Fraction)
    return m >= 0 and (x + 2) * r <= 8 * m + 7
def rule(rh): return [x for x in X if all(inI(x, r) for r in rh)]
def direct(ws):
    for lo, hi in ws:
        for k in range(3):
            a = [t for t in (8 * k + 1, 8 * k + 7) if lo <= t <= hi]
            b = [t for t in (8 * k + 3, 8 * k + 5) if lo <= t <= hi]
            if a and b: return True
    return False
def run(label, items, show=3):
    c = Counter(); ex = []; mism = []
    for lab, rh in items:
        rh = norm(rh); ws = windows(rh, 23)
        d = direct(ws); r = rule(rh)
        c[(d, bool(r))] += 1
        if d != bool(r): mism.append((lab, rh))
        if d and len(ex) < show: ex.append((lab, rh, r))
    print('%-28s members %6d | direct yes & rule yes %5d | direct no & rule no %6d | MISMATCHES (direct!=rule) %d' % (label, len(items), c[(True, True)], c[(False, False)], len(mism)))
    for lab, rh, r in ex: print('      occurs: ', lab, '[' + ', '.join(str(x) for x in rh) + ']', 'x in', r)
    for lab, rh in mism[:3]: print('      MISMATCH', lab, [str(x) for x in rh])
    return c
sets = {}
for f in sorted(glob.glob('win_rec_*_v1.pkl')):
    sets.setdefault(f.split('win_rec_')[1].split('_')[0], []).extend(pickle.load(open(f, 'rb')))
print('== 1. stored datasets (windows recomputed here by win_lib_v1.windows, rule vs direct)')
for name, recs in sets.items():
    run(name, [(r[0], r[1]) for r in recs])
# diagnostics on the stored J1 points
J = sets['J1']; best = Counter()
for lab, rh, *_ in J:
    rh = norm(rh)
    best[max(sum(inI(x, r) for r in rh) for x in X)] += 1
print('J1 stored points: largest number of the seven readings inside one I(x), x in X -> number of points:', sorted(best.items()))
print('J1 stored points with rho_7 < 3:', sum(1 for lab, rh, *_ in J if norm(rh)[-1] < 3), '; with rho_7 <= 7/3:', sum(1 for lab, rh, *_ in J if norm(rh)[-1] <= F(7, 3)))
print('== 2. lattice counts: sets {c_1=M, c_2<...<c_7 integers > M} (readings c/M) satisfying the rule, by M and x (exact count C(N-1,6))')
tot = Counter()
for M in range(1, 41):
    for x in X:
        N = sum(1 for c in range(M, 12 * M + 1) if inI(x, F(c, M)))
        if N >= 7 and inI(x, F(1)):
            tot[M] += comb(N - 1, 6)
            if M <= 16 or M == 40: print('  M=%d x=%d: %d allowed readings (incl. reading 1) -> %d sets' % (M, x, N, comb(N - 1, 6)))
print('  M with at least one set (M<=40):', sorted(tot))
print('== 3. exact lattice examples')
for lab, c, M in (('M=5 {5..11}', range(5, 12), 5), ('M=15 {15,27..32}', [15] + list(range(27, 33)), 15), ('M=7 {7,8,..,13}', range(7, 14), 7)):
    rh = norm([F(x, M) for x in c]); ws = windows(rh, 23)
    print('  ', lab, 'rule x:', rule(rh), 'direct:', direct(ws), 'windows in [1,23]:', [(str(a), str(b)) for a, b in ws][:8])
print('== 4. 20,000 arrangements near progressions (exact rationals, seeds fixed)')
rnd = random.Random(20261003); itemsA = []; itemsB = []
for i in range(10000):
    s = rnd.choice([F(1, 50), F(1, 20), F(1, 10), F(1, 5), F(3, 10)])
    xs = sorted(F(y) * (1 + F(rnd.randint(-10000, 10000), 10000) * s) for y in range(1, 8))
    if len(set(xs)) == 7: itemsA.append((('A near y*c', i, str(s)), xs))
for i in range(10000):
    d = F(rnd.randint(1, 25), 50); dev = F(rnd.randint(1, 10), 20) * d
    xs = sorted(1 + (y - 1) * d + F(rnd.randint(-10000, 10000), 10000) * dev for y in range(1, 8))
    if len(set(xs)) == 7 and xs[0] >= 1 / F(2): itemsB.append((('B near 1+(y-1)d', i, str(d)), xs))
t0 = time.time()
cA = run('family A (near c,2c,..,7c)', itemsA)
cB = run('family B (near 1+(y-1)d)', itemsB)
print('   seconds', round(time.time() - t0))
