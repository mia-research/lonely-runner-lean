# E827: for the rational counterexample (2767/1000, 749/200, 957/200, 123/20, 683/100, 11889/500): which zones cover the seam interval (73/r7, 31/r6), and the greedy interval chain covering [1,7] (the data for a Lean disproof).
from fractions import Fraction as F
rs = [F(2767, 1000), F(749, 200), F(957, 200), F(123, 20), F(683, 100), F(11889, 500)]
lo, hi = F(73) / rs[5], F(31) / rs[4]
print('seam interval (73/r7, 31/r6) =', lo, hi, '=', float(lo), float(hi), ' 31/r6 > 73/r7:', hi > lo)
zones = []
for i, r in enumerate(rs):
    j = 1
    while F(8 * j - 1) / r < 7:
        zones.append((F(8 * j - 1) / r, F(8 * j + 1) / r, i + 2, j)); j += 1
zones.sort()
print('zones meeting the seam interval:', [(float(a), float(b), 'rho%d' % i, j) for a, b, i, j in zones if a < hi and b > lo])
chain = []; cur = F(1)
first = [z for z in zones if z[0] < 1 < z[1]]
z = max(first, key=lambda z: z[1]); chain.append(z); cur = z[1]
while cur <= 7:
    opts = [z for z in zones if z[0] < cur < z[1]]
    z = max(opts, key=lambda z: z[1]); chain.append(z); cur = z[1]
print('greedy chain (rho index, lap j, interval):')
for a, b, i, j in chain: print('  rho%d lap %d  (%s, %s)  = (%.6f, %.6f)' % (i, j, a, b, float(a), float(b)))
print('chain length', len(chain), 'last end', chain[-1][1], '> 7:', chain[-1][1] > 7)
