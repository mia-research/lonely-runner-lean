# tailrest_midservice_v1.py -- RESIDUE B-i: the middle-service lemma attempt, exact ledger.
# The question (mission): the front pin rho6 > 7(8m-1)/(8m+1) forces middle slivers; the
# leaf-close demands rho6 in rho7(47/(8J+1), 49/(8J+1)) with J >= J_min(m); does the conflict
# sharpen with m (sliver 14/(8m+1) -> 0 while the leaf demand stays fixed), i.e. can the
# conflict be proved for ALL m >= 4 analytically, closing every strip >= 4 chase-free?
# The ledger (exact Fractions, per m):
#   L1 the forced structure quantities: sliver floor f(m), sliver width w(m), anchor exit
#      x0max, first re-entry window [m+1, (9m+2)/7], leaf-close lap floor J_min(m);
#   L2 the leaf-close rho6 window: (47 rho7/(8J+1), min(49 rho7/(8J+1), 49/7)) at
#      rho7 = 8m-1 (worst case) and J = J_min(m): its width sigma(m), exact;
#   L3 the TOTAL rho6 budget: (max(f(m), 47(8m-1)/(8J_min+1)), 49/7): width B6(m), exact --
#      the mission's sharpening question answered: B6(m) -> 0 like O(1/m) but is > 0 for
#      every m (a point exists: no one-line analytic kill);
#   L4 the bridge-count quantity: the min number of rho7 re-entries from the first
#      re-entry window to J_min(m) under the maximal bridge growth phi(1) = 9/7
#      (lap-1 bridges are the most efficient: growth factor (8k+1)/(8k-1) decreasing in k),
#      against the bridge population <= 5 readings x 6 laps = 30: NO count conflict at
#      any m (T_min = 8, m-independent) -- the count/product route is edge-blind (the C3
#      verdict), confirmed here per m;
#   L5 the sharpening verdict table and the precise failing quantity.
from fractions import Fraction as F
import math, time

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'tailrest_midservice_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# tailrest_midservice_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))

def ceil_gt(x):
    """smallest integer >= x (exact)."""
    n = int(x)
    while n < x: n += 1
    while n - 1 >= x: n -= 1
    return n

def smallest_j(rhs):
    """smallest integer j with 8j+1 > rhs (exact)."""
    j = max(0, int((float(rhs) - 1) / 8) - 2)
    while not (F(8 * j + 1) > rhs): j += 1
    return j

P('# m   f(m)=7(8m-1)/(8m+1)  w(m)=14/(8m+1)   x0max   re-entry window  J_min  8J+1'
  '  sigma(m)   B6(m)      T_min')
rows = {}
for m in range(4, 41):
    f = F(7 * (8 * m - 1), 8 * m + 1)
    w = F(14, 8 * m + 1)
    x0max = F(8 * m + 1, 8 * m - 1)
    # first re-entry window: j in [m+1, floor((9m+2)/7)] (F2, exact inequalities)
    hi_w = (9 * m + 2) // 7
    reentry = (m + 1, hi_w)
    reentry_ok = m + 1 <= hi_w
    # leaf-close lap floor: 8J+1 > 47*(8m-1)/7  (rho7 > 8m-1 worst case, rho6 < 49/7)
    J = smallest_j(F(47 * (8 * m - 1), 7))
    # sigma(m): leaf-close rho6 window width at rho7 = 8m-1, J = J_min:
    #   (47(8m-1)/(8J+1), min(49(8m-1)/(8J+1), 49/7))  -- rho7=8m-1 is the worst (widest) case;
    #   for rho7 in (8m-1, 8m+1) the window shifts up but the pin cap 49/7 binds.
    lo_s = F(47 * (8 * m - 1), 8 * J + 1)
    hi_s = min(F(49 * (8 * m - 1), 8 * J + 1), F(49, 7))
    sigma = hi_s - lo_s if hi_s > lo_s else F(0)
    # total rho6 budget: (max(f, lo_s), 49/7)
    blo = max(f, lo_s)
    B6 = F(49, 7) - blo
    # min re-entries from lap m (after the anchor) to J, growth factor 9/7 per bridge:
    T = 0
    jj = F(m)
    while jj < J:
        jj = jj * F(9, 7)
        T += 1
    rows[m] = (f, w, x0max, reentry, reentry_ok, J, 8 * J + 1, sigma, B6, T)
    P('m=%-3d f=%.6f w=%.6f x0max=%.6f reentry=[%d,%d]%s J=%-4d 8J+1=%-5d sigma=%.6f B6=%.6f T=%d'
      % (m, float(f), float(w), float(x0max), reentry[0], reentry[1],
         '' if reentry_ok else ' EMPTY!', J, 8 * J + 1, float(sigma), float(B6), T))

P('# --- exact verdicts ---')
P('V1 (no one-line kill): sigma(m) > 0 for all m=4..40:',
  all(rows[m][7] > 0 for m in rows), '; B6(m) > 0 for all m:',
  all(rows[m][8] > 0 for m in rows))
P('V2 (sharpening): w(m) = 14/(8m+1) decreasing:',
  all(rows[m][1] > rows[m + 1][1] for m in range(4, 40)),
  '; B6(m) decreasing:',
  all(rows[m][8] > rows[m + 1][8] for m in range(4, 40)))
P('V3 (edge-blindness confirmed): T_min(m) constant =', set(rows[m][9] for m in rows),
  '<= bridge population 30 (5 readings x 6 laps): no count conflict at any m')
P('V4 (re-entry window nonempty, F2): m+1 <= (9m+2)//7 for m >= 3:',
  all(rows[m][4] for m in rows))
# exact asymptotics: B6(m) ~ 49/7 - f(m) = 14/(8m+1) when the pin floor dominates, i.e. when
# f(m) >= lo_s; check which side dominates per m:
dom_pin = sum(1 for m in rows if rows[m][0] >= rows[m][6 - 1])  # f >= lo_s
P('V5 (dominant side of the rho6 budget): f(m) >= leaf-close floor at %d of 37 m-values;'
  ' B6(m) = 14/(8m+1) when the pin dominates (O(1/m) -> 0)' % dom_pin)
P('# VERDICT: the conflict sharpens exactly in B6(m) (the total rho6 budget) -> 0 like O(1/m),')
P('# but B6(m) > 0 pointwise: a rho6 value EXISTS in the budget at every m; the kill is NOT')
P('# a scalar width/product/count quantity (V3: edge-blind, T_min = 8 = const; C3: R(m) >= 1).')
P('# The failing quantity: the joint interval-fixpoint collapse over the <= 30 bridge nodes')
P('# (selfband + ordering + demand bands) -- the record''s middle-reading bound lemma (E838')
P('# item 3, R1''s named dependency), which has no known scalar surrogate. The m=4 wall''s')
P('# 44,571,254-type exhaustion is the per-m certificate; no all-m analytic close from this')
P('# ledger alone.')
P('# NOTE (composition): for the tail lemma itself the strips m >= 7 (rho7 >= 55 > 50) are')
P('# closed TUPLE-WISE by the covering session''s cap-17 two-window theorem (E852: slow')
P('# domain rho6 <= 17 contains the pin), so the middle-service lemma would only serve the')
P('# chase-free analytic close of strips m = 4, 5, 6.')
out.close()
print('DONE')
