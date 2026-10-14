"""Is `2*g + 2 <= n` tight in `no_return_after_few_faster`?

The hypothesis enters the proof at exactly one place. Chain (FourDifferences.lean:113):

  return_growth (SmallOrders.lean:487):   a return needs   t_m > ((P+1-h)/(P+h)) * t_0
  growth bound  (hbound, in the theorem): t_m <= F^m * t_0,  F = ((P+1)+h)/((P+1)-h),  m <= g
  factor_pow_le_return (FourDifferences.lean:73), under 2g+2 <= n:
                                          F^g <= (P+1-h)/(P+h)
  => contradiction.

So the theorem's real requirement is the SHARP inequality

      F^g <= (P+1-h)/(P+h),     h = 1/n,   F = (P+1+h)/(P+1-h),

and `2g+2 <= n` is whatever `factor_pow_le_return` could prove of it. That proof goes through Bernoulli:
(1+y)^g <= 1/(1-g*y) with y = 2h/(P+1-h), then demands P+h <= (P+1-h)(1-g*y), which reduces to
2h(g+1) <= 1, i.e. 2g+2 <= n. Bernoulli is an over-estimate, so the two can differ.

This computes both, exactly, and reports where they part.
"""
import sys
from fractions import Fraction as F

def sharp_max_g(n, P, gmax=40):
    """largest g with ((P+1+h)/(P+1-h))^g <= (P+1-h)/(P+h), exactly"""
    h = F(1, n)
    num = F(P) + 1 + h; den = F(P) + 1 - h
    if den <= 0: return None
    fac = num / den
    target = (F(P) + 1 - h) / (F(P) + h)
    g = 0; cur = F(1)
    while g < gmax:
        nxt = cur * fac
        if nxt > target: return g
        cur = nxt; g += 1
    return gmax

def bernoulli_max_g(n, P):
    """largest g the shipped proof delivers: needs 2h(g+1) <= 1 AND g*y <= 1 (Bernoulli's own hypothesis)"""
    h = F(1, n)
    g1 = 0
    while 2 * h * (g1 + 2) <= 1: g1 += 1          # 2h(g+1) <= 1
    y = 2 * h / (F(P) + 1 - h)
    g2 = 0
    while (g2 + 1) * y <= 1: g2 += 1               # g*y <= 1
    return min(g1, g2)

n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
print(f"n = {n}, h = 1/{n};  shipped hypothesis 2g+2 <= n  =>  g <= {n//2 - 1}\n")
print(f"  {'P':>4} {'sharp max g':>12} {'proof delivers':>15} {'lost':>6}")
rows = []
for P in list(range(0, 13)) + [20, 50, 200, 1000, 10000]:
    s = sharp_max_g(n, P); b = bernoulli_max_g(n, P)
    rows.append((P, s, b))
    print(f"  {P:>4} {s:>12} {b:>15} {s-b:>6}")

uni_sharp = min(r[1] for r in rows)
uni_proof = min(r[2] for r in rows)
print(f"\n  P-uniform (min over P): sharp {uni_sharp}, shipped proof {uni_proof}")
print(f"  shipped hypothesis gives g <= {n//2 - 1}")
print()
print(f"  VERDICT")
print(f"   * as a hypothesis that must hold for EVERY P >= 0: sharp limit is {uni_sharp}, and the")
print(f"     shipped 2g+2 <= n gives {n//2 - 1}.  {'TIGHT' if uni_sharp == n//2 - 1 else 'NOT tight'}.")
worst = [r for r in rows if r[1] > r[2]]
if worst:
    print(f"   * but at small P the sharp bound is strictly better, e.g.:")
    for P, s, b in worst[:5]:
        print(f"       P = {P}: sharp allows g <= {s}, the proof delivers g <= {b}")
    print(f"     so the hypothesis is tight only in the P -> infinity limit; it is NOT tight per-P.")
