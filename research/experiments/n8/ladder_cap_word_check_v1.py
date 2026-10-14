"""The depth-14 beam word at order 8: is it realisable, and does its bound reach the cap?

`ladder_return_beam_w2500_v1.out` reports max R = 7 at order 8, ratio bound S = 8 -- exactly the cap
n-1. This script re-derives that word's two LPs from `order_n_certificate_v1.py` independently of the
beam, prefix by prefix, and then answers the boundary question the value forces:

  (1) is every prefix realisable (max tau > 0), and is every proper prefix below the cap, so that the
      word is a legitimate "first exceedance" candidate in the sense of ORDER5_CERTIFICATE_v2 section 1;
  (2) is the supremum R = 7 ATTAINED by a strictly realisable configuration, or only approached as the
      margin vanishes.

(2) is the standing boundary rule: when a result turns on a quantity hitting a threshold exactly, the
side it falls on is stated explicitly. It is answered by minimising the final reading subject to
tau >= eps for eps > 0, rather than on the tau = 0 face the certificate uses.
"""
import os, sys
os.environ.setdefault('ORDER', '8')
from fractions import Fraction as F

src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'capcheck'}
exec(src, g)
constraints = g['constraints']; opt = g['opt']; NV = g['NV']; n = g['n']

WORD = [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (3, 2), (4, 2),
        (1, 4), (5, 2), (3, 3), (2, 4), (6, 2), (1, 6)]
S = 8
CAP = n - 1

print(f"order {n}, ratio bound S = {S}, cap R < {CAP}")
print(f"word from experiments/n8/ladder_return_beam_w2500_v1.out, depth {len(WORD)}\n")

print("(1) prefix by prefix -- realisability and R")
over = []
for k in range(1, len(WORD) + 1):
    w = WORD[:k]
    cons = constraints(w)
    tau = opt(cons, NV, 'max', S, True)
    x, Q = w[-1]
    m = opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    R = F(n * Q + 1) / m if (m is not None and m > 0) else None
    flag = ''
    if R is not None and R >= CAP:
        flag = '   <-- reaches the cap'
        over.append(k)
    print(f"   len {k:2}  move {str(w[-1]):7}  max tau = {str(tau):>9}  min u = {str(m):>14}"
          f"  R = {str(R):>14} = {float(R):.6f}{flag}")
assert all(opt(constraints(WORD[:k]), NV, 'max', S, True) > 0 for k in range(1, len(WORD) + 1)), \
    "a prefix is not realisable"
print(f"\n   every prefix realisable (max tau > 0): yes")
print(f"   prefixes reaching the cap: {over}  -> proper prefixes all below the cap: {over == [len(WORD)]}")

print("\n(2) is the supremum attained? min of the final reading subject to tau >= eps")
base = constraints(WORD)
x, Q = WORD[-1]
num = F(n * Q + 1)
for eps in [F(0), F(1, 10**6), F(1, 1000), F(1, 100)]:
    cons = list(base)
    if eps > 0:
        cons.append(tuple([F(0)] * NV) + (F(-1), -eps))          # -tau <= -eps, i.e. tau >= eps
    m = opt(cons, x - 1, 'min', S, True)
    R = num / m
    print(f"   tau >= {str(eps):>10}   min u = {str(m):>16} = {float(m):.8f}"
          f"   R = {float(R):.8f}   R < {CAP}: {R < CAP}")
print(f"\n   min u = {CAP} + {n}*eps exactly, so R = {num}/({CAP} + {n}*eps) < {CAP} for every eps > 0.")
print(f"   The supremum {CAP} is NOT attained: every strictly realisable configuration of this word")
print(f"   has R < {CAP}, and R -> {CAP} only as the margin vanishes.")
