"""Does the general-n work say anything at order 8 that the order-8 development does not?

Two rules found this session are general n and have no order-8 counterpart on file:
  (a) the divisibility family  -- t = 1/q lonely when no disparity is divisible by q, q <= n
      (LRC.RationalN.ratWorks_le_order, an IFF via ratWorks_one_iff)
  (b) the coprime flank        -- gcd(e,n)=1 and no other disparity divisible by n
      (LRC.Resonance.flankWorks_of_coprime, primality removed 2026-09-22)
Test them on the order-8 cases the manuscript records as hard.
"""
from fractions import Fraction as F
import math
n = 8
HARD = {
  "(27,70,107,137,159,188,344,393)  -- 28 cascade moves, MANUSCRIPT_v19 6.7/6.10":
      (27,70,107,137,159,188,344,393),
  "(1,31,75,97,128,160,176,225)     -- 23 moves":
      (1,31,75,97,128,160,176,225),
}
def min_q(ds, Q=60):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q)!=1: continue
            if all(F(1,n) <= min(F((d*a)%q,q), 1-F((d*a)%q,q)) for d in ds): return (q,a)
    return None
def divis_rule(ds):                     # q <= n, a = 1 : no disparity divisible by q
    for q in range(2, n+1):
        if all(d % q for d in ds): return q
    return None
def coprime_flank(ds):                  # gcd(e,n)=1 and no other disparity divisible by n
    for e in ds:
        if math.gcd(e,n)==1 and all(d % n for d in ds if d != e): return e
    return None
for name, v in HARD.items():
    print(name)
    for k in range(len(v)):
        ds = tuple(sorted(abs(v[i]-v[k]) for i in range(len(v)) if i != k))
        dq, cf, mq = divis_rule(ds), coprime_flank(ds), min_q(ds)
        tag = []
        if dq: tag.append(f"divisibility q={dq}")
        if cf: tag.append(f"coprime flank e={cf}")
        if not tag: tag.append(f"neither; smallest rational witness {mq}")
        print(f"   subject {v[k]:>4}  disparities {ds}")
        print(f"        -> {'; '.join(tag)}")
    print()
