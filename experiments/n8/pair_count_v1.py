"""EXACT count, not a rate.  After gcd_covariant, blocking at modulus beta for a reading of
coprime part alpha is: the residues v = alpha*(8k+1) mod 8*beta run over v == alpha' (mod 8),
alpha' = alpha mod 8, hitting each of the beta such residues once.  It blocks iff v < beta or
v > 7*beta.  So

    blocked(alpha', beta) = #{ j >= 0 : alpha' + 8j < beta }  +  #{ j : 7beta < alpha' + 8j < 8beta }

Verify the formula, then read off when it differs between alpha' in {1,7} and {3,5}.
"""
from math import gcd

def formula(ap, beta):
    lo = sum(1 for j in range(0, beta+1) if 0 <= ap + 8*j < beta)
    hi = sum(1 for j in range(0, beta+1) if 7*beta < ap + 8*j < 8*beta)
    return lo + hi

def actual(ap, beta):
    """Direct: count v == ap mod 8 in [0,8beta) with min(v,8beta-v) < beta."""
    return sum(1 for v in range(0, 8*beta) if v % 8 == ap and min(v, 8*beta - v) < beta)

bad = 0
for beta in range(2, 300):
    for ap in (1,3,5,7):
        if formula(ap, beta) != actual(ap, beta): bad += 1
print(f"1. formula vs direct count, beta < 300, alpha' in {{1,3,5,7}} : mismatches {bad}")

print(f"\n2. blocked count by (alpha', beta mod 8), for beta = 8t + r  (t large)")
print(f"   {'beta mod 8':>11} {'ap=1':>6} {'ap=3':>6} {'ap=5':>6} {'ap=7':>6}   {'{1,7} vs {3,5}':>16}")
t = 40
for r in range(8):
    beta = 8*t + r
    if beta < 2: continue
    c = [formula(ap, beta) for ap in (1,3,5,7)]
    pm1 = c[0] + c[3]; pm3 = c[1] + c[2]
    d = pm1 - pm3
    print(f"   {r:>11} {c[0]:>6} {c[1]:>6} {c[2]:>6} {c[3]:>6}   {d:>+16}"
          + ("   SPLIT" if d != 0 else ""))
print(f"\n3. is the split exactly beta = 2,3,6,7 mod 8, with sign +1 at 2,3 and -1 at 6,7?")
ok = True
for beta in range(9, 600):
    c = [formula(ap, beta) for ap in (1,3,5,7)]
    d = (c[0]+c[3]) - (c[1]+c[2])
    r = beta % 8
    exp = 1 if r in (2,3) else (-1 if r in (6,7) else 0)
    if (d > 0) - (d < 0) != exp: ok = False; print(f"   exception beta={beta} r={r} d={d}")
print(f"   {ok}")
