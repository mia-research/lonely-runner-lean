"""Follow-up to late_event_law_v1 (exact).  In all three late events the subject's FAR runner (largest
difference) reads S = d_max/d_min in (7, 8) at the subject's own AP scale: it sits in the subject's slot
zone just below 8, i.e. it has come round the wrap into the subject's slot.  Three checks:
 (a) scale-relative shifts for the third case (shift by j * d_min / 60, since +/-3 is 0.15% of d_min);
 (b) how often S in (7,8) gives a late event among random arrangements (so the pattern is not read as sufficient);
 (c) a hill-climb for late events (u* > 1) with S >= 8, and with S <= 7 impossible by Thm 4.8."""
import random
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd

def cascade(ds, cap=3000):
    t = F(1, 8 * min(ds)); n = 0
    while n < cap:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, n
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); n += 1
    return None, n

def ustar(V, k):
    ds = readings(V, k); t, n = cascade(ds); return min(ds) * t, n, F(max(ds), min(ds))

print("(a) third case, scale-relative shifts (step = d_min/60 = 33)")
V = [1,1975,5265,6910,8737,9589,11845,15135]; k = 0
for j in range(1, 8):
    out = []
    for m in (-3, -2, -1, 1, 2, 3):
        W = V[:]; W[j] += 33 * m
        if len(set(W)) < 8 or min(W) <= 0: continue
        u, n, S = ustar(W, k); out.append(f"{m:+d}: {float(u):.3f}")
    print(f"  runner {V[j]:>6}: " + "; ".join(out))

print("\n(b) random arrangements in [1,400]: runners with S in (7,8), and how many are late (u* > 1)")
rnd = random.Random(7); inband = late = late_out = tot = 0
for _ in range(6000):
    V = rnd.sample(range(1, 401), 8)
    for k in range(8):
        u, n, S = ustar(V, k); tot += 1
        if 7 < S < 8:
            inband += 1; late += (u > 1)
        elif u > 1: late_out += 1
print(f"  {tot} runners; S in (7,8): {inband}, of which late: {late}; late with S outside (7,8): {late_out}")

print("\n(c) hill-climb for a late event with S >= 8 (objective u*, subject fixed as runner 0, S >= 8 enforced)")
best_overall = F(0); best_V = None
for restart in range(12):
    r = random.Random(100 + restart)
    while True:
        V = sorted(r.sample(range(1, 500), 8))
        u, n, S = ustar(V, 0)
        if S >= 8: break
    cur = u
    for it in range(2500):
        W = V[:]; j = r.randrange(1, 8); W[j] = max(1, W[j] + r.randint(-15, 15))
        if len(set(W)) < 8 or min(W) <= 0: continue
        u, n, S = ustar(W, W.index(V[0]) if V[0] in W else 0)
        if S >= 8 and u >= cur:
            V, cur = W, u
    if cur > best_overall: best_overall, best_V = cur, V
    print(f"  restart {restart:2d}: best u* = {cur} ({float(cur):.4f}) at V={V}, S={float(ustar(V,0)[2]):.3f}")
print(f"  overall best with S >= 8: u* = {best_overall} ({float(best_overall):.4f})")
