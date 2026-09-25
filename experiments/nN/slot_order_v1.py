"""Owner (2026-09-25): any arrangement is an AP read at the scale its speeds establish (scale
invariant); deviations move a runner's isolation away from the global event, but it occurs at the
SAME LOCATION around the circle.  Tested as: order the eight runners by speed (rank 1..8).  At the
AP's global event of class a (a odd), runner j sits in slot (j - k)*a mod 8 relative to subject k.
Claim: subject k is lonely at some instant where the other seven sit around the circle in that slot
order, for some class a.

Exact (fractions).  Relative speeds r_j = v_j - v_k are integers, period 1.  The lonely set is the
complement of the open zones ((m - 1/8)/|r|, (m + 1/8)/|r|) (BSM: touching zones leave the point);
within a lonely component the cyclic order changes only where two runners cross (r_i - r_j)t in Z,
so the order is tested at every component endpoint, isolated point, crossing time, and midpoint
between consecutive such times.
Objects: rule-miss sets as arrangements {0} u S (subject = the runner at speed 0); random
arrangements of 8 distinct integers in [0, 60], every subject.
"""
import json, random
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
def components(rs):
    z = sorted((F(8 * m - 1, 8 * abs(r)), F(8 * m + 1, 8 * abs(r))) for r in rs for m in range(0, abs(r) + 1))
    comps = []; cur = F(0)
    for a, b in z:
        if a > cur: comps.append((cur, a))
        elif a == cur and cur > 0: comps.append((cur, cur))
        cur = max(cur, b)
    return [(a, b) for a, b in comps if 0 < a and b < 1]
def slot_order_ok(v, k, t):
    """is there an odd a with the others in slot order (j - k)*a mod 8 around the circle at t?"""
    pos = {j: ((v[j] - v[k]) * t) % 1 for j in range(8) if j != k}
    order = [j for j, _ in sorted(pos.items(), key=lambda x: x[1])]
    for a in (1, 3, 5, 7):
        slots = [((j - k) * a) % 8 for j in order]
        if slots == sorted(slots): return a
    return None
def test(v, k):
    rs = [v[j] - v[k] for j in range(8) if j != k]
    classes = set()
    for lo, hi in components(rs):
        pts = {lo, hi}
        for i in range(8):
            for j in range(i + 1, 8):
                if i == k or j == k: continue
                dr = abs(v[i] - v[j])
                for m in range(ceil(lo * dr), floor(hi * dr) + 1): pts.add(F(m, dr))
        pts = sorted(p for p in pts if lo <= p <= hi)
        pts += [(pts[i] + pts[i + 1]) / 2 for i in range(len(pts) - 1)]
        for t in pts:
            a = slot_order_ok(v, k, t)
            if a: classes.add(a)
    return classes
rnd = random.Random(42)
H = [tuple(S) for S in json.load(open('hard_sets_41_60.json'))][:400]
res = Counter(); cls = Counter(); ex = []
for S in H:
    v = (0,) + S; c = test(v, 0)
    res['slot order holds' if c else 'NO lonely instant in slot order'] += 1
    for a in c: cls[a] += 1
    if not c and len(ex) < 3: ex.append(v)
print(f"400 rule-miss sets as arrangements {{0}} u S, subject at speed 0: {dict(res)};  classes found {dict(cls)};  e.g. {ex}")
res = Counter(); ex = []
for _ in range(300):
    v = tuple(sorted(rnd.sample(range(0, 61), 8)))
    for k in range(8):
        c = test(v, k); res['slot order holds' if c else 'NO lonely instant in slot order'] += 1
        if not c and len(ex) < 3: ex.append((v, k))
print(f"300 random arrangements in [0,60], all 8 subjects: {dict(res)};  e.g. {ex}")
