"""Named instants for EVERY runner of the doubled-slot family (E40), as formulas in m, checked exactly for m = 1..300.
Arrangement (unsorted, indexed by slot): v(i) = 100 + i for i != r, v(r) = 100 + s + 8m.  Slot s doubled, slot r empty.
Candidates:
  non-pair runner (i not in {s, r}):  t = 1/8
  far member (index r):               t = 1/(8 d_min)  (R1), except where the check fails -> printed
  home member (index s):              interior s in 1..6, or (s,r) in {(0,7),(7,0)}: t = 1/8 + 1/(64m)
                                      ends: t0 = (8N+1)/(8d) from the E40 table; t0 + 1/(64m) when the partner reads a
                                      whole number of laps at t0
Every failure is printed with the cascade's own event for that case."""
from fractions import Fraction as F
from math import floor
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely(v, k, t): return all(nd((v[i] - v[k]) * t) >= F(1, 8) for i in range(8) if i != k)
def event(v, k):
    ds = [abs(v[i] - v[k]) for i in range(8) if i != k]; t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
END = {2: (7, 3), 3: (7, 2), 4: (5, 1), 5: (6, 1), 6: (7, 1)}   # c -> (d, N) at s = 0; mirror at s = 7 with c -> 8 - c
def home_t(s, r, m):
    c = (r - s) % 8
    if 1 <= s <= 6 or (s, r) in ((0, 7), (7, 0)): return F(1, 8) + F(1, 64 * m)
    cc = c if s == 0 else 8 - c
    if cc not in END: return None
    d, N = END[cc]; t0 = F(8 * N + 1, 8 * d)
    return t0 + F(1, 64 * m) if (8 * m * t0) % 1 == 0 else t0
fails = []; checked = 0
for s in range(8):
    for r in range(8):
        if r == s: continue
        for m in range(1, 301):
            v = [100 + i for i in range(8)]; v[r] = 100 + s + 8 * m
            for k in range(8):
                if k == s: t = home_t(s, r, m)
                elif k == r: t = F(1, 8 * min(abs(v[i] - v[k]) for i in range(8) if i != k))
                else: t = F(1, 8)
                checked += 1
                if t is None or not lonely(v, k, t):
                    fails.append((s, r, m, 'home' if k == s else 'far' if k == r else 'other', t, event(v, k)))
print(f"checked {checked} (runner, arrangement) cases, m = 1..300; failures {len(fails)}")
from collections import defaultdict
g = defaultdict(list)
for s, r, m, who, t, ev in fails: g[(s, r, who)].append((m, ev))
for (s, r, who), L in sorted(g.items()):
    print(f"  s={s} r={r} {who}: {len(L)} m values, e.g. " + ", ".join(f"m={m}: cascade t*={ev}" for m, ev in L[:5]))
