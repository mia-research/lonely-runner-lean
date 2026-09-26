"""Owner: use the cascade to show what happens, in its own terms (no bands, no flanks, no mirror).  For the longest
relays found (hard_cases_v1), every move: the instant t (in units of 1/d_min), the setter, the jump (to the setter's
exit), the runners that ENTER the subject's slot during that jump (they are the next move's candidates), and for every
runner its time until it next reaches the slot, as a fraction of the jump.  The cascade stops at the first jump during
which no runner enters.  Exact (Fraction); speeds as given, every runner moving; subject = the slowest runner."""
import re
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import nd

E8 = F(1, 8)

def next_entry(d, t):
    """first instant >= t at which reading d enters the slot (position crosses k - 1/8 upward)"""
    k = floor(d * t + E8) + 1
    return (k - E8) / d

def trace(V):
    ds = sorted(v - V[0] for v in V[1:]); m = ds[0]; t = F(1, 8 * m); rows = []
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < E8]
        if not way:
            nxt = min((next_entry(d, t) - t) * m for d in ds)
            rows.append((t * m, None, None, [], nxt)); return ds, rows
        cand = {i: (F(floor(ds[i] * t - E8) + 1) + E8) / ds[i] for i in way}
        s = max(cand, key=lambda x: cand[x]); t2 = cand[s]
        entered = sorted(i for i, d in enumerate(ds) if i not in way and t < next_entry(d, t) < t2)
        rows.append((t * m, s, (t2 - t) * m, entered, None)); t = t2

Vs = []
for line in open('hard_cases_v1.out'):
    mm = re.search(r'V (\[[^\]]*\])', line)
    if mm: Vs.append(eval(mm.group(1)))
for V in Vs[:3]:
    ds, rows = trace(V)
    print(f"\nspeeds {V}: readings / d_min {[round(d / ds[0], 3) for d in ds]}")
    print("   t*d_min   | in the way -> setter | jump (x d_min) | entered during the jump")
    for tm, s, jump, ent, nxt in rows:
        if s is None:
            print(f"   {float(tm):8.4f}  | LONELY: slot empty; the next runner reaches the slot {float(nxt):.4f} later")
        else:
            print(f"   {float(tm):8.4f}  | setter {s} | jump {float(jump):.4f} | entered {ent}")
    per = {}
    for tm, s, jump, ent, nxt in rows:
        if s is not None: per[s] = per.get(s, 0) + 1
    print(f"   moves {len(rows) - 1}; times each runner set: {dict(sorted(per.items()))}; entrants per jump: "
          f"{[len(r[3]) for r in rows if r[1] is not None]}")
