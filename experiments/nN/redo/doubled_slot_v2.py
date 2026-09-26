"""doubled_slot_v1, broken down.  For each delayed pair member: home (the runner at s, inside the AP) or moved (at
s + 8m, far out); its event R = 8t* written as (8N+1)/d, d the flank's reduced distance and N its lap; and whether
(R, flank distance, lap) depend on m.  Grouped by c = (r - s) mod 8, the empty slot's offset from the doubled one."""
from fractions import Fraction as F
from math import floor
from collections import defaultdict
from doubled_slot_v1 import event

out = defaultdict(set)
for s in range(8):
    for r in range(8):
        if r == s: continue
        c = (r - s) % 8
        for m in range(1, 9):
            U = [x for x in range(8) if x != r] + [s + 8 * m]
            V = sorted(100 + u for u in U)
            for who, sp in (('home', 100 + s), ('moved', 100 + s + 8 * m)):
                k = V.index(sp); t, mv = event(V, k)
                if t <= F(1, 8): continue
                fl = [abs(v - sp) for v in V if v != sp and (abs(v - sp) * t) % 1 == F(1, 8)]
                d = min(fl); N = floor(d * t)
                out[(c, who)].add((s, 8 * t, d, N, m))
for c in range(1, 8):
    for who in ('home', 'moved'):
        rows = sorted(out[(c, who)])
        if not rows: print(f"c={c} {who:5s}: never delayed"); continue
        forms = defaultdict(set)
        for s, R, d, N, m in rows: forms[(s, R, d, N)].add(m)
        print(f"c={c} {who:5s}: {len(rows)} delayed (s,m) cases; events R = 8t* as (flank distance d, lap N) -> m values:")
        for (s, R, d, N), ms in sorted(forms.items())[:10]:
            print(f"      s={s}: R={R} = (8*{N}+1)/{d}   for m in {sorted(ms)}")
        if len(forms) > 10: print(f"      ... {len(forms) - 10} more")
