"""modgap_open_v3 (2026-10-06): re-block events in the real residual members.  R1 [P] (modgap_roles_v1): a reading in the way at state t_i and again at a later state t_j was moved across the whole clear
arc between them (d (t_j - t_i) >= 3/4).  Checked over every re-block event of all 6,677 members (any pair of states i < j, not only consecutive), and the member with the most re-blocks printed in full
(state, setter, readings in the way as (digits, residue mod 8, laps traversed since the previous state in which it was in the way)).  Exact."""
import sys, math, collections
sys.path.insert(0, '.')
exec(open('modgap_open_v1.py').read().split("out = open('modgap_open_v1.out'")[0])
from fractions import Fraction as F
out = open('modgap_open_v3.out', 'w'); out.write(__doc__ + "\n")
c = collections.Counter(); worst = (0, None)
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1)):
    for S in sets:
        path = cascade_path(S); ts = [q for q, _ in path]; last = {}; ev = 0
        for i, ti in enumerate(ts):
            for d in S:
                if cd(d * ti) < E8:
                    if d in last:
                        j = last[d]; c[('re-block: d (t_i - t_j) >= 3/4', d * (ti - ts[j]) >= F(3, 4))] += 1; ev += 1
                    last[d] = i
        c['events'] += ev
        if ev > worst[0]: worst = (ev, (name, S, path))
for k, v in sorted(c.items(), key=str): out.write("%s: %d\n" % (k, v))
ev, (name, S, path) = worst
out.write("\nmember with the most re-block events: %d events, source %s, %d-digit readings, residues mod 8 %s\n" % (ev, name, len(str(S[-1])), [d % 8 for d in S]))
ts = [q for q, _ in path]; last = {}
for i, (ti, setter) in enumerate(path):
    ways = []
    for d in S:
        if cd(d * ti) < E8:
            ways.append((S.index(d), d % 8, math.floor(d * (ti - ts[last[d]])) if d in last else None)); last[d] = i
    out.write("  state %d: setter index %s; in the way (index, residue mod 8, laps since last in the way): %s\n" % (i, S.index(setter) if setter else None, ways))
out.close(); print(open('modgap_open_v3.out').read()[len(__doc__):][:3500])
