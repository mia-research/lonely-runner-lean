"""The late events read off the cascade, no search.  Exact.

Input: the 34 late cases of late_event_S9_search_v1.out (control arm) plus the 3 recorded hard cases and the
S = 8 case of late_event_law_v2.  For each subject: the cascade in the R coordinate (R = d_min / D = 8 d_min t,
readings s_j = d_j / d_min), every move as (R before, setter reading s, the setter's lap M, R after).

Proved facts used (MANUSCRIPT_v21): R_final never lies in (7,9) (Thm 11.2); a move multiplies R by less than 9/7
(Thm 6.25).  Hence a late event (R_final > 7) must have a step landing in (7, 9), where d_min's own reading R is
within 1 of 8.  Checked here, together with: who blocks R = 1 (the bound), and the far runner's role.

Then the lap probe: give the far runner one or two extra laps (reading S -> S + 8, S + 16, i.e. speed difference
+ 8 d_min, + 16 d_min, other runners unchanged) and read the event again."""
import re, ast
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import readings, nd

def trace(ds):
    dmin = min(ds); t = F(1, 8 * dmin); steps = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, steps
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); tn = cand[d]
        M = floor(d * tn)                       # the lap whose opening is taken
        steps.append((8 * dmin * t, F(d, dmin), M, 8 * dmin * tn, sorted(F(x, dmin) for x in way)))
        t = tn

cases = []
for line in open('late_event_S9_search_v1.out'):
    m = re.search(r'LATE seed \d+: .* V=(\[[^\]]*\]) subject (\d+)', line)
    if m: cases.append((ast.literal_eval(m.group(1)), int(m.group(2))))
cases += [([27,70,107,137,159,188,344,393], 393), ([1,31,75,97,128,160,176,225], 1),
          ([1,1975,5265,6910,8737,9589,11845,15135], 1), ([109,154,234,273,313,337,390,469], 109)]
seen = set(); uniq = []
for V, s in cases:
    key = (tuple(sorted(V)), s)
    if key not in seen: seen.add(key); uniq.append((sorted(V), s))
print(f"{len(uniq)} distinct late subjects\n")

through79 = 0; first_blocker = Counter(); dmin_sets = 0; far_first = 0; far_setter_counts = Counter()
rows = []
for V, s in uniq:
    k = V.index(s); ds = readings(V, k); dmin = min(ds); S = F(max(ds), dmin)
    t, steps = trace(ds); R = 8 * dmin * t
    lands = [st for st in steps if 7 < st[3] < 9]
    through79 += bool(lands)
    step79 = next(i for i, st in enumerate(steps) if 7 < st[3] < 9)
    nxt = steps[step79 + 1]
    dmin_sets += (nxt[1] == 1)
    b0 = steps[0][4]                                   # readings in the way at R = 1
    far_first += (S in b0)
    first_blocker[tuple(sorted(float(x) for x in b0))] = 0
    far_setter_counts[sum(1 for st in steps if st[1] == S)] += 1
    rows.append((V, s, S, R, len(steps), step79, steps))
print(f"every late event lands in (7,9) at some step: {through79} of {len(uniq)}")
print(f"the move after that landing is set by d_min itself (reading 1): {dmin_sets} of {len(uniq)}")
print(f"the far runner is in the way at the bound R = 1: {far_first} of {len(uniq)}")
print(f"moves set by the far runner per case: {dict(sorted(far_setter_counts.items()))}\n")

print("Band-0 climb of each case: R at each step (R <= 7 part), and the setters' readings with lap M")
for V, s, S, R, n, i79, steps in rows[:12]:
    climb = " ".join(f"{float(st[0]):.3f}[{float(st[1]):.2f}:{st[2]}]" for st in steps[:i79 + 1])
    print(f"  {V} subj {s}: S={float(S):.3f} R*={float(R):.3f} moves={n}\n    {climb} -> {float(steps[i79][3]):.3f}")

print("\nLap probe: the far difference given extra laps, d_max -> d_max + 8 d_min, + 16 d_min (other differences")
print("unchanged; realised with positive speeds as the runner at speed 1 of (1, 1 + d, ...)); event in laps u*")
res = Counter()
for V, s, S, R, n, i79, steps in rows:
    k = V.index(s); ds = readings(V, k); dmin = min(ds); dmax = max(ds)
    out = [f"u*={float(R/8):.3f}"]
    for extra in (8, 16):
        dsW = sorted(set(d for d in ds if d != dmax) | {dmax + extra * dmin})
        tW, stW = trace(dsW); u = min(dsW) * tW
        out.append(f"+{extra}: u*={float(u):.3f} ({len(stW)} mv)"); res[(extra, u > 1)] += 1
    print(f"  {V} subj {s} S={float(S):.3f}: " + "; ".join(out))
print("\nlap probe summary ((extra, still late?): count):", dict(res))
