"""modgap_shell_v1 (2026-10-06): the 1/7-cascade of the full seven readings and the shell states.  Exact.  A state s of the cascade at threshold 1/7 (start 1/(7 d_min); move to the largest
(7 round(x s) + 1)/(7 x) among readings x with ||x s|| < 1/7) has blocked set B(s) = readings with ||x s|| < 1/7.  A SHELL state: |B| = 0 (S lonely at 1/7) or |B| = 1, B = {d}, ||d s|| >= 1/8:
there the other six are at distance >= 1/7 and d at >= 1/8, so (6,1) holds at s [P].  Walk up to CAP = 400 states.  Recorded per set: the index of the first shell state (None if none within CAP), the
sizes |B| along the walk (counts over states), whether the first state with |B| <= 1 is a shell state, and, for the walk's states with |B| = 1, the position of d in [0, 1/7).  Populations: the 28 hard sets,
hard_sets_41_60.json, the stored members (C, BS, DA, DB, T1[:1500]); and the two tight sets (1..7), (1,2,3,4,5,7,12) for contrast."""
import sys, re, json, collections, math
sys.path.insert(0, '.')
from fractions import Fraction as F
from members_reach_check_v1 import load, full_residual
H = F(1, 7); E8 = F(1, 8); CAP = 400
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def walk(S):
    t = F(1, 7 * min(S)); states = []
    for i in range(CAP):
        B = [x for x in S if cd(x * t) < H]
        states.append((t, B))
        if not B: return states
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return states
def shell(t, B):
    return len(B) == 0 or (len(B) == 1 and cd(B[0] * t) >= E8)
hard = sorted({tuple(map(int, m.group(1).split(','))) for m in (re.match(r'\s*\(([\d, ]+)\):', l) for l in open('../order5_transfer_v1.out')) if m})
hard = [h for h in hard if len(h) == 7]
h2 = []
def wk(x):
    if isinstance(x, list) and x and all(isinstance(v, int) for v in x) and len(x) == 7: h2.append(tuple(sorted(x)))
    elif isinstance(x, list):
        for v in x: wk(v)
    elif isinstance(x, dict):
        for v in x.values(): wk(v)
wk(json.load(open('../hard_sets_41_60.json'))); h2 = sorted(set(h2))
C = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
st = json.load(open('divisible_members_v2.json'))
DA = list(dict.fromkeys(tuple(sorted(S)) for S in st['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in st['B']))
known = set(C) | set(BS) | set(DA) | set(DB)
T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in json.load(open('members_5978_v1.json'))) if S not in known and full_residual(S)]
out = open('modgap_shell_v1.out', 'w'); out.write(__doc__ + "\n")
pops = (('28 hard', hard), ('hard 41-60', h2), ('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1[:1500]', T1[:1500]), ('tight', [(1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 12)]))
for name, sets in pops:
    c = collections.Counter(); first = collections.Counter(); sizes = collections.Counter(); firstB = collections.Counter(); ex = []
    for S in sets:
        W = walk(S)
        idx = next((i for i, (t, B) in enumerate(W) if shell(t, B)), None)
        first[idx if idx is None or idx <= 8 else '>8'] += 1
        for t, B in W: sizes[len(B)] += 1
        j = next((i for i, (t, B) in enumerate(W) if len(B) <= 1), None)
        c['first state with |B| <= 1 reached'] += j is not None
        c['  ... and it is a shell state'] += (j is not None and shell(*W[j]))
        c['walk ended in S lonely at 1/7 (|B| = 0)'] += (not W[-1][1])
        c['walk hit the cap with no shell state'] += idx is None
        if idx is None and len(ex) < 5: ex.append((S if len(str(S[-1])) < 12 else '[%d-digit]' % len(str(S[-1])), len(W)))
    out.write("\n==== %s: %d sets\n  index of the first shell state: %s\n  |B| over all states visited: %s\n" % (name, len(sets), dict(sorted(first.items(), key=str)), dict(sorted(sizes.items()))))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    for e in ex: out.write("  no shell state within the cap: %s (states %d)\n" % e)
out.close(); print(open('modgap_shell_v1.out').read()[len(__doc__):])
