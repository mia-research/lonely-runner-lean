"""modgap_f7_forced_v1 (2026-10-06): the conditions forced by 'no lonely instant at 1/7' at the grid instants (Lean: exists_dvd_of_no_lonely_seven, exists_residue_of_no_lonely_seven) against EightResidual.
(F1) for every q in 2..7 some reading is divisible by q; (F2) some reading is 0, 1 or 7 mod 8; (F3) some reading is 0, 3 or 5 mod 8.  [P] EightResidual's field 'q divides some reading for q = 5, 6, 7, 8' implies all three
(2, 3, 4 divide 6 or 8 resp.; a multiple of 8 is 0 mod 8).  Checked on every stored residual member and hard set.  Then WHERE the 1/7 instants of residual sets lie: the least denominator q7 of a rational in the first
lonely component of S at 1/7 (exact: simplest rational in [t, r], Stern-Brocot), against the grid bound q <= 64 of the residual's small-resolution field: counts of q7 <= 64 and q7 > 64, and the distribution of q7 for the hard sets."""
import sys, re, json, math, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from members_reach_check_v1 import load, full_residual
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def casc7(S, t):
    while True:
        B = [x for x in S if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
def comp7(S):
    t = casc7(S, F(1, 7 * min(S)))
    best = None
    for x in S:
        N = math.ceil(x * t - F(6, 7)); e = (N + F(6, 7)) / x
        if best is None or e < best: best = e
    return t, best
def simplest(x, y):
    n = math.floor(x)
    if n == x: return F(n)
    if n + 1 <= y: return F(n + 1)
    return n + 1 / simplest(1 / (y - n), 1 / (x - n))
def forced(S):
    return (all(any(d % q == 0 for d in S) for q in range(2, 8)), any(d % 8 in (0, 1, 7) for d in S), any(d % 8 in (0, 3, 5) for d in S))
hard = sorted({tuple(map(int, m.group(1).split(','))) for m in (re.match(r'\s*\(([\d, ]+)\):', l) for l in open('../order5_transfer_v1.out')) if m}); hard = [h for h in hard if len(h) == 7]
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
out = open('modgap_f7_forced_v1.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('28 hard', hard), ('hard 41-60', h2), ('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1[:1500]', T1[:1500])):
    c = collections.Counter(); qs = collections.Counter(); fullres = 0
    for S in sets:
        f = forced(S); c['F1 all q<=7'] += f[0]; c['F2 residue 0,+-1'] += f[1]; c['F3 residue 0,+-3'] += f[2]
        l, r = comp7(S); q7 = simplest(l, r).denominator
        qs['q7 <= 64' if q7 <= 64 else ('q7 in (64, 1000]' if q7 <= 1000 else 'q7 > 1000')] += 1
    out.write("\n==== %s: %d sets\n  forced conditions satisfied: %s\n  least denominator of the first 1/7 component: %s\n" % (name, len(sets), dict(c), dict(qs)))
out.close(); print(open('modgap_f7_forced_v1.out').read()[len(__doc__):])
