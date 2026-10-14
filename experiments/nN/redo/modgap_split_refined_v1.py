"""modgap_split_refined_v1 (2026-10-06): an r-dependent common-factor block split.  S = F + R, F a block with gcd G (all readings of F multiples of G), R the rest with k = |R| readings (1 <= k <= 6), x = max R.
[P] by the framework's own orders: the rest R (k readings) has a 1/(k+1)-lonely instant tau (order k+1: existenceAtN_k+1, k <= 6); on [tau - delta, tau + delta], delta = (1/(k+1) - 1/8)/x, every reading of R stays at distance >= 1/8
(a reading moves by at most x |s - tau|); F (|F| = 7 - k <= 6 readings) has a lonely instant at 1/7 hence 1/8 (order 7), and L(F) is invariant under t -> t + 1/G (each f in F is a multiple of G), so the closed interval
[tau - delta, tau + delta] of length 2 delta >= 1/G contains a lonely instant of F, which is lonely for S.  Condition:  2 G (1/(k+1) - 1/8) >= x  i.e. G >= x / (2 (1/(k+1) - 1/8)).  Constants K_k = 1/(2 (1/(k+1) - 1/8)):
k=1: 4/3, k=2: 12/5, k=3: 4, k=4: 20/3, k=5: 12, k=6: 28 (the record's block_split, which uses 28 for every k).
Recorded per population: the number of sets with a split of each k (some F with |R| = k satisfying the condition), by the smallest k, and how many of them the record's uniform-28 block_split already excludes.  Exact (Fractions)."""
import sys, json, itertools, collections, re
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from members_reach_check_v1 import load, full_residual, block_split
K = {k: 1 / (2 * (F(1, k + 1) - F(1, 8))) for k in range(1, 7)}
def refined(S):
    S = tuple(sorted(S)); res = []
    for k in range(1, 7):
        for R in itertools.combinations(S, k):
            Fb = [x for x in S if x not in R]
            G = reduce(gcd, Fb)
            if F(G) >= K[k] * max(R): res.append((k, R, G))
    return res
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
out = open('modgap_split_refined_v1.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('28 hard', hard), ('hard 41-60', h2), ('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 (all 5,431)', T1)):
    c = collections.Counter(); least = collections.Counter(); ex = []
    for S in sets:
        r = refined(S)
        if r:
            c['some refined split'] += 1; k0 = min(k for k, _, _ in r); least[k0] += 1
            c['  ... and the uniform 28 split already applies'] += block_split(S)
            if len(ex) < 3: ex.append((S if len(str(S[-1])) < 12 else '[%d-digit]' % len(str(S[-1])), r[0][0], r[0][2] if len(str(r[0][2])) < 14 else '[G %d-digit]' % len(str(r[0][2]))))
        c['uniform 28 block_split applies'] += block_split(S)
    out.write("\n==== %s: %d sets\n" % (name, len(sets)))
    for k, v in sorted(c.items()): out.write("  %s: %d\n" % (k, v))
    out.write("  smallest k among the refined splits: %s\n" % dict(sorted(least.items())))
    for e in ex: out.write("  e.g. %s, k = %d, G = %s\n" % e)
out.close(); print(open('modgap_split_refined_v1.out').read()[len(__doc__):])
