"""modgap_div_paths_v1 (2026-10-06): the 1/7-cascade of the full seven readings on the divisible family (DA 41, DB 371 stored members of shape (3, oooo), every odd reading dividing a cofactor).
Per member: the walk's states, for each state the set of readings in the way at 1/7 and the setter, as a role string over {M multiple of 8, O odd} with the reading's rank by size (0 = smallest); the landing state;
then the distribution of (setter role sequence) over the family and the first state at which S is lonely at 1/7.  Exact."""
import sys, json, math, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def walk(S, cap=60):
    t = F(1, 7 * min(S)); path = []
    for _ in range(cap):
        B = [x for x in S if cd(x * t) < H]
        if not B: path.append((t, B, None)); return path
        nt, st = max((F(7 * round(x * t) + 1, 7 * x), x) for x in B)
        path.append((t, B, st)); t = nt
    return path
st = json.load(open('divisible_members_v2.json'))
DA = list(dict.fromkeys(tuple(sorted(S)) for S in st['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in st['B']))
role = lambda S, d: ('M' if d % 8 == 0 else 'O') + str(S.index(d))
out = open('modgap_div_paths_v1.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('DA', DA), ('DB', DB)):
    seqs = collections.Counter(); blk = collections.Counter(); lens = collections.Counter(); first_blocked = collections.Counter()
    ex = []
    for S in sets:
        P = walk(S)
        seq = tuple(role(S, s) for _, _, s in P if s)
        seqs[tuple(r[0] + ('' ) for r in seq)] += 1
        lens[len(P) - 1] += 1
        first_blocked[tuple(sorted(role(S, x)[0] for x in P[0][1]))] += 1
        if len(ex) < 4: ex.append((S, [(str(t)[:18], [role(S, x) for x in B], role(S, s) if s else None) for t, B, s in P]))
    out.write("\n==== %s: %d members\n  moves in the 1/7-walk: %s\n  setter roles in order (M/O only): %s\n  readings in the way at the first state: %s\n" %
              (name, len(sets), dict(sorted(lens.items())), dict(sorted(seqs.items(), key=lambda kv: -kv[1])), dict(first_blocked)))
    for S, p in ex:
        out.write("  example (ranks 0..6; M = multiple of 8, O = odd): readings of %d digits; path (t, in the way, setter): %s\n" % (len(str(S[-1])), p))
out.close(); print(open('modgap_div_paths_v1.out').read()[len(__doc__):][:5000])
