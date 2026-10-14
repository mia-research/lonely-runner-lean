"""modgap_roles_v1 (2026-10-06): the roles of the readings along the cascade path and their interaction with the setters' moduli.  Exact.
Path states t_0 = 1/(8 d_min), t_1, ..., t_n = t*; at state t_i the blocked readings are those with ||d t_i|| < 1/8; the setter of step i+1 is the blocked reading
maximising (8 round(d t_i) + 1)/(8 d).  Roles: setter (sets some step), freed (blocked at some state, never the setter), pure (never blocked at any state t_0..t_n).
Statements recorded, per population (S1 non-unit-fraction sets, T2, T3; definitions as modgap_ancestor_v1):
  R1 [P] every reading blocked at t_i is clear or passed at t_{i+1} unless it crosses the whole clear arc in the jump (speed d times the jump >= 3/4): count of
         blocked-at-i readings that are blocked again at t_{i+1}, and whether each such reading satisfies d (t_{i+1} - t_i) >= 3/4 (the crossing case).
  R2  the numbers of setters, freed, pure readings per set, and the cross-tabulation with the chain length.
  R3  for the PURE readings: slack at t* = min(||d t*|| - 1/8) in units of 1/(8 e) (e the final opener): against the slack of EVERY integer d' in [1, d_max] that is clear at t*
      (exact enumeration, same set), reported as: share of pure readings whose slack is below the median slack of all clear integers.
  R4  the joint-allowance check: for each pure reading, the number of path states at which d lies in the allowed residue window (all of them, by definition); and for random
      integers d' in [1, d_max] (every integer, exact), the number never blocked on the path: reported as a count, to see how restrictive the joint condition is.
[PROVISIONAL: counting tool; supports: the comparison of pure readings with the integers that are clear at t*]"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from functools import reduce
from math import gcd
from modgap_lib_v1 import cascade_path, openers, component, simplest, cd, E8
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
def t3():
    pools = {k: [d for d in range(1, 41) if d % 8 == k] for k in range(8)}
    for p in itertools.product(pools[0], pools[1], pools[2], pools[3], pools[5], pools[6], pools[7]):
        S = tuple(sorted(p))
        if reduce(gcd, S) == 1: yield S
out = open('modgap_roles_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen in (('S1', s1()), ('T2', t2()), ('T3', t3())):
    c = collections.Counter(); roles = collections.Counter(); n = 0; below = tot = 0; allclear_n = []; reb = collections.Counter()
    for S in gen:
        path = cascade_path(S); ts = [p for p, _ in path]; t = ts[-1]
        tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t)
        if len(op) != 1: continue
        e = op[0]; n += 1
        setters = {d for _, d in path if d}
        blocked_at = [[d for d in S if cd(d * ti) < E8] for ti in ts]
        everblocked = set(x for b in blocked_at for x in b)
        freed = everblocked - setters; pure = set(S) - everblocked
        roles[(len(path) - 1 if len(path) < 6 else 6, len(setters), len(freed), len(pure))] += 1
        for i in range(len(ts) - 1):
            for d in blocked_at[i]:
                if cd(d * ts[i + 1]) < E8:
                    reb['re-blocked'] += 1; reb['  of which d*jump >= 3/4'] += (d * (ts[i + 1] - ts[i]) >= F(3, 4))
                else: reb['cleared by the jump'] += 1
        # R3
        slack = lambda d: (cd(d * t) - E8) * 8 * e
        allclear = sorted(slack(d) for d in range(1, S[-1] + 1) if cd(d * t) >= E8)
        med = allclear[len(allclear) // 2]
        for d in pure:
            tot += 1; below += slack(d) < med
        # R4
        never = [d for d in range(1, S[-1] + 1) if all(cd(d * ti) >= E8 for ti in ts)]
        allclear_n.append((len(never), S[-1]))
    out.write("\n==== %s: %d sets (unique opener, non-unit-fraction)\n" % (name, n))
    out.write("  R1 across jumps: %s\n" % dict(reb))
    byrole = collections.Counter()
    for (L, ns, nf, npure), v in roles.items(): byrole[(ns, nf, npure)] += v
    out.write("  R2 (setters, freed, pure) -> sets: %s\n" % dict(sorted(byrole.items())))
    out.write("  R2 (moves capped 6, setters, freed, pure) first 25: %s\n" % dict(sorted(roles.items())[:25]))
    out.write("  R3 pure readings with slack below the median slack of all integers clear at t*: %d of %d\n" % (below, tot))
    out.write("  R4 integers d' in [1, d_max] never blocked on the whole path, per set: min %d, max %d; sets: %d; (count, d_max) histogram of count: %s\n" %
              (min(a for a, _ in allclear_n), max(a for a, _ in allclear_n), len(allclear_n), dict(sorted(collections.Counter(a for a, _ in allclear_n).items())[:15])))
out.close(); print(open('modgap_roles_v1.out').read()[len(__doc__):])
