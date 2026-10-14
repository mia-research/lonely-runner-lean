"""modgap_takeover_v1 (2026-10-06): the 8% of modgap_bystander_v1 where the bystander's takeover continues the chain (category iii).  For T minimal with
cascade(T) = t*, bystander d blocked at t*, t' = cascade(T + {d}) later than d's own edge.  Recorded per case (all listed in the .out as lines after the counts, first 60):
  x = the opener of t' (reading at 1/8 there), classified: x = d ; x = e (T's own opener at t*) ; x = f (T's closer at its t_R) ; x in the chain setters P(T) ; x in T but never a
  setter of T's path (a former bystander of T that now sets: role swap) ; and whether the new path's setters are all inside T + {d}.
  Also: number of moves from d's edge to t' (the chain length after the takeover), and whether e is blocked at d's edge (is the old opener the one pushed).
Population as modgap_bystander_v1 (first 4,000 non-unit-fraction S1 sets; d in [1,72] not in T).  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from functools import reduce
from math import gcd
from modgap_lib_v1 import cascade, cascade_path, openers, component, cd, E8
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
out = open('modgap_takeover_v1.out', 'w'); out.write(__doc__ + "\n")
c = collections.Counter(); lines = []; nset = 0
for S in s1():
    if nset >= 4000: break
    t = cascade(S); tR0, cl0 = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR0)) >= t: continue
    nset += 1
    T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
    pathT = cascade_path(list(T)); PT = {d for _, d in pathT if d}
    tR, clT = component(list(T), t); eT = openers(list(T), t); fT = clT
    for d in range(1, 73):
        if d in T: continue
        if t * 8 * 1 and cd(d * t) >= E8: continue
        U = list(T) + [d]; pathU = cascade_path(U); tp = pathU[-1][0]
        edge = F(8 * round(d * t) + 1, 8 * d)
        if tp == edge: continue
        x = openers(U, tp)
        newset = {y for _, y in pathU if y}
        cls = []
        for xx in x:
            if xx == d: cls.append('d')
            elif xx in eT: cls.append('e (T\'s old opener)')
            elif xx in fT: cls.append('f (T\'s old closer)')
            elif xx in PT: cls.append('in P(T), not e or f')
            else: cls.append('in T, not a setter of T (role swap)')
        key = tuple(sorted(set(cls)))
        c[('opener of t\'', key)] += 1
        c[('new path setters all in T + {d}', newset <= set(U))] += 1
        c[('e blocked at d\'s edge', e_b := any(cd(e * edge) < E8 for e in eT))] += 1
        moves_after = sum(1 for ti, _ in pathU if ti > edge)
        c[('moves after d\'s edge (>= 1)', min(moves_after, 4))] += 1
        c[('d > max T', d > max(T))] += 1
        if len(lines) < 60: lines.append((T, str(t), d, str(edge), str(tp), x, key, sorted(PT), eT, fT))
for k, v in sorted(c.items(), key=str): out.write("%s: %d\n" % (k, v))
out.write("\nfirst 60 cases: (T, t*, d, d's edge, t', openers of t', classes, P(T), e, f)\n")
for l in lines: out.write("  %s\n" % (l,))
out.close(); print(open('modgap_takeover_v1.out').read()[len(__doc__):][:3800])
