"""modgap_gap_v1 (2026-10-06): T's lonely set as a union of components; where a bystander's edge lands; two bystanders.  Exact.
Owner 2026-10-06 (chat): authorises a rule 7 exception for the termination attempt.  This file makes no termination claim; it records what the exact structure shows.
T minimal with cascade(T) = t*; L(T) = {s : T lonely at s}; d blocked at t* with edge E_d = (8 round(d t*) + 1)/(8d); U = T + {d}.
 GA [P] cascade(U) = E_d iff T is lonely at E_d  (d stands at 1/8 exactly at E_d and is blocked on [t*, E_d); lonely instants of U are lonely for T).  checked for every blocked d.
 GB [P] a closer c of T (f t_R = M + 7/8) is blocked on [t_R, F_c) with F_c = (8(M+1) + 1)/(8c): so c is in the way at E_d (> t_R) iff E_d < F_c.  checked; and the
        'other-only' continuation cases (no closer in the way at E_d) are exactly those with E_d >= F_c for every closer c.
 GC two bystanders d1 < d2 both blocked at t*: t12 = cascade(T + {d1, d2}), t1 = cascade(T + {d1}), t2 = cascade(T + {d2}).  [P] t12 >= max(t1, t2); equality iff
    d2 is clear at t1 (when t1 >= t2) or d1 is clear at t2 (when t2 >= t1)... recorded: share with t12 = max(t1, t2) ('no interaction'), and for t12 > max: the opener at t12 (d1, d2,
    or a T reading) and the roles.
Populations: first 300 non-unit-fraction S1 sets (GA, GB: d in [1,72]; GC: d1 < d2 in [1,30]).
[PROVISIONAL: counting tool; supports: the counts]"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, openers, component, cd, E8, E78
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
out = open('modgap_gap_v1.out', 'w'); out.write(__doc__ + "\n")
c = collections.Counter(); nset = 0; ex = []
for S in s1():
    if nset >= 300: break
    t = cascade(S); tR0, _ = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR0)) >= t: continue
    nset += 1
    T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
    TL = list(T); tR, clT = component(TL, t)
    Fc = [F(8 * (int(f * tR - E78) + 1) + 1, 8 * f) for f in clT]
    lonelyT = lambda s: all(cd(x * s) >= E8 for x in TL)
    blocked = [d for d in range(1, 73) if d not in T and cd(d * t) < E8]
    single = {}
    for d in blocked:
        E = F(8 * round(d * t) + 1, 8 * d); tp = cascade(TL + [d]); single[d] = tp
        c[('GA landing = E_d iff T lonely at E_d', (tp == E) == lonelyT(E))] += 1
        if E > tR and tp > E:
            inway = [x for x in clT if cd(x * E) < E8]
            c[('GB closer in the way at E_d iff E_d < F_c (all closers)', all((x in inway) == (E < fc) for x, fc in zip(clT, Fc)))] += 1
            other_only = not inway
            c[('GB no closer in the way  <=>  E_d >= F_c for every closer', other_only == all(E >= fc for fc in Fc))] += 1
    bl = [d for d in blocked if d <= 30]
    for d1, d2 in itertools.combinations(bl, 2):
        t12 = cascade(TL + [d1, d2]); m = max(single[d1], single[d2])
        c[('GC t12 >= max(t1, t2)', t12 >= m)] += 1
        if t12 == m: c['GC no interaction: t12 = max(t1, t2)'] += 1
        else:
            op = openers(TL + [d1, d2], t12)
            r = tuple(sorted('d1' if x == d1 else ('d2' if x == d2 else 'T') for x in op))
            c[('GC interaction (t12 > max): opener roles', r)] += 1
            if len(ex) < 10: ex.append((T, str(t), d1, d2, str(single[d1]), str(single[d2]), str(t12), op))
out.write("sets: %d\n" % nset)
for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
out.write("  examples of GC interaction: (T, t*, d1, d2, t1, t2, t12, openers)\n")
for e in ex: out.write("    %s\n" % (e,))
out.close(); print(open('modgap_gap_v1.out').read()[len(__doc__):])
