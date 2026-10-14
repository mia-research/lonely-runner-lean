"""modgap_takeover_v2 (2026-10-06): the clean-takeover criterion.  T minimal with cascade(T) = t*, t_R(T) the right end of T's lonely component at t*, d blocked at t*
with edge E_d = (8 round(d t*) + 1)/(8 d).
 K1 [P] if E_d <= t_R(T) then cascade(T + {d}) = E_d and d is the opener (T is lonely on [t*, t_R(T)], so at E_d every reading of T is clear, and d sits at 1/8 exactly;
        no lonely instant of T + {d} lies in [t*, E_d) because d is blocked there (its blocked window ends at E_d)).
 K2 [P] if E_d > t_R(T) then cascade(T + {d}) > E_d is not forced by this argument; recorded: how often cascade(T + {d}) = E_d anyway, and the opener at the landing.
Checked for every blocked d in [1, 72], over the first 4,000 non-unit-fraction S1 sets and the first 4,000 of T2.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, openers, component, cd, E8
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
out = open('modgap_takeover_v2.out', 'w'); out.write(__doc__ + "\n")
for name, gen, DM in (('S1', s1(), 72), ('T2', t2(), 84)):
    c = collections.Counter(); nset = 0
    for S in gen:
        if nset >= 4000: break
        t = cascade(S); tR0, _ = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR0)) >= t: continue
        nset += 1
        T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
        tR, clT = component(list(T), t)
        for d in range(1, DM + 1):
            if d in T or cd(d * t) >= E8: continue
            E = F(8 * round(d * t) + 1, 8 * d); tp = cascade(list(T) + [d])
            if E <= tR:
                c[('K1: E_d <= t_R(T) => landing = E_d and d is the opener', tp == E and (d * tp - E8).denominator == 1)] += 1
            else:
                c[('K2: E_d > t_R(T); landing = E_d', tp == E)] += 1
                c[('K2: E_d > t_R(T); landing > E_d', tp > E)] += 1
    out.write("\n==== %s: %d sets\n" % (name, nset))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
out.close(); print(open('modgap_takeover_v2.out').read()[len(__doc__):])
