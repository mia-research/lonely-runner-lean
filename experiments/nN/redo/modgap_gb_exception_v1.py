"""modgap_gb_exception_v1 (2026-10-06): the single case of modgap_gap_v1 where GB failed ('a closer c of T is in the way at E_d iff E_d < F_c').  Re-run over the same first 300
non-unit-fraction S1 sets and print every failing case with the blocked windows of each closer written out exactly (cases where E_d is beyond F_c but c is blocked again in
a later lap of its own, i.e. E_d is in c's NEXT blocked window).  GB as stated used only the first blocked window [t_R, F_c); the exact blocked set of c is the union of
all its windows (M + k + 7/8, M + k + 9/8)/c.  Corrected statement GB': c is in the way at E_d iff E_d lies in some window ((k + 7/8)/c, (k + 9/8)/c) for a whole k >= M.  Checked."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, component, cd, E8, E78
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
out = open('modgap_gb_exception_v1.out', 'w'); out.write(__doc__ + "\n")
c = collections.Counter(); nset = 0
for S in s1():
    if nset >= 300: break
    t = cascade(S); tR0, _ = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR0)) >= t: continue
    nset += 1
    T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
    TL = list(T); tR, clT = component(TL, t)
    Ms = [int(f * tR - E78) for f in clT]
    Fc = [F(8 * (M + 1) + 1, 8 * f) for f, M in zip(clT, Ms)]
    for d in range(1, 73):
        if d in T or cd(d * t) >= E8: continue
        E = F(8 * round(d * t) + 1, 8 * d); tp = cascade(TL + [d])
        if not (E > tR and tp > E): continue
        inway = [x for x in clT if cd(x * E) < E8]
        orig = all((x in inway) == (E < fc) for x, fc in zip(clT, Fc))
        def win(x, M):
            k = math.floor(x * E - E78)          # E in ((k+7/8)/x, (k+9/8)/x) iff x E in (k + 7/8, k + 9/8)
            return k >= M and F(8 * k + 7, 8) < x * E < F(8 * k + 9, 8)
        fixed = all((x in inway) == win(x, M) for x, M in zip(clT, Ms))
        c[('GB original', orig)] += 1; c[("GB' (any window k >= M)", fixed)] += 1
        if not orig:
            out.write("FAIL GB: T=%s t*=%s t_R=%s closers=%s laps M=%s F_c=%s d=%d E_d=%s in the way=%s; E_d*c - M = %s\n" %
                      (T, t, tR, clT, Ms, [str(x) for x in Fc], d, E, inway, [str(x * E - M) for x, M in zip(clT, Ms)]))
for k, v in sorted(c.items(), key=str): out.write("%s: %d\n" % (k, v))
out.close(); print(open('modgap_gb_exception_v1.out').read()[len(__doc__):])
