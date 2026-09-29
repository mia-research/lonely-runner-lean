"""E181 follow-up: births.  At a simple-pinch BIRTH of the first window (window k born at tau, a single instant t0 with a
on +1/8 and b on -1/8), reflect the pair around its own period (least multiple Q > t0 with the other five strictly
clear at Q - t0).  By the same identity (time reversed) the reflected window should be a window at tau that DIES there:
a window just before tau, not just after.  Exact; same subsamples as partial_reflection_v1."""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import partial_reflection_v1 as PR
import deform_pinch_v1 as D
from quantity_tests_v1 import E8

DELTA = F(1, 10 ** 15)


def study(S):
    S = tuple(sorted(S)); x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    rows = []
    for e in r['events']:
        if e.get('kind') != 'birth' or e.get('tau') is None or e['tau'] == 0 or not e.get('simple'):
            continue
        tau, t0, k = e['tau'], e['t0'], e['kb']
        ds = D.readings_at(x, tau); m = min(ds)
        pos = [d * t0 - math.floor(d * t0) for d in ds]
        a = pos.index(E8); b = pos.index(F(7, 8))
        Qab = PR.lcm_rat(1 / ds[a], 1 / ds[b])
        found = None
        j0 = math.floor(t0 / Qab) + 1
        for j in range(j0, j0 + PR.JMAX):
            Q = j * Qab; t2 = Q - t0; lab = []; ok = True
            for i, d in enumerate(ds):
                if i in (a, b):
                    lab.append(int(Q * d) - k[i] - 1)
                else:
                    f = d * t2 - math.floor(d * t2)
                    if not (E8 < f < F(7, 8)):
                        ok = False; break
                    lab.append(math.floor(d * t2))
            if ok:
                found = (j, t2, tuple(lab)); break
        rec = dict(found=found is not None, R0=float(8 * m * t0))
        if found:
            j, t2, lab = found
            before = D.feasible(D.readings_at(x, tau - DELTA), lab)[0]
            after = D.feasible(D.readings_at(x, tau + DELTA), lab)[0]
            rec.update(j=j, R_part=float(8 * m * t2), dies=(before and not after))
        rows.append(rec)
    return rows


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    out = open('partial_reflection_v1b.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            rows = [x for rs in pool.map(study, sets) for x in rs]
            fnd = [x for x in rows if x['found']]
            out.write("\n== %s: simple-pinch births after s = 0: %d ==\n" % (name, len(rows)))
            out.write("  partner found (other five strictly clear at Q - t0): %d; the partner is a window that dies at tau: %d\n" %
                      (len(fnd), sum(x['dies'] for x in fnd)))
            if fnd:
                med = lambda v: sorted(v)[len(v) // 2]
                out.write("  multiple j: %s; R medians: born %.2f, partner %.2f\n" % (
                    dict(sorted(Counter(x['j'] for x in fnd).items())[:12]), med([x['R0'] for x in fnd]), med([x['R_part'] for x in fnd])))
    out.close()
    print(open('partial_reflection_v1b.out').read()[len(__doc__):])
