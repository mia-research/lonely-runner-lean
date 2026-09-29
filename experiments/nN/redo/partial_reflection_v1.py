"""E181 (2026-09-29): partial reflection at the deformation's pinches, against the cascade.

Owner: "yes put the reflection identity in Lean and test it" and "Could there be a series of pinches interacting
between the other 6 so its like an orchestrated overlapping pattern?"

Lean: LonelyRunner/LRC/Spec/PartialReflectionN.lean, partial_reflected_right_inequalities (built on PinchReflectionN).
Reflect only the pinching pair R = {a, b} (a on +1/8 leaving, b on -1/8 entering, at the dying window's instant t0)
around a common period Q of the PAIR alone (Q d_a, Q d_b whole at tau; Q > t0).  The reflected instant is Q - t0; the
pair's labels there are Q d_i - k_i - 1; every other reading keeps its own label floor(d_c (Q - t0)) and must be
strictly clear at Q - t0 (the theorem's hypothesis hfree).  Q runs over multiples j Q_ab of the pair's least period.

Per death of the first window along the deformation paths of E178 (subsamples), recorded exactly:
  * the least multiple j for which the other five readings are strictly clear (the theorem applies); its R;
  * THEOREM CHECK: at tau + delta the reflected labels form a window (the theorem's conclusion) -- must hold whenever
    the hypotheses hold;
  * PLACE TEST: is the cascade's replacement (the new first window just after tau) that partial reflection?
  * for comparison, the full reflection's R (period of all seven readings).
Simple pinches only (a and b named); multi-pinches reported by count.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from quantity_tests_v1 import cd, E8

DELTA = F(1, 10 ** 15)
JMAX = 400
_orig = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig(x, sa, ka, sb, kb)
    rec['ka'], rec['kb'] = ka, kb
    return rec


D.classify = classify_k


def lcm_rat(r1, r2):
    """Least positive common multiple of two positive rationals."""
    return F(math.lcm(r1.numerator, r2.numerator), math.gcd(r1.denominator, r2.denominator))


def period(ds):
    q = 1
    for d in ds:
        q = q * d.denominator // math.gcd(q, d.denominator)
    g = 0
    for d in ds:
        g = math.gcd(g, int(d * q))
    return F(q, g)


def study(S):
    S = tuple(sorted(S))
    x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    rows = []
    for e in r['events']:
        if e.get('kind') != 'death' or e.get('tau') is None or e['tau'] == 0:
            continue
        tau, t0, k = e['tau'], e['t0'], e['ka']
        ds = D.readings_at(x, tau)
        m = min(ds)
        if not e['simple']:
            rows.append(dict(simple=False)); continue
        pos = [d * t0 - math.floor(d * t0) for d in ds]
        a = next(i for i, p in enumerate(pos) if p == E8)
        b = next(i for i, p in enumerate(pos) if p == F(7, 8))
        Qab = lcm_rat(1 / ds[a], 1 / ds[b])            # least common period of the pair
        found = None
        j0 = math.floor(t0 / Qab) + 1
        for j in range(j0, j0 + JMAX):
            Q = j * Qab
            t2 = Q - t0
            lab = []
            ok = True
            for i, d in enumerate(ds):
                if i in (a, b):
                    lab.append(int(Q * d) - k[i] - 1)
                else:
                    f = d * t2 - math.floor(d * t2)
                    if not (E8 < f < F(7, 8)):
                        ok = False; break
                    lab.append(math.floor(d * t2))
            if ok:
                found = (j, Q, t2, tuple(lab)); break
        P = period(ds)
        rec = dict(simple=True, R0=float(8 * m * t0), R_full=float(8 * m * (P - t0)), found=found is not None)
        if found:
            j, Q, t2, lab = found
            after = D.feasible(D.readings_at(x, tau + DELTA), lab)[0]
            before = D.feasible(D.readings_at(x, tau - DELTA), lab)[0]
            rec.update(j=j, R_part=float(8 * m * t2), thm_ok=after, born=(after and not before),
                       is_replacement=(lab == e['kb']), Q_is_full=((Q / P).denominator == 1))
        rows.append(rec)
    return S, rows


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    out = open('partial_reflection_v1.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            res = pool.map(study, sets)
            rows = [x for S, rs in res for x in rs]
            simp = [x for x in rows if x['simple']]
            fnd = [x for x in simp if x['found']]
            out.write("\n== %s: deaths after s = 0: %d (simple %d, multi %d) ==\n" % (name, len(rows), len(simp), len(rows) - len(simp)))
            out.write("  partial reflection with the other five strictly clear, within %d multiples of the pair period: %d of %d\n" % (JMAX, len(fnd), len(simp)))
            out.write("  THEOREM CHECK (reflected labels a window just after tau): %d of %d; born exactly at tau: %d\n" %
                      (sum(x['thm_ok'] for x in fnd), len(fnd), sum(x['born'] for x in fnd)))
            out.write("  PLACE TEST (the cascade's replacement IS that partial reflection): %d of %d\n" %
                      (sum(x['is_replacement'] for x in fnd), len(fnd)))
            out.write("  multiple j used: %s\n" % dict(sorted(Counter(x['j'] for x in fnd).items())[:15]))
            if fnd:
                med = lambda v: sorted(v)[len(v) // 2]
                out.write("  R medians: dying window %.2f; partial reflection %.2f; full reflection %.1f\n" % (
                    med([x['R0'] for x in fnd]), med([x['R_part'] for x in fnd]), med([x['R_full'] for x in fnd])))
                out.write("  partial reflection is the full one (Q a multiple of the full period): %d\n" % sum(x['Q_is_full'] for x in fnd))
                rep = [x for x in fnd if x['is_replacement']]
                if rep:
                    out.write("  when it is the replacement: R dying %.2f -> partial %.2f (medians); j %s\n" % (
                        med([x['R0'] for x in rep]), med([x['R_part'] for x in rep]), dict(Counter(x['j'] for x in rep).most_common(5))))
    out.close()
    print(open('partial_reflection_v1.out').read()[len(__doc__):])
