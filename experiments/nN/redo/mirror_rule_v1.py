"""E180 (2026-09-29): reflect each pinch of the deformation around the common period at tau.

Owner: "There may be a more general rule here: reflect a pinched isolation event around a common grid period.  This
swaps the boundary runners, and the active inequality reverses sign -- so the obstruction that kills the old window can
support the new o[ne]" (message cut off).

At an event tau of the deformation (deform_pinch_v1, E178) the tight window k is a single instant t0.  The readings
d_i(tau) are rational; P is their least common period (P d_i(tau) = N_i, integers), P > t0.  The REFLECTED window has
lap assignment k'_i = N_i - k_i - 1 and sits at P - t0.  Derivation (reasoned, in the E180 log entry): for a simple pinch
(a on +1/8, b on -1/8) the active inequalities satisfy g_k'(s) = g_k(s) + 8 (N_a d_b(s) - N_b d_a(s)); both vanish at
tau and their slopes have opposite signs because P > t0.  So a death of k at tau is a birth of k' at tau, and a birth of
k is a death of k'.
Checked here, exactly, at every event of the subsamples: k' is a window at tau (a single instant at P - t0); for a death
of k, k' is not a window just before tau and is a window just after (born); for a birth of k, the reverse (dies).
"Just before/after" = tau -+ delta with delta = 1/10^15 (all other constraints keep their margin at that distance; the
check reports any case where that fails).  Multi-pinches are checked the same way and reported separately.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D

DELTA = F(1, 10 ** 15)
_orig_classify = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig_classify(x, sa, ka, sb, kb)
    rec['k'] = ka if rec.get('kind') == 'death' else kb
    return rec


D.classify = classify_k


def period(ds):
    q = 1
    for d in ds:
        q = q * d.denominator // math.gcd(q, d.denominator)
    g = 0
    for d in ds:
        g = math.gcd(g, int(d * q))
    return F(q, g)


def check(S):
    S = tuple(sorted(S))
    x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    out = []
    for e in r['events']:
        tau = e.get('tau')
        if tau is None or tau == 0:
            continue
        k = e['k']
        ds = D.readings_at(x, tau)
        P = period(ds)
        N = [int(P * d) for d in ds]
        kp = tuple(n - ki - 1 for n, ki in zip(N, k))
        ok_t, lo_t, hi_t = D.feasible(ds, kp)
        tight = ok_t and lo_t == hi_t
        at_mirror = tight and lo_t == P - e['t0']
        before = D.feasible(D.readings_at(x, tau - DELTA), kp)[0]
        after = D.feasible(D.readings_at(x, tau + DELTA), kp)[0]
        kb, ka = D.feasible(D.readings_at(x, tau - DELTA), k)[0], D.feasible(D.readings_at(x, tau + DELTA), k)[0]
        if e['kind'] == 'death':
            expected = (not before) and after
        else:
            expected = before and (not after)
        out.append(dict(kind=e['kind'], simple=e['simple'], tight=tight, at_mirror=at_mirror, expected=expected,
                        before=before, after=after, k_before=kb, k_after=ka,
                        R_mirror=float(8 * min(ds) * (P - e['t0'])), R0=e['R0']))
    return S, out


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    out = open('mirror_rule_v1.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            res = pool.map(check, sets)
            ev = [e for S, es in res for e in es]
            out.write("\n== %s: paths %d, events after s = 0: %d ==\n" % (name, len(res), len(ev)))
            for simple in (True, False):
                sub = [e for e in ev if e['simple'] == simple]
                if not sub:
                    continue
                out.write("  %s pinches %d: reflected window tight at tau, at P - t0: %d; behaves as derived "
                          "(death <-> birth): %d\n" % ('simple' if simple else 'multi', len(sub),
                          sum(e['at_mirror'] for e in sub), sum(e['expected'] for e in sub)))
                bad = [e for e in sub if not e['expected']]
                out.write("     not as derived: %d; (kind, reflected before, after, original before, after): %s\n" %
                          (len(bad), dict(Counter((e['kind'], e['before'], e['after'], e['k_before'], e['k_after']) for e in bad))))
            out.write("  where the reflected window sits, R = 8 d_min (P - t0): median %.1f, max %.1f; original R median %.2f\n" % (
                sorted(e['R_mirror'] for e in ev)[len(ev) // 2], max(e['R_mirror'] for e in ev), sorted(e['R0'] for e in ev)[len(ev) // 2]))
    out.close()
    print(open('mirror_rule_v1.out').read()[len(__doc__):])
