"""E178 (2026-09-29): follow the isolation along the deformation from the AP to each arrangement; classify every pinch.

Owner: "yes run the deformation and pinch test".

THE PATH (WindowPinchN's deformation, shape coordinates, ArrangementShapeN): the subject is the slowest runner, at 0;
the span is 7.  Target readings S (whole numbers) give shape readings x_i = 7 S_i / S_7 (i = 1..7, x_7 = 7).  Along
s in [0, 1] the readings are d_i(s) = i + s (x_i - i): the AP 1..7 at s = 0, the target at s = 1; order is preserved,
so each disparity ratio is affine in s (disparity_ratio_affine).

THE ORACLE: at each s the cascade's landing (first isolation) and the lonely components, computed exactly; the
landing is compared with the first component (oracle check, every tenth grid point).  A window is a lap assignment k
with max_i (8k_i+1)/(8d_i) <= min_i (8k_i+7)/(8d_i) (lap_windows_iff); distinct windows are disjoint, so the first
isolation changes only when its window closes to a single point (DEATH) or a new window opens from a single point before
it (BIRTH).  Both are pinches.  Events are located by exact bisection between grid points and the parameter tau is then
solved exactly from the tight pair constraint (8k_i+1) d_j(s) = (8k_j+7) d_i(s), linear in s (first_pinch).

AT EACH EVENT (exact, at tau):
  pinch type    the tight window is a single instant t0; readings exactly on +1/8 (leaving) and on -1/8 (entering).
                SIMPLE = one of each, every other reading strictly inside its clear band (PinchOpenN's hypotheses; the
                readings are rational at tau, so a common period P exists).  MULTI otherwise.
  protected     some other window of positive width exists at tau (then the subject is lonely at every nearby s,
                whatever the pinch type).
  UNPROTECTED   a multi-pinch with no positive-width window anywhere at tau: neither PinchOpenN nor an open window
                covers the neighbourhood of tau.  These are listed individually.
  replacement   (deaths) the new first window just after tau: its lap assignment compared with the dying one (which
                readings' laps change, by how much); whether it starts at the mirror P - t0 (PinchOpenN); the jump in
                R = 8 d_min t.
Populations: Case B to 24, every 100th (2,104 targets); late band shapes, every 10th (540); Case C sample (500 random
7-sets with readings <= 200 and spread > 24, seed 13).  Grid: 400 steps in s; two events between neighbouring grid
points whose effects cancel on the landing are not seen (scope).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8, next_opening
from wave_incident_v1 import lonely_components

NGRID = 400
EPS = F(1, 10 ** 12)


def readings_at(x, s):
    return [F(i) + s * (x[i - 1] - i) for i in range(1, 8)]


def components(ds, need=2):
    T = F(2) / min(ds)
    for _ in range(6):
        comps = lonely_components(ds, F(0), T)
        comps = [c for c in comps if c[0] > 0]
        if len(comps) >= need:
            return comps
        T *= 2
    return comps


def cascade_landing(ds, cap=100000):
    """The cascade from the bound 1/(8 d_min), no period cutoff (readings are rational along the path)."""
    t = 1 / (8 * min(ds))
    for _ in range(cap):
        way = [d for d in ds if cd(d * t) < E8]
        if not way:
            return t
        t = max(next_opening(d, t) for d in way)
    return None


def laps(ds, t):
    return tuple(math.floor(d * t) for d in ds)


def feasible(ds, k):
    lo = max(F(8 * ki + 1) / (8 * d) for ki, d in zip(k, ds))
    hi = min(F(8 * ki + 7) / (8 * d) for ki, d in zip(k, ds))
    return lo <= hi, lo, hi


def first_window(x, s):
    ds = readings_at(x, s)
    comps = components(ds, need=1)
    a, b = comps[0]
    return laps(ds, a)


def pair_roots(x, k):
    """For each ordered pair (i, j), the s where (8k_i+1) d_j(s) = (8k_j+7) d_i(s), with the slope sign."""
    out = []
    e = [x[i - 1] - i for i in range(1, 8)]
    for i in range(7):
        for j in range(7):
            if i == j:
                continue
            A = (8 * k[j] + 7) * (i + 1) - (8 * k[i] + 1) * (j + 1)
            B = (8 * k[j] + 7) * e[i] - (8 * k[i] + 1) * e[j]
            if B != 0:
                out.append((F(-A) / B, B, i, j))
    return out


def classify(x, sa, ka, sb, kb):
    okb, _, _ = feasible(readings_at(x, sb), ka)
    if not okb:                                     # death of ka
        kind, k = 'death', ka
        roots = [r for r, B, i, j in pair_roots(x, ka) if B < 0 and sa <= r <= sb]
        tau = min(roots) if roots else None
    else:                                           # birth of kb
        kind, k = 'birth', kb
        roots = [r for r, B, i, j in pair_roots(x, kb) if B > 0 and sa <= r <= sb]
        tau = max(roots) if roots else None
    if tau is None:
        return dict(kind=kind + '?', tau=None)
    ds = readings_at(x, tau)
    ok, lo, hi = feasible(ds, k)
    t0 = lo
    pos = [d * t0 - math.floor(d * t0) for d in ds]
    openers = [i for i, p in enumerate(pos) if p == E8]
    closers = [i for i, p in enumerate(pos) if p == F(7, 8)]
    simple = len(openers) == 1 and len(closers) == 1
    comps = components(ds, need=4)
    wide = [c for c in comps if c[1] > c[0]]
    protected = bool(wide)
    rec = dict(kind=kind, tau=tau, t0=t0, point=(lo == hi), simple=simple, nopen=len(openers), nclose=len(closers),
               protected=protected, R0=float(8 * min(ds) * t0))
    if kind == 'death':
        q = 1
        for d in ds:
            q = q * d.denominator // math.gcd(q, d.denominator)
        g = 0
        for d in ds:
            g = math.gcd(g, int(d * q))
        P = F(q, g)
        okn, lon, hin = feasible(ds, kb)
        rec.update(mirror=(lon == P - t0), R_new=float(8 * min(ds) * lon),
                   lapdiff=tuple(b - a for a, b in zip(ka, kb)))
    return rec


def events(x, sa, ka, sb, kb, out, depth=0):
    if ka == kb:
        return
    if sb - sa < EPS or depth > 60:
        out.append(classify(x, sa, ka, sb, kb)); return
    sm = (sa + sb) / 2
    km = first_window(x, sm)
    events(x, sa, ka, sm, km, out, depth + 1)
    events(x, sm, km, sb, kb, out, depth + 1)


def follow(S):
    S = sorted(S)
    x = [F(7 * d, S[-1]) for d in S]
    grid = [F(j, NGRID) for j in range(NGRID + 1)]
    ks = []; oracle_bad = 0
    for j, s in enumerate(grid):
        ds = readings_at(x, s)
        comps = components(ds, need=1)
        ks.append(laps(ds, comps[0][0]))
        if j % 10 == 0:
            if cascade_landing(ds) != comps[0][0]:
                oracle_bad += 1
    ev = []
    for j in range(NGRID):
        events(x, grid[j], ks[j], grid[j + 1], ks[j + 1], ev)
    return dict(S=tuple(S), events=ev, oracle_bad=oracle_bad, k0=ks[0], k1=ks[-1])


def work(sets):
    return [follow(S) for S in sets]


def report(name, res, out):
    out.write("\n== %s ==  paths %d\n" % (name, len(res)))
    out.write("oracle check (cascade landing = first component, every tenth grid point): %d violations\n" %
              sum(r['oracle_bad'] for r in res))
    ev = [e for r in res for e in r['events']]
    out.write("events: %d (per path %s)\n" % (len(ev), dict(sorted(Counter(len(r['events']) for r in res).items()))))
    out.write("kinds: %s\n" % dict(Counter(e['kind'] for e in ev)))
    good = [e for e in ev if e.get('tau') is not None]
    out.write("tight window a single point at tau: %d of %d\n" % (sum(e['point'] for e in good), len(good)))
    out.write("pinch type: simple %d, multi %d; multi by (on +1/8, on -1/8): %s\n" % (
        sum(e['simple'] for e in good), sum(not e['simple'] for e in good),
        dict(Counter((e['nopen'], e['nclose']) for e in good if not e['simple']).most_common(10))))
    out.write("protected by another positive-width window at tau: %d of %d\n" % (sum(e['protected'] for e in good), len(good)))
    unp = [(r['S'], e) for r in res for e in r['events'] if e.get('tau') is not None and not e['simple'] and not e['protected']]
    out.write("UNPROTECTED (multi-pinch, no positive-width window): %d\n" % len(unp))
    for S, e in unp[:25]:
        out.write("   %s  %s tau=%s  t0 R=%.4f  on +1/8: %d, on -1/8: %d\n" % (S, e['kind'], e['tau'], e['R0'], e['nopen'], e['nclose']))
    de = [e for e in good if e['kind'] == 'death']
    out.write("deaths: %d; replacement at the mirror P - t0: %d\n" % (len(de), sum(e['mirror'] for e in de)))
    out.write("deaths, lap changes (number of readings whose lap changes): %s\n" %
              dict(sorted(Counter(sum(1 for v in e['lapdiff'] if v) for e in de).items())))
    out.write("deaths, lap change vectors (top 12): %s\n" % Counter(e['lapdiff'] for e in de).most_common(12))
    out.write("deaths, jump in R (new - old): %s\n" % dict(sorted(Counter(round(e['R_new'] - e['R0'], 1) for e in de).items())[:25]))
    out.write("first window at s = 0 (the AP): %s; at s = 1: first 5 %s\n" %
              (dict(Counter(r['k0'] for r in res)), [r['k1'] for r in res[:5]]))
    out.flush()


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('deform_pinch_v1.out', 'w'); out.write(__doc__ + "\n")
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::100]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    late = late_shapes()[::10]
    with Pool(8) as pool:
        for name, sets in [('Case B to 24, every 100th', caseB), ('late band shapes, every 10th', late),
                           ('Case C sample (500)', caseC)]:
            res = [r for part in pool.map(work, [sets[i::64] for i in range(64)]) for r in part]
            report(name, res, out)
    out.close()
    print(open('deform_pinch_v1.out').read()[len(__doc__):])
