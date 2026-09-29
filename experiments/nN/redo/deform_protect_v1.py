"""E179 (2026-09-29): the window that protects each pinch along the deformation from the AP -- where does it come from?

Owner: "yes identify the protecting window at each event".

Same path, grid and events as deform_pinch_v1 (E178).  At every event after s = 0 the PROTECTORS are the windows of
positive width that exist at tau.  For a fixed lap assignment k each pair condition (8k_i+1) d_j(s) <= (8k_j+7) d_i(s)
is linear in s, so the parameters where k is a window form one interval [s_lo, s_hi] (computed exactly).  Hence:
  ORIGIN AP      k is a window at s = 0: one of the AP's class windows, at the AP instant (8n+c)/8 (c odd), with
                 k_i = floor(i (8n+c)/8); it has existed along the whole path up to tau.
  ORIGIN BORN    k first became a window at s_lo in (0, tau): born along the path.
Per target: the AP class windows (c, n <= 20) that are still windows at s = 1 (they persist through the whole path,
since the parameter set is an interval containing 0 and 1), and whether one of them is the target's first isolation.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from deform_pinch_v1 import follow, readings_at, components, laps, feasible

NMAX = 20


def s_interval(x, k):
    """[s_lo, s_hi] of parameters where lap assignment k is a window (None if empty)."""
    e = [x[i - 1] - i for i in range(1, 8)]
    lo, hi = None, None
    for i in range(7):
        for j in range(7):
            if i == j:
                continue
            A = (8 * k[j] + 7) * (i + 1) - (8 * k[i] + 1) * (j + 1)
            B = (8 * k[j] + 7) * e[i] - (8 * k[i] + 1) * e[j]
            if B == 0:
                if A < 0:
                    return None
            elif B > 0:
                r = F(-A) / B
                lo = r if lo is None or r > lo else lo
            else:
                r = F(-A) / B
                hi = r if hi is None or r < hi else hi
    if lo is not None and hi is not None and lo > hi:
        return None
    return (lo, hi)


def ap_class(k):
    """(c, n) if k is the lap assignment of the AP instant (8n+c)/8."""
    for n in range(0, NMAX + 1):
        for c in (1, 3, 5, 7):
            if all(k[i - 1] == (i * (8 * n + c)) // 8 for i in range(1, 8)):
                return (c, n)
    return None


def study(S):
    S = tuple(sorted(S))
    x = [F(7 * d, S[-1]) for d in S]
    r = follow(S)
    evs = []
    for e in r['events']:
        if e.get('tau') is None or e['tau'] == 0:
            continue
        ds = readings_at(x, e['tau'])
        comps = components(ds, need=6)
        prot = []
        for a, b in comps:
            if b > a:
                k = laps(ds, a)
                iv = s_interval(x, k)
                origin = 'AP' if iv is not None and (iv[0] is None or iv[0] <= 0) else 'born'
                prot.append(dict(k=k, iv=iv, origin=origin, cls=ap_class(k), R=float(8 * min(ds) * a)))
        evs.append(dict(tau=e['tau'], kind=e['kind'], prot=prot))
    # AP class windows persisting to s = 1
    persist = []
    for n in range(0, NMAX + 1):
        for c in (1, 3, 5, 7):
            k = tuple((i * (8 * n + c)) // 8 for i in range(1, 8))
            ok, lo, hi = feasible([F(v) for v in x], k)
            if ok:
                persist.append(((c, n), float(8 * x[0] * lo)))
    ds1 = x
    comps1 = components(ds1, need=1)
    first_k = laps(ds1, comps1[0][0])
    return dict(S=S, evs=evs, persist=persist, first_cls=ap_class(first_k), first_R=float(8 * x[0] * comps1[0][0]))


def work(sets):
    return [study(S) for S in sets]


def report(name, res, out):
    ev = [e for r in res for e in r['evs']]
    out.write("\n== %s ==  paths %d, events after s = 0: %d\n" % (name, len(res), len(ev)))
    out.write("events with at least one protector: %d\n" % sum(bool(e['prot']) for e in ev))
    ap = [e for e in ev if any(p['origin'] == 'AP' for p in e['prot'])]
    out.write("events protected by a window from the AP: %d; only by windows born along the path: %d\n" %
              (len(ap), sum(1 for e in ev if e['prot'] and not any(p['origin'] == 'AP' for p in e['prot']))))
    out.write("the AP class (c, n) of the earliest AP-origin protector: %s\n" %
              dict(Counter(min((p for p in e['prot'] if p['origin'] == 'AP'), key=lambda p: p['R'])['cls'] for e in ap).most_common(12)))
    born = [e for e in ev if e['prot'] and not any(p['origin'] == 'AP' for p in e['prot'])]
    for e in born[:8]:
        out.write("   born-only event tau=%s %s: protectors %s\n" % (e['tau'], e['kind'],
                  [(p['k'], str(p['iv'][0]), p['cls'], round(p['R'], 3)) for p in e['prot'][:3]]))
    out.write("per path: every event protected by an AP-origin window: %d of %d\n" %
              (sum(all(any(p['origin'] == 'AP' for p in e['prot']) for e in r['evs']) for r in res), len(res)))
    npers = Counter(len(r['persist']) > 0 for r in res)
    out.write("targets with an AP class window persisting to s = 1 (n <= %d): %d of %d\n" % (NMAX, npers[True], len(res)))
    out.write("   earliest persisting class (c, n): %s\n" %
              dict(Counter(min(r['persist'], key=lambda z: z[1])[0] for r in res if r['persist']).most_common(12)))
    out.write("targets whose first isolation IS an AP class window: %d; its class: %s\n" %
              (sum(r['first_cls'] is not None for r in res), dict(Counter(r['first_cls'] for r in res if r['first_cls']).most_common(8))))
    nop = [r for r in res if not r['persist']]
    out.write("targets with no persisting AP class window (first 10): %s\n" % [(r['S'], round(r['first_R'], 3)) for r in nop[:10]])
    out.flush()


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('deform_protect_v1.out', 'w'); out.write(__doc__ + "\n")
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
    print(open('deform_protect_v1.out').read()[len(__doc__):])
