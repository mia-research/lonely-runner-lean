"""E179 follow-up: name each protector by the place list of E174-E176 (place_general_v1.place_G, applied to the
protector's left end at tau): the bound, a reading's next opening 9/(8e), one separation from those, a rung of the
nearest runner's ladder (itself, displaced by one separation, or the stretch at it; least q), or none.
Subsamples: Case B every 400th, late band shapes every 40th, Case C first 100."""
import sys, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from deform_pinch_v1 import follow, readings_at, components, laps
from deform_protect_v1 import s_interval, ap_class
from place_general_v1 import place_G


def name_protectors(S):
    S = tuple(sorted(S))
    x = [F(7 * d, S[-1]) for d in S]
    r = follow(S)
    rows = []
    for e in r['events']:
        if e.get('tau') is None or e['tau'] == 0:
            continue
        ds = readings_at(x, e['tau'])
        for a, b in components(ds, need=6):
            if b > a:
                k = laps(ds, a)
                iv = s_interval(x, k)
                origin = 'AP' if iv is not None and (iv[0] is None or iv[0] <= 0) else 'born'
                p = place_G(tuple(sorted(ds)), a)
                rows.append((origin, p[0], p[1], ap_class(k), round(float(8 * min(ds) * a), 3)))
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
    out = open('deform_protect_v1b.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            res = pool.map(name_protectors, sets)
            rows = [x for S, rs in res for x in rs]
            out.write("\n== %s: paths %d, protector instances %d ==\n" % (name, len(res), len(rows)))
            for origin in ('AP', 'born'):
                sub = [x for x in rows if x[0] == origin]
                out.write("  %s-origin %d: place %s; least q %s\n" % (origin, len(sub), dict(Counter(x[1] for x in sub).most_common()),
                          dict(sorted(Counter(x[2] for x in sub if x[2] is not None).items()))))
            born = [x for x in rows if x[0] == 'born']
            out.write("  born, most common R of the protector's left end: %s\n" % Counter(x[4] for x in born).most_common(12))
            out.write("  not placed (first 10): %s\n" % [x for x in rows if x[1] == 'none'][:10])
    out.close()
    print(open('deform_protect_v1b.out').read()[len(__doc__):])
