"""E178 follow-up: (a) the events with no other positive-width window -- are they exactly the s = 0 event (the AP,
whose windows are all single points)?  (b) the deaths with a negative jump in R -- what are they?
Same path, grid and event location as deform_pinch_v1; subsamples."""
import sys, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from deform_pinch_v1 import follow, readings_at, feasible


def look(S):
    r = follow(S)
    un = [e for e in r['events'] if e.get('tau') is not None and not e['protected']]
    neg = [e for e in r['events'] if e.get('kind') == 'death' and e['R_new'] < e['R0']]
    return r['S'], [(e['tau'], e['kind'], e['simple']) for e in un], [(e['tau'], e['R0'], e['R_new'], e['lapdiff']) for e in neg]


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    out = open('deform_pinch_v1b.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            res = pool.map(look, sets)
            un = [u for S, us, ns in res for u in us]
            out.write("\n%s: paths %d; events with no other positive-width window %d; their tau %s; simple %d\n" %
                      (name, len(res), len(un), dict(Counter(str(u[0]) for u in un).most_common(5)), sum(u[2] for u in un)))
            neg = [(S, n) for S, us, ns in res for n in ns]
            out.write("   deaths with negative jump: %d; first: %s\n" % (len(neg), [(S, str(n[0]), round(n[1], 3), round(n[2], 3), n[3]) for S, n in neg[:6]]))
    out.close()
    print(open('deform_pinch_v1b.out').read()[len(__doc__):])
