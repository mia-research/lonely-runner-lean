"""E175 follow-up: the 768 by nearest reading d_min; traces of the sets with d_min >= 2 (the 1/10 and 1/11 rungs)."""
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from place_768_v1 import unplaced_of, analyse

if __name__ == '__main__':
    with Pool(8) as pool:
        sets = [T for part in pool.map(unplaced_of, range(1, 19)) for T in part]
        res = pool.map(analyse, sets)
    out = open('place_768_v1c.out', 'w'); out.write(__doc__ + "\n")
    out.write('d_min distribution: %s\n' % dict(sorted(Counter(x['T'][0] for x in res).items())))
    for k in ('Q1', 'Q2'):
        out.write('%s rung (R = 8 d_min r) by d_min: %s\n' % (k, dict(Counter(
            (x['T'][0], str(x['rp'].get(k)), float(8 * x['T'][0] * x['rp'][k]) if k in x['rp'] else None)
            for x in res).most_common(12))))
    out.write('landing R by d_min: %s\n' % dict(Counter((x['T'][0], str(x['R'])) for x in res).most_common(12)))
    shown = Counter()
    for x in res:
        m = x['T'][0]
        if shown[m] >= 3:
            continue
        shown[m] += 1; T = x['T']
        out.write('\n%s lands t*=%s R=%s host %s/K%s closer %s/L%s\n' %
                  (T, x['ts'], x['R'], T[x['b']['host']], x['b']['K'], T[x['b']['closer']], x['b']['L']))
        for t, way, setters in x['trace']:
            out.write('   t=%s R=%.4f in slot %s leaves %s\n' % (t, float(8 * m * t), way, setters))
        for k, r in x['rp'].items():
            out.write('   %s at rung %s (R=%.4f): in the way there %s; divisible by %d: %s\n' %
                      (k, r, float(8 * m * r), x['rel'][k]['way'], r.denominator, x['rel'][k]['q_divides']))
    out.close()
    print(open('place_768_v1c.out').read())
