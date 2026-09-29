"""E175 follow-up: the residue of each reading in the subject's slot at the 768's rungs.

Reading d is in the slot at rung a/q exactly when |d a - n q| < q/8 for an integer n.  For q <= 8 that forces
d a = n q, so q divides d (gcd(a, q) = 1): only multiples of q (E100's rung R1 used D_q).  For q >= 9 a reading with
d a = +-1 (mod q) also fits.  Recorded: the signed residue r = d a - q round(d a/q) of every reading in the slot at the
rung that places each of the 768 (Q1: the rung the runner leaves from; Q2: the rung that closes the stretch).
"""
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from place_768_v1 import unplaced_of, analyse


def residue(d, r):
    a, q = r.numerator, r.denominator
    n = round(F(d * a, q))
    return d * a - q * n


if __name__ == '__main__':
    with Pool(8) as pool:
        sets = [T for part in pool.map(unplaced_of, range(1, 19)) for T in part]
        res = pool.map(analyse, sets)
    out = open('place_768_v1d.out', 'w'); out.write(__doc__ + "\n")
    for k in ('Q1', 'Q2'):
        c = Counter(); per = Counter()
        for x in res:
            if k not in x['rp']:
                continue
            r = x['rp'][k]
            rs = tuple(sorted(residue(d, r) for d in x['rel'][k]['way']))
            per[rs] += 1
            for v in rs:
                c[(r.denominator, v)] += 1
        out.write("%s: residues (q, r) of the readings in the slot at the rung: %s\n" % (k, dict(sorted(c.items()))))
        out.write("%s: per set, the residues present: %s\n" % (k, dict(per.most_common())))
    q1 = [x for x in res if 'Q1' in x['rp']]
    exact = sum(all(residue(d, x['rp']['Q1']) == 0 for d in x['rel']['Q1']['way']) for x in q1)
    out.write("Q1 sets whose slot at the rung holds only exact multiples of q: %d; holding a reading one off the grid: %d; "
              "of %d\n" % (exact, len(q1) - exact, len(q1)))
    out.close()
    print(open('place_768_v1d.out').read()[len(__doc__):])
