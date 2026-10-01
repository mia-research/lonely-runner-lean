"""E246 Part A' (2026-10-01): the shapes at the top of six_gap_v2.out, constructed at larger readings.

Q (six_gap_v2.q_of): the largest span (s0 + G)/max(s0, 9/(8 a1)) of a blocked stretch in the first period; c's first arc
can hold no isolation iff Q > 7.  Families read off the 20 largest Q (each built for a = 10 .. 300 and reduced by its
gcd):
  AP1  {a, a+1, ..., a+5}                       (14..19 at the top; derived limit 5/3 as a grows, E245)
  AP2  {a, a+2, ..., a+10}, a odd               (step-2 progressions: (20, 22, ..., 28, 31) region)
  AP2' {a, a+2, a+4, a+6, a+8, a+11}            ((20, 22, 24, 26, 28, 31))
  TC   {a, a+2, a+3, a+5, 2a+2, 2a+3}           ((14, 16, 17, 19, 30, 31))
  CL4  {a, a+1, a+2, a+3, 2a+3, 3a-2}           ((10, 11, 12, 13, 23, 28))
Reported per family: Q at each a in steps, its greatest value and where.
"""
import math
from fractions import Fraction as F
from multiprocessing import Pool
from six_gap_v2 import q_of

FAM = {
    'AP1': lambda a: [a + i for i in range(6)],
    'AP2': lambda a: [a + 2 * i for i in range(6)] if a % 2 else None,
    "AP2'": lambda a: [a, a + 2, a + 4, a + 6, a + 8, a + 11],
    'TC': lambda a: [a, a + 2, a + 3, a + 5, 2 * a + 2, 2 * a + 3],
    'CL4': lambda a: [a, a + 1, a + 2, a + 3, 2 * a + 3, 3 * a - 2],
}


def one(args):
    name, a = args
    S = FAM[name](a)
    if S is None or len(set(S)) < 6:
        return name, a, None
    g = math.gcd(*S); S = tuple(sorted(x // g for x in S))
    _, q, s0, s1, bad = q_of(S)
    return name, a, (float(q), float(s0), float(s1), bad)


if __name__ == '__main__':
    jobs = [(n, a) for n in FAM for a in range(10, 301)]
    with Pool(8) as pool:
        res = pool.map(one, jobs, chunksize=4)
    out = open('six_gap_v3.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("check failures: %d" % sum(r[2][3] for r in res if r[2]))
    for n in FAM:
        rr = [(a, r) for nm, a, r in res if nm == n and r]
        best = max(rr, key=lambda x: x[1][0])
        w("\n%s: greatest Q %.4f at a = %d (stretch %.4f to %.4f); Q > 7 at %d values of a" % (n, best[1][0], best[0], best[1][1], best[1][2], sum(1 for a, r in rr if r[0] > 7)))
        w("   Q at a = 10, 20, 40, 80, 160, 300 (or the nearest built): %s" % [(a, round(r[0], 4)) for a, r in rr if a in (10, 11, 20, 21, 40, 41, 80, 81, 160, 161, 299, 300)])
    out.close()
    print(open('six_gap_v3.out').read()[len(__doc__):])
