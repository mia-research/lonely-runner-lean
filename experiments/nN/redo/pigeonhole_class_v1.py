"""E385 (2026-10-05), pigeonhole_class_v1: the whole-number sets covered by D1 of E384, and what the cascade does on them.
[PROVISIONAL: counting tool] D1 = pigeonhole (q >= 2 equally spaced positions cannot all lie in the open blocked arc).
CLASS Z: whole-number 7-sets S (readings), overall gcd G; after dividing by G, some six-subset has gcd g > 1 (then g does not
divide the remaining reading, so the remaining reading d satisfies d/g = p/q with q = g >= 2, and D1 gives a lonely instant
with the six's clear set non-empty by order seven).  Complement R: every six-subset coprime after normalising.
RECORDED (exact): class sizes over every 7-subset of 1..24; the cascade landing in units R = 8 d_min t of each set; the number
of sets in each class with a gate-crossed landing (R > 9); the largest R in each class.  Misses of nothing are predicted; this
is a map of where the cascade works hard.
"""
import itertools, math
from fractions import Fraction as F
from multiprocessing import Pool
import deform_pinch_v1 as D

def work(chunk):
    out = []
    for S in chunk:
        G = 0
        for x in S: G = math.gcd(G, x)
        T = tuple(x // G for x in S)
        z = False
        for i in range(7):
            g = 0
            for j in range(7):
                if j != i: g = math.gcd(g, T[j])
            if g > 1: z = True; break
        ds = [F(x) for x in S]
        t = D.cascade_landing(ds, cap=200000)
        R = 8 * min(ds) * t
        out.append((z, R > 9, R, S))
    return out

if __name__ == '__main__':
    sets = list(itertools.combinations(range(1, 25), 7))
    chunks = [sets[i:i + 2000] for i in range(0, len(sets), 2000)]
    with Pool(4) as pool:
        res = [r for c in pool.map(work, chunks) for r in c]
    out = open('pigeonhole_class_v1.out', 'w'); out.write(__doc__ + "\n")
    for name, flag in (('Z (some six-subset has gcd > 1 after normalising)', True), ('R (every six-subset coprime)', False)):
        rr = [r for r in res if r[0] == flag]
        mx = max(rr, key=lambda r: r[2])
        out.write("%s: %d sets; gate-crossed (R > 9): %d; largest R = %s at S = %s\n" % (name, len(rr), sum(1 for r in rr if r[1]), mx[2], mx[3]))
    out.close(); print(open('pigeonhole_class_v1.out').read()[len(__doc__):])
