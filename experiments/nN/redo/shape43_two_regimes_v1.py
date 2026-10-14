"""E394 (2026-10-05), shape43_two_regimes_v1: the free-edge move (E393) and a second condition, on shape (4,3).
Owner: "we should be able to piece together a full proof of n=8 from everything we have ... believe in the work".
SECOND CONDITION (stated before the run) [PROVISIONAL: counting tool]: the multiples are clear at t = a/8 + d s exactly when
8 s lies in the cofactors' lonely set (a union of windows, period 1/gcd(E)); a non-multiple c is blocked for s in arcs of length
1/(4c), period 1/c (any residue, any class: only the blocked arcs matter).  In a cofactor window of s-length L, c blocks at most
(Lc + 1)/(4c) = L/4 + 1/(4c) of it, so three non-multiples block at most 3L/4 + sum 1/(4 c_j); if L > sum_j 1/c_j this is below L and
some s in the window is clear for all three.  Hence (II): some cofactor window has s-length L > 1/c_1 + 1/c_2 + 1/c_3 => lonely.
RECORDED (exact): on the leftover of E393 (shape (4,3), readings <= 48): how many satisfy (II); the union of (I) and (II); the
sets that satisfy neither, individually (first 25); for them the exact cascade landing's nearest class and the largest cofactor window
length against sum 1/c.  Exact (Fractions).
"""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from wave_incident_v1 import lonely_components
from shape43_freeedge_v1 import work as rule_work

def second(item):
    Ms, ns = item
    Es = [F(m // 8) for m in Ms]
    g = 0
    for m in Ms: g = math.gcd(g, m // 8)
    T = F(1, g) if g else F(1)
    comps = [c for c in lonely_components(Es, F(0), T) if c[0] > 0]
    Lmax = max((b - a for a, b in comps), default=F(0)) / 8
    need = sum(F(1, c) for c in ns)
    return (Ms, ns, Lmax > need, Lmax, need)

if __name__ == '__main__':
    mults = list(range(8, 49, 8)); non = [c for c in range(1, 49) if c % 8]
    items = [(Ms, ns) for Ms in itertools.combinations(mults, 4) for ns in itertools.combinations(non, 3)]
    chunks = [items[i:i + 4000] for i in range(0, len(items), 4000)]
    with Pool(4) as pool:
        rr = [r for c in pool.map(rule_work, chunks) for r in c]
        left = [(r[0], r[1]) for r in rr if not r[3]]
        res = pool.map(second, left, chunksize=200)
    o = open('shape43_two_regimes_v1.out', 'w'); o.write(__doc__ + "\n")
    both = [r for r in res if r[2]]; neither = [r for r in res if not r[2]]
    o.write("shape (4,3), readings <= 48: sets passing the first fields %d; rule I applies %d; leftover of I: %d; of the leftover, condition II holds: %d; neither I nor II: %d\n" % (len(rr), len(rr) - len(left), len(left), len(both), len(neither)))
    for Ms, ns, ok, L, need in neither[:25]:
        o.write("  neither: multiples %s non-multiples %s  longest cofactor window (s) %s  sum 1/c %s\n" % (Ms, ns, L, need))
    o.close(); print(open('shape43_two_regimes_v1.out').read()[len(__doc__):][:3500])
