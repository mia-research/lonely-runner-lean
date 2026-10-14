"""E403 (2026-10-05), grid_cover_cofactors_v1: when do the three cofactors block every point m/w of an odd walker's
grid?  Exact integer arithmetic, finite.

Derived (by hand) before the run: in shape (3,4) of type (o,o,o,o) the four odd non-multiples block all eight shifts
(tau + k)/8 only as a perfect partition; at tau = m/w (w one of the odd readings) w blocks one shift, so a shift is free
[PROVISIONAL: counting tool; supports: the free shift at such tau].  So S is lonely whenever some point m/w is clear for
the three cofactors c (||c*m/w|| >= 1/8).  A cofactor c blocks m/w iff (c*m mod w) lies in the open window
(-w/8, w/8), which depends on c only through c mod w.
Recorded: for every odd w in [3, W] and every multiset {r1, r2, r3} of residues mod w, whether the three block all of
Z/w; for those that do, whether some r_i = 0 (w divides that cofactor).  Exhaustive in the stated range.
"""
import sys, itertools

def blocks(r, m, w):
    x = (r * m) % w
    return 8 * x < w or 8 * (w - x) < w      # x in (-w/8, w/8) mod w, strict

def covers(rs, w):
    return all(any(blocks(r, m, w) for r in rs) for m in range(w))

if __name__ == '__main__':
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    out = open('grid_cover_cofactors_v1.out', 'w'); out.write(__doc__ + "\n")
    for w in range(3, W + 1, 2):
        tot = cov = cov0 = 0; ex = []
        for rs in itertools.combinations_with_replacement(range(w), 3):
            tot += 1
            if covers(rs, w):
                cov += 1
                if 0 in rs: cov0 += 1
                elif len(ex) < 6: ex.append(rs)
        out.write("w = %d: triples %d, covering %d, covering with some residue 0 %d, covering with none 0 %d %s\n" % (w, tot, cov, cov0, cov - cov0, ex))
    out.close(); print(open('grid_cover_cofactors_v1.out').read()[len(__doc__):])
