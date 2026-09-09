r"""
tb_limit_v1 -- a fast EXACT rank-2 class limit, validated against rt_limit_v2.rank2_limit.

rt_limit_v2.floor_joint_law_2d enumerates the FULL product of the four floor-value
ranges and clips a polygon for each tuple, so its cost is the product of the range
sizes even though almost every tuple is empty; that product exceeds 10^5 for lattices
whose saturated-kernel basis has moderate entries, which is what made the height->4
class enumerations intractable.

Here the same partition is computed by depth-first clipping: after clipping to the
strip of coordinate rho, the range of admissible floor values for coordinate rho+1 is
read off the current polygon, so only NON-EMPTY cells are ever visited.  The arithmetic
is identical -- Sutherland-Hodgman clipping and the shoelace formula in exact
Fractions -- so the output is the same rational number, and __main__ checks that on
every height-<=3 rank-2 class plus a random sample of higher-height ones.

Boundary exactness: cells are the closed polygons { d <= c.s <= d+1 }; overlaps are
measure-zero edges and contribute 0 to the area, and the partition is asserted to sum
to exactly 1.  No cell is ever evaluated at a sample point, so requirement (i) does not
arise here.
"""
from fractions import Fraction as F
import itertools

import rt_limit_v2 as RL

MU = (0, 1, 2, 3)
UNIT = [(F(0), F(0)), (F(1), F(0)), (F(1), F(1)), (F(0), F(1))]


def _clip(poly, a, b, c, keep_ge):
    if not poly:
        return poly
    out = []
    n = len(poly)

    def val(p):
        v = a * p[0] + b * p[1] - c
        return -v if keep_ge else v

    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        vp, vq = val(p), val(q)
        if vp <= 0:
            out.append(p)
        if (vp < 0 < vq) or (vq < 0 < vp):
            t = vp / (vp - vq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def _area(poly):
    if len(poly) < 3:
        return F(0)
    s = F(0)
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def floor_joint_law_2d(rows):
    """{ d-tuple : exact area of { s in [0,1)^2 : floor(rows_rho . s) = d_rho } }."""
    out = {}

    def rec(k, poly, d):
        if not poly or _area(poly) == 0:
            return
        if k == 4:
            out[tuple(d)] = out.get(tuple(d), F(0)) + _area(poly)
            return
        c1, c2 = rows[k]
        if c1 == 0 and c2 == 0:
            rec(k + 1, poly, d + [0])
            return
        vals = [c1 * x + c2 * y for (x, y) in poly]
        lo, hi = min(vals), max(vals)
        dlo = lo.numerator // lo.denominator
        dhi = hi.numerator // hi.denominator
        for dv in range(dlo, dhi + 1):
            q = _clip(poly, c1, c2, F(dv), True)
            q = _clip(q, c1, c2, F(dv + 1), False)
            rec(k + 1, q, d + [dv])

    rec(0, UNIT, [])
    tot = sum(out.values())
    assert tot == 1, (rows, tot)
    return out


def rank2_limit(M):
    B, rk = RL.kernel_basis([list(r) for r in M])
    assert rk == 2 and len(B[0]) == 2, (M, rk)
    rows = [tuple(B[r]) for r in range(4)]
    law = floor_joint_law_2d(rows)
    tot = F(0)
    for ks in itertools.product(range(4), repeat=2):
        base = [rows[r][0] * ks[0] + rows[r][1] * ks[1] for r in range(4)]
        for d, A in law.items():
            a = [(base[r] + d[r]) % 4 for r in range(4)]
            if len({ar ^ mr for ar, mr in zip(a, MU)}) == 4:
                tot += A
    return tot / 16


if __name__ == "__main__":
    import random, time
    print("validating tb_limit_v1.rank2_limit against rt_limit_v2.rank2_limit")
    ADM3 = [v for v in itertools.product(range(-3, 4), repeat=4) if RL.admissible(v)]
    seen = set()
    n = bad = 0
    t0 = t1 = 0.0
    for i in range(len(ADM3)):
        for j in range(i + 1, len(ADM3)):
            k, rk = RL.lattice_key([list(ADM3[i]), list(ADM3[j])])
            if rk != 2 or k in seen:
                continue
            seen.add(k)
            rows = [list(r) for r in k]
            B, _ = RL.kernel_basis(rows)
            size = 1
            for r in range(4):
                c1, c2 = B[r][0], B[r][1]
                size *= (max(0, c1) + max(0, c2)) - (min(0, c1) + min(0, c2)) + 1
            if size > 200000:
                continue
            a = time.time(); v1 = RL.rank2_limit(rows); t0 += time.time() - a
            a = time.time(); v2 = rank2_limit(rows); t1 += time.time() - a
            n += 1
            if v1 != v2:
                bad += 1
                print("   MISMATCH", k, v1, v2)
    print(f"   height-<=3 rank-2 lattices compared: {n}   mismatches {bad}")
    print(f"   rt_limit_v2 total {t0:.1f}s   tb_limit_v1 total {t1:.1f}s"
          f"   speedup {t0/max(t1,1e-9):.1f}x")

    random.seed(3)
    ADM6 = [v for v in itertools.product(range(-6, 7), repeat=4) if RL.admissible(v)]
    n = bad = 0
    for _ in range(60):
        u, v = random.sample(ADM6, 2)
        k, rk = RL.lattice_key([list(u), list(v)])
        if rk != 2:
            continue
        rows = [list(r) for r in k]
        B, _ = RL.kernel_basis(rows)
        size = 1
        for r in range(4):
            c1, c2 = B[r][0], B[r][1]
            size *= (max(0, c1) + max(0, c2)) - (min(0, c1) + min(0, c2)) + 1
        if size > 400000:
            continue
        n += 1
        if RL.rank2_limit(rows) != rank2_limit(rows):
            bad += 1
            print("   MISMATCH", k)
    print(f"   random height-<=6 rank-2 lattices compared: {n}   mismatches {bad}")
