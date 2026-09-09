r"""
tb_hunt_v3 -- class-level search for a violation of (H3u).  Rewrite of tb_hunt_v2
with an O(1) realisability test in place of the witness-box enumeration.

    (H3u)   Tail_3(e) = o(e) - o_inf(sat L_3(e))  <=  1/12  whenever rank L_3(e) <= 2.

MECHANISM (declared before the data).  For a saturated realisable M' of rank <= 2, put
M_3(M') = saturation of the height-<=3 part of M' and Delta(M') = o_inf(M') -
o_inf(M_3(M')).  Deep members e of the class have o(e) -> o_inf(M') and
sat L_3(e) = M_3(M'), so limsup over the class of Tail_3 = Delta(M').  A realisable
class with Delta > 1/12 therefore REFUTES (H3u), with an explicit witness obtained by
going deep in the class; Delta <= 1/12 on every realisable class is what (H3u)
requires in the limit.

Because M_3(M') is saturated inside the saturated M', rank M_3 = 2 forces M_3 = M' and
Delta = 0.  So only planes whose height-<=3 part has rank <= 1 can violate.

REALISABILITY, exactly and in O(1).  With B a Z-basis of the saturated kernel of M'
(4 x 2), the class has a positive unit witness iff
  (C) the open cone { alpha in R^2 : B_rho . alpha > 0 for all rho } is nonempty, and
  (G) B alpha = (1,3,5,7) mod 8 is solvable for alpha in (Z/8)^2.
(C) and (G) are necessary; they are sufficient because an open 2-dimensional cone
contains a ball of any radius, hence a point of every coset of 8 Z^2.  (C) is decided
by testing the finitely many candidate directions +-B_rho^perp, B_rho and their
pairwise sums; the exactness of that test is cross-validated below against
rt_limit_v2.witnesses on every plane of the height-<=3 run.

POPULATION LABELS (requirement (iii)).  Both arms are PARAMETER boxes over generator
HEIGHT (sup-norm <= HMAX), not speed boxes.  Realisability is decided exactly, so no
alpha box enters; where explicit witnesses are printed, their true max speed is shown.

usage:  python3 tb_hunt_v3.py [HMAX] [CELLCAP]
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce

import rt_limit_v2 as RL
import tb_limit_v1 as TB   # exact, DFS-clipped, validated against RL.rank2_limit

HMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
CELLCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
RHO = (1, 3, 5, 7)
BUDGET = F(1, 12)
FLOOR = F(3, 32)

PAIRIDX = [(i, j) for i in range(4) for j in range(i + 1, 4)]
TRIPLES = [(i, j, k) for i in range(4) for j in range(i + 1, 4)
           for k in range(j + 1, 4)]


def plucker(u, v):
    p = tuple(u[i] * v[j] - u[j] * v[i] for (i, j) in PAIRIDX)
    if not any(p):
        return None
    g = reduce(gcd, [abs(x) for x in p])
    p = tuple(x // g for x in p)
    for x in p:
        if x:
            if x < 0:
                p = tuple(-y for y in p)
            break
    return p


def in_plane(p, v):
    d = dict(zip(PAIRIDX, p))
    for (i, j, k) in TRIPLES:
        if d[(i, j)] * v[k] - d[(i, k)] * v[j] + d[(j, k)] * v[i] != 0:
            return False
    return True


def cone_ok(B):
    """exists alpha in R^2 with B_rho . alpha > 0 for every rho."""
    if any(B[r][0] == 0 and B[r][1] == 0 for r in range(4)):
        return False
    cand = []
    for r in range(4):
        c1, c2 = B[r][0], B[r][1]
        cand += [(-c2, c1), (c2, -c1), (c1, c2)]
    cand += [(a[0] + b[0], a[1] + b[1])
             for a, b in itertools.combinations(cand, 2)]
    for a in cand:
        if a == (0, 0):
            continue
        if all(B[r][0] * a[0] + B[r][1] * a[1] > 0 for r in range(4)):
            return True
    return False


def cong_ok(B):
    """B alpha = (1,3,5,7) mod 8 solvable."""
    for a1 in range(8):
        for a2 in range(8):
            if all((B[r][0] * a1 + B[r][1] * a2 - RHO[r]) % 8 == 0
                   for r in range(4)):
                return True
    return False


def realisable(B):
    return cone_ok(B) and cong_ok(B)


def cell_count(B):
    size = 1
    for r in range(4):
        c1, c2 = B[r][0], B[r][1]
        size *= (max(0, c1) + max(0, c2)) - (min(0, c1) + min(0, c2)) + 1
    return size


def limit_of_rows(rows):
    if not rows:
        return FLOOR
    if len(rows) == 1:
        return RL.rank1_limit(tuple(rows[0]))
    return TB.rank2_limit(rows)


if __name__ == "__main__":
    print(f"tb_hunt_v3   HMAX = {HMAX}   CELLCAP = {CELLCAP}")
    print(f"a realisable class with Delta > 1/12 = {float(BUDGET):.7f} refutes (H3u)\n")

    ADM3 = [v for v in itertools.product(range(-3, 4), repeat=4) if RL.admissible(v)]
    ADMH = [v for v in itertools.product(range(-HMAX, HMAX + 1), repeat=4)
            if RL.admissible(v)]
    HIGH = [v for v in ADMH if max(abs(x) for x in v) > 3]
    print(f"admissible primitive vectors: ht <= 3 : {len(ADM3)}   "
          f"ht <= {HMAX} : {len(ADMH)}   ht in [4,{HMAX}] : {len(HIGH)}")

    # ------------------------------------------------- rank-1 arm
    seen1, rows1 = set(), []
    for v in ADMH:
        k, _ = RL.lattice_key([list(v)])
        if k in seen1:
            continue
        seen1.add(k)
        B, _ = RL.kernel_basis([list(k[0])])
        if not (all(any(B[r][c] for c in range(3)) for r in range(4))):
            continue
        n0 = tuple(k[0])
        lim = RL.rank1_limit(n0)
        h = max(abs(x) for x in n0)
        s3 = lim if h <= 3 else FLOOR
        rows1.append((lim - s3, lim, s3, h, n0))
    rows1.sort(reverse=True)
    print(f"\n--- rank-1 classes ---")
    print(f"   distinct rank-1 classes of height <= {HMAX}: {len(rows1)}")
    print(f"   max o_inf = {max(r[1] for r in rows1)}   "
          f"min o_inf = {min(r[1] for r in rows1)}")
    print(f"   MAX Delta = {rows1[0][0]} = {float(rows1[0][0]):.7f}   at n0 = "
          f"{rows1[0][4]}   (budget {float(BUDGET):.7f})")
    print(f"   count with Delta > 1/12: {sum(1 for r in rows1 if r[0] > BUDGET)}")
    hi = [r for r in rows1 if r[3] >= 4]
    if hi:
        print(f"   restricted to height >= 4 (where Theorem A applies): "
              f"max o_inf = {max(r[1] for r in hi)}, max Delta = "
              f"{max(r[0] for r in hi)} = {float(max(r[0] for r in hi)):.7f}")

    # ------------------------------------------------- rank-2 arm
    keysA = {}
    for a in ADM3:
        for v in ADMH:
            p = plucker(a, v)
            if p is not None and p not in keysA:
                keysA[p] = (a, v)
    keysB = {}
    for i in range(len(HIGH)):
        for j in range(i + 1, len(HIGH)):
            p = plucker(HIGH[i], HIGH[j])
            if p is None or p in keysA or p in keysB:
                continue
            keysB[p] = (HIGH[i], HIGH[j])
    print(f"\n--- rank-2 classes ---")
    print(f"   arm A (a height-<=3 vector in the plane): {len(keysA)} planes")
    print(f"   arm B (no height-<=3 vector in the plane): {len(keysB)} planes")

    out, skipped, notreal, flat = [], [], 0, 0
    xval_bad = 0
    for arm, keys in (("A", keysA), ("B", keysB)):
        done = 0
        for p, (u, v) in keys.items():
            done += 1
            if done % 2000 == 0:
                print(f"   ... arm {arm}: {done}/{len(keys)}  kept {len(out)}  "
                      f"skipped {len(skipped)}  non-realisable {notreal}", flush=True)
            M = [list(u), list(v)]
            k, rk = RL.lattice_key(M)
            if rk != 2:
                continue
            rws = [list(r) for r in k]
            B, _ = RL.kernel_basis(rws)
            real = realisable(B)
            if HMAX <= 3:                      # cross-validate the O(1) test
                w = RL.witnesses(rws, PMAX=30, want=1)
                if bool(w) and not real:
                    xval_bad += 1
            if not real:
                notreal += 1
                continue
            if arm == "B":
                s3, rk3 = FLOOR, 0
            else:
                sh = [a for a in ADM3 if in_plane(p, a)]
                if not sh:
                    s3, rk3 = FLOOR, 0
                else:
                    k3, rk3 = RL.lattice_key([list(a) for a in sh])
                    if rk3 == 2:
                        flat += 1
                        continue
                    s3 = limit_of_rows([list(r) for r in k3])
            cc = cell_count(B)
            if cc > CELLCAP:
                skipped.append((k, cc, s3, arm))
                continue
            lim = TB.rank2_limit(rws)
            out.append((lim - s3, lim, s3, rk3, arm, k))
    out.sort(reverse=True)
    print(f"\n   planes with sub3 of rank 2 (Delta = 0 identically): {flat}")
    print(f"   planes not realisable: {notreal}")
    if HMAX <= 3:
        print(f"   cross-validation of the O(1) realisability test against "
              f"witnesses(PMAX=30): disagreements {xval_bad}")
    print(f"   planes SKIPPED for cell count > {CELLCAP}: {len(skipped)}")
    print(f"   planes evaluated: {len(out)}")
    if out:
        print(f"   max o_inf among them: {max(r[1] for r in out)}")
        print(f"   MAX Delta = {out[0][0]} = {float(out[0][0]):.7f}"
              f"   (budget {float(BUDGET):.7f})")
        nv = sum(1 for r in out if r[0] > BUDGET)
        print(f"   count with Delta > 1/12: {nv}")
        print(f"\n   {'Delta':>10} {'o_inf':>10} {'sub3':>10} rk3 arm  lattice")
        for d, lim, s3, rk3, arm, k in out[:30]:
            flag = "   <== REFUTES (H3u)" if d > BUDGET else ""
            print(f"   {float(d):>10.7f} {str(lim):>10} {str(s3):>10}  {rk3}  {arm}  "
                  f"{k}{flag}")
    if skipped:
        print(f"\n   the {len(skipped)} skipped planes, by cell count "
              f"(these are UNEVALUATED, not clean):")
        skipped.sort(key=lambda t: t[1])
        for k, cc, s3, arm in skipped[:15]:
            print(f"      cells {cc:>9}  arm {arm}  sub3 = {s3}  {k}")
