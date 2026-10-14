r"""
tb_hunt_v1 -- the targeted search for a violation of

    (H3u)   Tail_3(e) = o(e) - o_inf(L_3(e)^sat)  <=  1/12 ,
            whenever rank L_3(e) <= 2.

THE TARGET, stated before the search (this is the pre-declared mechanism, not a
post-hoc reading).  Tail_3 is a DIFFERENCE of two class limits plus a fluctuation:
if e has no resonance of height <= 3 at all then o_inf(L_3^sat) = 3/32, while the
true limit of o along the family is o_inf(M') for the lattice M' of ALL resonances.
So a violation needs a saturated lattice M' with

    (a)  NO nonzero vector of sup-norm height <= 3      (so L_3(e) = 0 for deep
         witnesses, hence o_inf(L_3^sat) = 3/32 exactly),
    (b)  o_inf(M') > 3/32 + 1/12 = 17/96 = 0.1770833...,
    (c)  realisable: positive primitive e with e_rho = rho mod 8 and n.e = 0 for
         all n in M'.

More generally, with h = the minimum height of M', any e whose only low resonances
are those of M' has  Tail_3(e) -> o_inf(M') - o_inf(M'_{<=3}) and the same search
covers the rank-1 case (M'_{<=3} of rank 1 with a small limit).

This script enumerates saturated rank-2 lattices generated at height <= HMAX,
records their minimum height and their EXACT limit, and reports every one that
satisfies (a)+(b), together with witnesses.

usage:  python3 tb_hunt_v1.py [HMAX] [PMAX]
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce

import rt_limit_v2 as RL

HMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
PMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
RHO = (1, 3, 5, 7)
THRESH = F(3, 32) + F(1, 12)          # 17/96


def min_height(M, cap=8):
    """minimum sup-norm of a nonzero vector of the SATURATED lattice spanned by M."""
    B, rk = RL.kernel_basis(M)
    Bt = [[B[r][c] for r in range(4)] for c in range(len(B[0]))]
    Lb, _ = RL.kernel_basis(Bt)
    rows = [tuple(Lb[r][c] for r in range(4)) for c in range(len(Lb[0]))]
    r = len(rows)
    best = None
    K = cap * 4
    for co in itertools.product(range(-K, K + 1), repeat=r):
        if all(c == 0 for c in co):
            continue
        v = [sum(co[t] * rows[t][i] for t in range(r)) for i in range(4)]
        h = max(abs(x) for x in v)
        if best is None or h < best:
            best = h
    return best, rows


def lattice_vectors_upto(rows, H):
    """all nonzero vectors of the lattice spanned by `rows` with sup-norm <= H."""
    r = len(rows)
    out = []
    K = H * 4 + 4
    for co in itertools.product(range(-K, K + 1), repeat=r):
        if all(c == 0 for c in co):
            continue
        v = tuple(sum(co[t] * rows[t][i] for t in range(r)) for i in range(4))
        if max(abs(x) for x in v) <= H:
            out.append(v)
    return out


if __name__ == "__main__":
    print(f"tb_hunt_v1   HMAX = {HMAX}   PMAX = {PMAX}")
    print(f"threshold for a refutation from the rank-0 floor: "
          f"o_inf(M') > 3/32 + 1/12 = {THRESH} = {float(THRESH):.7f}\n")

    adm = [v for v in itertools.product(range(-HMAX, HMAX + 1), repeat=4)
           if RL.admissible(v)]
    print(f"admissible primitive vectors of height <= {HMAX}: {len(adm)}")

    seen = {}
    skipped = 0
    for i in range(len(adm)):
        for j in range(i + 1, len(adm)):
            M = [list(adm[i]), list(adm[j])]
            B, rk = RL.kernel_basis(M)
            if rk != 2:
                continue
            key, _ = RL.lattice_key(M)
            if key in seen:
                continue
            rows = [list(r) for r in key]
            short = lattice_vectors_upto(rows, 3)
            h3 = len(short) == 0                       # condition (a)
            ws = RL.witnesses(M, PMAX=PMAX, want=3)
            if not ws:
                seen[key] = None
                continue
            try:
                lim = RL.rank2_limit(rows)
            except ValueError:
                skipped += 1
                seen[key] = None
                continue
            seen[key] = (lim, h3, ws)
    good = {k: v for k, v in seen.items() if v}
    print(f"distinct realisable saturated rank-2 classes met: {len(good)}"
          f"   (skipped for cell-count: {skipped})")

    noshort = [(v[0], k, v[2]) for k, v in good.items() if v[1]]
    print(f"of these, with NO nonzero vector of height <= 3: {len(noshort)}")
    if noshort:
        noshort.sort(reverse=True)
        mx = noshort[0][0]
        print(f"   max limit among them: {mx} = {float(mx):.7f}"
              f"   (need > {float(THRESH):.7f} for a refutation)")
        print(f"   {'limit':>10} {'float':>10}   lattice (HNF rows)   witnesses")
        for lim, k, ws in noshort[:25]:
            flag = "   <-- REFUTES (H3u) if the witness has no other low resonance" \
                if lim > THRESH else ""
            print(f"   {str(lim):>10} {float(lim):>10.7f}   {k}   {ws[:2]}{flag}")

    allr = sorted(((v[0], k, v[1], v[2]) for k, v in good.items()), reverse=True)
    print(f"\n   overall max rank-2 limit at height <= {HMAX}: "
          f"{allr[0][0]} = {float(allr[0][0]):.7f}")
    print(f"   count with limit > 1/4: {sum(1 for a in allr if a[0] > F(1,4))}")
    print(f"   count with limit > 1/3: {sum(1 for a in allr if a[0] > F(1,3))}")
