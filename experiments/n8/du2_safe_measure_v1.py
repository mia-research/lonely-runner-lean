r"""
du2_safe_measure_v1  --  n=8 DROPPED-UNIT leaf, representative speeds.
Exact safe set of the five non-divisible runners, for each of the 18 absent pairs
that contain at least one unit of Z/8.

Independent re-implementation (does not import du_safe_measure_v1).

Discipline enforced:
 (i)  BOUNDARY EXACTNESS.  No cell centre is ever evaluated.  For every cell [a,b)
      and every speed e we check by exact rational comparison that no integer k has
      a < k/e < b, and that floor(e*a) == floor(e*b) - [e*b in Z].  Both counts are
      reported.  The covered set is computed BOTH at entry and at exit and compared.
 (ii) EVERY UNCOVERED RESIDUE IS TRACKED.  Each cell records the full set
      U = Z/8 \ (union of bad sets); a window is reported with the per-cell U's and
      with the intersection of the U's over the window.
 (iii) INDEPENDENT INTEGER RECOMPUTATION.  The measure is recomputed by pure integer
      enumeration over b in [0, L), L = lcm(E_non), with t_e = (e*b)//L.  No Fractions.

Exact rational / integer arithmetic only.  Nothing here evaluates LRC(8) numerically.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd

UNITS = frozenset({1, 3, 5, 7})
Z8    = frozenset(range(8))


def bad(e, t):
    """{ r in Z/8 : (e*r + t) mod 8 in {0,7} }.  Depends only on e mod 8 and t mod 8."""
    return frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))


def breakpoints(speeds):
    pts = {F(0), F(1)}
    for e in speeds:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts)
    return list(zip(p, p[1:]))


def fl_entry(e, a):
    """floor(e*a) -- the value of floor(e*x) at the LEFT-CLOSED endpoint x = a."""
    v = e * a
    return v.numerator // v.denominator


def fl_exit(e, b):
    """lim_{x -> b^-} floor(e*x) = floor(e*b) - [e*b in Z]."""
    v = e * b
    f = v.numerator // v.denominator
    return f - 1 if v.denominator == 1 else f


def analyse(Enon):
    cells = breakpoints(Enon)
    n_interior = 0          # integers k with a < k/e < b   (must be 0)
    n_mismatch = 0          # floor entry != floor exit      (must be 0)
    n_setdiff  = 0          # covered(entry) != covered(exit) (must be 0)
    meas = F(0)
    safe = []               # (a, b, uncovered set)
    for a, b in cells:
        for e in Enon:
            lo = e * a
            k0 = lo.numerator // lo.denominator + 1     # least integer > e*a
            if F(k0, e) < b:
                n_interior += 1
            if fl_entry(e, a) != fl_exit(e, b):
                n_mismatch += 1
        cin = set(); cout = set()
        for e in Enon:
            cin  |= bad(e, fl_entry(e, a))
            cout |= bad(e, fl_exit(e, b))
        if cin != cout:
            n_setdiff += 1
        U = Z8 - cin
        if U:
            meas += b - a
            safe.append((a, b, frozenset(U)))
    # maximal windows = maximal runs of contiguous safe cells
    wins = []
    for a, b, U in safe:
        if wins and wins[-1][1] == a:
            wins[-1][1] = b
            wins[-1][2].append((a, b, U))
        else:
            wins.append([a, b, [(a, b, U)]])
    out = []
    for lo, hi, parts in wins:
        common = frozenset.intersection(*[U for _, _, U in parts])
        out.append((lo, hi, parts, common))
    return dict(ncells=len(cells), interior=n_interior, mismatch=n_mismatch,
                setdiff=n_setdiff, meas=meas, windows=out)


def integer_recount(Enon):
    """Independent: pure-integer enumeration in b-coordinates.  Returns (count, L)."""
    L = 1
    for e in Enon:
        L = L * e // gcd(L, e)
    cnt = 0
    for b in range(L):
        cov = 0
        for e in Enon:
            t = (e * b) // L
            for r in range(8):
                if (e * r + t) % 8 in (0, 7):
                    cov |= 1 << r
        if cov != 255:
            cnt += 1
    return cnt, L


def main():
    pairs = [A for A in combinations(range(1, 8), 2) if set(A) & UNITS]
    assert len(pairs) == 18, len(pairs)

    ti = tm = ts = 0
    worst = None
    rows = []
    print("n=8 DROPPED-UNIT leaf, representative speeds: exact safe set of E_non\n")
    print(f"{'absent':>8} | {'E_non':<17} | {'|S|':>8} | {'float':>8} | >1/2 | "
          f"{'surplus |S|-1/2':>16} | wins")
    print("-" * 92)
    for A in pairs:
        Enon = sorted(set(range(1, 8)) - set(A))
        R = analyse(Enon)
        ti += R['interior']; tm += R['mismatch']; ts += R['setdiff']
        m = R['meas']
        rows.append((A, Enon, R))
        if worst is None or m < worst[1]:
            worst = (A, m)
        print(f"{str(A):>8} | {str(Enon):<17} | {str(m):>8} | {float(m):8.5f} | "
              f"{str(m > F(1,2)):>4} | {str(m - F(1,2)):>16} | {len(R['windows'])}")

    print("-" * 92)
    print(f"BOUNDARY AUDIT over all 18 pairs:  interior breakpoints = {ti} ; "
          f"entry/exit floor mismatches = {tm} ; entry-vs-exit covered-set diffs = {ts}")
    print(f"MINIMUM |S| over the 18 pairs = {worst[1]} = {float(worst[1]):.6f}  at absent {worst[0]}")
    print(f"MINIMUM surplus over 1/2      = {worst[1] - F(1,2)} = {float(worst[1]-F(1,2)):.6f}")
    print(f"All 18 satisfy |S| > 1/2 ?  {all(r[2]['meas'] > F(1,2) for r in rows)}")

    print("\n\nINDEPENDENT INTEGER RECOUNT (pure integer, b-coordinates, no Fractions)")
    print(f"{'absent':>8} | {'L':>6} | {'#safe b':>8} | {'count/L':>10} | matches Fraction measure")
    print("-" * 72)
    allok = True
    for A, Enon, R in rows:
        cnt, L = integer_recount(Enon)
        ok = F(cnt, L) == R['meas']
        allok &= ok
        print(f"{str(A):>8} | {L:>6} | {cnt:>8} | {str(F(cnt,L)):>10} | {ok}")
    print(f"\nAll 18 integer recounts agree with the exact cell measure: {allok}")

    print("\n\nWINDOW DETAIL  (requirement (ii): every uncovered residue tracked)")
    for A, Enon, R in rows:
        print(f"\nabsent {A}  E_non = {Enon}   |S| = {R['meas']}   "
              f"cells = {R['ncells']}  windows = {len(R['windows'])}")
        for lo, hi, parts, common in R['windows']:
            print(f"   W = [{lo}, {hi})  len {hi-lo}  ({len(parts)} cells)  "
                  f"common uncovered = {sorted(common) if common else 'EMPTY'}")
            for a, b, U in parts:
                print(f"        [{a}, {b})  U = {sorted(U)}")


if __name__ == "__main__":
    main()
