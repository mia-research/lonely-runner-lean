"""Exact circle cover certificates for fast blocks with small harmonic slopes."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import ceil, floor, gcd, lcm

from fast_dilation_check import (
    WINDOWS, add_closed, base_time, dist, test_slow_cover,
)

CAP = Q(13, 100)
SPECIAL = (1, 1, 1, 3, 3)
FIRST = (1, 2, 5)
SPECIAL_TIMES = (1, 2, 3)
SIX = (1, 2, 3, 4, 5)


def cover_states(slopes, multipliers, cap):
    """Branch on an arc continuing past each right endpoint."""
    n = len(slopes)
    # All original bounds are integral in units of denominator. Refine
    # by n+1 so that strictness can be encoded by subtracting one unit.
    unit = lcm(*slopes) * lcm(*multipliers) * cap.denominator * (n+1)
    root = tuple(tuple(0 if i == j else unit//slopes[i] for j in range(n))
                 for i in range(n))
    for i in range(1, n):
        if slopes[i] == slopes[i-1]:
            root = add_closed(root, i-1, i, 0)
    states = {root}
    counts = []
    for m in multipliers:
        clauses = []
        for i, p in enumerate(slopes):
            for j in range(p):
                end = (j+cap)/p
                choices = []
                for h, r in enumerate(slopes):
                    if h == i:
                        continue
                    low = floor(r*(end-Q(m,p))-cap)
                    high = ceil(r*end+m+cap)
                    for k in range(low, high+1):
                        back = ((k+cap)/r-end)/m*unit
                        forward = (end-(k-cap)/r)/m*unit
                        assert back.denominator == forward.denominator == 1
                        c, d = int(forward), int(back)-1
                        if c+root[h][i] >= 0 and d+root[i][h] >= 0:
                            choices.append((i,h,c,d))
                clauses.append(choices)

        def branch(bounds, pending):
            best = None
            satisfied = set()
            for j in pending:
                feasible = []
                for i,h,c,d in clauses[j]:
                    if c >= bounds[i][h] and d >= bounds[h][i]:
                        satisfied.add(j)
                        break
                    if c+bounds[h][i] >= 0 and d+bounds[i][h] >= 0 and c+d >= 0:
                        feasible.append((i,h,c,d))
                else:
                    if not feasible:
                        return
                    if best is None or len(feasible) < len(best[1]):
                        best = (j,feasible)
            if best is None:
                yield bounds
                return
            selected, choices = best
            pending = tuple(j for j in pending if j != selected and j not in satisfied)
            for i,h,c,d in choices:
                updated = add_closed(bounds, i, h, c)
                if updated is not None:
                    updated = add_closed(updated, h, i, d)
                    if updated is not None:
                        yield from branch(updated, pending)

        states = {next_state for bounds in states
                  for next_state in branch(bounds, tuple(range(len(clauses))))}
        counts.append(len(states))
        if not states:
            break
    return counts


def uncovered_phase(slopes, offsets, m, cap):
    """Independently find a point outside the closed bad arcs, if one exists."""
    arcs = []
    for p,x in zip(slopes, offsets):
        for j in range(p):
            center = (Q(j,p)-m*x) % 1
            radius = cap/p
            for k in (-1,0,1):
                lo, hi = max(Q(0),center+k-radius), min(Q(1),center+k+radius)
                if lo <= hi:
                    arcs.append((lo,hi))
    end = Q(0)
    for lo,hi in sorted(arcs):
        if lo > end:
            return (lo+end)/2
        end = max(end,hi)
    return (end+1)/2 if end < 1 else None


U = (Q(11,80), Q(23,80))
TARGETS = (U, (Q(91,160),Q(149,240)), (1+U[0],1+U[1]))


def special_time(a):
    if a >= 7:
        midpoint = sum(U)/2
        return (floor(a*U[0]-midpoint)+1+midpoint)/a
    for v,w in TARGETS:
        lo,hi = max(U[0],v/a),min(U[1],w/a)
        if lo < hi:
            return (lo+hi)/2
    raise AssertionError(a)


def check_slow():
    test_slow_cover()
    reach = Q(1)
    for v,w in TARGETS:
        assert v/U[1] < reach < w/U[0]
        reach = w/U[0]
        for m in SPECIAL_TIMES:
            lap = floor(m*v)
            assert lap+Q(11,80) <= m*v <= m*w <= lap+Q(69,80)
    assert reach > 7 and 7*(U[1]-U[0]) > 1
    for m in SPECIAL_TIMES:
        assert Q(11,80) <= m*U[0] <= m*U[1] <= Q(69,80)
    for m in SIX:
        assert Q(3,20) <= m*Q(3,20) <= Q(17,20)


def check_lift(slopes, slow, drifts, base, base_time, multipliers):
    offsets = [b*base_time/p for p,b in zip(slopes,drifts)]
    for m in multipliers:
        phase = uncovered_phase(slopes,offsets,m,CAP)
        if phase is None:
            continue
        target = m*base_time
        actual = (round(base*target-phase)+phase)/base
        assert any(lo <= actual <= hi for lo,hi in WINDOWS)
        assert all(dist(v*actual) >= Q(1,8) for v in
                   (*slow, *(p*base+b for p,b in zip(slopes,drifts))))
        return
    raise AssertionError(slopes)


def main():
    check_slow()
    obstruction = tuple(map(Q, ("0","1/3","2/3","1/12","1/6")))
    assert all(uncovered_phase(SPECIAL,obstruction,m,Q(1,8)) is None for m in FIRST)
    assert uncovered_phase(SPECIAL,obstruction,3,CAP) is not None
    print("Exact control for the special choice of dilations verified.")
    for n, maximum, expected in ((5,9,1208),(6,4,75)):
        tested = 0
        for slopes in combinations_with_replacement(range(1,maximum+1),n):
            if len(set(slopes)) == 1 or gcd(*slopes) != 1:
                continue
            multipliers = SPECIAL_TIMES if slopes == SPECIAL else FIRST if n == 5 else SIX
            counts = cover_states(slopes,multipliers,CAP)
            assert counts[-1] == 0, (slopes,counts)
            tested += 1
            for a in (Q(1),Q(3,2),Q(7),Q(71,10)):
                drifts = tuple(Q((-1)**i*(i+1),3) for i in range(n))
                spread = max(map(abs,drifts))
                if n == 5:
                    t = special_time(a) if slopes == SPECIAL else base_time(a)
                    check_lift(slopes,(1,a),drifts,max(40*a,100*spread),t,multipliers)
                else:
                    check_lift(slopes,(1,),drifts,max(20,100*spread),Q(3,20),multipliers)
        assert tested == expected
        print(n,"fast readings:", tested,"mixed primitive slope patterns closed at",CAP,
              "with",4*tested,"exact lifted controls.")


if __name__ == "__main__":
    main()
