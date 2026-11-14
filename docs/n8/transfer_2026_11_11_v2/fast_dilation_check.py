"""Exact difference-bound proof for the dilation test on circle gaps."""
from fractions import Fraction as Q
from math import lcm


def add_closed(bounds, i, j, value):
    """Add z[i]-z[j] <= value to a closed difference-bound matrix."""
    if value >= bounds[i][j]:
        return bounds
    if bounds[j][i] + value < 0:
        return None
    n = len(bounds)
    return tuple(tuple(min(bounds[p][q], bounds[p][i]+value+bounds[j][q])
                       for q in range(n)) for p in range(n))


def add_floyd(bounds, i, j, value):
    """Independent replay using full shortest-path closure."""
    if value >= bounds[i][j]:
        return bounds
    n = len(bounds)
    rows = [list(row) for row in bounds]
    rows[i][j] = value
    for k in range(n):
        for p in range(n):
            for q in range(n):
                rows[p][q] = min(rows[p][q], rows[p][k]+rows[k][q])
        if any(rows[p][p] < 0 for p in range(n)):
            return None
    return tuple(tuple(row) for row in rows)


def test(multipliers, gap, n=5, add=add_closed):
    assert multipliers[0] == 1
    unit = gap.denominator * lcm(*multipliers)
    bounds = tuple(tuple(0 if i == j else unit for j in range(n)) for i in range(n))
    for i in range(1, n):
        bounds = add(bounds, i-1, i, 0)
        bounds = add(bounds, i, i-1, int(gap*unit))
    bounds = add(bounds, 0, n-1, -int((1-gap)*unit))

    def cover_once(bounds, multiplier):
        step = unit // multiplier
        cap = int(gap*step)

        def place(bounds, previous, previous_lap, unused):
            if not unused:
                final = add(bounds, 0, previous, -(step-cap)-previous_lap*step)
                if final is not None:
                    yield final
                return
            for i in unused:
                for lap in range(multiplier):
                    shift = (lap-previous_lap)*step
                    branch = add(bounds, i, previous, shift+cap)
                    if branch is None:
                        continue
                    branch = add(branch, previous, i, -shift)
                    if branch is None:
                        continue
                    branch = add(branch, i, 0, (lap+1)*step)
                    if branch is not None:
                        yield from place(branch, i, lap, tuple(j for j in unused if j != i))

        return place(bounds, 0, 0, tuple(range(1, n)))

    current = {bounds} if bounds is not None else set()
    sizes = [len(current)]
    for m in multipliers[1:]:
        current = {out for state in current for out in cover_once(state, m)}
        sizes.append(len(current))
    return sizes, current


I = (Q(11,80), Q(69,400))
J = (Q(91,400), Q(149,400))
K = (Q(331,400), Q(69,80))
SLOW_PAIRS = ((J,J), (I,J), (J,K),
              (J, (1+J[0],1+J[1])), (J, (2+J[0],2+J[1])))
WINDOWS = ((Q(1,8), Q(7,8)), (Q(9,8), Q(15,8)))
MARGIN = Q(1,80)
DILATIONS = (1,2,5)


def test_slow_cover():
    previous = Q(1)
    for (lo,hi),(left,right) in SLOW_PAIRS:
        assert left/hi < previous < right/lo
        previous = right/lo
        for m in DILATIONS:
            assert any(a+MARGIN <= m*lo <= m*hi <= b-MARGIN for a,b in WINDOWS)
            lap = int(m*left)
            assert lap+Q(1,8)+MARGIN <= m*left <= m*right <= lap+Q(7,8)-MARGIN
    assert previous > 7 and 7*(J[1]-J[0]) > 1
    print("Five overlapping ratio intervals and the a >= 7 continuation verified.")


def base_time(a):
    if a >= 7:
        midpoint = sum(J)/2
        shift = int(a*J[0]-midpoint)+1
        return (shift+midpoint)/a
    for (lo,hi),(left,right) in SLOW_PAIRS:
        start, stop = max(lo,left/a), min(hi,right/a)
        if start < stop:
            return (start+stop)/2
    raise AssertionError(a)


def dist(x):
    y = x % 1
    return min(y,1-y)


def largest_gap(points):
    points = sorted(x % 1 for x in points)
    length, left, right = max((b-a,a,b) for a,b in zip(points,points[1:]+[points[0]+1]))
    return length,(left+right)/2 % 1


def lift(slow, fast, t, multipliers, slow_margin):
    base = min(fast)
    drifts = [v-base for v in fast]
    assert base >= max(max(slow)/(2*slow_margin),50*max(drifts))
    for m in multipliers:
        target = m*t
        assert all(dist(v*target) >= Q(1,8)+slow_margin for v in slow)
        gap, phase = largest_gap(-b*target for b in drifts)
        if gap > Q(27,100):
            result = (round(base*target-phase)+phase)/base
            assert any(L <= result <= U for L,U in WINDOWS)
            assert all(dist(v*result) >= Q(1,8) for v in (*slow,*fast))
            return result
    raise AssertionError((slow,fast))


def main():
    cap = Q(27,100)
    sizes, result = test(DILATIONS,cap)
    assert sizes == [1,6,0] and not result
    assert test(DILATIONS,cap,add=add_floyd) == (sizes,result)
    print("Five-point dilation test, gap cap 27/100:", sizes)
    print("Independent Floyd-Warshall replay agrees.")
    six_dilations = (1,2,3,4,5)
    sizes, result = test(six_dilations,cap,n=6)
    assert sizes == [1,52,52,52,0] and not result
    assert test(six_dilations,cap,n=6,add=add_floyd) == (sizes,result)
    print("Six-point dilation test, gap cap 27/100:", sizes)
    print("Independent Floyd-Warshall replay agrees.")
    test_slow_cover()
    import random
    rng = random.Random(125)
    for i in range(1000):
        a = Q(rng.randint(100,10000),100) if i%2 else Q(rng.randint(100,700),100)
        if i < 5:
            a = (Q(1), Q(7), Q(149,91), Q(149,55), Q(549,91))[i]
        drift = sorted([Q(0), *(Q(rng.randint(0,2000),100) for _ in range(4))])
        base = max(40*a,50*max(drift))
        lift((1,a),[base+b for b in drift],base_time(a),DILATIONS,MARGIN)
        drift.append(Q(rng.randint(0,2000),100))
        base = max(20,50*max(drift))
        lift((1,),[base+b for b in drift],Q(3,20),six_dilations,Q(1,40))
    print("2,000 exact lifted witnesses, including boundary rates.")


if __name__ == "__main__":
    main()
