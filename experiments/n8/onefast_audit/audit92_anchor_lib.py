"""Replay representative slow-cell reductions with exact rational arithmetic."""

from collections import Counter
from fractions import Fraction as Q
from itertools import accumulate
from math import ceil, lcm

EDGE = Q(1, 8)


def phase(d, t):
    return (d * t) % 1


def open_at(d, t):
    return (ceil(d * t-EDGE)+EDGE)/d


def in_way(d, t):
    r = phase(d, t)
    return min(r, 1-r) < EDGE


def cascade(readings, t=None):
    if t is None:
        t = EDGE/min(readings)
    trace = []
    for _ in range(4000):
        blockers = [d for d in readings if in_way(d, t)]
        if not blockers:
            return t, trace
        after = max(open_at(d, t) for d in blockers)
        assert after > t
        setters = tuple(sorted(d for d in blockers if open_at(d, t) == after))
        # The chosen blocker covers [t, after) by a single open bad interval.
        for d in setters:
            assert phase(d, after) == EDGE
            assert d*(after-t) < 2 * EDGE
        trace.append((t, after, setters))
        t = after
    raise AssertionError(('step cap', readings, t))


def split_cascade(slow, fast):
    t = EDGE/min(slow)
    cells = []
    for _ in range(4000):
        a, st = cascade(slow, t)
        b = min((ceil(d * a+EDGE)-EDGE)/d for d in slow)
        u, ft = cascade(fast, a)
        cells.append((a, b, u, len(st), len(ft)))
        if u <= b:
            assert all(not in_way(d, u) for d in slow+fast)
            return u, cells
        assert u > t
        t = u
    raise AssertionError(('cell cap', slow, fast))


def summarize(p):
    t, moves = cascade(p)
    u, cells = split_cascade(p[:-1], p[-1:])
    assert t == u
    return t, len(moves), len(cells), cells[-1][:2]


def run():
    original=[27, 70, 107, 137, 159, 188, 344, 393]
    seeds = {
        'AP': (1, 2, 3, 4, 5, 6, 7),
        'tight 12': (1, 2, 3, 4, 5, 7, 12),
        'tight 13': (1, 4, 5, 6, 7, 11, 13),
        'sole free flank': (2, 3, 4, 5, 6, 7, 16),
        'fixed-grid miss': (1, 2, 32, 33, 34, 35, 61),
        '28 moves': tuple(sorted(original[-1]-x for x in original[:-1])),
        'residual control 1': (
            132413891019516093961272499200,
            3919451174177676381253666672989,
            4570927517993695563543127216305,
            4805300105098239049854579107661,
            5165465888671322825429240601792,
            5243590084372837320866391227299,
            5827535343768903295235603103458,
        ),
        'residual control 2': (
            132413891019516093961272499200,
            3919451174177676381253666672989,
            4157796178012805350383957162945,
            4435865349153789147702629123213,
            5165465888671322825429240601792,
            5243590084372837320866391227299,
            5827535343768903295235603103458,
        ),
    }
    moved = Counter()
    anchored = Counter()
    permuted = Counter()
    omitted_phase = Counter()
    residue = Counter()
    for name, p in seeds.items():
        t, n, ncells, (a, b)=summarize(p)
        if name == '28 moves':
            assert n == 28 and ncells == 6
            for j, (left, right, u, _, _) in enumerate(split_cascade(p[:-1], p[-1:])[1], 1):
                print(f'  {j}: [{left}, {right}] → {u}')
        print(f'{name:20s} moves={n:2d} cells={ncells:2d} point={a == b} shift={t>a} R={8 * p[0]*t}')
        # A relabeling or a sign choice for one fixed subject preserves its disparity set.
        for v in (p[::-1], p[2:]+p[:2], tuple(abs((-1)**i * d) for i, d in enumerate(p))):
            assert cascade(v) == cascade(p)
        # Permuting adjacent physical gaps changes the subject's readings.
        gaps = tuple(y-x for x, y in zip((0, )+p, p))
        for order in (gaps[::-1], gaps[1:]+gaps[:1], gaps[::2]+gaps[1::2]):
            _, nq, cq, _ = summarize(tuple(accumulate(order)))
            permuted['checks'] += 1
            permuted['different move count'] += nq != n
            permuted['different cell count'] += cq != ncells
        for i, d in enumerate(p):
            for delta in (Q(-1, 2), Q(-1, 17), Q(1, 17), Q(1, 2)):
                q = tuple(sorted(p[:i]+(d+delta, )+p[i+1:]))
                _, nq, cq, _ = summarize(q)
                moved['checks'] += 1
                moved['different move count'] += nq != n
                moved['different cell count'] += cq != ncells
        for count in (1, 2, 3):
            slow, fast = p[:-count], p[-count:]
            old = t
            old_split, cells = split_cascade(slow, fast)
            assert old  ==  old_split
            a, b, _, _, _ = cells[-1]
            den = lcm(*((d * a).denominator for d in fast))
            # Run the same dilation without enforcing the phase condition.
            bad = tuple(2 * d for d in fast)
            ub, _ = cascade(bad, a)
            omitted_phase['checks'] += 1
            omitted_phase['missed original cell'] += ub>b
            for r in sorted({1, min(2, den), min(3, den), den}):
                ur, _ = cascade(tuple(r * d for d in fast), a)
                for k in (1, 13):
                    nscale = r+den * k
                    un, _ = cascade(tuple(nscale * d for d in fast), a)
                    assert un == a+Q(r, nscale)*(ur-a)
                    accepts = r*(ur-a)<=nscale*(b-a)
                    assert accepts == (un<=b)
                    residue['checks'] += 1
                    residue['accepted'] += accepts
            for k in (1, 13, 1009):
                c = 1+den * k
                scaled = tuple(c * d for d in fast)
                target = a+(old-a)/c
                assert a<=target<=b and all(not in_way(d, target) for d in slow+scaled)
                new, trace = cascade(slow+scaled)
                assert new<=target
                _, ft = cascade(fast, a)
                us, fs = cascade(scaled, a)
                assert us == target
                assert [(a+(x-a)/c, a+(y-a)/c, tuple(c * d for d in w)) for x, y, w in ft] == fs
                anchored['checks'] += 1
                anchored['exact predicted full landing'] += new == target
                anchored['earlier full landing'] += new<target
                anchored['changed full move count'] += len(trace) != n
    for c in (1, 2, 3, 10**3, 10**9):
        assert cascade((2, 3, 4, 5, 6, 7, 16 * c))[0] == Q(1, 16)+Q(1, 128 * c)
    assert in_way(24, Q(1, 8))
    assert cascade((1, 2, 3, 4, 5, 7, 24))[0]>Q(1, 8)
    print('Gap permutations:', dict(permuted))
    print('Perturbations:', dict(moved))
    print('Anchored dilations:', dict(anchored))
    print('Doubling without phase condition:', dict(omitted_phase))
    print('Residue thresholds:', dict(residue))

if __name__ == '__main__':
    run()
