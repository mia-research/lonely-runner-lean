"""Exact regression of a two-sided failure and its forced successor.

No universal coverage assertion. The finite corners are regression checks;
the continuous family is proved in BidirectionalReplacementN.lean.
"""
from fractions import Fraction as F
from itertools import product
from math import floor

D = tuple(map(F, ['89/8', '127/8', '79/32', '2119/128',
                  '399/64', '87/64', '153/64']))


def phase(d, t):
    return d*t - floor(d*t)


def blocked(ds, t):
    return [i for i, d in enumerate(ds) if not F(1, 8) <= phase(d, t) <= F(7, 8)]


def inspect(ds, t):
    """Distinguish current-band retention from actual modulo clearance."""
    bad = blocked(ds, t)
    if len(bad) != 1:
        return {'time': str(t), 'blockers': [i+1 for i in bad]}
    bidx, = bad
    b = ds[bidx]
    K = floor(b*t + F(1, 2))
    z = b*t-K
    hf, hb = (F(1, 8)-z)/b, (z+F(1, 8))/b
    forward = [i for i, d in enumerate(ds) if i != bidx and
               d*hf > F(7, 8)-phase(d, t)]
    backward = [i for i, d in enumerate(ds) if i != bidx and
                d*hb > phase(d, t)-F(1, 8)]
    for i in set(forward) & set(backward):
        assert ds[i] > 3*b
    for i in forward:
        assert floor(ds[i]*(t+hf)-F(1, 8)) >= floor(ds[i]*t)
    return {'time': str(t), 'blocker': bidx+1,
            'forward_time': str(t+hf), 'forward_guards': [i+1 for i in forward],
            'forward_captured': [i+1 for i in blocked(ds, t+hf)],
            'backward_time': str(t-hb), 'backward_guards': [i+1 for i in backward],
            'backward_captured': [i+1 for i in blocked(ds, t-hb)]}


def run():
    assert not blocked(D, F(1))
    for m in (2, 3, 5):
        print(inspect(D, F(m)))
    first = F(33, 8)/D[5]
    assert first == F(88, 29) and blocked(D, first) == [4]
    next_label = floor(D[4]*3)+1
    second = (next_label+F(1, 8))/D[4]
    assert next_label == 19 and second == F(408, 133)
    assert not blocked(D, second)
    print('forced successor', second, 'labels', [floor(d*second) for d in D])
    # Reading 1 is clear at both ends but captured in between: its label changes.
    centre_crossing = F(34)/D[0]
    assert first < centre_crossing < second
    assert 0 in blocked(D, centre_crossing)
    print('intervening capture of reading 1', centre_crossing)
    count = 0
    for signs in product((-1, 1), repeat=6):
        ds = list(D)
        for i, s in zip((0, 1, 2, 3, 5, 6), signs):
            ds[i] += F(s, 10000)
        assert blocked(ds, F(3)) == [5]
        assert blocked(ds, F(33, 8)/ds[5]) == [4]
        assert not blocked(ds, second)
        count += 1
    print('exact box corner regressions', count)


if __name__ == '__main__':
    run()
