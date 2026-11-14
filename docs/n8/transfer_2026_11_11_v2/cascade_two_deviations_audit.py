"""Exact checks for the two-reading escape from the first slow cell."""
from collections import Counter
from fractions import Fraction as Q

from cascade_anchor_audit import cascade, in_way


def clear(readings, time):
    return all(not in_way(rate, time) for rate in readings)


def select_witness(x, y):
    a, b = Q(1, 8), Q(7, 40)
    if clear((x, y), a):
        return a, "initial opening"
    p, q = (x, y) if in_way(x, a) else (y, x)
    assert 7 < p < 9
    u = 9 / (8 * p)
    if clear((p, q), u):
        return u, "first rollover"
    if clear((p, q), b):
        return b, "first closing"
    assert q < Q(45, 7) or Q(75, 7) < q < Q(85, 7)
    if p >= Q(51, 7):
        return Q(7, 24), "second cell"
    if 5 < q < Q(17, 3):
        return Q(5, 8), "fourth point"
    return Q(3, 8), "third point"


def main():
    slow_blocks = (
        tuple(map(Q, (1, 2, 3, 4, 5))),
        (Q(1), Q(7, 3), Q(3), Q(27, 7), Q(23, 5)),
        (Q(1), Q(11, 6), Q(3), Q(21, 5), Q(9, 2)),
    )
    offsets = (Q(-1, 1024), Q(0), Q(1, 1024))
    edges = (Q(1), Q(5), Q(49, 9), Q(17, 3), Q(6), Q(45, 7), Q(7), Q(51, 7), Q(9), Q(75, 7), Q(11), Q(85, 7), Q(15))
    rates = sorted({edge + offset for edge in edges for offset in offsets if 1 <= edge + offset <= 15})
    pairs = {(p, q) for p in rates for q in rates if p < q}
    pairs |= {(Q(71, 10), Q(61, 10)), (Q(71, 10), Q(12)), (Q(15, 2), Q(63, 10)), (Q(71, 10), Q(111, 20))}
    counts = Counter()
    for slow in slow_blocks:
        for x, y in sorted(pairs):
            witness, branch = select_witness(x, y)
            readings = slow + (x, y)
            assert clear(readings, witness)
            landing, _ = cascade(readings)
            assert Q(1, 8) <= landing <= witness <= Q(5, 8)
            counts[branch] += 1
    assert cascade(slow_blocks[0] + (Q(71, 10), Q(111, 20)))[0] == Q(5, 8)
    print(sum(counts.values()), "exact checks", dict(counts))
    for x, y in ((Q(71, 10), Q(61, 10)), (Q(71, 10), Q(12)), (Q(15, 2), Q(63, 10)), (Q(71, 10), Q(111, 20))):
        print(x, y, select_witness(x, y))


if __name__ == "__main__":
    main()
