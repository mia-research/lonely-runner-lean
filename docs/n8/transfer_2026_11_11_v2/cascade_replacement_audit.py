"""Exact replay for the replacement cells when the reading at 3 moves."""
from collections import Counter
from fractions import Fraction as Q

from cascade_anchor_audit import cascade, in_way
from cascade_two_deviations_audit import clear


def replacement(s, x, y):
    a, b = Q(1, 8), Q(7, 40)
    if clear((x, y), a):
        return a, "first opening"
    p, q = (x, y) if in_way(x, a) else (y, x)
    assert 7 < p < 9
    u = 9 / (8 * p)
    if clear((p, q), u):
        return u, "first rollover"
    if clear((p, q), b):
        return b, "first closing"
    low = 5 < q < Q(45, 7)
    assert (low and 7 * p < 9 * q) or (
        Q(75, 7) < q < Q(85, 7) and 5 * p < 3 * q
    )
    if s <= 3:
        if p >= Q(51, 7):
            return Q(7, 24), "second closing"
        if 17 * s <= 7 * p and (17 * q <= 15 * p or Q(75, 7) < q):
            return 17 / (8 * p), "extended second cell"
        if low and q <= Q(31, 5):
            return Q(5, 8), "downward at 5/8"
        return Q(7, 8), "downward at 7/8"
    if not low:
        return Q(3, 8), "third cell"
    if p >= Q(68, 9):
        return Q(9, 32), "second opening"
    if q >= Q(17, 3):
        return Q(3, 8), "third cell"
    if 17 * q <= 31 * s and (17 * p <= 39 * s or 41 * s <= 17 * p):
        return 17 / (8 * s), "moving opening"
    if p <= Q(235, 33):
        return Q(33, 40), "late cell"
    return 49 / (8 * p), "late cell"


def main():
    boundaries = (Q(1), Q(5), Q(45, 7), Q(7), Q(235, 33), Q(51, 7),
                  Q(68, 9), Q(9), Q(75, 7), Q(85, 7), Q(15))
    eps = Q(1, 1024)
    rates = sorted({b + e for b in boundaries for e in (-eps, Q(0), eps)
                    if 1 <= b + e <= 15})
    pairs = {(x, y) for x in rates for y in rates if x < y}
    pairs |= {(Q(71, 10), Q(111, 20)), (Q(71, 10), Q(12)), (Q(15, 2), Q(63, 10))}
    counts = Counter()
    lost = 0
    for s in (Q(17, 7), Q(29, 10), 3 - eps, Q(3), 3 + eps, Q(301, 100), Q(31, 10), Q(28, 9)):
        for x, y in sorted(pairs):
            t, label = replacement(s, x, y)
            readings = (1, 2, s, 4, 5, x, y)
            assert clear(readings, t)
            assert Q(1, 8) <= cascade(readings)[0] <= t <= Q(7, 8)
            counts[label] += 1
            lost += not clear((1, 2, s, 4, 5), Q(3, 8))
    print(sum(counts.values()), "exact checks,", lost, "with the old slow 3/8 point lost")
    print(dict(counts))
    for s, p, q, expected in (
        (Q(29, 10), Q(71, 10), Q(12), Q(85, 284)),
        (Q(301, 100), Q(71, 10), Q(111, 20), Q(33, 40)),
        (Q(31, 10), Q(71, 10), Q(111, 20), Q(85, 124)),
    ):
        t, _ = cascade((1, 2, s, 4, 5, p, q))
        assert t == expected
        print(f"s={s}, p={p}, q={q}, first landing={t}")


if __name__ == "__main__":
    main()
