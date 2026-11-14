"""Exact replay when both edges of the second cell move."""
from collections import Counter
from fractions import Fraction as Q

from cascade_anchor_audit import cascade, in_way
from cascade_replacement_audit import replacement
from cascade_two_deviations_audit import clear


def adjusted_replacement(s, v, x, y):
    time, branch = replacement(s, x, y)
    if branch == "second opening":
        a = max(Q(9, 32), 9 / (8 * v))
        if s * a <= Q(7, 8):
            return a, "adjusted second opening"
        if v <= Q(75, 17):
            return Q(17, 40), "second cell lost, earlier backup"
        return Q(9, 16), "second cell lost, later backup"
    if branch == "moving opening" and in_way(v, time):
        p = x if in_way(x, Q(1, 8)) else y
        t = 49 / (8 * p) if p > Q(235, 33) else Q(33, 40)
        return t, "moving opening blocked"
    return time, branch


def main():
    eps = Q(1, 1024)
    edges = (Q(1), Q(5), Q(17, 3), Q(45, 7), Q(7), Q(51, 7),
             Q(68, 9), Q(9), Q(75, 7), Q(85, 7), Q(15))
    rates = sorted({a + h for a in edges for h in (-eps, Q(0), eps) if 1 <= a + h <= 15})
    pairs = {(x, y) for x in rates for y in rates if x < y}
    pairs |= {(Q(39, 5), Q(31, 5)), (Q(8), Q(25, 4)), (Q(71, 10), Q(111, 20))}
    counts = Counter()
    for s in (Q(17, 7), Q(29, 10), Q(3), Q(151, 50), Q(31, 10), Q(28, 9), Q(16, 5), Q(23, 7)):
        for v in (Q(27, 7), Q(39, 10), 4 - eps, Q(4), 4 + eps, Q(17, 4), Q(31, 7)):
            for x, y in sorted(pairs):
                t, branch = adjusted_replacement(s, v, x, y)
                readings = (1, 2, s, v, 5, x, y)
                assert clear(readings, t)
                assert Q(1, 8) <= cascade(readings)[0] <= t <= Q(7, 8)
                counts[branch] += 1
    print(sum(counts.values()), "exact checks", dict(counts))
    for s, v, p, q, expected in (
        (Q(151, 50), Q(39, 10), Q(39, 5), Q(31, 5), Q(15, 52)),
        (Q(31, 10), Q(39, 10), Q(8), Q(25, 4), Q(17, 40)),
    ):
        t, _ = cascade((1, 2, s, v, 5, p, q))
        assert t == expected
        print(f"s={s}, v={v}, p={p}, q={q}, first landing={t}")


if __name__ == "__main__":
    main()
