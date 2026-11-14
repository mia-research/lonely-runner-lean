"""Exact cascade replay around the moving fifth reading and dispatch boundaries."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product

from cascade_anchor_audit import cascade, in_way


def replacement(s, v, w, x, y):
    a, b = Q(1, 8), 7 / (8 * w)
    if not in_way(x, a):
        if not in_way(y, a):
            return a, "first opening"
        x, y = y, x

    p, q = x, y
    assert 7 < p < 9
    u = 9 / (8 * p)
    assert a <= u <= b
    if not in_way(q, u):
        return u, "first blocker opens"
    if not in_way(q, b):
        return b, "first closing"
    if 15 * w < 7 * q < 17 * w:
        assert 5 * p < 3 * q
        return Q(7, 8), "high second blocker"
    assert w < q and 7 * q < 9 * w and 7 * p < 9 * q
    if p >= Q(22, 3):
        return Q(9, 16), "low second blocker, larger p"
    if 25 * q > 31 * w:
        return Q(7, 8), "low second blocker, larger q"
    if 5 * s <= 3 * w:
        return 25 / (8 * w), "fifth reading opens"
    if 17 * w <= 15 * q:
        return 15 / (8 * w), "second closing"
    if 9 * v <= 7 * w:
        return 9 / (8 * w), "second opening"
    late = 33 / (8 * w)
    if 33 * p <= 47 * w:
        return late, "late fifth opening"
    assert 49 * q < 39 * p
    return max(late, 49 / (8 * p)), "late first-blocker opening"


def main():
    eps = Q(1, 1024)
    counts = Counter()
    for w in (Q(49, 10), 5 - eps, Q(5), 5 + eps, Q(101, 20), Q(46, 9)):
        edges = (Q(1), w, 9 * w / 7, 31 * w / 25, Q(7), Q(22, 3), Q(9),
                 15 * w / 7, 17 * w / 7, Q(15))
        rates = {a + h for a in edges for h in (-eps, 0, eps) if 1 <= a + h <= 15}
        pairs = set(product(rates, repeat=2))
        for p in (Q(71, 10), Q(15, 2), Q(22, 3), Q(8)):
            for q in (7 * p / 9, 5 * p / 3, Q(111, 20), 17 * w / 15, Q(25, 4)):
                for h in (-eps, 0, eps):
                    if 1 <= q + h <= 15:
                        pairs.update(((p, q + h), (q + h, p)))
        for p, q in ((Q(713, 100), Q(227, 40)), (47 * w / 33, Q(111, 20)),
                     (47 * w / 33 + eps, Q(111, 20)), (Q(71, 10), 17 * w / 15)):
            pairs.update(((p, q), (q, p)))
        slow_s = {Q(17, 7), Q(3), 3 * w / 5, 3 * w / 5 + eps, Q(23, 7)}
        slow_v = {Q(27, 7), Q(4), Q(31, 7)}
        slow_v.update(7 * w / 9 + h for h in (-eps, 0, eps)
                      if Q(27, 7) <= 7 * w / 9 + h <= Q(31, 7))
        for s, v, (x, y) in product(slow_s, slow_v, pairs):
            t, branch = replacement(s, v, w, x, y)
            readings = (1, 2, s, v, w, x, y)
            assert all(not in_way(d, t) for d in readings), (readings, t, branch)
            assert Q(1, 8) <= cascade(readings)[0] <= t <= Q(7, 8)
            counts[branch] += 1

    p, q, w = Q(71, 10), Q(111, 20), Q(101, 20)
    old = (1, 2, Q(3), Q(4), Q(5), p, q)
    moved = (1, 2, Q(3), Q(4), w, p, q)
    assert not in_way(5, Q(3, 8)) and in_way(w, Q(3, 8))
    before, _ = cascade(old)
    after, _ = cascade(moved)
    selected, branch = replacement(Q(3), Q(4), w, p, q)
    assert before == Q(5, 8) and after == selected == Q(125, 202)
    assert len(counts) == 11, counts
    s, v, p, q = Q(61, 20), Q(79, 20), Q(713, 100), Q(227, 40)
    rates = (1, 2, s, v, w, p, q)
    first, _ = cascade(rates)
    t, late_branch = replacement(s, v, w, p, q)
    assert in_way(s, 25 / (8 * w))
    assert first == Q(165, 227) < t == 33 / (8 * w)
    print(sum(counts.values()), "exact checks", dict(sorted(counts.items())))
    print(f"fifth reading 5 -> {w}, first landing {before} -> {after}, {branch}")
    print(f"middle opening blocked, first landing {first}, witness {t}, {late_branch}")


if __name__ == "__main__":
    main()
