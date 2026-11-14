"""Exact tests for the one-fast rejection rule and its two-cell certificates."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import ceil, floor
from random import Random

from cascade_anchor_audit import cascade

R = Q(1, 8)
WINDOWS = ((R, 1 - R), (1 + R, 2 - R))


def clear_cells(core):
    cells = list(WINDOWS)
    for reading in core:
        clipped = []
        for a, b in cells:
            for lap in range(floor(reading * a), floor(reading * b) + 1):
                left = max(a, (lap + R) / reading)
                right = min(b, (lap + 1 - R) / reading)
                if left <= right:
                    clipped.append((left, right))
        cells = clipped
    return cells


def rejects(d, cell, phase=0):
    a, b = cell
    return floor(d * b + phase - R) + 1 < d * a + phase + R


def first_fast_clear(d, a, phase):
    position = d * a + phase
    if R <= position % 1 <= 1 - R:
        return a
    return (ceil(position - R) + R - phase) / d


def incompatible(d, cell, other):
    a, b = cell
    c, e = other
    return floor(d * (e - a) - 2 * R) + 1 >= d * (c - b) + 2 * R


def phase_sweep(d, cells):
    """Every rejection predicate is constant between its two phase endpoints."""
    edges = sorted({Q(0), Q(1)} | {
        phase % 1
        for a, b in cells
        for phase in (R - d * b, -R - d * a)
    })
    return edges + [(a + b) / 2 for a, b in zip(edges, edges[1:])]


def anchored_controls():
    total = 0
    perturbations = tuple(product((-Q(1, 256), Q(0), Q(1, 256)), repeat=4))
    for w in (Q(41, 7), Q(59, 10), Q(6), Q(61, 10), Q(55, 9)):
        cells = ((R, 7 / (8 * w)), (41 / (8 * w), 7 * R), (9 * R, 55 / (8 * w)))
        assert all(a <= b for a, b in cells)
        for offsets in perturbations:
            slow = (1, *(i + off for i, off in enumerate(offsets, 2)), w)
            for a, b in cells:
                assert any(left <= a <= b <= right for left, right in clear_cells(slow))
            for d in (w, w + Q(1, 1024), Q(7), Q(11), 2 * w, 1024 * w):
                for phase in phase_sweep(d, cells):
                    accepts = []
                    for cell in cells:
                        a, b = cell
                        t = first_fast_clear(d, a, phase)
                        assert (t > b) == rejects(d, cell, phase)
                        if t <= b:
                            assert all(R <= (s * t) % 1 <= 1 - R for s in slow)
                            assert R <= (d * t + phase) % 1 <= 1 - R
                            accepts.append(t)
                    assert accepts
                    if phase == 0:
                        assert cascade((*slow, d))[0] <= min(accepts)
                    total += 1
    return total


def pinch_controls():
    checks = 0
    for w in (Q(145, 21), Q(111, 16), Q(223, 32), Q(7)):
        slow = (1, Q(11, 6), Q(19, 7), Q(9, 2), 5, w)
        cells = ((R, 7 / (8 * w)), (9 / (8 * w), Q(7, 40)))
        for a, b in cells:
            assert any(left <= a <= b <= right for left, right in clear_cells(slow))
        for d in (w, w + Q(1, 16), 3 * w - Q(1, 1024), 3 * w,
                  3 * w + Q(1, 1024), 100 * w):
            for phase in phase_sweep(d, cells):
                assert any(first_fast_clear(d, a, phase) <= b for a, b in cells)
                checks += 1
    return checks


def broader_controls():
    rng = Random(8)
    cores = [(1, *c) for c in combinations(range(2, 13), 5)]
    grid = [Q(i, 16) for i in range(17, 257)]
    cores += [(1, *sorted(rng.sample(grid, 5))) for _ in range(500)]
    counts = Counter()
    for slow in cores:
        cells = clear_cells(slow)
        for offset in (Q(1, 16), Q(1, 4), 1, 3, 8, 16):
            d = max(slow) + offset
            wide = any(d * (b - a) >= 2 * R for a, b in cells)
            pair = not wide and any(incompatible(d, c, e) for c, e in combinations(cells, 2))
            has_bad_phase = any(all(rejects(d, c, phase) for c in cells)
                                for phase in phase_sweep(d, cells))
            assert has_bad_phase == (not wide and not pair)
            if pair and any(3 * (f - e) <= e - a and d * (g - c) >= Q(5, 4)
                            and 9 * (c - b) <= 23 * (g - c)
                            for (a, b), (c, e), (f, g) in combinations(cells, 3)):
                counts["two cells forced by endpoint comparison"] += 1
            else:
                counts["one cell" if wide else "two cells" if pair else "common rejection"] += 1
    return dict(sorted(counts.items()))


def main():
    print(anchored_controls(), "anchored exact phase checks")
    print(pinch_controls(), "pinch exact phase checks")
    print("Broader exact controls", broader_controls())

    # A shifted fast reading blocks every first-window cell of this core.
    slow = (1, Q(4, 3), Q(10, 3), Q(17, 4), Q(19, 4), Q(16, 3))
    d, phase = Q(65, 12), Q(1, 5)
    cells = clear_cells(slow)
    first = [c for c in cells if c[1] <= 7 * R]
    assert len(first) == 3 and all(rejects(d, c, phase) for c in first)
    second = (Q(171, 128), Q(47, 34))
    assert second in cells and not rejects(d, second, phase)
    print("Shifted first-window failure at", slow, d, phase, "second window clears")


if __name__ == "__main__":
    main()
