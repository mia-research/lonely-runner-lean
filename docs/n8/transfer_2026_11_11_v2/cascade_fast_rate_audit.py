"""Exact coverage of every faster rate for fixed rational slow cores."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from math import floor
from random import Random

from cascade_rejection_audit import R, clear_cells, incompatible, phase_sweep, rejects


def rate_bands(cells, start, cap):
    for (a, b), (c, e) in combinations(cells, 2):
        for j in range(floor(cap * (e - a) - 2 * R) + 1):
            lower = max(start, (j + 2 * R) / (e - a))
            upper = min(cap, (j + 1 - 2 * R) / (c - b))
            if lower <= upper:
                yield lower, upper, j


def uncovered_rate(start, cap, bands):
    right = start
    for lower, upper, _ in sorted(bands):
        if lower > right:
            return (lower + right) / 2
        right = max(right, upper)
        if right >= cap:
            return None
    return (cap + right) / 2 if right < cap else None


def baseline_cores():
    rng = Random(8)
    grid = [Q(i, 16) for i in range(17, 257)]
    yield from ((1, *tail) for tail in combinations(range(2, 13), 5))
    yield from ((1, *sorted(rng.sample(grid, 5))) for _ in range(500))


def stress_cores():
    rng = Random(8321)
    yield from ((1, *tail) for tail in combinations(range(2, 18), 5))
    seeds = (
        (1, 2, 5, 6, 7, 8), (1, 3, 4, 5, 7, 11), (1, 4, 5, 6, 7, 11),
        (1, 4, 6, 7, 10, 11), (1, 5, 6, 7, 8, 11),
        (1, Q(4, 3), Q(10, 3), Q(17, 4), Q(19, 4), Q(16, 3)),
    )
    for core in seeds:
        for step in (Q(1, 128), Q(1, 16), Q(1, 8)):
            for _ in range(250):
                yield (1, *sorted(max(1, q + step * rng.randint(-3, 3)) for q in core[1:]))


def near_hardest_cores():
    rng = Random(12811)
    core = (1, Q(381, 128), Q(509, 128), Q(639, 128), Q(7), Q(11))
    yield core
    for step in (Q(1, 1024), Q(1, 256), Q(1, 64)):
        for _ in range(600):
            yield (1, *sorted(q + step * rng.randint(-4, 4) for q in core[1:]))


def hydro_cores():
    rng = Random(4188)
    seeds = (
        (1, 2, 5, 6, 7, 8), (1, 3, 4, 5, 7, 11), (1, 4, 5, 6, 7, 11),
        (1, 4, 6, 7, 10, 11), (1, 5, 6, 7, 8, 11), (1, 3, 4, 5, 7, 12),
    )
    for core in seeds:
        for den in (16, 64, 256):
            for _ in range(180):
                yield (1, *sorted(q + Q(rng.randint(-6, 6), den) for q in core[1:]))
    grid = [Q(i, 8) for i in range(9, 257)]
    yield from ((1, *sorted(rng.sample(grid, 5))) for _ in range(1200))


def cluster_hands_off(cells, rate, width):
    start, end = cells[0]
    for a, b in cells[1:]:
        if a - end > 3 * width:
            start = a
        end = b
        if rate * (end - start) >= 2 * R:
            return True
    return False


def audit(cores):
    counts = Counter()
    minimum_gap_bounds = Counter()
    actual_phase = Counter()
    first_obstruction = None
    for core in dict.fromkeys(cores):
        cells = clear_cells(core)
        width = max((b - a for a, b in cells), default=Q(0))
        if not width:
            counts["no positive-width cell"] += 1
            continue
        start, cap = max(core), 1 / (4 * width)
        if start >= cap:
            counts["wide at every rate"] += 1
            continue
        if any(start * (e - a) >= 2 * R and c - b <= 3 * width
               for (a, b), (c, e) in combinations(cells, 2)):
            counts["one zero-gap pair and width"] += 1
            continue
        if cluster_hands_off(cells, start, width):
            counts["longer cluster and width"] += 1
            continue
        bands = list(rate_bands(cells, start, cap))
        d = uncovered_rate(start, cap, bands)
        if d is None:
            max_gap = next(j for j in sorted({j for _, _, j in bands})
                           if uncovered_rate(start, cap, [b for b in bands if b[2] <= j]) is None)
            minimum_gap_bounds[max_gap] += 1
            if max_gap > 5:
                short = [b for b in bands if b[2] <= 5]
                a, b = Q(6, 37), Q(1, 6)
                if any(left <= a <= b <= right for left, right in cells):
                    lower = max(start, (3 + R) / b)
                    upper = min(cap, (4 - R) / a)
                    if lower <= upper:
                        short.append((lower, upper, 0))
                key = "shared slow cell" if uncovered_rate(start, cap, short) is None else "unresolved"
                actual_phase[key] += 1
            counts["chain of zero-gap pairs" if max_gap == 0 else "other integer gaps"] += 1
            continue
        theta = next(th for th in phase_sweep(d, cells)
                     if all(rejects(d, cell, th) for cell in cells))
        counts["shifted obstruction"] += 1
        if first_obstruction is None:
            first_obstruction = (core, d, theta)
    return dict(sorted(counts.items())), dict(sorted(minimum_gap_bounds.items())), dict(actual_phase), first_obstruction


def replay_stress_time_bank():
    times = (Q(5, 31), Q(7, 15), Q(1, 8), Q(9, 29), Q(8, 15), Q(7, 8),
             Q(3, 14), Q(11, 16), Q(15, 32), Q(9, 20), Q(5, 14))
    resolved = 0
    for core in dict.fromkeys(stress_cores()):
        cells = clear_cells(core)
        width = max(b - a for a, b in cells)
        start, cap = max(core), 1 / (4 * width)
        if start >= cap:
            continue
        bands = [band for band in rate_bands(cells, start, cap) if band[2] == 0]
        if uncovered_rate(start, cap, bands) is None:
            continue
        for t in times:
            if not any(a <= t <= b for a, b in cells):
                continue
            for lap in range(floor(start * t), floor(cap * t) + 1):
                lo = max(start, (lap + R) / t)
                hi = min(cap, (lap + 1 - R) / t)
                if lo <= hi:
                    bands.append((lo, hi, 0))
        assert uncovered_rate(start, cap, bands) is None, core
        resolved += 1
    return resolved


def main():
    print("Stress cores resolved by zero-gap pairs and the phase-zero time bank",
          replay_stress_time_bank(), flush=True)
    cells = clear_cells((1, 4, 6, 7, 10, 11))
    rate = Q(49, 4)
    assert len(cells) == 20
    assert all(not incompatible(rate, a, b) for a, b in zip(cells, cells[1:]))
    early, later = (Q(1, 8),) * 2, (Q(5, 16),) * 2
    assert early in cells and later in cells and incompatible(rate, early, later)
    batches = (("baseline", baseline_cores()), ("stress", stress_cores()),
               ("near hardest", near_hardest_cores()), ("Hydro", hydro_cores()))
    for label, cores in batches:
        counts, bounds, actual_phase, obstruction = audit(cores)
        print(label, sum(counts.values()), counts, flush=True)
        print("Minimum sufficient maximum integer gap among the residual cores", bounds, flush=True)
        if actual_phase:
            print("Actual phase closes the remaining rates after gaps through 5", actual_phase, flush=True)
        if obstruction is not None:
            print("First exact shifted obstruction", obstruction, flush=True)


if __name__ == "__main__":
    main()
