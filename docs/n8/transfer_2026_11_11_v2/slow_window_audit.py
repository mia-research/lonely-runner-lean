"""Exact lap intersections for the five- and six-slow window audit."""

from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import floor
from random import Random


W0 = (F(1, 8), F(7, 8))
W1 = (F(9, 8), F(15, 8))


def clear_intervals(rates, window, clearance=F(1, 8)):
    """Intersect the open clear intervals of all readings beyond the pinned one."""
    intervals = [window]
    for rate in rates[1:]:
        intersection = []
        for lo, hi in intervals:
            for lap in range(floor(lo * rate), floor(hi * rate) + 1):
                left = max(lo, (lap + clearance) / rate)
                right = min(hi, (lap + 1 - clearance) / rate)
                if left < right:
                    intersection.append((left, right))
        intervals = intersection
        if not intervals:
            break
    return intervals


def widest(intervals):
    return max((hi - lo for lo, hi in intervals), default=F(0))


def report(label, samples):
    missing_first = missing_both = count = 0
    minimum = example = None
    for rates in samples:
        first = widest(clear_intervals(rates, W0))
        second = widest(clear_intervals(rates, W1))
        best = max(first, second)
        count += 1
        missing_first += first == 0
        missing_both += best == 0
        if minimum is None or best < minimum:
            minimum, example = best, rates
    print(
        f"{label}: {count} tuples, {missing_first} missing W0, "
        f"{missing_both} missing both, minimum best width {minimum} at "
        f"{tuple(map(str, example))}",
        flush=True,
    )


def main():
    for n in (5, 6):
        grid = [F(i, 2) for i in range(2, 25)]
        report(
            f"{n} readings on the half grid from 1 to 12, with repeats",
            ((F(1), *tail) for tail in combinations_with_replacement(grid, n - 1)),
        )
        rng = Random(81415 + n)
        report(
            f"{n} readings, stratified rational sample",
            (
                (F(1), *sorted(F(rng.randint(1, d * cap), d) + 1 for _ in range(n - 1)))
                for cap in (2, 6, 12, 31, 63)
                for d in (7, 31, 127, 509)
                for _ in range(250)
            ),
        )

    e358 = tuple(map(F, ("1", "6559/2279", "26236/6779", "231/47", "26236/4115", "7")))
    assert not clear_intervals(e358, (F(1, 7), F(6, 7)), F(1, 7))
    assert (F(37035, 209888), F(47, 264)) in clear_intervals(e358, W0)
    print("E358 has a strict W0 interval at 1/8 and none at 1/7.")

    rates = tuple(map(F, ("1", "5/3", "33/7", "41/7", "7")))
    for window, expected, interval in (
        (W0, F(37402, 47355), (F(41, 56), F(217, 264))),
        (W1, F(13613, 15785), (F(89, 56), F(147, 88))),
    ):
        length = window[1] - window[0]
        loss = sum(
            length - sum(hi - lo for lo, hi in clear_intervals((F(1), rate), window))
            for rate in rates[1:]
        )
        assert loss == expected > length
        assert interval in clear_intervals(rates, window)
        print(f"{window}: sum of individual bad lengths {loss}, clear interval {interval}")


if __name__ == "__main__":
    main()
