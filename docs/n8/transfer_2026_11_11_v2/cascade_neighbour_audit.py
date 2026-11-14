"""Exact replay of the forward radius and forced-opening rules."""
from collections import Counter
from fractions import Fraction
from itertools import accumulate
from math import floor

from cascade_anchor_audit import cascade, in_way

RADIUS = Fraction(1, 8)


def lap_bounds(readings, time, radius):
    laps = {rate: floor(rate * time) for rate in readings}
    openings = {rate: (lap + radius) / rate for rate, lap in laps.items()}
    closings = {rate: (lap + 1 - radius) / rate for rate, lap in laps.items()}
    return laps, openings, closings


def forward_radius(readings, time):
    laps = {rate: floor(rate * time) for rate in readings}
    pair_limit = min(
        Fraction(d * (laps[e] + 1) - e * laps[d], d + e)
        for d in readings for e in readings
    )
    start_limit = min(laps[d] + 1 - d * time for d in readings)
    return min(pair_limit, start_limit)


def neighbour_replay(readings):
    time = RADIUS / min(readings)
    counts = Counter()
    for _ in range(4000):
        laps, openings, closings = lap_bounds(readings, time, RADIUS)
        candidate = max(time, max(openings.values()))
        earliest_close = min(closings.values())
        maximum = forward_radius(readings, time)
        assert (maximum >= RADIUS) == (candidate <= earliest_close)

        # The formula gives an attained endpoint and rules out any increase.
        _, at_max_open, at_max_close = lap_bounds(readings, time, maximum)
        assert max(time, max(at_max_open.values())) == min(at_max_close.values())

        if candidate <= earliest_close:
            assert all(not in_way(rate, candidate) for rate in readings)
            counts["singleton forward cell"] += candidate == earliest_close
            return candidate, counts

        rejected = [rate for rate in readings if closings[rate] < candidate]
        counts["forced jumps"] += 1
        counts["advances a currently clear reading"] += any(
            not in_way(rate, time) for rate in rejected
        )
        counts["tied earliest closing"] += (
            sum(close == earliest_close for close in closings.values()) > 1
        )
        assert all(
            closings[rate] < time or any(opening > closings[rate] for opening in openings.values())
            for rate in rejected
        )
        time = max((laps[rate] + 1 + RADIUS) / rate for rate in rejected)
    raise AssertionError(("neighbour replay exceeded cap", readings, time))


def main():
    seeds = [
        (1, 2, 3, 4, 5, 6, 7),
        (1, 2, 3, 4, 5, 7, 12),
        (1, 4, 5, 6, 7, 11, 13),
        (2, 3, 4, 5, 6, 7, 16),
        (1, 2, 32, 33, 34, 35, 61),
        (49, 205, 234, 256, 286, 323, 366),
        (1, 2, 3, 4, 7, 8, 15),
        (1, 2, 3, 4, 5, 6, 13),
    ]
    totals = Counter()
    for readings in seeds:
        expected, raw = cascade(readings)
        actual, counts = neighbour_replay(readings)
        assert expected == actual
        print(readings, len(raw), counts["forced jumps"], actual, dict(counts))

        gaps = tuple(b - a for a, b in zip((0,) + readings, readings))
        samples = [
            readings,
            tuple(accumulate(reversed(gaps))),
            tuple(accumulate(gaps[1:] + gaps[:1])),
        ]
        samples.extend(
            tuple(sorted(readings[:i] + (rate + delta,) + readings[i + 1:]))
            for i, rate in enumerate(readings)
            for delta in (Fraction(-1, 17), Fraction(1, 17), Fraction(1, 2))
        )
        for sample in samples:
            expected, _ = cascade(sample)
            actual, counts = neighbour_replay(sample)
            assert expected == actual
            totals.update(counts)
            totals["profiles"] += 1

    readings = seeds[-1]
    start = Fraction(1, 8)
    phases = {rate: (rate * start) % 1 for rate in readings}
    _, _, closings = lap_bounds(readings, start, RADIUS)
    assert max(phases, key=phases.get) == 6
    assert min(closings, key=closings.get) == 13
    print(dict(totals))


if __name__ == "__main__":
    main()
