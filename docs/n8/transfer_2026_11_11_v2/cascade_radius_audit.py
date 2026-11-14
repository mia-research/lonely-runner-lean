"""Exact boundary checks for initial-lap radius and the AP outlier."""
from fractions import Fraction as Q

from cascade_anchor_audit import cascade, in_way


def predicted_landing(x):
    if x == 7 or x >= 9:
        return Q(1, 8)
    if x >= Q(54, 7):
        return 9 / (8 * x)
    if x >= Q(68, 9):
        return Q(9, 32)
    if x >= Q(51, 7):
        return 17 / (8 * x)
    return Q(3, 8)


def main():
    boundaries = (Q(7), Q(51, 7), Q(68, 9), Q(54, 7), Q(9), Q(15))
    offsets = (Q(-1, 4096), Q(-1, 97), Q(0), Q(1, 97), Q(1, 4096))
    probes = {x + e for x in boundaries for e in offsets if 7 <= x + e <= 15}
    probes |= {(a + b) / 2 for a, b in zip(boundaries, boundaries[1:])}
    for scale in (Q(1), Q(5, 7), Q(37)):
        for x in probes:
            readings = tuple(scale * d for d in (1, 2, 3, 4, 5, 6, x))
            assert cascade(readings)[0] == predicted_landing(x) / scale

    first_cells = 0
    for m in (Q(1), Q(2, 3), Q(5, 2)):
        for ratio in (Q(3), Q(49, 9), Q(6), Q(20, 3), Q(7)):
            slow_max = m * ratio
            slow = tuple(m + (slow_max - m) * Q(j, 5) ** 2 for j in range(6))
            left, right = 1 / (8 * m), 7 / (8 * slow_max)
            values = {Q(7) + Q(1, 10_000), Q(8), Q(9) - Q(1, 10_000)}
            values |= {9 * ratio / 7 + offset for offset in offsets}
            for relative_rate in sorted(v for v in values if 7 < v < 9):
                fastest = m * relative_rate
                landing, _ = cascade(slow + (fastest,))
                accepts = 9 * slow_max <= 7 * fastest
                assert accepts == (landing <= right)
                if accepts:
                    assert landing == 9 / (8 * fastest)
                    assert left <= landing and all(not in_way(d, landing) for d in slow)
                first_cells += 1
    multiple = 0
    for x in (Q(71, 10), Q(8), Q(89, 10)):
        probe_edges = (7 * x / 9, x, 5 * x / 3, 17 * x / 9)
        for edge in probe_edges:
            for offset in offsets:
                d = edge + offset
                if not 6 < d <= 15 or d == x or 7 < d < x:
                    continue
                readings = tuple(sorted((Q(1), Q(2), Q(3), Q(4), Q(5), x, d)))
                candidate = 9 / (8 * x)
                accepts = all(
                    9 * rate <= 7 * x
                    or x <= rate and 3 * rate <= 5 * x
                    or 17 * x <= 9 * rate
                    for rate in readings
                )
                assert (cascade(readings)[0] == candidate) == accepts
                multiple += 1
    print(f"{multiple} multiple-reading rollover band checks")
    print(f"{3 * len(probes)} scaled AP-outlier boundary checks")
    print(f"{first_cells} general first-rollover checks")
    for x in boundaries:
        print(f"x={x}: t={predicted_landing(x)}")


if __name__ == "__main__":
    main()
