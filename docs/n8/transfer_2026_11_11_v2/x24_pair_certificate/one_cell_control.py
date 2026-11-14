"""An exact X24 profile for which no single slow cell works uniformly."""
from fractions import Fraction as Q


def intersect(left, right):
    return max(left[0], right[0]), min(left[1], right[1])


def slow_cells(speeds):
    cells = [(Q(1), Q(7)), (Q(9), Q(15))]
    for speed in speeds:
        gaps = [(Q(8*j+1, speed), Q(8*j+7, speed)) for j in range(47)]
        cells = [cell for a in cells for b in gaps
                 if (cell := intersect(a, b))[0] <= cell[1]]
    return cells


def blockers(cell):
    L, U = cell
    return [(a, b) for j in range(1, 48)
            if max(23, (a := (8*j-1)/L)) < min(25, (b := (8*j+1)/U))]


def main():
    cells = slow_cells((19, 20, 21, 22, 23))
    assert len(cells) == 44
    assert all(blockers(cell) for cell in cells)
    first = (Q(25, 19), Q(31, 23))
    second = (Q(49, 22), Q(47, 21))
    assert first in cells and second in cells
    assert blockers(first) == [(Q(589, 25), Q(759, 31))]
    assert blockers(second) == [(Q(1210, 49), Q(1197, 47))]
    assert Q(759, 31) < Q(1210, 49)
    print("44 maximal slow cells each have a blocker in [23,25]")
    print("cells", *map(str, first), "and", *map(str, second), "have disjoint blockers")


if __name__ == "__main__":
    main()
