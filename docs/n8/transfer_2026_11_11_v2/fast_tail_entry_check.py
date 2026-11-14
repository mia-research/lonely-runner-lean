"""Exact controls for the four-fast tail argument. Uses only rational arithmetic."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, gcd


def overlap_possible(p, q, phase_difference):
    """Check simultaneous bad phases for an affine circle at a fixed time."""
    first = [(Q(j, p)-Q(1, 8*p), Q(j, p)+Q(1, 8*p)) for j in range(p+1)]
    second = [((j-phase_difference-Q(1, 8))/q, (j-phase_difference+Q(1, 8))/q)
              for j in range(q+2)]
    return any(max(a, c, 0) < min(b, d, 1) for a,b in first for c,d in second)


def check_overlap_projection():
    count = 0
    for p in range(1, 7):
        for q in range(1, 7):
            d = gcd(p, q)
            for k in range(48):
                shift = Q(k, 48)
                residue = ((p//d)*shift) % 1
                distance = min(residue, 1-residue)
                projected = distance < Q((p+q)//d, 8)
                assert overlap_possible(p, q, shift) == projected
                count += 1
    print("Exact two-reading overlap checks:", count)


def tile_classes(q, fast_count):
    """Enumerate placements of 1/4 arcs and q equally spaced 1/(4q) arcs."""
    size = 4*q
    for offsets in combinations(range(4), fast_count):
        taken = {offset+4*j for offset in offsets for j in range(q)}
        free = set(range(size))-taken
        for starts in combinations(range(size), 4-fast_count):
            arcs = [{(a+i) % size for i in range(q)} for a in starts]
            if set().union(*arcs) == free:
                yield offsets, starts


def check_tiling_types():
    expected = {(1, 1, 1, 1), (1, 1, 2, 2), (1, 1, 1, 3)}
    types = {(1, 1, 1, 1)}
    for q in (2, 3):
        for n in (1, 2, 3):
            if next(tile_classes(q, n), None) is not None:
                types.add((1,)*(4-n)+(q,)*n)
    assert types == expected
    print("Instantaneous tiling slope types:", sorted(types))


def distance(phase):
    residue = phase % 1
    return min(residue, 1-residue)


def check_fast_controls():
    drifts = [Q(i, 4) for i in range(4)]
    # At t=1 the closed bad arcs tile. Just below it the wrap gap opens.
    assert all(min(distance(Q(j, 800)+b) for b in drifts) <= Q(1, 8)
               for j in range(800))
    t0 = Q(99, 100)
    theta = Q(1, 2)-3*t0/8
    assert all(distance(theta+b*t0) > Q(1, 8) for b in drifts)
    for base in (10**3, 10**6, 10**12):
        # Align the fast phase to theta within one half period of t0.
        t = (round(base*t0-theta)+theta)/base
        assert Q(19, 20) <= t <= Q(21, 20)
        assert all(distance((base+b)*t) > Q(1, 8) for b in drifts)
    print("Four almost-tiling readings: exact strict witnesses at three scales.")

    # Five equal leading slopes cover the full time interval for every base.
    # For any t in this interval, the largest gap between consecutive centers
    # is at most the maximum of these two endpoint values.
    a, b = Q(19, 20), Q(21, 20)
    maximum_center_gap = max(b/5, 1-4*a/5)
    assert maximum_center_gap == Q(6, 25) < Q(1, 4)
    print("Five-fast open cover: maximum center gap", maximum_center_gap)

    # One duplicated center and three singleton centers form an exact tiling
    # at t=1. Two singleton centers move apart immediately after t=1.
    drifts = [Q(0), Q(1), Q(1, 4), Q(1, 2), Q(3, 4)]
    assert sorted({d % 1 for d in drifts}) == [Q(i, 4) for i in range(4)]
    t0 = Q(101, 100)
    theta = 1-3*t0/8
    assert all(distance(theta+b*t0) > Q(1, 8) for b in drifts)
    for base in (10**3, 10**6, 10**12):
        t = (round(base*t0-theta)+theta)/base
        assert Q(19, 20) <= t <= Q(21, 20)
        assert all(distance((base+b)*t) > Q(1, 8) for b in drifts)
    print("Five-fast collision control: exact strict witnesses at three scales.")


def main():
    constant = Q(comb(80, 40), 4**40)**2
    bad_bound = Q(6, 7)**40
    assert Q(1, 300)+Q(4, 2400) == Q(1, 200) < constant-bad_bound
    assert Q(10, 7)**2 > 2  # (2 + sqrt(2))/4 < 6/7.
    print("Exact Fourier bounds verified: degree 40, 2400 and 100.")
    check_overlap_projection()
    check_tiling_types()
    check_fast_controls()


if __name__ == "__main__":
    main()
