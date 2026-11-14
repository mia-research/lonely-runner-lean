"""Exact cutoff arithmetic and shifted harmonic replay for the fast sectors."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product
from math import gcd, isqrt, lcm, prod
from random import Random

from fast_dilation_check import dist
from mixed_harmonic_check import CAP, cover_states, uncovered_phase


FOUR_CAP = Q(51, 400)
TARGET = Q(1251, 10000)
CORES = ((1, 1, 1, 1), (1, 1, 1, 3), (1, 1, 2, 2))
LAYER_COUNTS = (1000, 1209, 1819, 2166, 2976, 3546, 4844, 5379)


def verify_constants():
    overlap_budget = 8 * FOUR_CAP - 1
    assert overlap_budget == Q(1, 50)
    assert Q(1, 28) > overlap_budget
    for a, b in ((1, 2), (1, 3), (2, 3)):
        lower_overlap = min(Q(a+b, 8) - Q(1, 3), Q(a, 4), Q(b, 4))/(a*b)
        assert lower_overlap >= Q(1, 48) > overlap_budget
    assert 2 * FOUR_CAP - 8 * (FOUR_CAP - Q(1, 8)) > overlap_budget
    assert 26 * (CAP - TARGET) > TARGET
    assert 6 * FOUR_CAP < 1

    for k, expected in ((5, (28, 177, 3222, 11269)),
                        (6, (44, 313, 7224, 43544))):
        squares = []
        for rank, cap in enumerate((Q(1, 2), Q(6, 25), Q(1, 7), CAP)):
            bound = (Q(k-rank-1, 2)/(cap-TARGET))**2 + Q(sum(squares), 4)
            squares.append(bound.numerator//bound.denominator)
        assert tuple(squares) == expected
        if k == 5:
            cutoff = isqrt(prod(squares))
            assert cutoff == 424200
            print("Five-slope cutoff:", cutoff, "at threshold", TARGET)
        print(k, "exact relation squared-length bounds:", squares)

    rows = [row for row in combinations_with_replacement(range(-5, 6), 5)
            if row[0] < 0 < row[-1] and sum(x*x for x in row) <= 28
            and gcd(*row) == 1 and row <= tuple(-x for x in reversed(row))]
    assert len(rows) == 195
    print("Five-reading first relation:", len(rows), "primitive types up to sign and permutation")

    for k, length, upper in ((5, Q(1, 160), 6*10**78), (6, Q(1, 80), 9*10**92)):
        modes = 8 * k * 60000**k
        frequency = 8 * 60000**k / length
        cutoff = 6 * modes**2 * frequency
        assert cutoff < upper
        tent_lower_bound = Q(1, 60000**k)
        assert 2 * (Q(k, modes) + 1/(length*frequency)) == tent_lower_bound/2
        print(k, "real fast cutoff for length", length, ":", cutoff)

    for slow_max in (1, 2):
        length, time_max = Q(3, 20*slow_max), Q(15, 8)
        pmax = 40**4
        separation, pairs = Q(1, 8*pmax**2), 16*pmax**2
        inner_length = length/2
        width_factor = inner_length + 4*time_max/separation
        margin = min(Q(1, 64*pmax), separation/40,
                     inner_length/(100*pairs*width_factor))
        assert 8*margin < Q(1, 4*pmax)
        assert 10*margin < separation/2
        assert pairs*20*margin*width_factor <= inner_length/5
        cutoff = max(2400/length, pmax*2/length, pmax*100/(2*margin*length))
        assert cutoff < 5*10**40*slow_max**2
        print("Four real fast cutoff with slow bound", slow_max, ":", cutoff)


def check_exact_slices():
    """Test exact rational witnesses on the plane that evades the old test."""
    rows = ((1, 0), (0, 1), (101, 2), (2, 3), (3, 4), (4, 5))
    assert all(not all(0 < abs(a*u+b*v) <= 5 for a, b in rows)
               for u, v in product(range(-5, 6), repeat=2))
    random = Random(841)
    for _ in range(128):
        shift = [Q(random.randrange(97), 97) for _ in rows]
        u = Q(1, 3) - shift[0]
        slopes = tuple(b for _, b in rows[1:])
        offsets = [(x+a*u)/b for x, (a,b) in zip(shift[1:], rows[1:])]
        for q in (1, 2, 5):
            v = uncovered_phase(slopes, offsets, q, CAP)
            if v is not None:
                assert all(dist(q*(x+a*u)+b*v) > CAP for x, (a,b) in zip(shift, rows))
                break
        else:
            raise AssertionError(shift)
    print("Verified 128 rational shifted-plane witnesses at", CAP)


def replay(profile):
    return profile, cover_states(profile, (1, 2), CAP)


def verify_four_cap(pool):
    # Every pair of a candidate must have a reduced maximum at most seven.
    assert 2*CAP*Q(2, 11) > 8*CAP - 1
    ratios = sorted({Q(a, b) for a in range(1, 8) for b in range(1, a+1)})
    profiles = []
    for a, b, c in combinations_with_replacement(ratios, 3):
        if max((b/a).numerator, (c/a).numerator, (c/b).numerator) <= 7:
            base = lcm(a.denominator, b.denominator, c.denominator)
            profile = tuple(int(base*ratio) for ratio in (1, a, b, c))
            assert gcd(*profile) == 1
            profiles.append(profile)
    assert len(set(profiles)) == len(profiles) == 313
    assert max(profile[-1] for profile in profiles) == 210
    for p, counts in pool.map(replay, profiles, chunksize=1):
        assert counts[-1] == 0, (p, counts)
    print("Uniform four-reading threshold", CAP, "verified on", len(profiles),
          "possible profiles through maximum 210", flush=True)


def verify_frontier(pool):
    profiles_total = one_dilation = four_gcd = append_core = 0
    for top, expected in zip(range(11, 19), LAYER_COUNTS):
        profiles = [(*prefix, top)
                    for prefix in combinations_with_replacement(range(1, top+1), 4)
                    if gcd(*prefix, top) == 1]
        assert len(profiles) == expected
        first_survivors = 0
        for p, counts in pool.map(replay, profiles, chunksize=2):
            assert counts[-1] == 0, (p, counts)
            if counts[0]:
                first_survivors += 1
                if any(gcd(*(p[:i]+p[i+1:])) > 1 for i in range(5)):
                    four_gcd += 1
                else:
                    assert p[:-1] in CORES, p
                    append_core += 1
        profiles_total += len(profiles)
        one_dilation += first_survivors
        print("Maximum", top, ":", len(profiles), "profiles,", first_survivors,
              "first-dilation survivors, zero two-dilation survivors", flush=True)
    assert (profiles_total, one_dilation, four_gcd, append_core) == (22939, 258, 234, 24)
    print("First-dilation survivors:", four_gcd, "with four-slope gcd and",
          append_core, "append-one profiles")


def verify_cores(pool):
    for core in CORES:
        assert cover_states(core, (1, 2), CAP)[-1] == 0
        profiles = [(*core, n) for n in range(11, 26*max(core))]
        for p, counts in pool.map(replay, profiles, chunksize=1):
            assert counts[-1] == 0, (p, counts)
        print("Append-one core", core, ":", len(profiles),
              "finite profiles checked through maximum", profiles[-1][-1], flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--constants-only", action="store_true")
    parser.add_argument("--four-only", action="store_true")
    args = parser.parse_args()
    verify_constants()
    check_exact_slices()
    if not args.constants_only:
        with ProcessPoolExecutor(args.workers) as pool:
            verify_four_cap(pool)
            if not args.four_only:
                verify_frontier(pool)
                verify_cores(pool)
