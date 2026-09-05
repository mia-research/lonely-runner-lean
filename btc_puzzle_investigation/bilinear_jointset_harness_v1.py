#!/usr/bin/env python3
"""
bilinear_jointset_harness_v1.py

Scoped bilinear / joint-set probe after the F/A/D/G single-point cluster.

This records several all-pairs statistics for 82-key sets:
  - pairwise-difference distinct x ratio
  - cubic moment Sum eis(x(P_i-P_j))^3
  - epsilon profile of pairwise differences
  - norm-band profile of pairwise differences

Controls:
  - the real 82 solved pubkeys
  - exact-bit random scalar subsets with the same bit lengths as the real 82
  - 36k constructed known-generator subsets, bucket-matched to the real bit lengths
  - 36k constructed global subsets
  - random curve-point subsets
  - a planted arithmetic progression power row

Everything in the curve/lift/statistic path is exact integer arithmetic. Rank reports
are exact counts against matched null samples. This is a probe, not a closure theorem.
"""

import csv
import os
import random
from collections import defaultdict
from fractions import Fraction

import numpy as np

from ecc_secp256k1 import P as SECP_P, N_ORDER, scalar_mul
from int1_frame_operator_v1 import build_secp


HERE = os.path.dirname(os.path.abspath(__file__))


def emul(z, w):
    a, b = z
    c, d = w
    return (a * c - b * d, a * d + b * c - b * d)


def ecube(z):
    return emul(emul(z, z), z)


def enorm(z):
    a, b = z
    return a * a - a * b + b * b


def add_affine(A, B):
    if A is None:
        return B
    if B is None:
        return A
    x1, y1 = A
    x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % SECP_P == 0:
            return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, SECP_P) % SECP_P
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, SECP_P) % SECP_P
    x3 = (lam * lam - x1 - x2) % SECP_P
    y3 = (lam * (x1 - x3) - y1) % SECP_P
    return x3, y3


def neg_affine(A):
    return (A[0], (-A[1]) % SECP_P)


def bucket_for_bits(bits):
    if bits <= 16:
        return 16
    return ((bits + 15) // 16) * 16


def load_real_82():
    points = []
    bits = []
    buckets = []
    with open(os.path.join(HERE, "puzzles_verified.csv"), newline="") as f:
        for row in csv.DictReader(f):
            points.append((int(row["X"], 16), int(row["Y"], 16)))
            bit_count = int(row["bits"])
            bits.append(bit_count)
            buckets.append(bucket_for_bits(bit_count))
    return points, bits, buckets


def load_constructed_36k():
    path = os.path.join(HERE, "constructed_keys_fullrange_v1.npz")
    z = np.load(path, allow_pickle=True)
    by_bucket = defaultdict(list)
    all_points = []
    for n_bits, x, y in zip(z["N"], z["X"], z["Y"]):
        point = (int(x), int(y))
        by_bucket[int(n_bits)].append(point)
        all_points.append(point)
    return by_bucket, all_points


def sample_bucket_matched(by_bucket, buckets, rng):
    bucket_counts = defaultdict(int)
    for bucket in buckets:
        bucket_counts[bucket] += 1
    points = []
    for bucket, count in bucket_counts.items():
        points.extend(rng.sample(by_bucket[bucket], count))
    rng.shuffle(points)
    return points


def sample_global(all_points, size, rng):
    return rng.sample(all_points, size)


def sample_exact_bits(bits, rng):
    points = []
    for bit_count in bits:
        lo = 1 << (bit_count - 1)
        hi = 1 << bit_count
        points.append(scalar_mul(rng.randrange(lo, hi)))
    return points


def sample_random_curve(size, rng):
    return [scalar_mul(rng.randrange(1, N_ORDER)) for _ in range(size)]


def sample_ap(size, rng):
    d0 = rng.randrange(1, N_ORDER)
    delta = rng.randrange(1, 1 << 40)
    return [scalar_mul((d0 + i * delta) % N_ORDER) for i in range(size)]


def pairwise_stats(points, eis, eps):
    distinct_x = set()
    pair_count = 0
    cube_sum = [0, 0]
    eps_counts = [0, 0, 0]
    norm_counts = [0, 0, 0]
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            diff = add_affine(points[i], neg_affine(points[j]))
            if diff is None:
                continue
            pair_count += 1
            x = diff[0]
            distinct_x.add(x)
            z = eis(x)
            cube = ecube(z)
            cube_sum[0] += cube[0]
            cube_sum[1] += cube[1]
            e = eps(x)
            eps_counts[e if e in (0, 1) else 2] += 1
            nrm = enorm(z)
            if 16 * nrm < 3 * SECP_P:
                norm_counts[0] += 1
            elif 4 * nrm <= SECP_P:
                norm_counts[1] += 1
            else:
                norm_counts[2] += 1
    cube_norm = enorm(tuple(cube_sum))
    return {
        "pairs": pair_count,
        "distinct_ratio": Fraction(len(distinct_x), pair_count),
        "cube_norm": cube_norm,
        "eps_core": eps_counts[0],
        "eps_flap": eps_counts[1],
        "eps_other": eps_counts[2],
        "norm_low": norm_counts[0],
        "norm_mid": norm_counts[1],
        "norm_high": norm_counts[2],
    }


def fmt_fraction(frac, places=4):
    sign = "-" if frac < 0 else ""
    frac = abs(frac)
    scale = 10 ** places
    q = frac.numerator * scale // frac.denominator
    whole = q // scale
    part = q % scale
    return f"{sign}{whole}.{part:0{places}d}"


def fmt_value(label, value):
    if isinstance(value, Fraction):
        return fmt_fraction(value)
    if label == "cube_norm":
        return f"{value.bit_length()}b"
    return str(value)


def rank_line(label, obs, nulls):
    ordered = sorted(nulls)
    mid = ordered[len(ordered) // 2]
    le = sum(1 for value in nulls if value <= obs)
    ge = sum(1 for value in nulls if value >= obs)
    print(
        f"    {label:15s} obs={fmt_value(label, obs):>10s}  "
        f"null[min/med/max]={fmt_value(label, ordered[0])}/{fmt_value(label, mid)}/{fmt_value(label, ordered[-1])}  "
        f"rank<= {le}/{len(nulls)}  rank>= {ge}/{len(nulls)}"
    )


def report_against_null(name, obs_stats, null_stats):
    print(f"\n{name}")
    for key in (
        "distinct_ratio",
        "cube_norm",
        "eps_core",
        "eps_flap",
        "norm_low",
        "norm_mid",
        "norm_high",
    ):
        rank_line(key, obs_stats[key], [stats[key] for stats in null_stats])


def make_nulls(label, sampler, reps, eis, eps):
    out = []
    for r in range(reps):
        out.append(pairwise_stats(sampler(), eis, eps))
        if (r + 1) % 25 == 0:
            print(f"  built {label} null {r + 1}/{reps}")
    return out


def main():
    rng = random.Random(20260715)
    eis, eps = build_secp()
    real_points, real_bits, real_buckets = load_real_82()
    by_bucket, all_constructed = load_constructed_36k()
    size = len(real_points)
    reps_constructed = 120
    reps_exact_bits = 120
    reps_random = 60

    print("=" * 74)
    print("BILINEAR JOINT-SET HARNESS v1")
    print("=" * 74)
    print(f"  real set size={size}; pairs={size * (size - 1) // 2}")
    print("  exact-bit random reference: same bit lengths as the real 82.")
    print("  36k reference: bucket-matched by ceil(bits/16)*16; exact-bucket, not exact-bit.")
    print("  Verdicts are rank positions for these probes only, not closure claims.")

    real_stats = pairwise_stats(real_points, eis, eps)
    control_exact = pairwise_stats(sample_exact_bits(real_bits, rng), eis, eps)
    control_36k = pairwise_stats(sample_bucket_matched(by_bucket, real_buckets, rng), eis, eps)
    ap_stats = pairwise_stats(sample_ap(size, rng), eis, eps)

    exact_bit_nulls = make_nulls(
        "exact-bit random",
        lambda: sample_exact_bits(real_bits, rng),
        reps_exact_bits,
        eis,
        eps,
    )
    bucket_nulls = make_nulls(
        "36k bucket-matched",
        lambda: sample_bucket_matched(by_bucket, real_buckets, rng),
        reps_constructed,
        eis,
        eps,
    )
    global_nulls = make_nulls(
        "36k global",
        lambda: sample_global(all_constructed, size, rng),
        reps_constructed,
        eis,
        eps,
    )
    random_nulls = make_nulls(
        "random curve",
        lambda: sample_random_curve(size, rng),
        reps_random,
        eis,
        eps,
    )

    report_against_null("REAL 82 vs exact-bit random null", real_stats, exact_bit_nulls)
    report_against_null("REAL 82 vs 36k bucket-matched null", real_stats, bucket_nulls)
    report_against_null("REAL 82 vs 36k global null", real_stats, global_nulls)
    report_against_null("REAL 82 vs random curve null", real_stats, random_nulls)
    report_against_null("CONTROL exact-bit sample vs exact-bit null", control_exact, exact_bit_nulls)
    report_against_null("CONTROL 36k bucket sample vs 36k bucket null", control_36k, bucket_nulls)
    report_against_null("POWER ROW: planted AP vs 36k bucket null", ap_stats, bucket_nulls)

    print("\nReading:")
    print("  - distinct_ratio low rank detects AP-like pairwise collapse.")
    print("  - cubic/epsilon/norm ranks are scoped joint-set readouts of pairwise differences.")
    print("  - A rank edge is a follow-up target; a bulk rank is only a scoped null for this probe.")


if __name__ == "__main__":
    main()
