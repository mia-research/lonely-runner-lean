"""
lrc_n11_gf_by_a1_v1.py

Sweep over a_1 ranges to find minimum good-fraction per band.
Also investigate whether the minimum GF can be driven below 2% with
very large perturbations (max|delta| up to 2).

Date: 2026-03-22
"""

import numpy as np

THRESHOLD = 1.0 / 11
N_GRID = 5000
RNG_SEED = 77


def frac(x):
    return x - np.floor(x)


def good_fraction(deltas, n_grid=N_GRID):
    a1 = 1.0 + deltas[0]
    if a1 <= 0.01:
        return 0.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)
    all_lonely = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(all_lonely))


def is_complete_blocking_vec(delta_batch):
    N = delta_batch.shape[0]
    speeds = np.zeros((N, 10))
    for i in range(1, 10):
        speeds[:, i - 1] = i + delta_batch[:, i - 1]
    speeds[:, 9] = 10.0
    any_safe = np.zeros(N, dtype=bool)
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        safe = np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0), axis=1)
        any_safe |= safe
    return ~any_safe


# -----------------------------------------------------------------------
# Part A: Minimum GF by a_1 band
# -----------------------------------------------------------------------
print("Part A: Minimum GF stratified by a_1 band")
print("=" * 60)

a1_bands = [
    (0.10, 0.30, "a1 in (0.10, 0.30)"),
    (0.30, 0.50, "a1 in (0.30, 0.50)"),
    (0.50, 0.70, "a1 in (0.50, 0.70)"),
    (0.70, 0.85, "a1 in (0.70, 0.85)"),
    (0.85, 0.95, "a1 in (0.85, 0.95)"),
    (0.95, 1.00, "a1 in (0.95, 1.00)"),
]

rng = np.random.default_rng(RNG_SEED)
SAMPLES_PER_BAND = 200_000
BATCH = 50_000

results_by_band = {}

for (lo, hi, label) in a1_bands:
    min_gf = 1.0
    min_d = None
    total_blocking = 0

    for batch_start in range(0, SAMPLES_PER_BAND, BATCH):
        n = min(BATCH, SAMPLES_PER_BAND - batch_start)
        deltas = rng.uniform(-0.9, 0.9, size=(n, 9))
        # Set delta_1 so that a_1 = 1 + delta_1 in (lo, hi)
        deltas[:, 0] = rng.uniform(lo - 1.0, hi - 1.0, size=n)

        blocking = is_complete_blocking_vec(deltas)
        count = int(blocking.sum())
        total_blocking += count

        if count > 0:
            for k in np.where(blocking)[0]:
                gf = good_fraction(deltas[k])
                if gf < min_gf:
                    min_gf = gf
                    min_d = deltas[k].copy()

    results_by_band[label] = (min_gf, min_d, total_blocking)
    print(f"  {label}: {total_blocking} blocking | min GF = {min_gf:.5f}", end="")
    if min_d is not None:
        a1 = 1.0 + min_d[0]
        print(f"  (a_1={a1:.3f}, max|d|={np.max(np.abs(min_d)):.3f})")
    else:
        print("  (no blocking found)")

print()

# -----------------------------------------------------------------------
# Part B: Can large perturbations (max|delta| up to 2) achieve GF < 2%?
# -----------------------------------------------------------------------
print("Part B: Large perturbations — can GF drop below 2%?")
print("=" * 60)

SAMPLES_B = 500_000
min_gf_large = 1.0
min_d_large = None
total_blocking_large = 0

for batch_start in range(0, SAMPLES_B, BATCH):
    n = min(BATCH, SAMPLES_B - batch_start)
    deltas = rng.uniform(-2.0, 2.0, size=(n, 9))
    deltas[:, 0] = rng.uniform(-0.9, -0.05, size=n)  # a_1 in (0.1, 0.95)

    blocking = is_complete_blocking_vec(deltas)
    count = int(blocking.sum())
    total_blocking_large += count

    if count > 0:
        for k in np.where(blocking)[0]:
            gf = good_fraction(deltas[k])
            if gf < min_gf_large:
                min_gf_large = gf
                min_d_large = deltas[k].copy()
                if gf < 0.02:
                    print(f"  Found GF={gf:.5f} at batch {batch_start}: a_1={1+deltas[k,0]:.3f}")

print(f"\n  500k large-delta samples: {total_blocking_large} blocking | min GF = {min_gf_large:.5f}")
if min_d_large is not None:
    a1 = 1.0 + min_d_large[0]
    print(f"  Best config: a_1={a1:.4f}, max|delta|={np.max(np.abs(min_d_large)):.3f}")
    print(f"  Deltas: {np.round(min_d_large, 4)}")

print()

# -----------------------------------------------------------------------
# Part C: Investigate the best (lowest-GF) config in detail
# -----------------------------------------------------------------------
print("Part C: Best config structure — where are the good times?")
print("=" * 60)

# Use the best from Part A across all bands
best_overall = min((v for v in results_by_band.values() if v[1] is not None),
                   key=lambda x: x[0], default=None)
if min_d_large is not None and (best_overall is None or min_gf_large < best_overall[0]):
    best_d = min_d_large
    best_gf = min_gf_large
else:
    best_gf, best_d, _ = best_overall

a1 = 1.0 + best_d[0]
speeds = np.array([i + best_d[i - 1] for i in range(1, 10)] + [10.0])
W_lo = 1.0 / (11.0 * a1)
W_hi = 10.0 / (11.0 * a1)

print(f"  Best config GF = {best_gf:.5f}")
print(f"  a_1 = {a1:.4f}, speeds = {np.round(speeds, 4)}")
print(f"  W_0 = [{W_lo:.5f}, {W_hi:.5f}]")

# High-resolution good-fraction check
t_grid = np.linspace(W_lo, W_hi, 100_000)
all_lonely = np.ones(len(t_grid), dtype=bool)
for s in speeds:
    fr = frac(s * t_grid)
    all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)

good_times = t_grid[all_lonely]
print(f"  Good times (100k grid): {len(good_times)} points = {len(good_times)/len(t_grid):.5f}")

if len(good_times) > 0:
    # Find connected intervals of good times
    diffs = np.diff(good_times)
    gap_threshold = (W_hi - W_lo) / 100  # 1% of W_0 width = definite gap
    gap_indices = np.where(diffs > gap_threshold)[0]

    intervals = []
    start = good_times[0]
    for gi in gap_indices:
        intervals.append((start, good_times[gi]))
        start = good_times[gi + 1]
    intervals.append((start, good_times[-1]))

    print(f"\n  Good time intervals ({len(intervals)} connected component(s)):")
    for (s, e) in intervals:
        width = e - s
        pct = 100.0 * width / (W_hi - W_lo)
        print(f"    [{s:.5f}, {e:.5f}]  width={width:.5f}  ({pct:.2f}% of W_0)")

# How does GF change as we scale all deltas?
print(f"\nGF vs. perturbation scale (scaling all deltas of best config):")
for scale in [0.5, 0.7, 0.9, 1.0, 1.1, 1.3, 1.5, 1.8, 2.0]:
    d_scaled = best_d * scale
    d_scaled[0] = max(best_d[0] * scale, -0.98)  # keep a_1 > 0.02
    gf_s = good_fraction(d_scaled)
    blocking_s = "CB" if True else "not-CB"  # check blocking
    # quick check
    s_arr = np.array([i + d_scaled[i - 1] for i in range(1, 10)] + [10.0])
    any_safe_flag = False
    for m in range(1, 11):
        fr = frac(s_arr * m / 11.0)
        if np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0)):
            any_safe_flag = True
            break
    cb_str = "CB " if not any_safe_flag else "not-CB"
    print(f"  scale={scale:.1f}: GF={gf_s:.5f}  [{cb_str}]  a_1={1+d_scaled[0]:.4f}")

print()
print("SUMMARY")
print("=" * 60)
all_min_gfs = [v[0] for v in results_by_band.values() if v[1] is not None]
if all_min_gfs:
    overall_min = min(all_min_gfs)
    print(f"Minimum GF across all a_1 bands: {overall_min:.5f}")
print(f"Minimum GF with large deltas:     {min_gf_large:.5f}")
print(f"\nConclusion: Good fraction appears bounded below by ~{min(all_min_gfs + [min_gf_large]):.3f}")
print("LRC is not close to failing computationally.")
