"""
lrc_n11_min_good_fraction_v1.py

Find the complete-blocking configuration that MINIMISES the good-time fraction
in W_0. This is the "tightest near-LRC-failure" search.

n=11 EFN setup:
  speeds a_i = i + delta_i  (i=1..9),  a_10 = 10
  W_0 = [1/(11*a_1), 10/(11*a_1)]  — runner 1 always lonely here
  Good fraction = measure{t in W_0 : ALL runners lonely} / |W_0|

Strategy:
  Phase 1 — Broad random search over complete-blocking configs, track minimum GF.
  Phase 2 — Local optimisation starting from the worst Phase 1 configs.
  Phase 3 — Report the extremal configuration and its witness structure.

Date: 2026-03-22
"""

import numpy as np
from scipy.optimize import minimize

THRESHOLD = 1.0 / 11
N_GRID = 5000        # time-grid resolution for GF computation
RNG_SEED = 99


def frac(x):
    return x - np.floor(x)


def good_fraction(deltas, n_grid=N_GRID):
    """
    Compute good-time fraction in W_0 for a given delta vector (length 9).
    Returns float in [0, 1].
    """
    a1 = 1.0 + deltas[0]
    if a1 <= 0.05:
        return 0.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)

    # Runner 1 is lonely by construction throughout W_0.
    # Check runners 2..10 (speeds[1:]).
    all_lonely = np.ones(n_grid, dtype=bool)
    for s in speeds[1:]:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)

    return float(np.mean(all_lonely))


def is_complete_blocking(deltas):
    """True iff all 10 AP witnesses are blocked."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0:
        return False
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        if np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0)):
            return False   # witness m is safe → not complete-blocking
    return True


def is_complete_blocking_vec(delta_batch):
    """Vectorised complete-blocking check. delta_batch shape (N, 9)."""
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


def blocking_penalty(deltas):
    """
    Continuous relaxation: how 'far' from complete-blocking is this config?
    Returns 0 if complete-blocking, > 0 if some witness is safe.
    """
    a1 = 1.0 + deltas[0]
    if a1 <= 0.05:
        return 1.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    total = 0.0
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        # safety margin for this witness: min(frac - 1/11, 10/11 - frac) over runners
        margin = np.minimum(fr - THRESHOLD, 10.0 / 11.0 - fr)
        best_margin = np.max(margin)
        if best_margin > 0:
            total += 100.0 * best_margin  # penalise safe witnesses
    return total


def objective(deltas):
    """
    Minimise: good_fraction + large_penalty_if_not_blocking.
    We want the smallest good_fraction among complete-blocking configs.
    """
    a1 = 1.0 + deltas[0]
    if a1 <= 0.05 or a1 >= 1.1:
        return 1.0
    pen = blocking_penalty(deltas)
    gf = good_fraction(deltas)
    return gf + pen


# -----------------------------------------------------------------------
# PHASE 1: Broad random search — collect worst-GF complete-blocking configs
# -----------------------------------------------------------------------
print("=" * 65)
print("PHASE 1: Random search for low good-fraction complete-blocking configs")
print("=" * 65)

rng = np.random.default_rng(RNG_SEED)
BATCH = 100_000
N_BATCHES_P1 = 10   # 1M total samples

worst_gf_samples = []   # (gf, deltas) sorted by gf ascending
TOP_K = 50              # keep the 50 worst

total_blocking = 0
min_gf_found = 1.0

for batch_idx in range(N_BATCHES_P1):
    # Sample in the 'interesting' region: a_1 in (0.3, 0.95), others moderate
    deltas = rng.uniform(-0.9, 0.9, size=(BATCH, 9))
    deltas[:, 0] = rng.uniform(-0.7, -0.05, size=BATCH)  # a_1 in (0.3, 0.95)

    blocking = is_complete_blocking_vec(deltas)
    count = int(blocking.sum())
    total_blocking += count

    if count > 0:
        idx = np.where(blocking)[0]
        for k in idx:
            d = deltas[k]
            gf = good_fraction(d)
            if gf < min_gf_found:
                min_gf_found = gf
            if len(worst_gf_samples) < TOP_K or gf < worst_gf_samples[-1][0]:
                worst_gf_samples.append((gf, d.copy()))
                worst_gf_samples.sort(key=lambda x: x[0])
                worst_gf_samples = worst_gf_samples[:TOP_K]

    done = (batch_idx + 1) * BATCH
    print(f"  {done:>8,} sampled | blocking found: {total_blocking} | min GF so far: {min_gf_found:.5f}")

print(f"\nPhase 1 complete. {total_blocking} complete-blocking configs found.")
print(f"Minimum good fraction found in Phase 1: {min_gf_found:.6f}")
if worst_gf_samples:
    print(f"\nTop 5 worst-GF configs found:")
    for rank, (gf, d) in enumerate(worst_gf_samples[:5], 1):
        a1 = 1 + d[0]
        print(f"  [{rank}] GF={gf:.5f}  a_1={a1:.4f}  max|delta|={np.max(np.abs(d)):.4f}")
        print(f"       deltas = {np.round(d, 4)}")

print()

# -----------------------------------------------------------------------
# PHASE 2: Local optimisation from worst Phase 1 seeds
# -----------------------------------------------------------------------
print("=" * 65)
print("PHASE 2: Local optimisation — minimise good fraction")
print("=" * 65)

rng2 = np.random.default_rng(RNG_SEED + 1)
N_OPT = min(50, len(worst_gf_samples))
min_gf_opt = min_gf_found
min_config_opt = None
if worst_gf_samples:
    min_config_opt = worst_gf_samples[0][1].copy()

for trial in range(N_OPT):
    d0 = worst_gf_samples[trial][1].copy()
    # Add small noise to escape flat regions
    d0 += rng2.normal(0, 0.01, size=9)
    d0[0] = min(d0[0], -0.05)  # keep a_1 < 1

    res = minimize(objective, d0, method='Nelder-Mead',
                   options={'maxiter': 20000, 'xatol': 1e-7, 'fatol': 1e-8,
                            'adaptive': True})

    d_opt = res.x
    d_opt[0] = min(d_opt[0], -0.01)  # ensure a_1 < 1

    if is_complete_blocking(d_opt):
        gf = good_fraction(d_opt, n_grid=20000)  # higher resolution at candidate
        if gf < min_gf_opt:
            min_gf_opt = gf
            min_config_opt = d_opt.copy()
            print(f"  Trial {trial+1}: new minimum GF = {gf:.6f}  a_1 = {1+d_opt[0]:.4f}")

    if (trial + 1) % 10 == 0:
        print(f"  {trial+1}/{N_OPT} done | best GF = {min_gf_opt:.6f}")

print(f"\nPhase 2 minimum good fraction: {min_gf_opt:.6f}")
print()

# -----------------------------------------------------------------------
# PHASE 3: Detailed analysis of the extremal configuration
# -----------------------------------------------------------------------
print("=" * 65)
print("PHASE 3: Extremal configuration analysis")
print("=" * 65)

if min_config_opt is not None:
    d = min_config_opt
    a1 = 1.0 + d[0]
    speeds = np.array([i + d[i - 1] for i in range(1, 10)] + [10.0])

    print(f"\nExtremal config:")
    print(f"  a_1        = {a1:.6f}  (delta_1 = {d[0]:.6f})")
    print(f"  speeds     = {np.round(speeds, 5)}")
    print(f"  deltas     = {np.round(d, 5)}")
    print(f"  max|delta| = {np.max(np.abs(d)):.5f}")
    gf_final = good_fraction(d, n_grid=50000)
    print(f"  Good fraction (50k grid) = {gf_final:.6f}")

    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    print(f"\n  W_0 = [{W_lo:.5f}, {W_hi:.5f}]  (width = {W_hi - W_lo:.5f})")

    print("\nAP witness status:")
    for m in range(1, 11):
        t_m = m / 11.0
        in_W0 = (W_lo <= t_m <= W_hi)
        fr = frac(speeds * m / 11.0)
        lonely_per_runner = (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
        safe_witness = bool(np.all(lonely_per_runner))
        blocking_runners = [i + 1 for i, b in enumerate(lonely_per_runner) if not b]
        print(f"  t_{m:2d} = {t_m:.4f}  in_W0={str(in_W0):5s}  "
              f"{'SAFE' if safe_witness else 'BLOCKED by runners ' + str(blocking_runners)}")

    # Find the actual first lonely time in W_0
    t_grid = np.linspace(W_lo, W_hi, 100_000)
    all_lonely = np.ones(len(t_grid), dtype=bool)
    # Include runner 1 explicitly
    fr1 = frac(speeds[0] * t_grid)
    all_lonely &= (fr1 >= THRESHOLD) & (fr1 <= 10.0 / 11.0)
    for s in speeds[1:]:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)

    good_times = t_grid[all_lonely]
    print(f"\n  Good times in W_0 (100k grid): {np.sum(all_lonely)} points")
    if len(good_times) > 0:
        print(f"  First good time: {good_times[0]:.7f}")
        print(f"  Last good time:  {good_times[-1]:.7f}")
        print(f"  Good fraction:   {len(good_times)/len(t_grid):.6f}")

        # Check per-runner status at first good time
        t_star = good_times[0]
        print(f"\n  Runner positions at first good time t* = {t_star:.7f}:")
        for i, s in enumerate(speeds, 1):
            pos = frac(s * t_star)
            status = "LONELY" if THRESHOLD <= pos <= 10.0/11.0 else "BAD"
            print(f"    Runner {i:2d} (speed={s:.4f}): pos={pos:.4f}  [{status}]")
    else:
        print("  NO good times found on 100k grid — possible LRC violation or resolution issue!")

    # Stacking analysis: maximum number of simultaneously bad runners in W_0
    stacking = np.zeros(len(t_grid), dtype=int)
    for s in speeds:
        fr = frac(s * t_grid)
        bad = (fr < THRESHOLD) | (fr > 10.0 / 11.0)
        stacking += bad.astype(int)

    print(f"\n  Stacking in W_0:")
    for k in range(11):
        cnt = int(np.sum(stacking == k))
        if cnt > 0:
            pct = 100.0 * cnt / len(t_grid)
            print(f"    {k} runners bad: {cnt:>7,} ({pct:.2f}%)")

print()
print("=" * 65)
print("VERDICT")
print("=" * 65)
print(f"Minimum good fraction found: {min_gf_opt:.6f}")
if min_gf_opt > 0.001:
    print("LRC holds with substantial margin across all tested complete-blocking configs.")
    print(f"Good fraction bounded below by approx {min_gf_opt:.4f} (> 0).")
elif min_gf_opt > 0:
    print("LRC holds but with very small margin — near-failure config found.")
    print(f"Good fraction as small as {min_gf_opt:.6f} — investigate further.")
else:
    print("WARNING: Zero or near-zero good fraction found — potential LRC near-failure!")
