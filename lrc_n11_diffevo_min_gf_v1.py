"""
lrc_n11_diffevo_min_gf_v1.py

Global minimum good-fraction search using differential evolution.
This is the computational heart of Route 3: find the TRUE minimum GF
over all complete-blocking configs with |delta_i| <= 0.9.

If the minimum is > 0, this strongly supports c_M > 0 (Route 3 hypothesis).
If the minimum is 0, we've found a near-LRC-failure and need to investigate why.

Strategy:
  - Use scipy.optimize.differential_evolution (global, derivative-free)
  - Penalise non-blocking configs heavily
  - Run multiple independent evolutions from different seeds
  - Report the global best and the structure of the minimiser

Date: 2026-03-22
"""

import numpy as np
from scipy.optimize import differential_evolution, minimize
import time

THRESHOLD = 1.0 / 11
N_GRID_FAST = 3000
N_GRID_HIRES = 50000
RNG_SEED_BASE = 314159


def frac(x):
    return x - np.floor(x)


def good_fraction(deltas, n_grid=N_GRID_FAST):
    """Compute good fraction in W_0."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 1.0   # degenerate — penalise
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)
    all_lonely = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(all_lonely))


def blocking_penalty(deltas):
    """Continuous penalty for non-complete-blocking. Zero iff complete-blocking."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 1000.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    total = 0.0
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        # margin: how safe is the best (most dangerous) runner for this witness?
        margin = np.minimum(fr - THRESHOLD, 10.0 / 11.0 - fr)
        best_margin = np.max(margin)   # > 0 iff witness is safe
        if best_margin > 0:
            total += 200.0 * best_margin
    return total


def is_complete_blocking(deltas):
    a1 = 1.0 + deltas[0]
    if a1 <= 0:
        return False
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        if np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0)):
            return False
    return True


def objective(deltas):
    """Minimise: GF + blocking_penalty. Zero penalty inside CB."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005 or a1 > 0.9999:
        return 2.0   # out of domain
    pen = blocking_penalty(deltas)
    if pen > 0:
        return 1.0 + pen   # non-blocking: return > 1 (GF is in [0,1])
    return good_fraction(deltas)


# -----------------------------------------------------------------------
# RUN 1: Differential evolution, a_1 in (0.90, 1.00) tight band
# -----------------------------------------------------------------------
print("=" * 65)
print("DE Run 1: a_1 ∈ (0.90, 1.00), |delta_i| ≤ 0.90")
print("=" * 65)

bounds_tight = [(-0.10, -0.001)]   # delta_1 → a_1 in (0.90, 0.999)
bounds_tight += [(-0.90, 0.90)] * 8

t0 = time.time()
result1 = differential_evolution(
    objective, bounds_tight,
    seed=RNG_SEED_BASE,
    strategy='best1bin',
    popsize=25,
    maxiter=2000,
    tol=1e-9,
    mutation=(0.5, 1.5),
    recombination=0.9,
    polish=True,
    disp=True,
    workers=1,
)
t1 = time.time()

print(f"\nDE Run 1 complete in {t1-t0:.1f}s")
print(f"  Best objective: {result1.fun:.7f}")
d1 = result1.x
print(f"  a_1 = {1+d1[0]:.6f}")
print(f"  max|delta| = {np.max(np.abs(d1)):.5f}")
print(f"  deltas = {np.round(d1, 5)}")

if is_complete_blocking(d1):
    gf1 = good_fraction(d1, n_grid=N_GRID_HIRES)
    print(f"  GF (50k grid) = {gf1:.6f}  ← COMPLETE-BLOCKING ✓")
else:
    print(f"  WARNING: Not complete-blocking (penalty dominated)")
    # Try local polish
    res_polish = minimize(objective, d1, method='Nelder-Mead',
                          options={'maxiter': 50000, 'xatol': 1e-9, 'fatol': 1e-10})
    d1_polish = res_polish.x
    if is_complete_blocking(d1_polish):
        gf1 = good_fraction(d1_polish, n_grid=N_GRID_HIRES)
        d1 = d1_polish
        print(f"  After local polish: GF = {gf1:.6f}  ✓")
    else:
        gf1 = float('nan')
        print(f"  Still not complete-blocking after polish.")

print()

# -----------------------------------------------------------------------
# RUN 2: Differential evolution, a_1 in (0.95, 1.00) very tight
# -----------------------------------------------------------------------
print("=" * 65)
print("DE Run 2: a_1 ∈ (0.95, 1.00), |delta_i| ≤ 0.90")
print("=" * 65)

bounds_very_tight = [(-0.05, -0.001)]   # delta_1 → a_1 in (0.95, 0.999)
bounds_very_tight += [(-0.90, 0.90)] * 8

t0 = time.time()
result2 = differential_evolution(
    objective, bounds_very_tight,
    seed=RNG_SEED_BASE + 1,
    strategy='currenttobest1bin',
    popsize=30,
    maxiter=3000,
    tol=1e-10,
    mutation=(0.4, 1.2),
    recombination=0.9,
    polish=True,
    disp=True,
    workers=1,
)
t2 = time.time()

print(f"\nDE Run 2 complete in {t2-t0:.1f}s")
print(f"  Best objective: {result2.fun:.7f}")
d2 = result2.x
print(f"  a_1 = {1+d2[0]:.6f}")
print(f"  max|delta| = {np.max(np.abs(d2)):.5f}")

if is_complete_blocking(d2):
    gf2 = good_fraction(d2, n_grid=N_GRID_HIRES)
    print(f"  GF (50k grid) = {gf2:.6f}  ← COMPLETE-BLOCKING ✓")
    print(f"  deltas = {np.round(d2, 5)}")
else:
    gf2 = float('nan')
    print(f"  Not complete-blocking (objective dominated by penalty).")

print()

# -----------------------------------------------------------------------
# COMPARISON and detailed analysis
# -----------------------------------------------------------------------
print("=" * 65)
print("Summary and Detailed Analysis")
print("=" * 65)

best_gf = float('inf')
best_d = None
for (gf, d, label) in [(gf1, d1, "Run 1"), (gf2, d2, "Run 2")]:
    if not np.isnan(gf) and gf < best_gf:
        best_gf = gf
        best_d = d.copy()
        print(f"  {label}: GF = {gf:.6f}")

if best_d is not None:
    d = best_d
    a1 = 1.0 + d[0]
    speeds = np.array([i + d[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)

    print(f"\nBest extremal config:")
    print(f"  a_1 = {a1:.6f}")
    print(f"  speeds = {np.round(speeds, 5)}")
    print(f"  deltas = {np.round(d, 5)}")
    print(f"  max|delta| = {np.max(np.abs(d)):.5f}")
    print(f"  W_0 = [{W_lo:.5f}, {W_hi:.5f}]  (width = {W_hi-W_lo:.5f})")
    print(f"  Good fraction: {best_gf:.6f}")

    # AP witness status
    print("\nAP witness status:")
    for m in range(1, 11):
        t_m = m / 11.0
        in_W0 = W_lo <= t_m <= W_hi
        fr = frac(speeds * m / 11.0)
        lonely_all = np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0))
        blockers = [i + 1 for i, b in enumerate((fr < THRESHOLD) | (fr > 10.0 / 11.0)) if b]
        print(f"  t_{m:2d}={t_m:.4f}  in_W0={str(in_W0):5}  "
              f"{'SAFE' if lonely_all else 'blocked by ' + str(blockers)}")

    # Stacking profile
    t_grid = np.linspace(W_lo, W_hi, 200_000)
    stacking = np.zeros(len(t_grid), dtype=int)
    for s in speeds:
        fr = frac(s * t_grid)
        stacking += ((fr < THRESHOLD) | (fr > 10.0 / 11.0)).astype(int)

    print(f"\nStacking profile in W_0 (200k grid):")
    for k in range(12):
        cnt = int((stacking == k).sum())
        if cnt > 0:
            pct = 100.0 * cnt / len(t_grid)
            bar = '#' * int(pct * 2)
            print(f"  k={k:2d}: {cnt:>7,} ({pct:5.2f}%)  {bar}")

    # Find good times
    good_mask = stacking == 0
    good_times = t_grid[good_mask]
    print(f"\nGood times: {good_mask.sum()} / {len(t_grid)} ({100*good_mask.mean():.4f}%)")
    if len(good_times) > 0:
        print(f"  Range: [{good_times[0]:.6f}, {good_times[-1]:.6f}]")
        # Find connected intervals
        diffs = np.diff(good_times)
        gap_idx = np.where(diffs > (W_hi - W_lo) / 500)[0]
        intervals = []
        s = good_times[0]
        for gi in gap_idx:
            intervals.append((s, good_times[gi]))
            s = good_times[gi + 1]
        intervals.append((s, good_times[-1]))
        print(f"  Connected intervals ({len(intervals)}):")
        for (a, b) in intervals:
            print(f"    [{a:.6f}, {b:.6f}]  width={b-a:.6f}")

    # What makes the good interval so narrow?
    # Identify which runner has the tightest bad interval around the good region
    if len(good_times) > 0:
        t_star = good_times[0]
        t_star_pos = t_star + (good_times[-1] - good_times[0]) / 2
        print(f"\nRunner positions at centre of good region t={t_star_pos:.6f}:")
        for i, s in enumerate(speeds, 1):
            pos = frac(s * t_star_pos)
            margin_lo = pos - THRESHOLD
            margin_hi = 10.0 / 11.0 - pos
            margin = min(margin_lo, margin_hi)
            print(f"  Runner {i:2d} (speed={s:.4f}): pos={pos:.4f}  "
                  f"margin={margin:.4f}  {'LONELY' if margin >= 0 else 'BAD'}")

print()
print("=" * 65)
print("ROUTE 3 VERDICT")
print("=" * 65)
if not np.isnan(best_gf):
    print(f"Global minimum GF found by differential evolution: {best_gf:.6f}")
    if best_gf > 0.001:
        print("STRONG SUPPORT for Route 3: GF bounded away from 0.")
        print(f"  Empirical lower bound c_M ≥ {best_gf:.4f} for |delta_i| ≤ 0.9.")
    elif best_gf > 0:
        print("WEAK support: GF > 0 but very small. Needs further investigation.")
    else:
        print("FAILS: GF = 0 found — Route 3 hypothesis violated in this domain.")
else:
    print("Could not find complete-blocking minimum. Domain may be empty for these bounds.")
