"""
lrc_n11_seeded_de_v1.py

Seeded differential evolution: use random-search-collected complete-blocking
configs as the DE initial population. This avoids getting trapped in the
penalty region.

Also runs 300 Nelder-Mead polish runs from the worst-GF random seeds.

Date: 2026-03-22
"""

import numpy as np
from scipy.optimize import differential_evolution, minimize

THRESHOLD = 1.0 / 11
RNG_SEED = 999


def frac(x):
    return x - np.floor(x)


def good_fraction(deltas, n_grid=4000):
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 1.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)
    all_lonely = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(all_lonely))


def blocking_penalty_soft(deltas):
    """Soft penalty — smaller coefficient to allow DE to find feasible region."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 10.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    total = 0.0
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        margin = np.minimum(fr - THRESHOLD, 10.0 / 11.0 - fr)
        best_margin = np.max(margin)
        if best_margin > 0:
            total += best_margin
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


def is_complete_blocking_vec(delta_batch):
    N = delta_batch.shape[0]
    speeds = np.zeros((N, 10))
    for i in range(1, 10):
        speeds[:, i - 1] = i + delta_batch[:, i - 1]
    speeds[:, 9] = 10.0
    any_safe = np.zeros(N, dtype=bool)
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        any_safe |= np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0), axis=1)
    return ~any_safe


def objective_soft(deltas):
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005 or a1 >= 1.0:
        return 5.0
    pen = blocking_penalty_soft(deltas)
    return good_fraction(deltas) + 3.0 * pen


# -----------------------------------------------------------------------
# Step 1: Collect seed population via random sampling
# -----------------------------------------------------------------------
print("Step 1: Collecting seed population of complete-blocking configs")
rng = np.random.default_rng(RNG_SEED)

N_SEED = 3_000_000
BATCH = 200_000
POPSIZE_TARGET = 300

seed_pool = []   # (gf, delta) sorted by gf ascending
total_cb = 0

for b in range(N_SEED // BATCH):
    deltas = rng.uniform(-0.90, 0.90, size=(BATCH, 9))
    # Oversample from a_1 close to 1 (where minimum GF lives)
    r = rng.random(BATCH)
    # 40% in (0.90, 1.00), 30% in (0.97, 1.00), 30% in (0.50, 1.00)
    mask1 = r < 0.40
    mask2 = (r >= 0.40) & (r < 0.70)
    deltas[mask1, 0] = rng.uniform(-0.10, -0.001, size=mask1.sum())
    deltas[mask2, 0] = rng.uniform(-0.03, -0.001, size=mask2.sum())
    # rest: uniform in (-0.90, -0.001)
    mask3 = r >= 0.70
    deltas[mask3, 0] = rng.uniform(-0.90, -0.001, size=mask3.sum())

    blocking = is_complete_blocking_vec(deltas)
    cnt = int(blocking.sum())
    total_cb += cnt

    for k in np.where(blocking)[0]:
        gf = good_fraction(deltas[k])
        if len(seed_pool) < POPSIZE_TARGET or gf < seed_pool[-1][0]:
            seed_pool.append((gf, deltas[k].copy()))
            seed_pool.sort(key=lambda x: x[0])
            seed_pool = seed_pool[:POPSIZE_TARGET]

    batch_min = seed_pool[0][0] if seed_pool else float('nan')
    print(f"  Batch {b+1}/{N_SEED//BATCH}: {cnt} CB | total={total_cb} | "
          f"pool min GF={batch_min:.5f} | pool size={len(seed_pool)}")

print(f"\nSeed pool: {len(seed_pool)} configs")
print(f"Min GF in seed pool: {seed_pool[0][0]:.6f}")
print(f"a_1 of min: {1+seed_pool[0][1][0]:.5f}")
print(f"Max GF in seed pool: {seed_pool[-1][0]:.6f}")

# -----------------------------------------------------------------------
# Step 2: DE with seeded population
# -----------------------------------------------------------------------
print("\nStep 2: DE with seeded initial population")

seed_deltas = np.array([d for (_, d) in seed_pool])

bounds = [(-0.90, -0.001)] + [(-0.90, 0.90)] * 8

result_de = differential_evolution(
    objective_soft,
    bounds,
    seed=RNG_SEED + 1,
    init=seed_deltas,
    strategy='randtobest1bin',
    popsize=len(seed_deltas) // 9,   # popsize = N / ndim, roughly
    maxiter=500,
    tol=1e-9,
    mutation=(0.3, 1.0),
    recombination=0.85,
    polish=False,
    disp=True,
    workers=1,
)

print(f"\nDE result: f = {result_de.fun:.7f}")
d_de = result_de.x
if is_complete_blocking(d_de):
    gf_de = good_fraction(d_de, n_grid=50000)
    print(f"  GF (50k) = {gf_de:.6f}  a_1 = {1+d_de[0]:.5f}  max|d| = {np.max(np.abs(d_de)):.4f}")
else:
    gf_de = float('nan')
    print("  DE result not in complete-blocking region — polishing from seed pool instead")

# -----------------------------------------------------------------------
# Step 3: Nelder-Mead polish from all 300 seed configs
# -----------------------------------------------------------------------
print("\nStep 3: Nelder-Mead polish from seed pool")

def objective_nm(deltas):
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005 or a1 >= 1.0:
        return 5.0
    pen = blocking_penalty_soft(deltas)
    if pen > 0:
        return 1.0 + 10.0 * pen
    return good_fraction(deltas, n_grid=4000)

min_gf_nm = seed_pool[0][0]
min_d_nm = seed_pool[0][1].copy()

for trial, (gf0, d0) in enumerate(seed_pool):
    # Perturb slightly and polish
    d_start = d0 + rng.normal(0, 0.005, size=9)
    d_start[0] = np.clip(d_start[0], -0.90, -0.001)
    d_start[1:] = np.clip(d_start[1:], -0.90, 0.90)

    res = minimize(objective_nm, d_start, method='Nelder-Mead',
                   options={'maxiter': 20000, 'xatol': 1e-8, 'fatol': 1e-9,
                            'adaptive': True})
    d_opt = res.x
    d_opt[0] = np.clip(d_opt[0], -0.90, -0.001)

    if is_complete_blocking(d_opt):
        gf = good_fraction(d_opt, n_grid=8000)
        if gf < min_gf_nm:
            min_gf_nm = gf
            min_d_nm = d_opt.copy()
            print(f"  Trial {trial+1}: new min GF = {gf:.6f}  a_1 = {1+d_opt[0]:.5f}")

    if (trial + 1) % 50 == 0:
        print(f"  {trial+1}/{len(seed_pool)} done | min GF = {min_gf_nm:.6f}")

print(f"\nNelder-Mead min GF: {min_gf_nm:.6f}")

# -----------------------------------------------------------------------
# Step 4: High-resolution verification of best config
# -----------------------------------------------------------------------
print("\nStep 4: High-resolution analysis of best config")

best_gf = min(x for x in [seed_pool[0][0], gf_de if not np.isnan(gf_de) else float('inf'),
                            min_gf_nm] if not np.isnan(x))
best_d = None
if best_gf == min_gf_nm:
    best_d = min_d_nm
elif not np.isnan(gf_de) and gf_de <= min_gf_nm and gf_de <= seed_pool[0][0]:
    best_d = d_de
else:
    best_d = seed_pool[0][1]

d = best_d
a1 = 1.0 + d[0]
speeds = np.array([i + d[i - 1] for i in range(1, 10)] + [10.0])
W_lo = 1.0 / (11.0 * a1)
W_hi = 10.0 / (11.0 * a1)
gf_final = good_fraction(d, n_grid=200000)

print(f"\nBest config:")
print(f"  a_1 = {a1:.6f}  (delta_1 = {d[0]:.6f})")
print(f"  speeds = {np.round(speeds, 5)}")
print(f"  max|delta| = {np.max(np.abs(d)):.5f}")
print(f"  GF (200k grid) = {gf_final:.6f}")
print(f"  W_0 = [{W_lo:.5f}, {W_hi:.5f}]  (width = {W_hi-W_lo:.5f})")

# AP witness blocking table
print("\nAP witnesses:")
for m in range(1, 11):
    t_m = m / 11.0
    in_W0 = W_lo <= t_m <= W_hi
    fr = frac(speeds * m / 11.0)
    safe = np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0))
    blk = [(i+1, round(fr[i], 4)) for i in range(9) if fr[i] < THRESHOLD or fr[i] > 10/11]
    print(f"  t_{m:2d}  in_W0={str(in_W0):5}  {'SAFE' if safe else 'blocked:'+str(blk)}")

# Stacking profile
t_grid = np.linspace(W_lo, W_hi, 500_000)
stacking = np.zeros(len(t_grid), dtype=int)
for s in speeds:
    fr = frac(s * t_grid)
    stacking += ((fr < THRESHOLD) | (fr > 10.0 / 11.0)).astype(int)

print(f"\nStacking in W_0:")
for k in range(12):
    cnt = int((stacking == k).sum())
    if cnt > 0:
        pct = 100.0 * cnt / len(t_grid)
        print(f"  k={k:2d}: {cnt:>8,} ({pct:5.2f}%)")

print()
print("=" * 65)
print("ROUTE 3 FINAL VERDICT")
print("=" * 65)
print(f"Seed pool minimum GF:         {seed_pool[0][0]:.6f}")
print(f"Nelder-Mead minimum GF:       {min_gf_nm:.6f}")
print(f"High-res verified minimum GF: {gf_final:.6f}")
print()
if gf_final > 0.001:
    print(f"STRONG SUPPORT: GF ≥ {gf_final:.4f} confirmed on the extremal config.")
    print("Route 3 compactness argument holds empirically.")
    print("The analytical lower bound c_M > 0 remains to be proved,")
    print(f"but the empirical floor is c_M ≈ {gf_final:.4f}.")
elif gf_final > 0:
    print(f"MARGINAL: GF = {gf_final:.6f} > 0 but very small.")
else:
    print("FAILS: Zero GF found in bounded-delta regime — investigate!")
