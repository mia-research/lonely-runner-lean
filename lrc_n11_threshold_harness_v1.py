"""
lrc_n11_threshold_harness_v1.py
Computational verification of the candidate theorem:
  If |delta_i| < 0.5 for all i=1..9, no complete-blocking configuration exists.

n=11 LRC setup:
  speeds a_i = i + delta_i  (i=1..9),  a_10 = 10
  witness m safe iff {a_i * m/11} in [1/11, 10/11] for ALL i=1..10
  complete-blocking: NO m in {1..10} is safe

Date: 2026-03-22
"""

import numpy as np

RNG_SEED = 42
N_SAMPLES_PHASE1 = 5_000_000
N_OPT_STARTS_PHASE2 = 500
THRESHOLD = 1/11

# -----------------------------------------------------------------------
def frac(x):
    return x - np.floor(x)

def is_lonely_at_witness(deltas, m):
    """
    Returns True iff witness m is safe for ALL runners.
    deltas: array of shape (9,) — perturbations delta_1..delta_9
    a_i = i + delta_i for i=1..9;  a_10 = 10
    """
    residues = np.array([frac((i + deltas[i-1]) * m / 11) for i in range(1, 10)])
    r10 = frac(10 * m / 11)
    all_r = np.append(residues, r10)
    return np.all(all_r >= THRESHOLD) and np.all(all_r <= 10/11)

def is_complete_blocking(deltas):
    """Returns True iff ALL witnesses m=1..10 are blocked."""
    for m in range(1, 11):
        if is_lonely_at_witness(deltas, m):
            return False  # found a safe witness → not complete-blocking
    return True

def is_complete_blocking_vec(delta_batch):
    """
    Vectorised: delta_batch shape (N, 9).
    Returns boolean array of shape (N,).
    """
    N = delta_batch.shape[0]
    speeds = np.zeros((N, 10))
    for i in range(1, 10):
        speeds[:, i-1] = i + delta_batch[:, i-1]
    speeds[:, 9] = 10.0

    any_safe = np.zeros(N, dtype=bool)
    for m in range(1, 11):
        fracs = frac(speeds * m / 11)          # (N, 10)
        safe = np.all((fracs >= THRESHOLD) & (fracs <= 10/11), axis=1)  # (N,)
        any_safe |= safe

    return ~any_safe   # complete-blocking iff no safe witness

# -----------------------------------------------------------------------
# PHASE 1: Random search in |delta_i| < 0.5
# -----------------------------------------------------------------------
print("=" * 60)
print("PHASE 1: Random search in |delta_i| < 0.5, delta_1 < 0")
print(f"  Samples: {N_SAMPLES_PHASE1:,}  |  Seed: {RNG_SEED}")
print("=" * 60)

rng = np.random.default_rng(RNG_SEED)
BATCH = 200_000
found_examples = []
total_blocking = 0

for batch_start in range(0, N_SAMPLES_PHASE1, BATCH):
    n = min(BATCH, N_SAMPLES_PHASE1 - batch_start)
    deltas = rng.uniform(-0.5, 0.5, size=(n, 9))
    deltas[:, 0] = rng.uniform(-0.5, 0.0, size=n)   # delta_1 < 0 → a_1 < 1

    blocking = is_complete_blocking_vec(deltas)
    count = blocking.sum()
    total_blocking += count

    if count > 0 and len(found_examples) < 5:
        idx = np.where(blocking)[0]
        for k in idx[:5 - len(found_examples)]:
            found_examples.append(deltas[k].copy())

    if (batch_start // BATCH) % 5 == 4:
        done = batch_start + n
        print(f"  {done:>8,} sampled | blocking found so far: {total_blocking}")

print(f"\nPhase 1 result: {total_blocking} complete-blocking configs found in {N_SAMPLES_PHASE1:,} samples")
if found_examples:
    print("\nExample(s) found:")
    for ex in found_examples:
        a = [i+1 + ex[i] for i in range(9)] + [10.0]
        print(f"  deltas = {np.round(ex, 6)}")
        print(f"  speeds = {np.round(a, 6)}")
        print(f"  max|delta| = {np.max(np.abs(ex)):.6f}")
else:
    print("  → No complete-blocking config found with |delta_i| < 0.5")

print()

# -----------------------------------------------------------------------
# PHASE 2: Optimisation — find minimum max|delta_i| for complete blocking
# -----------------------------------------------------------------------
print("=" * 60)
print("PHASE 2: Optimisation — minimum max|delta_i| for complete blocking")
print(f"  Starting points: {N_OPT_STARTS_PHASE2}")
print("=" * 60)

from scipy.optimize import minimize, differential_evolution

def blocking_score(deltas_flat):
    """
    Returns a scalar. Zero means a witness is safe (not blocking).
    Positive means potential complete-blocking.
    We want to MAXIMISE blocking while minimising max|delta|.
    """
    deltas = deltas_flat
    speeds = np.array([i + deltas[i-1] for i in range(1, 10)] + [10.0])
    total = 0.0
    for m in range(1, 11):
        fracs = frac(speeds * m / 11)
        # For this witness to be blocked, at least one runner must be outside [1/11, 10/11]
        # Violation per runner: max(0, 1/11 - frac) or max(0, frac - 10/11)
        lower_viol = np.maximum(0, THRESHOLD - fracs)
        upper_viol = np.maximum(0, fracs - 10/11)
        viol = lower_viol + upper_viol
        best_viol = np.max(viol)   # best violator for this witness
        total += best_viol
    return total

def objective(deltas_flat):
    """
    Minimise: max|delta_i| - large_penalty * blocking_score
    Subject to: delta_1 < 0 (a_1 < 1), all |delta_i| unconstrained
    """
    score = blocking_score(deltas_flat)
    return np.max(np.abs(deltas_flat)) - 2.0 * score

best_threshold = np.inf
best_config = None
rng2 = np.random.default_rng(RNG_SEED + 1)

for trial in range(N_OPT_STARTS_PHASE2):
    # Start from a broader range to look for minimum threshold
    d0 = rng2.uniform(-1.0, 1.0, size=9)
    d0[0] = -abs(d0[0])   # delta_1 < 0

    res = minimize(objective, d0, method='Nelder-Mead',
                   options={'maxiter': 5000, 'xatol': 1e-8, 'fatol': 1e-8})

    d_opt = res.x
    d_opt[0] = -abs(d_opt[0])   # enforce delta_1 < 0

    if is_complete_blocking(d_opt):
        thresh = np.max(np.abs(d_opt))
        if thresh < best_threshold:
            best_threshold = thresh
            best_config = d_opt.copy()

    if trial % 100 == 99:
        status = f"best threshold so far: {best_threshold:.6f}" if best_config is not None else "no blocking found yet"
        print(f"  {trial+1}/{N_OPT_STARTS_PHASE2} done | {status}")

print(f"\nPhase 2 result:")
if best_config is not None:
    a = [i+1 + best_config[i] for i in range(9)] + [10.0]
    print(f"  Minimum max|delta_i| for complete blocking: {best_threshold:.6f}")
    print(f"  Achieved at deltas = {np.round(best_config, 6)}")
    print(f"  Speeds = {np.round(a, 6)}")
    for m in range(1, 11):
        safe = is_lonely_at_witness(best_config, m)
        print(f"    witness m={m}: {'SAFE' if safe else 'blocked'}")
else:
    print("  No complete-blocking configuration found by optimisation.")

# -----------------------------------------------------------------------
print()
print("=" * 60)
print("VERDICT")
print("=" * 60)
if total_blocking == 0 and (best_config is None or best_threshold >= 0.5):
    print("HOLDS: No complete-blocking configuration found with max|delta_i| < 0.5.")
    print("Candidate theorem supported computationally.")
    if best_config is not None:
        print(f"Minimum threshold found: {best_threshold:.6f} (>= 0.5 as predicted).")
    else:
        print("Optimisation also found no complete-blocking configuration at any threshold.")
else:
    print("FAILS or THRESHOLD LOWER THAN 0.5:")
    if total_blocking > 0:
        print(f"  Phase 1: {total_blocking} complete-blocking configs with max|delta_i| < 0.5 found!")
    if best_config is not None and best_threshold < 0.5:
        print(f"  Phase 2: minimum threshold = {best_threshold:.6f} < 0.5!")
    print("Investigate the example(s) above.")
