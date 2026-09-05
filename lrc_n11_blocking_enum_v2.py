"""
lrc_n11_blocking_enum_v2.py
Route 3, Step 4: Simultaneous-closure consistency check.

For each of 256 sign patterns (sgn(delta_2),...,sgn(delta_9)):
  1. Find the minimum-GF complete-blocking config with that sign pattern.
  2. Report GF per slot I_1..I_9.
  3. Identify which slots remain open (GF > 0).
  4. Report minimum total GF and which pattern achieves it.

Usage:
    python3 lrc_n11_blocking_enum_v2.py [--quick] [--pattern NNNN]

    --quick   : 20 random starts per pattern instead of 100 (faster, less accurate)
    --pattern : run a single pattern given as 8-bit binary string e.g. 10110100
"""

import numpy as np
from scipy.optimize import minimize
import sys
import json

THRESHOLD = 1.0 / 11.0

def frac(x):
    return x - np.floor(x)

# ── Slot definitions ──────────────────────────────────────────────────────────
# I_{m-1} = [(11m-10)/110, (11m-1)/110],  m = 2..10
SLOTS = []
for m in range(2, 11):
    lo = (11*m - 10) / 110.0
    hi = (11*m - 1)  / 110.0
    SLOTS.append((lo, hi, m))  # (left, right, witness_m)

# ── Core functions ────────────────────────────────────────────────────────────

def speeds_from_deltas(deltas):
    """Return speed array [a_1,...,a_9, a_10=10] from deltas [d_1,...,d_9]."""
    return np.array([i + deltas[i-1] for i in range(1, 10)] + [10.0])

def good_fraction(deltas, n_grid=50000):
    a1 = 1.0 + deltas[0]
    if a1 <= 0:
        return 1.0
    speeds = speeds_from_deltas(deltas)
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)
    ok = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        ok &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(ok))

def slot_good_fraction(deltas, slot_idx, n_grid=5000):
    """GF restricted to slot I_{slot_idx} (0-indexed: 0=I_1,...,8=I_9)."""
    speeds = speeds_from_deltas(deltas)
    lo, hi, _ = SLOTS[slot_idx]
    t_grid = np.linspace(lo, hi, n_grid)
    ok = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        ok &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(ok))

def blocking_penalty(deltas):
    a1 = 1.0 + deltas[0]
    if a1 <= 0:
        return 1e9
    speeds = speeds_from_deltas(deltas)
    pen = 0.0
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        if np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0)):
            pen += 100.0
    return pen

def is_sign_compatible(deltas, pattern):
    """Check that sgn(deltas[1:]) matches the 8-bit pattern (+/-).
       pattern is list of +1/-1 for runners 2..9 (indices 1..8 in deltas)."""
    for i, sgn in enumerate(pattern):
        d = deltas[i + 1]  # delta for runner (i+2)
        if abs(d) < 1e-6:
            continue  # near-zero OK for either sign
        if sgn * d < 0:
            return False
    return True

def objective(deltas, pattern):
    pen = blocking_penalty(deltas)
    if pen > 0.01:
        return pen
    # Soft sign constraint
    sign_pen = 0.0
    for i, sgn in enumerate(pattern):
        d = deltas[i + 1]
        if sgn * d < 0:
            sign_pen += 10.0 * abs(d)
    if sign_pen > 0.01:
        return 100.0 + sign_pen
    return good_fraction(deltas, n_grid=8000)

def find_min_gf_for_pattern(pattern, n_starts=50, seed=None):
    """Find minimum-GF CB config consistent with given sign pattern.

    pattern: list of +1/-1 for runners 2..9 (deltas[1..8]).
    Returns (best_gf, best_deltas) or (None, None) if no CB config found.
    """
    rng = np.random.default_rng(seed)
    best_gf = 1.0
    best_d = None

    for _ in range(n_starts):
        # Sample deltas respecting sign pattern
        d = np.zeros(9)
        d[0] = rng.uniform(-0.9, -0.01)  # delta_1 < 0 always (a_1 < 1)
        for i, sgn in enumerate(pattern):
            lo, hi = (0.01, 0.9) if sgn > 0 else (-0.9, -0.01)
            d[i + 1] = rng.uniform(lo, hi)

        pen = blocking_penalty(d)
        if pen > 0.01:
            continue

        result = minimize(
            lambda x: objective(x, pattern),
            d,
            method='Nelder-Mead',
            options={'maxiter': 30000, 'xatol': 1e-7, 'fatol': 1e-7}
        )

        if blocking_penalty(result.x) < 0.01 and is_sign_compatible(result.x, pattern):
            gf = good_fraction(result.x, n_grid=20000)
            if gf < best_gf:
                best_gf = gf
                best_d = result.x.copy()

    return best_gf, best_d

# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    quick = '--quick' in sys.argv
    single_pattern = None
    if '--pattern' in sys.argv:
        idx = sys.argv.index('--pattern')
        bits = sys.argv[idx + 1]
        single_pattern = [+1 if b == '1' else -1 for b in bits]

    n_starts = 20 if quick else 50

    results = []
    patterns_to_run = []

    if single_pattern is not None:
        patterns_to_run = [single_pattern]
    else:
        for mask in range(256):
            pat = [+1 if (mask >> (7 - i)) & 1 else -1 for i in range(8)]
            patterns_to_run.append(pat)

    total = len(patterns_to_run)
    print(f"Running {total} sign pattern(s), {n_starts} starts each.")
    print()

    global_best_gf = 1.0
    global_best_d = None
    global_best_pat = None

    for pidx, pattern in enumerate(patterns_to_run):
        pat_str = ''.join('+' if s > 0 else '-' for s in pattern)
        best_gf, best_d = find_min_gf_for_pattern(pattern, n_starts=n_starts, seed=pidx * 17)

        if best_d is None:
            print(f"[{pidx+1:3d}/{total}] Pattern {pat_str}: NO CB CONFIG FOUND")
            results.append({'pattern': pat_str, 'gf': None, 'deltas': None, 'slot_gf': None})
            continue

        # Per-slot GF
        slot_gfs = [slot_good_fraction(best_d, s, n_grid=10000) for s in range(9)]
        open_slots = [m for s, (_, _, m) in enumerate(SLOTS) if slot_gfs[s] > 0.001]

        print(f"[{pidx+1:3d}/{total}] Pattern {pat_str}: GF={best_gf*100:.4f}%  "
              f"a1={1+best_d[0]:.5f}  open_slots={open_slots}")

        if best_gf < global_best_gf:
            global_best_gf = best_gf
            global_best_d = best_d.copy()
            global_best_pat = pat_str

        results.append({
            'pattern': pat_str,
            'gf': float(best_gf),
            'deltas': [float(x) for x in best_d],
            'slot_gf': [float(x) for x in slot_gfs],
            'open_slots': open_slots,
        })

    # Summary
    print()
    print("=" * 70)
    print(f"Global minimum GF: {global_best_gf*100:.6f}%")
    print(f"Achieved by pattern: {global_best_pat}")
    if global_best_d is not None:
        speeds = speeds_from_deltas(global_best_d)
        print(f"Speeds: {[f'{s:.5f}' for s in speeds]}")
        print()
        print("Blocking structure:")
        for m in range(1, 11):
            fr = frac(speeds * m / 11.0)
            blocked = [j+1 for j, f in enumerate(fr) if f < THRESHOLD or f > 10/11]
            print(f"  t_{m}: blocked by runners {blocked}")
        print()
        print("Per-slot GF (high-res):")
        for s, (lo, hi, m) in enumerate(SLOTS):
            sgf = slot_good_fraction(global_best_d, s, n_grid=20000)
            print(f"  I_{s+1} (t_{m}): {sgf*100:.4f}%")

    # Save JSON
    out_path = 'reports/lrc_n11_blocking_enum_v2_results.json'
    try:
        import os
        os.makedirs('reports', exist_ok=True)
        with open(out_path, 'w') as f:
            json.dump({
                'global_min_gf': float(global_best_gf),
                'global_best_pattern': global_best_pat,
                'global_best_deltas': [float(x) for x in global_best_d] if global_best_d is not None else None,
                'per_pattern': results,
            }, f, indent=2)
        print(f"\nResults saved to {out_path}")
    except Exception as e:
        print(f"(Could not save JSON: {e})")

if __name__ == '__main__':
    main()
