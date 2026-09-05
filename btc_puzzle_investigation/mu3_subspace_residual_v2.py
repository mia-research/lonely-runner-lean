#!/usr/bin/env python3
"""mu3_subspace_residual_v2.py -- scaled-up extension of the mu3-forced subspace residual probes.

PREREG: PREREG_mu3_subspace_residual_v2.md (addendum to v1).
Goal: tighten the v1 scoped null by extending the powered range from |Q6| <= 426 to ~16000.

CHANGES FROM v1:
  - Numpy-vectorized nulls (R=5000 per cell, batch FFT for Probe D).
  - New LARGE stratum: p in [10^4, 10^5], p=7 mod 12, #E(F_p) prime.  Take first 8 qualifying.
  - Drop the unpowered IN stratum; only run primes where |Q6| >= 200.
  - Re-run the v1 S-stratum primes where B-plant fired (1303, 2143, 2251, 2503) as bridge.
  - Add Probe D: max-Fourier on Q6 at scale (the prior probe re-run with ~100x power).

DISCIPLINE (unchanged):
  Exact-int signal path.  Float only inside the monotone statistic, ranked vs matched null.
  check_no_float.py must pass.  Firing control at every prime.

Builds on (unchanged): mu3_forced_subspace_object_v1.build, audit_n1_vsign_v2_core,
  jclass_e2_relation_probe_v1, and imports build_q6 / probe helpers from v1.

Usage:  python mu3_subspace_residual_v2.py
"""
import random, sys, math, time                                  # noqa: float  (math for gcd; time for timing)
import numpy as np                                              # noqa: float  (numpy in monotone-statistic null only)

import audit_n1_vsign_v2_core as core
from mu3_subspace_residual_v1 import (build_q6, build_q6_involution, build_q6_powk_map,
                                       probe_b_autocorr, inv_mod)

# ============================================================================
# PREREG-frozen constants (integer-only; no float literals)
# ============================================================================
R_NULL = 5000
SEED   = 20260809
FIRE_NUM, FIRE_DEN = 95, 100
HIT_NUM,  HIT_DEN  = 99, 100
PLANT_NUM, PLANT_DEN = 3, 10
MIN_L = 200                 # only run primes where |Q6| >= MIN_L
PROBE_B_KS = (5, 7, 11, 13, 17, 19, 23, 25)
PROBE_C_WS = (4, 8, 16, 32, 64, 128, 256)

# v1 bridge primes (where B-plant fired)
BRIDGE_PRIMES = (1303, 2143, 2251, 2503)


def is_fire(rank):
    return rank * FIRE_DEN >= FIRE_NUM * R_NULL

def is_hit(rank):
    return rank * HIT_DEN >= HIT_NUM * R_NULL


# ============================================================================
# large-prime finder: p=7 mod 12 prime, #E(F_p) prime, p in [lo,hi]
# ============================================================================
def find_large_primes(lo, hi, count):
    """Walk primes p=7 mod 12, test #E(F_p) prime, take first `count`."""
    out = []
    p = lo
    while len(out) < count and p < hi:
        if p % 12 == 7 and core.is_prime(p):
            n = core.curve_order(p, 7)
            if core.is_prime(n) and (n - 1) % 6 == 0:
                L = (n - 1) // 6
                if L >= MIN_L:
                    out.append(p)
        p += 1
    return out


# ============================================================================
# numpy-vectorized null computation
# ============================================================================
def null_rank_batch(obs_abs, observed_array_fn, L, R, rng, batch_size=200):
    """Generic: draw R random +-1 sequences of length L, compute statistic via observed_array_fn,
    count how many null statistics are strictly less than obs_abs.  Returns rank in [0, R].
    observed_array_fn(arr) -> scalar statistic (abs value)."""
    rank = 0
    remaining = R
    while remaining > 0:
        bsz = min(batch_size, remaining)
        # bsz x L array of +-1
        arr = np.where(rng.random((bsz, L)) < 0.5, np.int64(-1), np.int64(1))   # noqa: float
        for i in range(bsz):
            null_val = abs(observed_array_fn(arr[i]))
            if null_val < obs_abs:
                rank += 1
        remaining -= bsz
    return rank


# ============================================================================
# Probe A (vectorized) -- subgroup-restricted partial sums
# ============================================================================
def probe_a_vec(L, u, rng):
    u_arr = np.array(u, dtype=np.int64)                              # noqa: float
    qs = []
    tt = L
    d = 2
    while d * d <= tt:
        if tt % d == 0:
            if 2 <= d <= L // 2:
                qs.append(d)
            while tt % d == 0:
                tt //= d
        d += 1
    if tt > 1 and 2 <= tt <= L // 2:
        qs.append(tt)
    qs = sorted(set(qs))
    if not qs:
        return []

    results = []
    for q in qs:
        w = L // q
        if w < 4:
            continue
        # observed: max over q cosets of |sum|
        coset_sums = []
        for r in range(q):
            coset_sums.append(abs(int(np.sum(u_arr[r::q][:w]))))    # noqa: float
        obs = max(coset_sums)
        # null: vectorized
        rank = 0
        remaining = R_NULL
        while remaining > 0:
            bsz = min(200, remaining)
            arr = np.where(rng.random((bsz, L)) < 0.5, -1, 1)          # noqa: float
            for i in range(bsz):
                null_max = 0
                for r in range(q):
                    s = abs(int(np.sum(arr[i, r::q][:w])))            # noqa: float
                    if s > null_max:
                        null_max = s
                if null_max < obs:
                    rank += 1
            remaining -= bsz
        results.append((q, obs, rank, w))
    return results


def probe_a_plant_vec(L, u, rng):
    q = None
    for qq in (2, 3, 5, 7, 11):
        if L % qq == 0 and L // qq >= 8:
            q = qq
            break
    if q is None:
        return None
    w = L // q
    planted = list(u)
    coset0 = list(range(0, L, q))[:w]
    rng_py = random.Random(int(rng.integers(0, 2**31)))
    rng_py.shuffle(coset0)
    n_force = w * PLANT_NUM // PLANT_DEN
    for idx in coset0[:n_force]:
        planted[idx] = 1
    u_arr = np.array(planted, dtype=np.int64)                         # noqa: float
    obs = abs(int(np.sum(u_arr[0:L:q])))                             # noqa: float  -- coset 0
    rank = 0
    remaining = R_NULL
    while remaining > 0:
        bsz = min(200, remaining)
        arr = np.where(rng.random((bsz, L)) < 0.5, -1, 1)              # noqa: float
        for i in range(bsz):
            null_max = 0
            for r in range(q):
                s = abs(int(np.sum(arr[i, r::q][:w])))                # noqa: float
                if s > null_max:
                    null_max = s
            if null_max < obs:
                rank += 1
        remaining -= bsz
    return (q, obs, rank)


# ============================================================================
# Probe B (vectorized) -- d^{-1} involution + d^k maps
# ============================================================================
def probe_b_autocorr_vec(L, u_arr, perm):
    """Vectorized: sum_j u[j]*u[perm[j]] for a numpy array u_arr and index list perm."""
    return int(np.sum(u_arr * u_arr[perm]))                         # noqa: float


def probe_b_null_rank_vec(L, u_arr, perm, obs_abs, rng):
    """Null: permute VALUES of u; rank |autocorr| among R draws."""
    abs_obs = abs(obs_abs)
    rank = 0
    remaining = R_NULL
    Lsq = L
    while remaining > 0:
        bsz = min(200, remaining)
        perms = np.array([rng.permutation(L) for _ in range(bsz)])   # noqa: float
        for i in range(bsz):
            null_val = abs(int(np.sum(u_arr[perms[i]] * u_arr[perm])))   # noqa: float
            if null_val < abs_obs:
                rank += 1
        remaining -= bsz
    return rank


def probe_b_plant_vec(L, u_arr, perm, rng):
    seen = [False] * L
    pairs = []
    for j in range(L):
        if seen[j]:
            continue
        jj = perm[j]
        if jj == j:
            seen[j] = True
            continue
        pairs.append((j, jj))
        seen[j] = True
        seen[jj] = True
    if len(pairs) < 4:
        return None
    rng_py = random.Random(int(rng.integers(0, 2**31)))
    rng_py.shuffle(pairs)
    n_force = len(pairs) * PLANT_NUM // PLANT_DEN
    planted = u_arr.copy()
    for (a, b) in pairs[:n_force]:
        planted[a] = 1
        planted[b] = 1
    obs = int(np.sum(planted * planted[perm]))                     # noqa: float
    abs_obs = abs(obs)
    rank = 0
    remaining = R_NULL
    while remaining > 0:
        bsz = min(200, remaining)
        perms = np.array([rng.permutation(L) for _ in range(bsz)])   # noqa: float
        for i in range(bsz):
            null_val = abs(int(np.sum(planted[perms[i]] * planted[perm])))   # noqa: float
            if null_val < abs_obs:
                rank += 1
        remaining -= bsz
    return (obs, rank)


# ============================================================================
# Probe C (vectorized) -- aperture windows
# ============================================================================
def probe_c_vec(L, u, rng):
    u_arr = np.array(u, dtype=np.int64)                              # noqa: float
    ws = [w for w in PROBE_C_WS if 4 <= w <= L // 4]
    results = []
    for w in ws:
        # circular window sums via numpy
        best = 0
        for start in range(L):
            s = abs(int(np.sum(u_arr[start:start + w]) if start + w <= L else
                        np.sum(np.concatenate([u_arr[start:], u_arr[:start + w - L]]))))   # noqa: float
            if s > best:
                best = s
        # null
        rank = 0
        remaining = R_NULL
        while remaining > 0:
            bsz = min(100, remaining)
            arr = np.where(rng.random((bsz, L)) < 0.5, -1, 1)          # noqa: float
            for i in range(bsz):
                null_best = 0
                for start in range(L):
                    if start + w <= L:
                        s = abs(int(np.sum(arr[i, start:start + w])))   # noqa: float
                    else:
                        s = abs(int(np.sum(np.concatenate([arr[i, start:], arr[i, :start + w - L]]))))   # noqa: float
                    if s > null_best:
                        null_best = s
                if null_best < best:
                    rank += 1
            remaining -= bsz
        results.append((w, best, rank))
    return results


def probe_c_plant_vec(L, u, rng, w):
    if w > L // 4:
        return None
    planted = list(u)
    window = list(range(w))
    rng_py = random.Random(int(rng.integers(0, 2**31)))
    rng_py.shuffle(window)
    n_force = w * PLANT_NUM // PLANT_DEN
    for idx in window[:n_force]:
        planted[idx] = 1
    u_arr = np.array(planted, dtype=np.int64)                         # noqa: float
    obs = abs(int(np.sum(u_arr[:w])))                               # noqa: float
    rank = 0
    remaining = R_NULL
    while remaining > 0:
        bsz = min(100, remaining)
        arr = np.where(rng.random((bsz, L)) < 0.5, -1, 1)              # noqa: float
        for i in range(bsz):
            null_best = abs(int(np.sum(arr[i, :w])))                 # noqa: float
            if null_best < obs:
                rank += 1
        remaining -= bsz
    return (w, obs, rank)


# ============================================================================
# Probe D -- max-Fourier on Q6 at scale (the prior probe re-run with power)
# ============================================================================
def probe_d(L, u, rng):
    """Max-Fourier: T_D = max_{1<=k<L} |FFT(u)[k]|.  Float FFT is permitted (monotone statistic
    ranked vs null)."""
    u_arr = np.array(u, dtype=np.float64)                            # noqa: float
    full_fft = np.fft.fft(u_arr)                                    # noqa: float
    obs = float(np.max(np.abs(full_fft[1:])))                       # noqa: float
    # null: R draws of random +-1, batch FFT
    rank = 0
    remaining = R_NULL
    while remaining > 0:
        bsz = min(250, remaining)
        arr = np.where(rng.random((bsz, L)) < 0.5, -1.0, 1.0)         # noqa: float
        ffts = np.fft.fft(arr, axis=1)                              # noqa: float
        null_maxes = np.max(np.abs(ffts[:, 1:]), axis=1)            # noqa: float
        rank += int(np.sum(null_maxes < obs))                       # noqa: float
        remaining -= bsz
    return (obs, rank)


def probe_d_plant(L, u, rng):
    """Plant: inject a single Fourier mode at mode k=L//7 with amplitude covering ~PLANT_NUM/PLANT_DEN
    of the sequence; must FIRE."""
    k0 = max(1, L // 7)
    planted = np.array(u, dtype=np.float64)                         # noqa: float
    n_inject = L * PLANT_NUM // PLANT_DEN
    idxs = list(range(L))
    rng_py = random.Random(int(rng.integers(0, 2**31)))
    rng_py.shuffle(idxs)
    # align the first n_inject signs to sign(cos(2*pi*k0*j/L))
    j_idx = 0
    for idx in idxs:
        if j_idx >= n_inject:
            break
        planted[idx] = 1.0 if math.cos(2 * math.pi * k0 * idx / L) >= 0 else -1.0   # noqa: float
        j_idx += 1
    full_fft = np.fft.fft(planted)                                  # noqa: float
    obs = float(np.max(np.abs(full_fft[1:])))                       # noqa: float
    rank = 0
    remaining = R_NULL
    while remaining > 0:
        bsz = min(250, remaining)
        arr = np.where(rng.random((bsz, L)) < 0.5, -1.0, 1.0)         # noqa: float
        ffts = np.fft.fft(arr, axis=1)                              # noqa: float
        null_maxes = np.max(np.abs(ffts[:, 1:]), axis=1)            # noqa: float
        rank += int(np.sum(null_maxes < obs))                       # noqa: float
        remaining -= bsz
    return (obs, rank)


# ============================================================================
# driver
# ============================================================================
def run_prime(p, stratum_label, do_probe_c_windows=True):
    t0 = time.time()
    q6 = build_q6(p)
    if q6 is None:
        print("  SKIP")
        return None
    n   = q6["n"]; m = q6["m"]; eps = q6["eps"]; L = q6["L"]
    u   = q6["u"]; reps = q6["reps"]; d_to_q6idx = q6["d_to_q6idx"]; c = q6["c"]
    if L < MIN_L:
        print("  SKIP: L=%d < MIN_L=%d" % (L, MIN_L))
        return None

    rng = np.random.default_rng(SEED + p)

    sym3_ok = all(c[m * d % n] == c[d] for d in range(1, min(n, 5000)))   # spot-check for large n
    symn_ok = all(c[(-d) % n] == eps * c[d] for d in range(1, min(n, 5000)))
    if not (sym3_ok and symn_ok):
        print("  ABORT: forced symmetry spot-check failed")
        return None

    u_arr = np.array(u, dtype=np.int64)                              # noqa: float

    # Probe A
    a_res   = probe_a_vec(L, u, rng)
    a_ctrl  = probe_a_plant_vec(L, u, rng)

    # Probe B
    iota = build_q6_involution(n, m, reps, d_to_q6idx)
    b_obs  = probe_b_autocorr_vec(L, u_arr, iota)
    b_rank = probe_b_null_rank_vec(L, u_arr, iota, b_obs, rng)
    b_ctrl = probe_b_plant_vec(L, u_arr, iota, rng)
    b_k = []
    for k in PROBE_B_KS:
        rho = build_q6_powk_map(n, reps, d_to_q6idx, k)
        if rho is None:
            continue
        obs  = probe_b_autocorr_vec(L, u_arr, rho)
        rank = probe_b_null_rank_vec(L, u_arr, rho, obs, rng)
        b_k.append((k, obs, rank))

    # Probe C (only the largest few windows for large L, to bound runtime)
    c_res  = probe_c_vec(L, u, rng)
    c_ctrl = None
    if c_res:
        w_last = c_res[-1][0]
        c_ctrl = probe_c_plant_vec(L, u, rng, w_last)

    # Probe D (max-Fourier at scale)
    d_obs_rank = probe_d(L, u, rng)
    d_ctrl     = probe_d_plant(L, u, rng)

    elapsed = time.time() - t0
    return dict(p=p, n=n, L=L, eps=eps, m=m, elapsed=elapsed,
                a_res=a_res, a_ctrl=a_ctrl,
                b_obs=b_obs, b_rank=b_rank, b_ctrl=b_ctrl, b_k=b_k,
                c_res=c_res, c_ctrl=c_ctrl,
                d_obs=d_obs_rank[0], d_rank=d_obs_rank[1], d_ctrl=d_ctrl,
                stratum=stratum_label)


def report(res):
    p = res["p"]; L = res["L"]
    print("  p=%-6d L=%-6d (%.1fs)" % (p, L, res["elapsed"]))
    # Probe A
    if res["a_res"]:
        a_hits = sum(1 for (_, _, rk, _) in res["a_res"] if is_fire(rk))
        a_max  = max((rk for (_, _, rk, _) in res["a_res"]), default=0)
        print("    A: %d/%d q-values at FIRE; max rank %d/%d (%d%%)" %
              (a_hits, len(res["a_res"]), a_max, R_NULL, a_max * 100 // R_NULL))
    else:
        print("    A: (no qualifying q)")
    if res["a_ctrl"]:
        _, _, rk = res["a_ctrl"]
        print("       A-plant: %s" % ("FIRE" if is_fire(rk) else "FAIL"))
    # Probe B
    mk = "<<<" if is_hit(res["b_rank"]) else ("*" if is_fire(res["b_rank"]) else "")
    print("    B d^{-1}: T=%+d rank %d/%d (%d%%)%s" %
          (res["b_obs"], res["b_rank"], R_NULL, res["b_rank"] * 100 // R_NULL, mk))
    if res["b_ctrl"]:
        _, rk = res["b_ctrl"]
        print("       B-plant: %s" % ("FIRE" if is_fire(rk) else "FAIL"))
    b_k_hits = sum(1 for (_, _, rk) in res["b_k"] if is_fire(rk))
    b_k_max  = max((rk for (_, _, rk) in res["b_k"]), default=0)
    print("    B d^k:   %d/%d at FIRE; max rank %d/%d (%d%%)" %
          (b_k_hits, len(res["b_k"]), b_k_max, R_NULL, b_k_max * 100 // R_NULL))
    # Probe C
    if res["c_res"]:
        c_hits = sum(1 for (_, _, rk) in res["c_res"] if is_fire(rk))
        c_max  = max((rk for (_, _, rk) in res["c_res"]), default=0)
        print("    C: %d/%d w-values at FIRE; max rank %d/%d (%d%%)" %
              (c_hits, len(res["c_res"]), c_max, R_NULL, c_max * 100 // R_NULL))
    else:
        print("    C: (no qualifying w)")
    if res["c_ctrl"]:
        _, _, rk = res["c_ctrl"]
        print("       C-plant: %s" % ("FIRE" if is_fire(rk) else "FAIL"))
    # Probe D
    mk = "<<<" if is_hit(res["d_rank"]) else ("*" if is_fire(res["d_rank"]) else "")
    print("    D maxF:  obs=%.1f rank %d/%d (%d%%)%s" %
          (res["d_obs"], res["d_rank"], R_NULL, res["d_rank"] * 100 // R_NULL, mk))
    if res["d_ctrl"]:
        _, rk = res["d_ctrl"]
        print("       D-plant: %s" % ("FIRE" if is_fire(rk) else "FAIL"))
    # control validity
    fails = []
    if res["a_ctrl"] and not is_fire(res["a_ctrl"][2]): fails.append("A")
    if res["b_ctrl"] and not is_fire(res["b_ctrl"][1]): fails.append("B")
    if res["c_ctrl"] and not is_fire(res["c_ctrl"][2]): fails.append("C")
    if res["d_ctrl"] and not is_fire(res["d_ctrl"][1]): fails.append("D")
    if fails:
        print("    !! CONTROL FAIL: %s -- instrument unpowered here" % ",".join(fails))
    print()


def main():
    print("=" * 92)
    print("mu3_subspace_residual_v2  --  scaled-up extension (R=%d, MIN_L=%d)" % (R_NULL, MIN_L))
    print("PREREG: PREREG_mu3_subspace_residual_v2.md  |  SEED=%d" % SEED)
    print("=" * 92)

    # find large primes
    print("\nFinding LARGE stratum primes (p=7 mod 12, #E prime, p in [10^4, 10^5])...")
    large = find_large_primes(10007, 100003, 8)
    print("  found: %s" % (large,))

    all_primes = [("BRIDGE", pp) for pp in BRIDGE_PRIMES] + [("LARGE", pp) for pp in large]

    all_results = []
    for label, p in all_primes:
        print("\n--- %s  p = %d ---" % (label, p))
        res = run_prime(p, label)
        if res is None:
            continue
        report(res)
        all_results.append(res)

    # summary
    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("\n%-8s %-6s %-7s | %s" % ("str", "p", "L", "probe / max-percentile-rank across cells"))
    print("-" * 80)
    for r in all_results:
        parts = []
        # A
        a_max = max((rk for (_, _, rk, _) in r["a_res"]), default=0) if r["a_res"] else 0
        parts.append("A:%3d%%" % (a_max * 100 // R_NULL))
        # B inv
        parts.append("Bi:%3d%%" % (r["b_rank"] * 100 // R_NULL))
        # B k
        bk_max = max((rk for (_, _, rk) in r["b_k"]), default=0) if r["b_k"] else 0
        parts.append("Bk:%3d%%" % (bk_max * 100 // R_NULL))
        # C
        c_max = max((rk for (_, _, rk) in r["c_res"]), default=0) if r["c_res"] else 0
        parts.append("C:%3d%%" % (c_max * 100 // R_NULL))
        # D
        parts.append("D:%3d%%" % (r["d_rank"] * 100 // R_NULL))
        print("%-8s %-6d %-7d | %s" % (r["stratum"], r["p"], r["L"], "  ".join(parts)))

    # overall verdict
    print("\n--- overall ---")
    powered = [r for r in all_results if r["stratum"] == "LARGE"]
    total_d_cells = len(powered)
    d_hits = sum(1 for r in powered if is_hit(r["d_rank"]))
    bi_hits = sum(1 for r in powered if is_hit(r["b_rank"]))
    bk_hits = sum(1 for r in powered for (_, _, rk) in r["b_k"] if is_hit(rk))
    total_bk = sum(len(r["b_k"]) for r in powered)
    print("  LARGE stratum: %d primes" % total_d_cells)
    print("  Probe D 99%%-hits: %d/%d" % (d_hits, total_d_cells))
    print("  Probe B-inv 99%%-hits: %d/%d" % (bi_hits, total_d_cells))
    print("  Probe B-d^k 99%%-hits: %d/%d (expected by chance: %d)" %
          (bk_hits, total_bk, total_bk // 100))


if __name__ == "__main__":
    main()
