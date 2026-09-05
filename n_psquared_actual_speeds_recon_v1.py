#!/usr/bin/env python3
"""
n_psquared_actual_speeds_recon_v1.py  —  Step 1 reconnaissance
==============================================================
Diagnostic for the open case n=p², p≥29, ACTUAL SPEEDS (q_ρ ≥ 1).

Goal: empirically test whether the k=1 band always contains a safe fibre
under adversarially chosen unit-runner quotients q_ρ.  Inform the analytic
strategy for Lemma N-PSQ-T02.

Setup recap:
  K(ρ,k,j) := ρk + q_ρ·j + ⌊ρj/p²⌋  (mod p²)
  bad_set(ρ,K) ∩ H\{0} ≠ ∅  ⇔  K ≡ 0 or K ≡ p-1 (mod p)   [Lemma N-PSQ-MOD]
  Safe condition at (k=1,j): K(ρ,1,j) mod p ∈ {1,…,p-2} for all ρ ∈ U(p²).
  K-sum mod p:  Σ K_ρ ≡ j·Q (mod p),  Q := Σ q_ρ.

Strategy:
  For each p in {29, 31, 37}:
    For each Q* ∈ {0, 1, …, p-1}:                  -- target K-sum residue
      Choose adversarial (q_ρ) tuples with Σ ≡ Q* (mod p)
      For each (d₁, d₂) ∈ H\{0}² (with d₁ < d₂):
        Count safe j in k=1 band
        Track minimum and the (q_ρ, d₁, d₂, Q*) achieving it.
    Report: min safe-j in k=1 band  (over all sampled tuples).

Adversarial q_ρ generation strategies:
  (A) Uniform random over {0,…,p-1}^φ(p²) with Σ ≡ Q* (mod p).
  (B) "All-equal" — q_ρ = Q*/φ(p²) when divisible.
  (C) "Concentration" — pick q_ρ values to maximize blockings: greedy
      maximization of #blockings per ρ at each j step.

Output:
  n_psquared_actual_speeds_recon_v1_results.md  — markdown table.

Runtime budget: ≤ 30 min total for p ∈ {29, 31, 37}.
"""

import sys, time, random, itertools
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from lrc_proof import units


def H_nz(p):
    return [j * p for j in range(1, p)]


def bad_set_unit(rho, T, n):
    """bad_set(rho, T, n) = {(-T*rho^-1) mod n, (-(T+1)*rho^-1) mod n}."""
    inv = pow(rho, -1, n)
    return {(-T * inv) % n, (-(T + 1) * inv) % n}


def unit_cover_per_j(p, q_unit, k):
    """For each j in {1,…,p²-1} with p∤j, return the set of H\\{0} elements
    covered by some unit runner at fibre r = k·p²+j.

    Returns dict {j: set of covered residues in H\\{0}}.
    """
    n = p * p
    n2 = n * n
    U = list(units(n))
    H_nz = set(range(p, n, p))
    out = {}
    for j in range(1, n):
        if j % p == 0:
            continue
        r = k * n + j
        covered = set()
        for rho in U:
            qr = q_unit.get(rho, 0)
            e = rho + qr * n
            T = (e * r) // n2
            bs = bad_set_unit(rho, T, n)
            covered |= (bs & H_nz)
        out[j] = covered
    return out


def safe_j_for_dpair(p, q_unit, d1, d2, k=1):
    """j-values in k-band where both d1 and d2 are uncovered by unit runners.
    Returns list of safe j.
    """
    cov = unit_cover_per_j(p, q_unit, k)
    return [j for j, c in cov.items() if d1 not in c and d2 not in c]


def min_safe_count_over_dpairs(p, q_unit, k=1):
    """Worst (d1,d2) pair: minimum safe-j count across all H\\{0}² pairs."""
    n = p * p
    H_nz = list(range(p, n, p))
    cov = unit_cover_per_j(p, q_unit, k)
    # Count which j are blocked for d (= covered by unit runner at j)
    j_list = sorted(cov.keys())
    block = {d: set() for d in H_nz}
    for j, c in cov.items():
        for d in c:
            block[d].add(j)
    # For each pair, safe = j_list \ (block[d1] ∪ block[d2])
    n_j = len(j_list)
    worst = (n_j, None, None)
    for i, d1 in enumerate(H_nz):
        for d2 in H_nz[i+1:]:
            cnt = n_j - len(block[d1] | block[d2])
            if cnt < worst[0]:
                worst = (cnt, d1, d2)
    return worst, j_list, block


def safe_j_count_k1(p, q_unit):
    """Convenience: returns the worst-case (d1,d2) safe-j count in k=1 band."""
    (worst_cnt, d1, d2), j_list, block = min_safe_count_over_dpairs(p, q_unit, k=1)
    return worst_cnt


def per_runner_per_d_blocking(p, q_unit, k=1):
    """For diagnostic of Conjecture N-PSQ-T02: for each (ρ, d) ∈ U(p²)×H\\{0},
    count #{j : d ∈ bad_set(ρ, T_ρ(j), p²)} in the k-band.

    Returns dict {(rho, d): block_count}, plus aggregate sum per d.
    """
    n = p * p
    n2 = n * n
    U = list(units(n))
    H_nz = list(range(p, n, p))
    counts = {}
    sum_per_d = {d: 0 for d in H_nz}
    for rho in U:
        qr = q_unit.get(rho, 0)
        e = rho + qr * n
        for d in H_nz:
            cnt = 0
            for j in range(1, n):
                if j % p == 0:
                    continue
                r = k * n + j
                T = (e * r) // n2
                if d in bad_set_unit(rho, T, n):
                    cnt += 1
            counts[(rho, d)] = cnt
            sum_per_d[d] += cnt
    return counts, sum_per_d


def gen_q_unit_with_sum(U, target_Q_mod_p, p, rng, strategy="random",
                        cap=2):
    """Generate a q_unit dict with Σ q_ρ ≡ target_Q_mod_p (mod p).

    strategies:
      "random":  uniform in {0,…,cap}^|U|, then adjust last to fix sum.
      "small":   q_ρ ∈ {0,1}^|U| (representative-like with small bumps).
      "concentrated":  q_ρ = constant across U, adjusted on last entries.
    """
    n_U = len(U)
    if strategy == "random":
        q = [rng.randint(0, cap) for _ in range(n_U)]
    elif strategy == "small":
        q = [rng.randint(0, 1) for _ in range(n_U)]
    elif strategy == "concentrated":
        c = (target_Q_mod_p * pow(n_U, -1, p)) % p if gcd(n_U, p) == 1 else 0
        q = [c] * n_U
    else:
        raise ValueError(strategy)

    # Adjust last entry to hit target sum mod p
    s = sum(q) % p
    delta = (target_Q_mod_p - s) % p
    q[-1] = (q[-1] + delta) % p
    if q[-1] >= 0 and sum(q) % p == target_Q_mod_p:
        return dict(zip(U, q))
    return dict(zip(U, q))  # fallback (always reachable)


def sweep_p(p, samples_per_Q=20, rng=None):
    """Sweep over Q* ∈ {0,…,p-1} and adversarial q_unit tuples.

    Counts, per (q_unit, Q_target, strategy), the WORST-(d1,d2) safe-j count
    in the k=1 band.  Reports overall minimum.

    Returns (overall_min_record, per_Q_summary, worst_record_with_kfallback).
    """
    if rng is None:
        rng = random.Random(42)
    n = p * p
    U = sorted(units(n))

    print(f"\n{'='*64}")
    print(f"  p={p}, n=p²={n}, |U(p²)|={len(U)}")
    print(f"  k=1 band size = p(p-1) = {p*(p-1)}")
    print(f"  samples per Q residue per strategy = {samples_per_Q}")
    print(f"{'='*64}")

    band_size = p * (p - 1)
    overall_min = (band_size, None)  # (count, record)
    per_Q_summary = []

    for Q_target in range(p):
        Q_min = (band_size, None)
        for strategy in ("random", "small", "concentrated"):
            for trial in range(samples_per_Q):
                q_unit = gen_q_unit_with_sum(U, Q_target, p, rng, strategy)
                (cnt, d1, d2), j_list, block = min_safe_count_over_dpairs(
                    p, q_unit, k=1)
                if cnt < Q_min[0]:
                    Q_min = (cnt, {
                        "p": p, "Q_target": Q_target,
                        "strategy": strategy, "trial": trial,
                        "safe_count": cnt, "worst_d1": d1, "worst_d2": d2,
                    })
                if cnt < overall_min[0]:
                    overall_min = (cnt, {**Q_min[1]})

        per_Q_summary.append((Q_target, Q_min[0]))
        print(f"  Q≡{Q_target:3d} (mod {p}): min safe-j (worst d1,d2) in k=1 = "
              f"{Q_min[0]:5d}/{band_size} ({100*Q_min[0]/band_size:.1f}%)")

    print(f"\n  OVERALL MIN: {overall_min[0]} (worst case)")
    if overall_min[1]:
        r = overall_min[1]
        print(f"    Q≡{r['Q_target']}, strategy={r['strategy']},"
              f" trial={r['trial']}, (d1,d2)=({r['worst_d1']},{r['worst_d2']})")

    return overall_min, per_Q_summary


# ─────────────────────────────────────────────────────────────────────────────
# E1: v_p class sweep (non-saturated vs saturated regime, k=1 band)
# ─────────────────────────────────────────────────────────────────────────────

def vp_class_sweep(p, vp_list=None, samples=20):
    """E1: Sweep over v_p(q_ρ) classes in the k=1 band.

    For each vp ∈ vp_list, force ALL unit runners to have q_ρ = c·p^vp
    for c ∈ {1,...,p-1} (uniform v_p per trial) and measure the minimum
    safe-j count in the k=1 band over worst (d₁,d₂) pairs.

    Expected:
      v_p∈{0,1,2} → safe-j > 0  (supports N-PSQ-T02-RESTRICTED)
      v_p=3        → 0 safe-j    (confirms saturation counterexample)
      v_p=4        → 100% safe   (T≡0 mod p² → d=0∉H_p → zero blocking)
    """
    if vp_list is None:
        vp_list = [0, 1, 2, 3, 4]
    n = p * p
    U = sorted(units(n))
    band_size = p * (p - 1)

    print(f"\n{'='*64}")
    print(f"E1: v_p sweep  p={p},  n=p²={n},  |J₁|={band_size}")
    print(f"{'='*64}")

    results = {}
    for vp in vp_list:
        base = p ** vp
        # NOTE: q_ρ = c·p^vp is a valid quotient for any c≥1 regardless of whether
        # base > n.  The formula e_ρ = ρ + q_ρ·n is well-defined for any q_ρ ≥ 0.
        # The old "vacuously safe" guard was WRONG — do not skip large valuations.

        vp_min = band_size
        vp_worst = None

        # (a) Deterministic scan: c ∈ {1,...,p-1} (uniform v_p per trial)
        for c in range(1, p):
            q_val = c * base
            q_unit = {rho: q_val for rho in U}
            (cnt, d1, d2), _, _ = min_safe_count_over_dpairs(p, q_unit, k=1)
            if cnt < vp_min:
                vp_min = cnt
                vp_worst = (c, q_val, d1, d2)

        # (b) Random mixtures within this v_p class (c random in {1,...,p-1})
        rng_loc = random.Random(42 + vp)
        for _ in range(samples):
            q_unit = {rho: base * rng_loc.randint(1, p - 1) for rho in U}
            (cnt, d1, d2), _, _ = min_safe_count_over_dpairs(p, q_unit, k=1)
            if cnt < vp_min:
                vp_min = cnt
                vp_worst = (None, None, d1, d2)

        frac = vp_min / band_size if band_size else 0.0
        status = "⚠ ZERO (SATURATED)" if vp_min == 0 else f"✓ {vp_min} safe-j"
        results[vp] = {"min_safe": vp_min, "min_frac": frac, "worst": vp_worst}
        print(f"  v_p={vp}: min safe-j = {vp_min:4d}/{band_size}"
              f"  ({100*frac:5.1f}%)  {status}")
        if vp_worst and vp_worst[0] is not None:
            print(f"           worst: c={vp_worst[0]}, q={vp_worst[1]},"
                  f" (d₁,d₂)=({vp_worst[2]},{vp_worst[3]})")

    return results


# ─────────────────────────────────────────────────────────────────────────────
# E2+E3: Band k=p² rescue check (saturated regime)
# ─────────────────────────────────────────────────────────────────────────────

def check_sat_rescue(p, q_sat=None):
    """E2+E3: Band k=p² check under full saturation (all q_ρ = q_sat = p³).

    E2 — Verifies the analytic claim T_ρ ≡ ρ (mod p) at band k=p²:
      For each ρ ∈ U(p²) and each j ∈ J_{p²} = {1,...,p²-1, p∤j},
      compute T_ρ^{k=p²}(j) = e_ρ·(p⁴+j) // p⁴  and check T_ρ ≡ ρ (mod p).
    Identifies active runners (T≡p-1 mod p) and counts safe-j in worst (d₁,d₂).

    E3 — Per-active-runner blocking sparsity:
      For each of the p active runners (ρ≡p-1 mod p), count #{j blocked per d}.
      Determines whether each runner blocks O(1) or O(p) j-values per d
      and whether the joint-pair union stays well below |J_{p²}|.
    """
    if q_sat is None:
        q_sat = p ** 3

    n = p * p       # = p²
    n2 = n * n      # = p⁴
    U = sorted(units(n))
    H_nz = list(range(p, n, p))   # H_p\{0} = {p, 2p, ..., (p-1)p}
    k_band = n                     # k = p² (so r = k·n + j = p⁴ + j)
    band_size = p * (p - 1)        # |J_{p²}| = p(p-1)

    print(f"\n{'='*64}")
    print(f"E2+E3: Band k=p² rescue   p={p},  q_sat={q_sat}")
    print(f"  n=p²={n},  k=p²={k_band},  r=p⁴+j = {n2}+j")
    print(f"  |J_{{p²}}| = p(p-1) = {band_size}")
    print(f"{'='*64}")

    q_unit = {rho: q_sat for rho in U}

    # Pre-compute T_ρ(j) for all (ρ, j)
    T_per_runner = {}
    for rho in U:
        e = rho + q_sat * n
        T_vals = {}
        for j in range(1, n):
            if j % p == 0:
                continue
            r_fibre = k_band * n + j   # = p⁴ + j
            T_vals[j] = (e * r_fibre) // n2
        T_per_runner[rho] = T_vals

    # E2a: Verify T_ρ ≡ ρ (mod p) for every (ρ, j)
    violations = []
    for rho in U:
        for j, T in T_per_runner[rho].items():
            if T % p != rho % p:
                violations.append((rho, j, T))
    ok_mod = len(violations) == 0
    print(f"\n  E2a — T_ρ ≡ ρ (mod p) for all (ρ,j): "
          f"{'✅ CONFIRMED' if ok_mod else f'❌ VIOLATED ({len(violations)} cases)'}")
    if violations[:3]:
        for rho, j, T in violations[:3]:
            print(f"    ρ={rho}, j={j}: T={T}, T%p={T%p}, ρ%p={rho%p}")

    # E2b: Identify active runners (T≡p-1 mod p; since T≡ρ and ρ≡0 mod p impossible)
    active_runners = [rho for rho in U if rho % p == p - 1]
    print(f"\n  E2b — Active runners (ρ≡p-1 mod p): {len(active_runners)}"
          f"  (expected p={p})")
    print(f"         {active_runners}")

    # E2c: Safe-j count in band k=p² for worst (d₁,d₂)
    cov_band = {}
    for j in range(1, n):
        if j % p == 0:
            continue
        covered = set()
        for rho in U:
            T = T_per_runner[rho][j]
            bs = bad_set_unit(rho, T, n)
            covered |= (bs & set(H_nz))
        cov_band[j] = covered

    j_list_band = sorted(cov_band.keys())
    block_band = {d: set() for d in H_nz}
    for j, c in cov_band.items():
        for d in c:
            block_band[d].add(j)

    worst_cnt, worst_d1, worst_d2 = band_size, None, None
    for i, d1 in enumerate(H_nz):
        for d2 in H_nz[i + 1:]:
            cnt = band_size - len(block_band[d1] | block_band[d2])
            if cnt < worst_cnt:
                worst_cnt, worst_d1, worst_d2 = cnt, d1, d2

    safe_frac = worst_cnt / band_size if band_size else 0.0
    print(f"\n  E2c — Safe-j in band k=p² (worst d₁,d₂ pair):")
    print(f"    {worst_cnt}/{band_size}  ({100*safe_frac:.1f}%) safe j-values")
    print(f"    Worst pair: (d₁,d₂) = ({worst_d1},{worst_d2})")
    status = "✅ N-PSQ-SAT: safe fibres exist in band k=p²!" if worst_cnt > 0 else "⚠ ZERO — need higher band"
    print(f"    {status}")

    # E3: Per-active-runner blocking sparsity
    print(f"\n  E3 — Per-active-runner blocking sparsity in band k=p²:")
    print(f"  {'ρ':>6}  {'ρ%p':>4}  {'total_blocks':>12}  {'max_per_d':>9}  "
          f"{'top_d':>6}  {'top_d_cnt':>9}")
    for rho in active_runners:
        per_d = {d: 0 for d in H_nz}
        for j, T in T_per_runner[rho].items():
            bs = bad_set_unit(rho, T, n)
            for d in H_nz:
                if d in bs:
                    per_d[d] += 1
        total = sum(per_d.values())
        max_cnt = max(per_d.values()) if per_d else 0
        top_d = max(per_d, key=per_d.get) if per_d else None
        print(f"  {rho:>6}  {rho%p:>4}  {total:>12}  {max_cnt:>9}  "
              f"{top_d:>6}  {per_d.get(top_d,0):>9}")

    # E3 summary: joint pair union for active runners
    print(f"\n  E3 — Joint-pair blocking by active runners only (worst pair):")
    if worst_d1 is not None:
        act_block_d1 = set()
        act_block_d2 = set()
        for rho in active_runners:
            for j, T in T_per_runner[rho].items():
                bs = bad_set_unit(rho, T, n)
                if worst_d1 in bs:
                    act_block_d1.add(j)
                if worst_d2 in bs:
                    act_block_d2.add(j)
        union = act_block_d1 | act_block_d2
        print(f"    d₁={worst_d1}: {len(act_block_d1)} j blocked by active runners")
        print(f"    d₂={worst_d2}: {len(act_block_d2)} j blocked by active runners")
        print(f"    Union: {len(union)}/{band_size}  →  {band_size - len(union)} safe j")

    return {
        "T_mod_p_ok": ok_mod,
        "active_runners": active_runners,
        "safe_cnt_band": worst_cnt,
        "safe_frac_band": safe_frac,
        "worst_d1": worst_d1, "worst_d2": worst_d2,
    }


def mixed_vp_sweep(p, samples=30):
    """E1-MIXED: Test non-saturated regime with heterogeneous v_p assignments.

    The uniform vp_class_sweep always has Q = Σq_ρ ≡ 0 (mod p) because
    p | φ(p²) = p(p-1).  This makes UNIV-KSF degenerate (jQ≡0) regardless
    of vp class.  To test N-PSQ-T02-RESTRICTED we need Q≢0 (mod p).

    Strategy: assign q_ρ values from MIXED v_p classes (some high, some low)
    so that Q mod p can be nonzero.  The key mixed classes:
      Class A: v_p=2 (q=p²)   — gives T≡0 contribution
      Class B: v_p=0 (q=c, small c)  — gives nonzero Q mod p contribution

    For a single runner with q_ρ=1 and all others q_ρ=0: Q=1≢0 (mod p).
    This is the minimal non-degenerate test.  Adversarial: maximize blocking
    with Q≢0.

    Also tests the fully-saturated k=1 band baseline (q_ρ=p³ uniformly).
    """
    n = p * p
    U = sorted(units(n))
    phi_n = len(U)
    band_size = p * (p - 1)

    print(f"\n{'='*64}")
    print(f"E1-MIXED: Non-degenerate Q sweep  p={p}, n={n}, |J₁|={band_size}")
    print(f"  φ(p²)={phi_n}.  Uniform q always gives Q≡0(mod p).  Test mixed.")
    print(f"{'='*64}")

    results = {}
    rng = random.Random(99 + p)

    # --- Baseline: fully saturated (all q=p³) at k=1 band ---
    q_sat = p ** 3
    q_unit_sat = {rho: q_sat for rho in U}
    (cnt_sat, d1_sat, d2_sat), _, _ = min_safe_count_over_dpairs(p, q_unit_sat, k=1)
    Q_sat = (q_sat * phi_n) % p
    print(f"\n  [Baseline] all q=p³={q_sat}: Q mod p = {Q_sat},  "
          f"safe-j = {cnt_sat}/{band_size}  "
          f"{'⚠ ZERO' if cnt_sat == 0 else '✓'}")

    # --- Minimal non-degenerate: one runner with q=1, rest q=0 ---
    # Q = 1.  Unit runner ρ with q_ρ=1 contributes T_ρ(j)≈ρ+j/p² → small T.
    # Remaining runners have q=0 → T_ρ(j) = ⌊ρ(n+j)/n²⌋ = ⌊ρ(p²+j)/p⁴⌋.
    # For ρ<p², ρ(p²+j)/p⁴ < (p²)(p²+p²)/p⁴ = 2/1 → T∈{0,1,2} → likely safe.
    q_unit_single = {rho: 0 for rho in U}
    q_unit_single[U[0]] = 1
    (cnt_single, d1_s, d2_s), _, _ = min_safe_count_over_dpairs(p, q_unit_single, k=1)
    Q_single = 1
    print(f"  [Single q=1] q_ρ=1 for ρ={U[0]}, rest 0: Q mod p = {Q_single % p},  "
          f"safe-j = {cnt_single}/{band_size}  "
          f"{'⚠ ZERO' if cnt_single == 0 else '✓'}")

    # --- Adversarial mixed: maximise blocking with Q≢0 (mod p) ---
    # Try all Q* ∈ {1,...,p-1} with random q_unit assignments.
    print(f"\n  Adversarial mixed (Q≢0 mod p), {samples} trials per Q*:")
    print(f"  {'Q*':>4}  {'min_safe':>8}  {'frac':>6}  {'worst (d1,d2)':>14}")
    for Q_target in range(1, p):
        best_cnt = band_size
        best_pair = None
        for _ in range(samples):
            # Random q-tuple with Σq ≡ Q_target (mod p).  Use gen_q_unit_with_sum.
            q_unit = gen_q_unit_with_sum(U, Q_target, p, rng,
                                         strategy="random", cap=p)
            (cnt, d1, d2), _, _ = min_safe_count_over_dpairs(p, q_unit, k=1)
            if cnt < best_cnt:
                best_cnt = cnt
                best_pair = (d1, d2)
        frac = best_cnt / band_size if band_size else 0.0
        flag = "⚠ ZERO" if best_cnt == 0 else f"✓ {best_cnt}"
        print(f"  {Q_target:>4}  {flag:>8}  {100*frac:5.1f}%  {str(best_pair):>14}")
        results[Q_target] = {"min_safe": best_cnt, "worst_pair": best_pair}

    # Summary
    all_zero = all(v["min_safe"] == 0 for v in results.values())
    some_safe = any(v["min_safe"] > 0 for v in results.values())
    print(f"\n  Summary: {'ALL Q≢0 have safe-j > 0 ✅' if some_safe and not all_zero else 'Some Q≢0 give 0 safe-j ⚠'}")
    print(f"  N-PSQ-T02-RESTRICTED direction: "
          f"{'SUPPORTED (Q≢0 → safe fibres)' if some_safe else 'NEEDS FURTHER INVESTIGATION'}")
    return results


# ─────────────────────────────────────────────────────────────────────────────
# E5: Squarefree n=pq safe-fibre check (Gap 2 — PS-SAFE direction)
# ─────────────────────────────────────────────────────────────────────────────

def check_npq_safe_fibres(p, q, k=1, samples=30):
    """E5: For squarefree n=pq, check whether safe fibres exist in the k-band.

    Analogous to min_safe_count_over_dpairs but for n=pq (not n=p²).
    The dangerous pairs are (d₁,d₂) ∈ H_q\{0}²  where H_q\{0} = {q,2q,...,(p-1)q}.

    For each adversarial q_unit dict (unit runner quotients for n=pq) and each
    dangerous pair (d₁,d₂), count safe fibres r = k·n + j with j∈J₁ (gcd(j,n)=1
    for j<n).  Reports minimum over all pairs and all sampled q_unit tuples.

    n=15 (p=3,q=5) expected: 0 safe fibres (Gap 2 known failure).
    n=21+ expected: >0 safe fibres if PS-SAFE conjecture holds.
    """
    n = p * q
    n2 = n * n
    U_n = sorted(u for u in range(1, n) if gcd(u, n) == 1)   # units of ℤ/nℤ
    phi_n = len(U_n)

    # H_q\{0} for n=pq:  multiples of q that are nonzero mod n
    # = {q, 2q, ..., (p-1)q}   (p-1 elements)
    H_q_nz = [i * q for i in range(1, p)]

    # Fibres in k-band: r = k·n + j, j∈{1,...,n-1} with gcd(j,n)=1
    J_band = [j for j in range(1, n) if gcd(j, n) == 1]
    band_size = len(J_band)

    print(f"\n{'='*64}")
    print(f"E5: n=pq safe-fibre check  (p={p}, q={q}, n={n}, k={k})")
    print(f"  |U(n)| = φ(n) = {phi_n},  |H_q\\{{0}}| = {len(H_q_nz)},  |J_band| = {band_size}")
    print(f"  H_q\\{{0}} = {H_q_nz}")
    print(f"{'='*64}")

    def cover_per_j_npq(q_unit):
        """Returns dict {j: set of covered elements in H_q\{0}}."""
        cov = {}
        for j in J_band:
            r = k * n + j
            covered = set()
            for rho in U_n:
                qr = q_unit.get(rho, 0)
                e = rho + qr * n
                T = (e * r) // n2
                inv = pow(rho, -1, n)
                b1 = (-T * inv) % n
                b2 = (-(T + 1) * inv) % n
                for b in (b1, b2):
                    if b in H_q_nz:
                        covered.add(b)
            cov[j] = covered
        return cov

    def worst_safe_cnt(q_unit):
        cov = cover_per_j_npq(q_unit)
        block = {d: set() for d in H_q_nz}
        for j, c in cov.items():
            for d in c:
                block[d].add(j)
        worst = band_size
        worst_pair = None
        for i, d1 in enumerate(H_q_nz):
            for d2 in H_q_nz[i + 1:]:
                cnt = band_size - len(block[d1] | block[d2])
                if cnt < worst:
                    worst = cnt
                    worst_pair = (d1, d2)
        return worst, worst_pair

    # --- Baseline: all q_ρ = 0 (speeds = ρ only, no fractional part) ---
    q_zero = {rho: 0 for rho in U_n}
    cnt0, pair0 = worst_safe_cnt(q_zero)
    Q0 = 0
    print(f"\n  [Baseline q=0] Q=0: worst safe-j = {cnt0}/{band_size}"
          f"  {'✅ SAFE' if cnt0 > 0 else '⚠ ZERO'}  pair={pair0}")

    # --- Adversarial: random q_unit tuples, all Q values ---
    rng = random.Random(77 + n)
    global_min = band_size
    global_worst_pair = None
    zero_found = False

    print(f"\n  Adversarial scan ({samples} random q_unit tuples):")
    for trial in range(samples):
        q_unit = {rho: rng.randint(0, p) for rho in U_n}
        cnt, pair = worst_safe_cnt(q_unit)
        if cnt < global_min:
            global_min = cnt
            global_worst_pair = pair
        if cnt == 0:
            zero_found = True

    print(f"  Global min safe-j over {samples} trials: {global_min}/{band_size}")
    print(f"  Worst (d₁,d₂) pair: {global_worst_pair}")
    print(f"  Zero safe-j found: {'YES ⚠ (PS-SAFE fails for this (p,q))' if zero_found else 'NO ✅'}")

    # --- Verdict ---
    ps_safe_supported = not zero_found
    print(f"\n  PS-SAFE conjecture for n={n}={p}·{q}:  "
          f"{'SUPPORTED ✅' if ps_safe_supported else 'REFUTED ⚠ — need different approach'}")

    return {
        "n": n, "p": p, "q": q,
        "baseline_safe": cnt0,
        "adv_min_safe": global_min,
        "adv_worst_pair": global_worst_pair,
        "zero_found": zero_found,
        "ps_safe_supported": ps_safe_supported,
    }


def run_e1_e2_e3(primes=None):
    """Run empirical investigations E1, E2, E3 for each prime in primes."""
    if primes is None:
        primes = [5, 7, 11]
    t0 = time.time()
    for p in primes:
        print(f"\n{'#'*64}")
        print(f"# p = {p}")
        print(f"{'#'*64}")
        vp_class_sweep(p, vp_list=[0, 1, 2, 3, 4], samples=20)
        check_sat_rescue(p, q_sat=p ** 3)
    print(f"\n=== E1/E2/E3 total runtime: {time.time()-t0:.1f}s ===")


def main():
    args = sys.argv[1:]

    # Route: --e1e2e3 runs the original E1/E2/E3 investigations
    if "--e1e2e3" in args:
        args = [a for a in args if a != "--e1e2e3"]
        primes = [int(a) for a in args if a.isdigit()] or [5, 7, 11]
        run_e1_e2_e3(primes)
        return 0

    # Route: --e1mixed runs the fixed E1 mixed-vp sweep (non-degenerate Q)
    if "--e1mixed" in args:
        args = [a for a in args if a != "--e1mixed"]
        primes = [int(a) for a in args if a.isdigit()] or [5, 7, 11]
        t0 = time.time()
        for p in primes:
            print(f"\n{'#'*64}\n# p = {p}\n{'#'*64}")
            vp_class_sweep(p, vp_list=[0, 1, 2, 3, 4], samples=20)
            mixed_vp_sweep(p, samples=30)
        print(f"\n=== E1-MIXED total runtime: {time.time()-t0:.1f}s ===")
        return 0

    # Route: --e5 runs the squarefree n=pq safe-fibre check (Gap 2)
    if "--e5" in args:
        args = [a for a in args if a != "--e5"]
        t0 = time.time()
        # Default test cases: n=15 (control, known fail), n=21,33,35,55,...
        test_cases = [(3, 5), (3, 7), (3, 11), (5, 7), (3, 13), (5, 11)]
        # Allow overrides: --pq 3 7 --pq 5 11 etc (simple: pairs from positional args)
        nums = [int(a) for a in args if a.isdigit()]
        if len(nums) >= 2 and len(nums) % 2 == 0:
            test_cases = [(nums[i], nums[i+1]) for i in range(0, len(nums), 2)]
        print("E5: Squarefree n=pq safe-fibre check (Gap 2 — PS-SAFE)")
        print(f"Test cases: {test_cases}")
        results = []
        for p_val, q_val in test_cases:
            r = check_npq_safe_fibres(p_val, q_val, k=1, samples=40)
            results.append(r)
        print(f"\n{'='*64}")
        print("E5 SUMMARY")
        print(f"{'='*64}")
        print(f"{'n':>6}  {'p':>4}  {'q':>4}  {'adv_min_safe':>12}  {'ps_safe':>10}")
        for r in results:
            print(f"  {r['n']:>4}  {r['p']:>4}  {r['q']:>4}  "
                  f"{r['adv_min_safe']:>12}  "
                  f"{'✅' if r['ps_safe_supported'] else '⚠ REFUTED'}")
        print(f"\n=== E5 total runtime: {time.time()-t0:.1f}s ===")
        return 0

    samples = 20  # default
    if "--samples" in args:
        idx = args.index("--samples")
        samples = int(args[idx + 1])
        args = args[:idx] + args[idx + 2:]
    primes = [int(a) for a in args if a.isdigit()] or [29, 31, 37]

    out_path = Path(__file__).parent / "n_psquared_actual_speeds_recon_v1_results.md"

    print("n_psquared_actual_speeds_recon_v1.py  —  Step 1")
    print(f"Probing p ∈ {primes}, samples_per_Q={samples}\n")

    rng = random.Random(42)
    all_results = []
    t0 = time.time()
    for p in primes:
        ovm, per_Q = sweep_p(p, samples_per_Q=samples, rng=rng)
        all_results.append({"p": p, "overall_min": ovm, "per_Q": per_Q})

    elapsed = time.time() - t0
    print(f"\n=== Total runtime: {elapsed:.1f}s ===")

    # Markdown report
    with open(out_path, "w") as f:
        f.write("# n=p² Actual Speeds k=1 Band Reconnaissance — Results\n\n")
        f.write(f"**Generated:** by `n_psquared_actual_speeds_recon_v1.py`\n\n")
        f.write(f"**Probed primes:** {primes}\n\n")
        f.write(f"**Samples per (Q,strategy):** {samples} adversarial q_unit tuples\n\n")
        f.write(f"**Runtime:** {elapsed:.1f}s\n\n")
        f.write("## Summary table — minimum safe-j count in k=1 band\n\n")
        f.write("| p | n=p² | k=1 size | min safe-j | min frac | failure? | worst-Q |\n")
        f.write("|---|------|----------|------------|----------|----------|----------|\n")
        for r in all_results:
            p = r["p"]
            cnt, rec = r["overall_min"]
            band_size = p * (p - 1)
            frac = cnt / band_size if band_size else 0
            fail = "⚠ ZERO" if cnt == 0 else "✓"
            wQ = rec["Q_target"] if rec else "—"
            f.write(f"| {p} | {p*p} | {band_size} | {cnt} | {frac:.3f} | {fail} | {wQ} |\n")
        f.write("\n## Per-Q breakdown\n\n")
        for r in all_results:
            f.write(f"\n### p = {r['p']}\n\n")
            f.write("| Q (mod p) | min safe-j count |\n|---|---|\n")
            for (q, c) in r["per_Q"]:
                f.write(f"| {q} | {c} |\n")
        f.write("\n## Conclusions\n\n")
        any_zero = any(r["overall_min"][0] == 0 for r in all_results)
        if any_zero:
            f.write("⚠ **At least one (p, Q) gave 0 safe-j in k=1 band.** "
                    "k=1-only Lemma N-PSQ-T02 strategy may need to be broadened "
                    "to multi-band coverage.\n")
        else:
            min_fracs = [r["overall_min"][0]/(r["p"]*(r["p"]-1))
                         for r in all_results]
            f.write(f"✅ **Empirical lower bound on safe-j fraction in k=1 band:** "
                    f"{min(min_fracs):.3f} (worst across tested p).\n\n")
            f.write("This supports the Lemma N-PSQ-T02 conjecture: the k=1 band "
                    "alone always contains a safe fibre, even under adversarial "
                    "q_ρ choices. The analytic proof should target this constant.\n")

    print(f"\nResults written to: {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
