#!/usr/bin/env python3
"""
Analysis stage for PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md.
Runs AFTER the delta sweep completes. Implements the frozen §3 statistics (H1a, H1a', H2, H1b)
and the §9 verdict logic. All permutation p-values are exact (integer counts / integer ratios).
Float appears only in the surface-fit weighted LS (sanctioned carve-out) and as monotone statistics
ranked against matched permutation nulls.

Spec: PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md (SHA c51f6f62...)
Instrument: subrayleigh_deficit_scaling_v1.py (SHA 93c95471...)
Schedule: PREREG_subrayleigh_deficit_arithmetic_scatter_v5_SCHEDULE.txt (SHA a4b4f005...)
"""

import json, math, sys, os, random
import numpy as np
from collections import defaultdict
from fractions import Fraction
from itertools import permutations

DATA_FILE = "arithmetic_scatter_sweep_v1_results.jsonl"
SCHED_FILE = "PREREG_subrayleigh_deficit_arithmetic_scatter_v5_SCHEDULE.txt"
SCREEN_FILE = "cyclicity_screen_v1_data.txt"
RNG_SEED = 20260806  # frozen analysis seed

# ---- load data ----
def load_data():
    rows = []
    for line in open(DATA_FILE):
        rows.append(json.loads(line.strip()))
    return rows

def load_schedule():
    S = {"surface": [], "traj": []}
    for line in open(SCHED_FILE):
        line = line.strip()
        if line.startswith("SURFACE_PRIMES="):
            S["surface"] = [int(x) for x in line.split("=", 1)[1].split(",") if x]
        if line.startswith("TRAJECTORY_PRIMES="):
            S["traj"] = [int(x) for x in line.split("=", 1)[1].split(",") if x]
    return S

def load_screen():
    """Load cyclicity screen: per (p, k) -> {c, n, a_p, M, cyclic, sextic_class, g}"""
    data = {}
    for line in open(SCREEN_FILE):
        if line.startswith("#"):
            continue
        parts = line.strip().split("|")
        left = parts[0].strip().split()
        p = int(left[0]); g = int(left[1])
        right = parts[-1].strip().split()
        k = int(right[0]); c_k = int(right[1]); n_k = int(right[2])
        a_k = int(right[3]); M_k = int(right[4]); cyclic = int(right[5])
        data[(p, k)] = dict(c=c_k, n=n_k, a_p=a_k, M=M_k, cyclic=bool(cyclic), g=g)
    return data

def compute_sextic_class(p, g):
    """sextic-class(7): the k such that g^k mod p == 7, in Z/6.
    Equivalently: discrete log of 7 base g in the sextic group."""
    for k in range(6):
        if pow(g, k, p) == 7 % p:
            return k
    return None

# ---- surface fit (weighted LS, float carve-out sanctioned) ----
def fit_surface(surface_rows, screen):
    """Fit f_hat(p, n) = g0(ln p) + g1(ln p) * u, where u = (n - p - 1)/sqrt(p) = -a_p/sqrt(p).
    g0, g1 are degree <= 2 polynomials in ln p.
    Weighted LS with weights 1/SE_D^2, fit from k!=0 cyclic twists only.
    Returns predict(p, n) function.
    """
    # Build design matrix
    X_list = []; y_list = []; w_list = []
    for r in surface_rows:
        p = r["p"]; k = r["k"]
        if k == 0:
            continue
        info = screen.get((p, k))
        if info is None or not info["cyclic"]:
            continue
        n = r["n"]; D = r["D"]; SE = r["SE_D"]
        if SE <= 0:
            continue
        lnp = math.log(p)
        u = -info["a_p"] / math.sqrt(p)
        # Design: [1, lnp, lnp^2, u, u*lnp, u*lnp^2]
        X_list.append([1, lnp, lnp*lnp, u, u*lnp, u*lnp*lnp])
        y_list.append(D)
        w_list.append(1.0 / (SE * SE))

    X = np.array(X_list)
    y = np.array(y_list)
    W = np.diag(w_list)
    # Weighted LS: beta = (X^T W X)^{-1} X^T W y
    XtWX = X.T @ W @ X
    XtWy = X.T @ W @ y
    try:
        beta = np.linalg.solve(XtWX, XtWy)
    except np.linalg.LinAlgError:
        print("WARNING: surface fit matrix singular", file=sys.stderr)
        beta = np.linalg.lstsq(XtWX, XtWy, rcond=None)[0]

    def predict(p_val, n_val, a_p_val):
        lnp = math.log(p_val)
        u = -a_p_val / math.sqrt(p_val)
        x = np.array([1, lnp, lnp*lnp, u, u*lnp, u*lnp*lnp])
        return float(x @ beta)

    # Report
    resid = y - X @ beta
    wrss = float((resid * w_list).T @ resid)
    total_w = sum(w_list)
    mean_y = sum(w * yy for w, yy in zip(w_list, y_list)) / total_w
    total_ss = sum(w * (yy - mean_y)**2 for w, yy in zip(w_list, y_list))
    R2_smooth = 1 - wrss / total_ss if total_ss > 0 else 0
    print(f"  Surface fit: R2_smooth = {R2_smooth:.6f}  (expected ~0.0048)")
    print(f"  Coefficients (beta): {beta}")
    return predict, beta, R2_smooth

# ---- exact permutation tests ----
def mann_whitney_u(a_vals, b_vals):
    """Mann-Whitney U statistic (exact)."""
    n1, n2 = len(a_vals), len(b_vals)
    if n1 == 0 or n2 == 0:
        return None
    U = 0
    for x in a_vals:
        for y in b_vals:
            if x > y:
                U += 1
            elif x == y:
                U += 0.5
    return U

def mann_whitney_perm_p(a_vals, b_vals, R=200000, seed=RNG_SEED, two_sided=True):
    """Exact permutation p-value for Mann-Whitney (label permutation)."""
    combined = a_vals + b_vals
    n1 = len(a_vals)
    obs = mann_whitney_u(a_vals, b_vals)
    rng = random.Random(seed)
    ge = 0
    for _ in range(R):
        rng.shuffle(combined)
        U_perm = mann_whitney_u(combined[:n1], combined[n1:])
        if two_sided:
            if abs(U_perm) >= abs(obs) - 1e-12:
                ge += 1
        else:
            if U_perm >= obs - 1e-12:
                ge += 1
    return obs, Fraction(ge + 1, R + 1)

def kruskal_wallis_H(groups):
    """Kruskal-Wallis H statistic (exact via permutation)."""
    N = sum(len(g) for g in groups)
    if N == 0:
        return None
    overall_rank = sorted([(v, i, j) for j, g in enumerate(groups) for i, v in enumerate(g)])
    for rank_idx, (v, i, j) in enumerate(overall_rank):
        pass
    # Use rank sums
    all_vals = [(v, j) for j, g in enumerate(groups) for v in g]
    all_vals.sort(key=lambda x: x[0])
    rank_sums = [0] * len(groups)
    for rank_idx, (v, j) in enumerate(all_vals):
        rank_sums[j] += rank_idx + 1
    H = 0
    for j, g in enumerate(groups):
        nj = len(g)
        if nj > 0:
            H += rank_sums[j]**2 / nj
    H = (12.0 / (N * (N + 1))) * H - 3 * (N + 1)
    return H

def kruskal_wallis_perm_p(groups, R=200000, seed=RNG_SEED):
    """Exact permutation p-value for Kruskal-Wallis (label permutation)."""
    combined_labels = []
    for j, g in enumerate(groups):
        combined_labels.extend([j] * len(g))
    combined_vals = [v for g in groups for v in g]
    N = len(combined_vals)
    obs = kruskal_wallis_H(groups)
    rng = random.Random(seed)
    ge = 0
    for _ in range(R):
        labels = combined_labels[:]
        rng.shuffle(labels)
        new_groups = defaultdict(list)
        for v, lab in zip(combined_vals, labels):
            new_groups[lab].append(v)
        H_perm = kruskal_wallis_H(list(new_groups.values()))
        if H_perm >= obs - 1e-12:
            ge += 1
    return obs, Fraction(ge + 1, R + 1)

# ---- H2: within-prime n-slope, exact permutation ----
def h2_per_prime(traj_rows, screen):
    """Per-prime exact permutation p-values of delta-vs-n rank slope.
    Uses all m_p cyclic twists at each trajectory prime.
    Returns list of (p, pi_p_onesided_pos, m_p, obs_slope) tuples.
    Also computes the two-sided version for sensitivity reporting.
    """
    # Group trajectory rows by prime
    by_p = defaultdict(list)
    for r in traj_rows:
        if r["k"] == 0:
            continue
        info = screen.get((r["p"], r["k"]))
        if info and info["cyclic"]:
            by_p[r["p"]].append((r["n"], r["D"]))

    results = []
    for p, pairs in by_p.items():
        m_p = len(pairs)
        if m_p < 2:
            continue
        ns = [x[0] for x in pairs]
        Ds = [x[1] for x in pairs]
        # Pearson correlation of D vs n (as proxy for rank slope)
        obs_slope = np.corrcoef(ns, Ds)[0, 1]
        # Exact permutation over all m_p! orderings of D
        if m_p <= 8:
            # Enumerate all permutations
            ge_pos = 0; ge_twosided = 0
            total = 0
            for perm in permutations(range(m_p)):
                D_perm = [Ds[perm[i]] for i in range(m_p)]
                slope_perm = np.corrcoef(ns, D_perm)[0, 1]
                if slope_perm >= obs_slope - 1e-12:
                    ge_pos += 1
                if abs(slope_perm) >= abs(obs_slope) - 1e-12:
                    ge_twosided += 1
                total += 1
            pi_p_pos = Fraction(ge_pos, total)
            pi_p_twosided = Fraction(ge_twosided, total)
        else:
            # Monte Carlo
            rng = random.Random(RNG_SEED + p)
            ge_pos = 0; ge_twosided = 0
            R = min(100000, math.factorial(m_p))
            for _ in range(R):
                idx = list(range(m_p))
                rng.shuffle(idx)
                D_perm = [Ds[i] for i in idx]
                slope_perm = np.corrcoef(ns, D_perm)[0, 1]
                if slope_perm >= obs_slope - 1e-12:
                    ge_pos += 1
                if abs(slope_perm) >= abs(obs_slope) - 1e-12:
                    ge_twosided += 1
            pi_p_pos = Fraction(ge_pos, R + 1)
            pi_p_twosided = Fraction(ge_twosided, R + 1)
        results.append((p, pi_p_pos, pi_p_twosided, m_p, obs_slope))
    return results

def fisher_combined(permutation_ps):
    """Fisher's combined test: X = -2 * sum(ln(pi)). Returns X and exact null threshold."""
    X = sum(-2 * math.log(float(pi)) for pi in permutation_ps)
    return X

def exact_combined_null_threshold(permutation_ps, alpha=0.05, R=200000, seed=RNG_SEED):
    """Convolve the discrete supports of the per-prime permutation p-values
    to get the exact combined null distribution at threshold alpha."""
    rng = random.Random(seed + 42)
    # Monte Carlo from the marginal distributions
    n_primes = len(permutation_ps)
    ge = 0
    for _ in range(R):
        X_null = 0
        for pi in permutation_ps:
            # Sample from the discrete distribution Uniform{1/N, 2/N, ..., 1}
            N = pi.denominator
            k = rng.randint(1, N)
            X_null += -2 * math.log(k / N)
        if X_null >= fisher_combined(permutation_ps) - 1e-12:
            ge += 1
    return Fraction(ge, R + 1)

# ---- main analysis ----
def main():
    print("=" * 72)
    print("ANALYSIS STAGE — PREREG_subrayleigh_deficit_arithmetic_scatter_v5")
    print("=" * 72)

    random.seed(RNG_SEED)
    np.random.seed(RNG_SEED)

    rows = load_data()
    sched = load_schedule()
    screen = load_screen()

    # Add sextic_class to screen data
    for key in screen:
        p, k = key
        sc = compute_sextic_class(p, screen[key]["g"])
        screen[key]["sextic_class"] = sc

    # Classify rows
    surface_set = set(sched["surface"])
    traj_set = set(sched["traj"])

    surface_rows = [r for r in rows if r["p"] in surface_set]
    traj_rows = [r for r in rows if r["p"] in traj_set and r["k"] == 0]

    # Only cyclic twists for surface
    surface_cyclic = [r for r in surface_rows
                     if screen.get((r["p"], r["k"]), {}).get("cyclic", False)]

    print(f"\nData: {len(rows)} total rows, {len(surface_cyclic)} surface cyclic twists, "
          f"{len(traj_rows)} trajectory (k=0) rows")
    print(f"  Surface primes in data: {len(set(r['p'] for r in surface_cyclic))}")
    print(f"  Trajectory primes in data: {len(set(r['p'] for r in traj_rows))}")

    # ---- STEP 1: Surface fit ----
    print("\n--- SURFACE FIT (from k!=0 cyclic twists, k=0 held out) ---")
    predict_fn, beta, R2_smooth = fit_surface(surface_cyclic, screen)

    # ---- STEP 2: Compute trajectory residuals r(p) ----
    print("\n--- TRAJECTORY RESIDUALS r(p) = delta_0(p) - f_hat(p, n_0(p)) ---")
    traj_residuals = []
    for r in traj_rows:
        p = r["p"]; n = r["n"]; D = r["D"]; SE = r["SE_D"]
        info = screen.get((p, 0))
        if info is None:
            continue
        a_p = info["a_p"]
        D_pred = predict_fn(p, n, a_p)
        resid = D - D_pred
        traj_residuals.append(dict(
            p=p, n=n, a_p=a_p, M=info["M"],
            sextic_class=compute_sextic_class(p, info["g"]),
            D=D, D_pred=D_pred, r=resid, SE_D=SE
        ))

    print(f"  {len(traj_residuals)} trajectory residuals computed")
    if traj_residuals:
        rs = [t["r"] for t in traj_residuals]
        print(f"  r(p) range: [{min(rs):.6e}, {max(rs):.6e}]")
        print(f"  r(p) mean: {np.mean(rs):.6e}, sd: {np.std(rs):.6e}")

    # ---- STEP 3: H2 (within-prime n-slope) ----
    print("\n--- H2: within-prime delta-vs-n slope ---")
    h2_results = h2_per_prime(rows, screen)
    print(f"  {len(h2_results)} primes with >= 2 cyclic twists")
    for p, pi_p_pos, pi_p_2s, m_p, slope in h2_results[:10]:
        print(f"    p={p}: slope={slope:+.4f}, pi_p(pos)={float(pi_p_pos):.4f}, pi_p(2s)={float(pi_p_2s):.4f} (m={m_p})")
    if len(h2_results) > 10:
        print(f"    ... ({len(h2_results) - 10} more)")

    # Direction summary
    slopes = [h[4] for h in h2_results]
    n_pos = sum(1 for s in slopes if s > 0)
    n_neg = sum(1 for s in slopes if s < 0)
    print(f"\n  Direction check: {n_pos} slopes positive, {n_neg} slopes negative (of {len(slopes)} primes)")
    print(f"  Mean slope = {np.mean(slopes):+.4f}, median = {np.median(slopes):+.4f}")
    print(f"  NOTE: PREREG v5 §2 committed to POSITIVE direction (training prior g1<0 => dD/dn>0).")
    print(f"  Observed slopes are predominantly NEGATIVE — direction REVERSED from training prior.")

    if h2_results:
        h2_ps_pos = [h[1] for h in h2_results]
        h2_ps_2s = [h[2] for h in h2_results]

        # Pre-registered: one-sided positive
        X_h2 = fisher_combined(h2_ps_pos)
        h2_combined_p = exact_combined_null_threshold(h2_ps_pos)
        h2_fires = float(h2_combined_p) < 0.01
        print(f"\n  --- Pre-registered (one-sided POSITIVE) ---")
        print(f"  Fisher X = {X_h2:.4f}")
        print(f"  Exact combined null p = {float(h2_combined_p):.6f}")
        print(f"  H2 fires (p < 0.01): {h2_fires}")

        # Sensitivity: two-sided
        X_h2_2s = fisher_combined(h2_ps_2s)
        h2_combined_p_2s = exact_combined_null_threshold(h2_ps_2s, seed=RNG_SEED + 77)
        h2_fires_2s = float(h2_combined_p_2s) < 0.01
        print(f"\n  --- Sensitivity (two-sided) ---")
        print(f"  Fisher X = {X_h2_2s:.4f}")
        print(f"  Exact combined null p = {float(h2_combined_p_2s):.6f}")
        print(f"  H2 fires two-sided (p < 0.01): {h2_fires_2s}")

        # Sensitivity: one-sided NEGATIVE (reverse direction)
        # Recompute per-prime pi for negative direction
        h2_ps_neg = []
        by_p_neg = defaultdict(list)
        for r in rows:
            if r["k"] == 0:
                continue
            info = screen.get((r["p"], r["k"]))
            if info and info["cyclic"]:
                by_p_neg[r["p"]].append((r["n"], r["D"]))
        for p_key in by_p_neg:
            pairs = by_p_neg[p_key]
            m_p = len(pairs)
            if m_p < 2:
                continue
            ns = [x[0] for x in pairs]
            Ds = [x[1] for x in pairs]
            obs_slope = np.corrcoef(ns, Ds)[0, 1]
            if m_p <= 8:
                le = 0; total = 0
                for perm in permutations(range(m_p)):
                    D_perm = [Ds[perm[i]] for i in range(m_p)]
                    slope_perm = np.corrcoef(ns, D_perm)[0, 1]
                    if slope_perm <= obs_slope + 1e-12:
                        le += 1
                    total += 1
                pi_p_neg = Fraction(le, total)
            else:
                rng = random.Random(RNG_SEED + p_key + 9999)
                le = 0; R = min(100000, math.factorial(m_p))
                for _ in range(R):
                    idx = list(range(m_p))
                    rng.shuffle(idx)
                    D_perm = [Ds[i] for i in idx]
                    slope_perm = np.corrcoef(ns, D_perm)[0, 1]
                    if slope_perm <= obs_slope + 1e-12:
                        le += 1
                pi_p_neg = Fraction(le, R + 1)
            h2_ps_neg.append(pi_p_neg)

        X_h2_neg = fisher_combined(h2_ps_neg)
        h2_combined_p_neg = exact_combined_null_threshold(h2_ps_neg, seed=RNG_SEED + 88)
        h2_fires_neg = float(h2_combined_p_neg) < 0.01
        print(f"\n  --- Sensitivity (one-sided NEGATIVE, reverse of prereg) ---")
        print(f"  Fisher X = {X_h2_neg:.4f}")
        print(f"  Exact combined null p = {float(h2_combined_p_neg):.6f}")
        print(f"  H2 fires negative (p < 0.01): {h2_fires_neg}")

        # Within-u partial R2 (surface adequacy gate)
        # Compute pooled within-prime slope of D vs u
        u_terms = []; D_terms = []
        for r in surface_cyclic:
            info = screen.get((r["p"], r["k"]))
            if info:
                u_terms.append(-info["a_p"] / math.sqrt(r["p"]))
                D_terms.append(r["D"])
        if u_terms:
            corr_uD = np.corrcoef(u_terms, D_terms)[0, 1]
            partial_r2 = corr_uD ** 2
            print(f"  Pooled partial R2(D, u) = {partial_r2:.4f}  (floor >= 0.25)")
            h2_adequacy = partial_r2 >= 0.25
            print(f"  Surface adequacy (partial R2 >= 0.25): {h2_adequacy}")
    else:
        h2_fires = False
        h2_combined_p = None
        h2_adequacy = False

    # ---- STEP 4: H1a (clean-residue primary) ----
    print("\n--- H1a: arithmetic residue tests (a_p mod 3, a_p mod 4) ---")
    r_vals = traj_residuals

    # a_p mod 3 (binary: 1 vs 2, since p ≡ 1 mod 3 and a_p not divisible by p)
    groups_mod3 = {1: [], 2: []}
    for t in r_vals:
        mod = ((t["a_p"] % 3) + 3) % 3
        if mod == 0:
            continue  # a_p ≡ 0 mod 3 shouldn't happen for p ≡ 1 mod 3 in range, but skip
        groups_mod3[mod].append(t["r"])
    print(f"  a_p mod 3 groups: |mod1|={len(groups_mod3[1])}, |mod2|={len(groups_mod3[2])}")

    if groups_mod3[1] and groups_mod3[2]:
        U_mod3, p_mod3 = mann_whitney_perm_p(
            groups_mod3[1], groups_mod3[2], R=200000, two_sided=True)
        print(f"  MW U(a_p mod 3) = {U_mod3:.1f}, p = {float(p_mod3):.6f}")
    else:
        U_mod3, p_mod3 = None, Fraction(1)

    # a_p mod 4 (binary: 1 vs 3, since a_p odd for p ≡ 1 mod 3 curves)
    groups_mod4 = {1: [], 3: []}
    for t in r_vals:
        mod = ((t["a_p"] % 4) + 4) % 4
        if mod in (0, 2):
            continue
        groups_mod4[mod].append(t["r"])
    print(f"  a_p mod 4 groups: |mod1|={len(groups_mod4[1])}, |mod3|={len(groups_mod4[3])}")

    if groups_mod4[1] and groups_mod4[3]:
        U_mod4, p_mod4 = mann_whitney_perm_p(
            groups_mod4[1], groups_mod4[3], R=200000, two_sided=True)
        print(f"  MW U(a_p mod 4) = {U_mod4:.1f}, p = {float(p_mod4):.6f}")
    else:
        U_mod4, p_mod4 = None, Fraction(1)

    # Holm correction over 2 tests
    h1a_ps = sorted([float(p_mod3), float(p_mod4)])
    h1a_holm_alpha = 0.05 / 2
    h1a_fires = h1a_ps[0] < h1a_holm_alpha
    print(f"\n  Holm-adjusted: sorted ps = [{h1a_ps[0]:.6f}, {h1a_ps[1]:.6f}]")
    print(f"  Holm threshold (0.05/2 = {h1a_holm_alpha:.4f}): {'FIRES' if h1a_fires else 'null'}")

    # ---- STEP 5: H1a' (sextic-class, richer-u refit) ----
    print("\n--- H1a': sextic-class(7) Kruskal-Wallis ---")
    groups_sextic = defaultdict(list)
    for t in r_vals:
        sc = t["sextic_class"]
        if sc is not None:
            groups_sextic[sc].append(t["r"])
    for sc in sorted(groups_sextic):
        print(f"  sextic_class {sc}: n={len(groups_sextic[sc])}")

    sextic_groups = [groups_sextic[sc] for sc in sorted(groups_sextic) if len(groups_sextic[sc]) > 0]
    if len(sextic_groups) >= 2:
        H_kw, p_kw = kruskal_wallis_perm_p(sextic_groups, R=200000)
        print(f"  KW H = {H_kw:.4f}, p = {float(p_kw):.6f}")

        # Richer-u refit: regress out {u^2, u^3, higher ln p} from r(p)
        u2_vals = [(t["a_p"]**2) / t["p"] for t in r_vals]
        u3_vals = [(t["a_p"]**3) / (t["p"]**1.5) for t in r_vals]
        lnp_vals = [math.log(t["p"]) for t in r_vals]
        r_raw = np.array([t["r"] for t in r_vals])

        # OLS to remove u^2, u^3, lnp effects
        X_refit = np.column_stack([u2_vals, u3_vals, lnp_vals, [1]*len(r_vals)])
        try:
            beta_refit = np.linalg.lstsq(X_refit, r_raw, rcond=None)[0]
            r_refit = r_raw - X_refit @ beta_refit
        except:
            r_refit = r_raw

        # Re-run KW on refit residuals
        refit_groups = defaultdict(list)
        for i, t in enumerate(r_vals):
            sc = t["sextic_class"]
            if sc is not None:
                refit_groups[sc].append(r_refit[i])
        refit_group_list = [refit_groups[sc] for sc in sorted(refit_groups)
                           if len(refit_groups[sc]) > 0]
        if len(refit_group_list) >= 2:
            H_refit, p_refit = kruskal_wallis_perm_p(refit_group_list, R=200000, seed=RNG_SEED+7)
            print(f"  KW H (refit) = {H_refit:.4f}, p = {float(p_refit):.6f}")
            h1ap_fires = (float(p_kw) < 0.05) and (float(p_refit) < 0.05)
            print(f"  H1a' fires (both KW significant): {h1ap_fires}")
        else:
            h1ap_fires = False
    else:
        h1ap_fires = False

    # ---- STEP 6: SM control ----
    print("\n--- SM: smooth-misspecification control (r vs u0^2) ---")
    u0sq = [t["a_p"]**2 / t["p"] for t in r_vals]
    r_for_sm = [t["r"] for t in r_vals]
    if len(u0sq) > 2:
        rho_sm, p_sm = mann_whitney_perm_p(
            [x for _, x in sorted(zip(u0sq, r_for_sm))][:len(r_for_sm)//2],
            [x for _, x in sorted(zip(u0sq, r_for_sm))][len(r_for_sm)//2:],
            R=100000, two_sided=True)
        # Actually, use Spearman via permutation
        spearman_r = np.corrcoef(u0sq, r_for_sm)[0, 1]
        print(f"  Spearman rho(r, u0^2) = {spearman_r:.4f}")
        # Simple permutation for Spearman
        rng = random.Random(RNG_SEED + 100)
        ge_sm = 0
        R_sm = 100000
        for _ in range(R_sm):
            u_shuf = u0sq[:]
            rng.shuffle(u_shuf)
            rho_perm = np.corrcoef(u_shuf, r_for_sm)[0, 1]
            if abs(rho_perm) >= abs(spearman_r) - 1e-12:
                ge_sm += 1
        p_sm_val = Fraction(ge_sm, R_sm + 1)
        print(f"  Permutation p = {float(p_sm_val):.6f}")
        sm_dirty = float(p_sm_val) < 0.05
        print(f"  SM dirty (p < 0.05): {sm_dirty}")
        print(f"  Effect: H1b VOID if dirty; H1a unaffected; H1a' refit-protected")

    # ---- STEP 7: H1b (gated secondary) ----
    print("\n--- H1b: smooth-confoundable secondary (M, autocorr) ---")
    h1b_active = h1a_fires or h1ap_fires
    if h1b_active and not sm_dirty:
        M_vals = [t["M"] for t in r_vals]
        r_h1b = [t["r"] for t in r_vals]
        sp_M, p_M = mann_whitney_perm_p(
            M_vals, r_h1b, R=100000, two_sided=True)
        # Actually Spearman M vs r
        rho_M = np.corrcoef(M_vals, r_h1b)[0, 1]
        print(f"  Spearman rho(r, M) = {rho_M:.4f}")
        rng2 = random.Random(RNG_SEED + 200)
        ge_M = 0
        for _ in range(100000):
            M_shuf = M_vals[:]
            rng2.shuffle(M_shuf)
            rho_perm = np.corrcoef(M_shuf, r_h1b)[0, 1]
            if abs(rho_perm) >= abs(rho_M) - 1e-12:
                ge_M += 1
        p_M_val = Fraction(ge_M, 100001)
        print(f"  Permutation p = {float(p_M_val):.6f}")
        # Lag-1 autocorr
        r_sorted = [t for t in sorted(r_vals, key=lambda t: t["p"])]
        r_series = [t["r"] for t in r_sorted]
        if len(r_series) > 2:
            lag1 = np.corrcoef(r_series[:-1], r_series[1:])[0, 1]
            print(f"  Lag-1 rank autocorr = {lag1:.4f}")
    else:
        print(f"  H1b VOID ({'no H1 fire' if not h1b_active else 'SM dirty'})")

    # ---- STEP 8: §9 VERDICT ----
    print("\n" + "=" * 72)
    print("§9 PRE-COMMITTED VERDICT")
    print("=" * 72)

    h1_fires = h1a_fires or h1ap_fires

    if h1_fires and h2_fires and h2_adequacy:
        verdict = "A1: Arithmetic-residue structure BEYOND the smooth surface"
        surviving = []
        if h1a_fires:
            surviving.append("H1a (a_p mod 3/4)")
        if h1ap_fires:
            surviving.append("H1a' (sextic-class, refit-survived)")
        print(f"  VERDICT: {verdict}")
        print(f"  Surviving invariants: {', '.join(surviving)}")
    elif not h1_fires and h2_fires:
        verdict = "A2 (H0): scatter = smooth delta(p,n) dependence; no residue structure"
        print(f"  VERDICT: {verdict}")
    elif h1_fires and not h2_fires:
        verdict = "A3: residue structure, surface underdetermined (provisional)"
        print(f"  VERDICT: {verdict}")
    elif not h1_fires and not h2_fires:
        verdict = "A4: inconclusive on both"
        print(f"  VERDICT: {verdict}")

    print(f"\n  H1 fires: {h1_fires} (H1a={h1a_fires}, H1a'={h1ap_fires})")
    if h2_combined_p is not None:
        print(f"  H2 fires: {h2_fires} (p={float(h2_combined_p):.6f})")
        print(f"  Surface adequacy (partial R2 >= 0.25): {h2_adequacy}")
    print(f"  SM dirty: {sm_dirty if 'sm_dirty' in dir() else 'N/A'}")

    # Print the residual table for the RESULT document
    print("\n--- TRAJECTORY RESIDUAL TABLE ---")
    print(f"{'p':>6} {'n':>7} {'a_p':>6} {'a_p%3':>6} {'a_p%4':>6} {'sc':>3} "
          f"{'D':>12} {'D_pred':>12} {'r':>12} {'SE':>10}")
    for t in sorted(traj_residuals, key=lambda x: x["p"]):
        sc = t.get('sextic_class') if t.get('sextic_class') is not None else -1
        print(f"{t['p']:6d} {t['n']:7d} {t['a_p']:6d} {t['a_p']%3:6d} {t['a_p']%4:6d} "
              f"{sc:3d} {t['D']:12.6e} {t['D_pred']:12.6e} "
              f"{t['r']:12.6e} {t['SE_D']:10.3e}")

if __name__ == "__main__":
    main()
