"""
Phase 5 — Residue-structure investigation of the 681 counterexamples.

Hypothesis (from manual trace of n=3, G=[3], A=[1,5], p=2):
  CE occur when I_G's residues mod L_G are constrained to a strict subset of
  [0, L_G), which forces the bands to start at constrained residues mod L_A,
  which can miss a residue class where I_A's targets land.

For each hard-regime input we compute:
  - res_G_mod_LG: |{α mod L_G : α ∈ I_G}|  (residue spread of I_G)
  - res_G_mod_LG_full: bool — is res_G_mod_LG = L_G? (full coverage)
  - shift_residues_mod_LA: {(r * L_A) mod (n*L_G*L_A) // L_G mod L_A : r ∈ shift_set}
    (the residues mod L_A where bands' β-starts live)
  - target_residues_mod_LA: {β mod L_A : β ∈ I_A}
  - missed_residues_mod_LA: residues mod L_A that bands' β-coverage doesn't hit
  - target_in_missed: bool — is there a target in a missed residue?

The hypothesis predicts:
  N_joint = 0  ⟺  (target_in_missed is True given residue constraints)

For non-CE inputs (N_joint ≥ 1), we expect res_G_mod_LG to be larger or
target_in_missed to be False.

Output: CSV plus a summary partitioning inputs by the hypothesis.
"""

import csv
import itertools
import math
from functools import reduce


def gcd_list(xs):
    return reduce(math.gcd, xs, 0)


def lcm(a, b):
    return a * b // math.gcd(a, b)


def lcm_list(xs):
    return reduce(lcm, xs, 1)


def isprime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def good_cell_idx(speeds, n, L):
    result = []
    for m in range(n * L):
        ok = True
        for v in speeds:
            d = L // v
            r = (m // d) % n
            if not (1 <= r <= n - 2):
                ok = False
                break
        if ok:
            result.append(m)
    return result


def classify_lrc(n, G_speeds, A_speeds, p):
    """Returns 'DI', 'ModDI', or 'neither'."""
    # DI check
    if len(A_speeds) == 1 and len(G_speeds) == n - 2:
        q = A_speeds[0]
        V = p * q
        if isprime(p) and V > 0 and V not in G_speeds:
            slow_with_V = G_speeds + [V]
            if len(set(slow_with_V)) == len(slow_with_V) and gcd_list(slow_with_V) == 1:
                L = lcm_list(G_speeds)
                if math.gcd(p, L) == 1:
                    slow_sorted = sorted(G_speeds)
                    if (n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]:
                        return 'DI'
    # ModDI check (simplified)
    if isprime(p):
        for q_idx in range(len(A_speeds)):
            w = A_speeds[:q_idx] + A_speeds[q_idx+1:]
            q = A_speeds[q_idx]
            r = len(w)
            if r < 1 or r > n - 3:
                continue
            slow_div = [p * wk for wk in w]
            slow_full = G_speeds + slow_div
            if len(slow_full) != n - 2:
                continue
            if len(set(slow_full)) != len(slow_full):
                continue
            if not all(math.gcd(v, p) == 1 for v in G_speeds):
                continue
            V = p * q
            if V in slow_full:
                continue
            speeds_all = slow_full + [V]
            if gcd_list(speeds_all) != 1:
                continue
            slow_sorted = sorted(slow_full)
            if (n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]:
                return 'ModDI'
    return 'neither'


def compute_residue_structure(n, G_speeds, A_speeds, p):
    """Compute the residue-mod-L_G structure of I_G and band coverage."""
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    nLG = n * L_G
    nLA = n * L_A
    nLGLA = nLG * L_A
    M = nLGLA * p

    I_G = good_cell_idx(G_speeds, n, L_G)
    I_A = good_cell_idx(A_speeds, n, L_A)

    # Residue spread of I_G mod L_G
    res_G_mod_LG = set(a % L_G for a in I_G)
    res_G_mod_LG_count = len(res_G_mod_LG)
    res_G_mod_LG_full = (res_G_mod_LG_count == L_G)

    # Compute bands' β-coverage (β = floor((m'' mod nLGLA)/L_G))
    # For each α in I_G, band = [r*L_A, r*L_A + L_A*p) mod nLGLA,
    # where r = α*p mod nLG.
    band_betas = set()
    for a in I_G:
        r = (a * p) % nLG
        band_start = r * L_A
        for e in range(L_A * p):
            pos = (band_start + e) % nLGLA
            beta = pos // L_G
            band_betas.add(beta)

    target_betas = set(I_A)

    intersect = band_betas & target_betas
    N_joint_indicator = len(intersect)  # 0 or positive

    # Compute residue spread of β-coverage and targets mod L_A
    band_betas_mod_LA = set(b % L_A for b in band_betas)
    target_betas_mod_LA = set(b % L_A for b in target_betas)

    # Missed residues mod L_A in band coverage
    missed_LA = set(range(L_A)) - band_betas_mod_LA
    target_in_missed_LA = bool(target_betas_mod_LA & missed_LA)

    # Are targets ONLY in missed residues mod L_A? (Strong CE indicator)
    targets_all_missed = bool(target_betas) and target_betas_mod_LA.issubset(missed_LA)

    return {
        "n": n,
        "G_speeds": "-".join(map(str, G_speeds)),
        "A_speeds": "-".join(map(str, A_speeds)),
        "p": p,
        "kG": len(G_speeds),
        "kA": len(A_speeds),
        "L_G": L_G,
        "L_A": L_A,
        "cIG": len(I_G),
        "cIA": len(I_A),
        "res_G_mod_LG": res_G_mod_LG_count,
        "res_G_mod_LG_full": int(res_G_mod_LG_full),
        "n_band_betas": len(band_betas),
        "n_band_betas_mod_LA": len(band_betas_mod_LA),
        "n_missed_LA": len(missed_LA),
        "target_in_missed_LA": int(target_in_missed_LA),
        "targets_all_missed_LA": int(targets_all_missed),
        "N_joint": N_joint_indicator,
        "lrc_class": classify_lrc(n, G_speeds, A_speeds, p),
    }


def main():
    print("=" * 78)
    print("PHASE 5 — Residue-mod-L_G structure of I_G in counterexamples")
    print("=" * 78)
    print()
    print("Hypothesis: CE occur when I_G's residues mod L_G are constrained,")
    print("forcing bands to miss a residue class mod L_A where targets live.")
    print()

    SPEED_POOL = list(range(1, 9))
    PRIMES = [p for p in range(2, 20) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

    rows = []
    for n in NS:
        for kG in [1, 2, 3]:
            for G_speeds_tup in itertools.combinations(SPEED_POOL, kG):
                G_speeds = list(G_speeds_tup)
                L_G = lcm_list(G_speeds)
                if not good_cell_idx(G_speeds, n, L_G):
                    continue
                for kA in [1, 2]:
                    for A_speeds_tup in itertools.combinations(SPEED_POOL, kA):
                        A_speeds = list(A_speeds_tup)
                        if set(G_speeds) & set(A_speeds):
                            continue
                        L_A = lcm_list(A_speeds)
                        if not good_cell_idx(A_speeds, n, L_A):
                            continue
                        for p in PRIMES:
                            if math.gcd(p, L_G) != 1:
                                continue
                            if p in G_speeds or p in A_speeds:
                                continue
                            if not (p < n * L_G):
                                continue
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                            if g_all != 1:
                                continue
                            row = compute_residue_structure(n, G_speeds, A_speeds, p)
                            rows.append(row)

    print(f"Total scanned: {len(rows)}")

    # Partition by hypothesis prediction
    ce = [r for r in rows if r["N_joint"] == 0]
    pos = [r for r in rows if r["N_joint"] >= 1]

    print(f"Counterexamples (N_joint=0): {len(ce)}")
    print(f"Positive (N_joint>=1):       {len(pos)}")
    print()

    # Hypothesis test 1: residue coverage
    print("HYPOTHESIS TEST 1: I_G residue coverage mod L_G")
    print("-" * 78)
    ce_full = sum(1 for r in ce if r["res_G_mod_LG_full"] == 1)
    ce_partial = sum(1 for r in ce if r["res_G_mod_LG_full"] == 0)
    pos_full = sum(1 for r in pos if r["res_G_mod_LG_full"] == 1)
    pos_partial = sum(1 for r in pos if r["res_G_mod_LG_full"] == 0)
    print(f"{'':<25} {'CE':<10} {'Positive':<10}")
    print(f"{'I_G covers all L_G res':<25} {ce_full:<10} {pos_full:<10}")
    print(f"{'I_G partial coverage':<25} {ce_partial:<10} {pos_partial:<10}")
    print()

    # Hypothesis test 2: targets in missed residues mod L_A
    print("HYPOTHESIS TEST 2: targets in missed residues mod L_A")
    print("-" * 78)
    ce_targets_missed = sum(1 for r in ce if r["target_in_missed_LA"] == 1)
    ce_targets_ok = sum(1 for r in ce if r["target_in_missed_LA"] == 0)
    pos_targets_missed = sum(1 for r in pos if r["target_in_missed_LA"] == 1)
    pos_targets_ok = sum(1 for r in pos if r["target_in_missed_LA"] == 0)
    print(f"{'':<35} {'CE':<10} {'Positive':<10}")
    print(f"{'Some target in missed mod L_A':<35} {ce_targets_missed:<10} {pos_targets_missed:<10}")
    print(f"{'No target in missed mod L_A':<35} {ce_targets_ok:<10} {pos_targets_ok:<10}")
    print()

    # Hypothesis test 3: ALL targets in missed residues mod L_A (strong CE)
    print("HYPOTHESIS TEST 3: ALL targets in missed mod L_A")
    print("-" * 78)
    ce_all_missed = sum(1 for r in ce if r["targets_all_missed_LA"] == 1)
    pos_all_missed = sum(1 for r in pos if r["targets_all_missed_LA"] == 1)
    print(f"{'':<35} {'CE':<10} {'Positive':<10}")
    print(f"{'ALL targets in missed mod L_A':<35} {ce_all_missed:<10} {pos_all_missed:<10}")
    print()

    # Compound: I_G partial AND ALL targets missed (the structural mechanism)
    print("COMPOUND: I_G partial coverage AND all targets in missed mod L_A")
    print("-" * 78)
    ce_compound = sum(1 for r in ce if r["res_G_mod_LG_full"] == 0 and r["targets_all_missed_LA"] == 1)
    pos_compound = sum(1 for r in pos if r["res_G_mod_LG_full"] == 0 and r["targets_all_missed_LA"] == 1)
    print(f"{'':<35} {'CE':<10} {'Positive':<10}")
    print(f"{'Compound condition':<35} {ce_compound:<10} {pos_compound:<10}")
    print()

    # By n, k_G + k_A
    print("Counterexample breakdown by (n, kG+kA):")
    for nn in NS:
        for kgkasum in range(2, 8):
            ce_sub = [r for r in ce if r["n"] == nn and r["kG"] + r["kA"] == kgkasum]
            if ce_sub:
                avg_resG = sum(r["res_G_mod_LG"] for r in ce_sub) / len(ce_sub)
                avg_LG = sum(r["L_G"] for r in ce_sub) / len(ce_sub)
                full_cov = sum(1 for r in ce_sub if r["res_G_mod_LG_full"] == 1)
                print(f"  n={nn}, kG+kA={kgkasum}: {len(ce_sub)} CE | avg L_G={avg_LG:.1f} | avg res_G_mod_LG={avg_resG:.1f} | full coverage: {full_cov}")

    # Write CSV
    out_path = "/Users/trentpalelei/Desktop/Math Ex/reports/phase5_residue_structure.csv"
    import os
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    fieldnames = list(rows[0].keys()) if rows else []
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)
    print()
    print(f"Wrote {len(rows)} rows to {out_path}")


if __name__ == "__main__":
    main()
