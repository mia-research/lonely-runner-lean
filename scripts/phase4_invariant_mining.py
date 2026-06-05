"""
Phase 4 — Mining structural invariants that separate the 681 abstract
counterexamples (Conjecture 5.2-H FAILS as abstract statement) from
LRC-realisable hard-case inputs (Conjecture 5.2-H HOLDS empirically).

For each input (n, G_speeds, A_speeds, p) with p < n*L_G (hard case) and
both index sets non-empty, compute:

  Basic:
  - kG, kA: |G_speeds|, |A_speeds|
  - L_G, L_A: lcms
  - n_L_G_L_A = n * L_G * L_A
  - M = n_L_G_L_A * p
  - p_over_nLG = p / (n L_G)              # easy-case ratio (< 1 in hard case)

  Cell-count invariants:
  - cIG = |I_G|, cIA = |I_A|
  - mu_G = cIG / (n L_G), mu_A = cIA / (n L_A)

  GCD invariants:
  - gcd_p_nLG, gcd_p_n, gcd_p_LA

  Shift-set invariants:
  - shift_set_size = |{(a p) mod (n L_G) : a in I_G}|
  - shift_set_size_mod_LG = |{(a p) mod L_G : a in I_G}|  # how surjective onto L_G-cosets

  Coverage invariants:
  - band_union_count = |union of [r_a L_A, r_a L_A + L_A p) (mod n L_G L_A)
                          : a in I_G}|
  - target_count = |I_A| * L_G
  - N_joint = number of m'' in [0, M) with alpha(m'') in I_G AND beta(m'') in I_A

  Classification:
  - is_DI, is_ModDI, is_neither (LRC-realisable status)

Outputs: CSV with one row per input, partitioned by classification.

Separation analysis: scan invariants for one where 681 counterexamples (N_joint=0)
and LRC-realisable inputs (N_joint >= 1) have disjoint value ranges.
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


def classify_di(n, G_speeds, A_speeds, p):
    if len(A_speeds) != 1:
        return False
    q = A_speeds[0]
    if len(G_speeds) != n - 2:
        return False
    if not isprime(p):
        return False
    V = p * q
    if V <= 0 or V in G_speeds:
        return False
    slow_with_V = G_speeds + [V]
    if len(set(slow_with_V)) != len(slow_with_V):
        return False
    if gcd_list(slow_with_V) != 1:
        return False
    L = lcm_list(G_speeds)
    if math.gcd(p, L) != 1:
        return False
    slow_sorted = sorted(G_speeds)
    if not ((n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]):
        return False
    return True


def classify_moddi(n, G_speeds, A_speeds, p):
    if len(A_speeds) < 1:
        return False
    if not isprime(p):
        return False
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
        if not ((n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]):
            continue
        return True
    return False


def compute_invariants(n, G_speeds, A_speeds, p):
    """Compute all candidate invariants. Returns dict."""
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    nLG = n * L_G
    nLA = n * L_A
    nLGLA = nLG * L_A
    M = nLGLA * p

    I_G = good_cell_idx(G_speeds, n, L_G)
    I_A = good_cell_idx(A_speeds, n, L_A)

    cIG = len(I_G)
    cIA = len(I_A)
    mu_G = cIG / nLG
    mu_A = cIA / nLA

    # Shift set R = {(a*p) mod (n L_G) : a in I_G}
    R = set((a * p) % nLG for a in I_G)
    R_mod_LG = set((a * p) % L_G for a in I_G)

    # Band-union: union of [r * L_A, r * L_A + L_A * p) (mod nLGLA) for r in R
    # Use a set of integers; size of union
    band_union_count = 0
    if nLGLA <= 100_000:  # only do this for small instances
        band_union = set()
        for r in R:
            for offset in range(L_A * p):
                band_union.add((r * L_A + offset) % nLGLA)
        band_union_count = len(band_union)
    else:
        band_union_count = -1  # marker for too-large

    target_count = cIA * L_G

    # N_joint: number of m'' in [0, M) with alpha in I_G AND beta in I_A
    I_G_set = set(I_G)
    I_A_set = set(I_A)
    N_joint = 0
    if M <= 5_000_000:
        for mpp in range(M):
            alpha = mpp // (L_A * p)
            beta = (mpp % nLGLA) // L_G
            if alpha in I_G_set and beta in I_A_set:
                N_joint += 1
                # No early break — we want the full count
    else:
        N_joint = -1

    return {
        "n": n,
        "G_speeds": "-".join(map(str, G_speeds)),
        "A_speeds": "-".join(map(str, A_speeds)),
        "p": p,
        "kG": len(G_speeds),
        "kA": len(A_speeds),
        "L_G": L_G,
        "L_A": L_A,
        "nLG": nLG,
        "nLA": nLA,
        "nLGLA": nLGLA,
        "M": M,
        "p_over_nLG": p / nLG,
        "cIG": cIG,
        "cIA": cIA,
        "mu_G": round(mu_G, 6),
        "mu_A": round(mu_A, 6),
        "gcd_p_nLG": math.gcd(p, nLG),
        "gcd_p_n": math.gcd(p, n),
        "gcd_p_LA": math.gcd(p, L_A),
        "shift_set_size": len(R),
        "shift_set_size_mod_LG": len(R_mod_LG),
        "band_union_count": band_union_count,
        "target_count": target_count,
        "expected_joint": round(mu_G * mu_A * M, 4),
        "N_joint": N_joint,
        "is_DI": int(classify_di(n, G_speeds, A_speeds, p)),
        "is_ModDI": int(classify_moddi(n, G_speeds, A_speeds, p)),
    }


def main():
    print("=" * 78)
    print("PHASE 4 — Structural invariant mining for Conjecture 5.2-H")
    print("=" * 78)
    print()

    SPEED_POOL = list(range(1, 9))
    PRIMES = [p for p in range(2, 20) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

    rows = []
    total_scanned = 0
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
                                continue  # only hard case
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                            if g_all != 1:
                                continue
                            total_scanned += 1
                            row = compute_invariants(n, G_speeds, A_speeds, p)
                            rows.append(row)

    print(f"Total scanned: {total_scanned}")
    print()

    # Classify by N_joint and LRC-realisability
    n_ce = sum(1 for r in rows if r["N_joint"] == 0)
    n_lrc_di = sum(1 for r in rows if r["N_joint"] >= 1 and r["is_DI"] == 1)
    n_lrc_moddi = sum(1 for r in rows if r["N_joint"] >= 1 and r["is_ModDI"] == 1)
    n_nonlrc_pos = sum(1 for r in rows if r["N_joint"] >= 1
                       and r["is_DI"] == 0 and r["is_ModDI"] == 0)

    print(f"Counterexamples (N_joint=0):                {n_ce}")
    print(f"LRC-realisable DI inputs (N_joint>=1):      {n_lrc_di}")
    print(f"LRC-realisable ModDI inputs (N_joint>=1):   {n_lrc_moddi}")
    print(f"Non-LRC with N_joint>=1:                    {n_nonlrc_pos}")
    print()

    # Write CSV
    out_path = "/Users/trentpalelei/Desktop/Math Ex/reports/phase4_invariants.csv"
    import os
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    fieldnames = list(rows[0].keys()) if rows else []
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)
    print(f"Wrote {len(rows)} rows to {out_path}")

    # Separation analysis: for each invariant column, check if values
    # on N_joint=0 are disjoint from values on N_joint>=1 (specifically for
    # LRC-realisable inputs).
    print()
    print("=" * 78)
    print("Separation analysis (counterexamples vs LRC-realisable inputs)")
    print("=" * 78)
    ce = [r for r in rows if r["N_joint"] == 0]
    lrc = [r for r in rows if r["N_joint"] >= 1 and (r["is_DI"] or r["is_ModDI"])]
    print(f"CE: {len(ce)} rows; LRC: {len(lrc)} rows")
    print()
    numeric_cols = [
        "p_over_nLG", "cIG", "cIA", "mu_G", "mu_A",
        "gcd_p_nLG", "gcd_p_n", "gcd_p_LA",
        "shift_set_size", "shift_set_size_mod_LG",
        "band_union_count", "target_count", "expected_joint",
        "kG", "kA", "L_G", "L_A",
    ]
    print(f"{'Invariant':<25} {'CE range':<30} {'LRC range':<30} {'Sep?':<5}")
    print("-" * 90)
    for col in numeric_cols:
        ce_vals = [r[col] for r in ce if r[col] != -1]
        lrc_vals = [r[col] for r in lrc if r[col] != -1]
        if not ce_vals or not lrc_vals:
            continue
        ce_min, ce_max = min(ce_vals), max(ce_vals)
        lrc_min, lrc_max = min(lrc_vals), max(lrc_vals)
        # Check separation
        sep = ""
        if ce_max < lrc_min:
            sep = "CE<LRC"
        elif lrc_max < ce_min:
            sep = "LRC<CE"
        elif ce_min > lrc_max:
            sep = "CE>LRC"
        elif lrc_min > ce_max:
            sep = "LRC>CE"
        elif ce_min == ce_max and ce_min not in lrc_vals:
            sep = "CE-iso"
        print(f"{col:<25} [{ce_min},{ce_max}]{'':<10} [{lrc_min},{lrc_max}]{'':<10} {sep}")


if __name__ == "__main__":
    main()
