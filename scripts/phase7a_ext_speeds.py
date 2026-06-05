"""
Phase 7a-ext — Extended search with speeds 1..12 to confirm n=9, 10 are
residual-free for LRC-shape.

Phase 7a (speeds 1..8) found 0 residual at n=9. But the search was limited
(124 LRC-shape inputs only). This extension uses speeds 1..12 to enlarge
the search and check if residual stays at 0 for n ∈ {9, 10}.

Same logic as phase7a, just with SPEED_POOL = list(range(1, 13)).
"""

import csv
import itertools
import math
import os
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


def band_coverage(n, G_speeds, A_speeds, p, I_G):
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    nLG = n * L_G
    nLGLA = nLG * L_A
    band_betas = set()
    for a in I_G:
        r = (a * p) % nLG
        band_start = r * L_A
        for e in range(L_A * p):
            pos = (band_start + e) % nLGLA
            beta = pos // L_G
            band_betas.add(beta)
    return band_betas


def compute_row(n, G_speeds, A_speeds, p):
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    nLA = n * L_A
    I_G = good_cell_idx(G_speeds, n, L_G)
    I_A = good_cell_idx(A_speeds, n, L_A)
    band_betas = band_coverage(n, G_speeds, A_speeds, p, I_G)
    N_joint = len(band_betas & set(I_A))
    pigeon_ok = (len(band_betas) + len(I_A)) > nLA
    return {
        "n": n, "G_speeds": "-".join(map(str, G_speeds)),
        "A_speeds": "-".join(map(str, A_speeds)), "p": p,
        "kG": len(G_speeds), "kA": len(A_speeds),
        "L_G": L_G, "L_A": L_A, "nLA": nLA,
        "cIG": len(I_G), "cIA": len(I_A),
        "n_band_betas": len(band_betas),
        "pigeonhole_holds": int(pigeon_ok),
        "N_joint": N_joint,
        "lrc_class": classify_lrc(n, G_speeds, A_speeds, p),
    }


def main():
    print("=" * 78)
    print("PHASE 7a-ext — Extended speeds (1..12) for n ∈ {9, 10}")
    print("=" * 78)
    SPEED_POOL = list(range(1, 13))
    PRIMES = [p for p in range(2, 25) if isprime(p)]
    NS_CARDS = {
        9: [(6, 2), (7, 1)],
        10: [(7, 2), (8, 1)],
    }
    M_BUDGET = 10_000_000

    rows = []
    total_seen = 0
    for n in [9, 10]:
        print(f"\nScanning n = {n} ...")
        for (kG, kA) in NS_CARDS[n]:
            count = 0
            for G_speeds_tup in itertools.combinations(SPEED_POOL, kG):
                G_speeds = list(G_speeds_tup)
                L_G = lcm_list(G_speeds)
                I_G_local = good_cell_idx(G_speeds, n, L_G)
                if not I_G_local:
                    continue
                for A_speeds_tup in itertools.combinations(SPEED_POOL, kA):
                    A_speeds = list(A_speeds_tup)
                    if set(G_speeds) & set(A_speeds):
                        continue
                    L_A = lcm_list(A_speeds)
                    I_A_local = good_cell_idx(A_speeds, n, L_A)
                    if not I_A_local:
                        continue
                    for p in PRIMES:
                        if math.gcd(p, L_G) != 1:
                            continue
                        if p in G_speeds or p in A_speeds:
                            continue
                        if not (p < n * L_G):
                            continue
                        M = n * L_G * L_A * p
                        if M > M_BUDGET:
                            continue
                        g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                        if g_all != 1:
                            continue
                        total_seen += 1
                        count += 1
                        row = compute_row(n, G_speeds, A_speeds, p)
                        if row["lrc_class"] in {"DI", "ModDI"}:
                            rows.append(row)
            print(f"  kG={kG}, kA={kA}: scanned {count} candidates")

    print()
    print(f"Total inputs considered: {total_seen}")
    print(f"Total LRC-shape rows: {len(rows)}")

    pigeon_ok_count = sum(1 for r in rows if r["pigeonhole_holds"] == 1)
    pigeon_fail_count = len(rows) - pigeon_ok_count
    print(f"  Pigeonhole holds: {pigeon_ok_count}")
    print(f"  Pigeonhole fails: {pigeon_fail_count}")

    ce_count = sum(1 for r in rows if r["N_joint"] == 0)
    print(f"  CE count (should be 0): {ce_count}")

    for n in [9, 10]:
        n_rows = [r for r in rows if r["n"] == n]
        n_lrc = len(n_rows)
        n_pigeon_ok = sum(1 for r in n_rows if r["pigeonhole_holds"] == 1)
        n_resid = sum(1 for r in n_rows if r["pigeonhole_holds"] == 0)
        n_ce = sum(1 for r in n_rows if r["N_joint"] == 0)
        print(f"  n={n}: total={n_lrc}, pigeon_ok={n_pigeon_ok}, "
              f"residual={n_resid}, CE={n_ce}")

    residual_rows = [r for r in rows if r["pigeonhole_holds"] == 0]
    print(f"\nResidual cases ({len(residual_rows)}):")
    if residual_rows:
        keys = ["n", "G_speeds", "A_speeds", "p", "kG", "kA", "L_G", "L_A",
                "cIG", "cIA", "n_band_betas", "N_joint", "lrc_class"]
        print(" | ".join(f"{k:>16}" for k in keys))
        for r in residual_rows[:50]:
            print(" | ".join(f"{r[k]!s:>16}" for k in keys))

    if rows:
        out_path = "/Users/trentpalelei/Desktop/Math Ex/reports/phase7a_ext_speeds.csv"
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        fieldnames = list(rows[0].keys())
        with open(out_path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            for r in rows:
                w.writerow(r)
        print(f"\nWrote {len(rows)} rows to {out_path}")


if __name__ == "__main__":
    main()
