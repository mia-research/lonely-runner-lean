"""
Phase 7a-quick — focused n=10 search, smaller scope.

Speeds 1..10, primes 2..13, n in {9, 10}, kG up to (n-2), kA up to 2.
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


def main():
    print("PHASE 7a-quick (n=9, 10, speeds ≤ 10, primes ≤ 13)")
    SPEED_POOL = list(range(1, 11))
    PRIMES = [p for p in range(2, 14) if isprime(p)]
    NS_CARDS = {
        9: [(6, 2), (7, 1)],
        10: [(7, 2), (8, 1)],
    }
    M_BUDGET = 5_000_000

    rows = []
    for n in [9, 10]:
        for (kG, kA) in NS_CARDS[n]:
            cnt = 0
            for G_t in itertools.combinations(SPEED_POOL, kG):
                G_speeds = list(G_t)
                L_G = lcm_list(G_speeds)
                if not good_cell_idx(G_speeds, n, L_G):
                    continue
                for A_t in itertools.combinations(SPEED_POOL, kA):
                    A_speeds = list(A_t)
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
                        if math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0)) != 1:
                            continue
                        cls = classify_lrc(n, G_speeds, A_speeds, p)
                        if cls not in {'DI', 'ModDI'}:
                            continue
                        I_G = good_cell_idx(G_speeds, n, L_G)
                        band_betas = band_coverage(n, G_speeds, A_speeds, p, I_G)
                        nLA = n * L_A
                        pigeon_ok = (len(band_betas) + len(I_A_local)) > nLA
                        N_j = len(band_betas & set(I_A_local))
                        rows.append({
                            "n": n, "G": "-".join(map(str, G_speeds)),
                            "A": "-".join(map(str, A_speeds)), "p": p,
                            "kG": kG, "kA": kA, "L_G": L_G, "L_A": L_A,
                            "cIG": len(I_G), "cIA": len(I_A_local),
                            "nband": len(band_betas), "pigeon_ok": int(pigeon_ok),
                            "N_joint": N_j, "lrc_class": cls,
                        })
                        cnt += 1
            print(f"  n={n} (kG={kG}, kA={kA}): {cnt} LRC-shape")

    print(f"\nTotal LRC-shape: {len(rows)}")
    pigeon_ok = sum(r['pigeon_ok'] for r in rows)
    pigeon_fail = len(rows) - pigeon_ok
    ce = sum(1 for r in rows if r['N_joint'] == 0)
    print(f"Pigeonhole holds: {pigeon_ok}; fails: {pigeon_fail}; CE: {ce}")

    for n in [9, 10]:
        nr = [r for r in rows if r['n'] == n]
        nrok = sum(r['pigeon_ok'] for r in nr)
        nrfail = len(nr) - nrok
        nrce = sum(1 for r in nr if r['N_joint'] == 0)
        print(f"  n={n}: total={len(nr)}, pigeon_ok={nrok}, residual={nrfail}, CE={nrce}")

    residual = [r for r in rows if r['pigeon_ok'] == 0]
    if residual:
        print(f"\nResidual cases ({len(residual)}):")
        for r in residual[:30]:
            print(f"  n={r['n']} G={r['G']} A={r['A']} p={r['p']} "
                  f"cIG={r['cIG']} cIA={r['cIA']} nband={r['nband']} "
                  f"N_j={r['N_joint']} class={r['lrc_class']}")

    if rows:
        out_path = "/Users/trentpalelei/Desktop/Math Ex/reports/phase7a_n10_quick.csv"
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            for r in rows:
                w.writerow(r)
        print(f"\nWrote to {out_path}")


if __name__ == "__main__":
    main()
