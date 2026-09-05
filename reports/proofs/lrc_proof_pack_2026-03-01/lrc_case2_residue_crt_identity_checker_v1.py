#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from itertools import combinations, product

OUT_ROWS = "/tmp/lrc_case2_residue_crt_identity_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_residue_crt_identity_summary_v1.md"

EXHAUSTIVE_MAX = {
    3: 12,
    4: 9,
    5: 7,
}
RANDOM_PLAN = [
    (6, 4000, 8),
    (7, 3000, 7),
    (8, 2000, 10),
]


def solve_linear_residue(e: int, c: int, n: int):
    """Return (modulus m, residue r) for a ≡ r (mod m), or None if unsolvable.

    Equation: e a ≡ c (mod n).
    """
    g = math.gcd(e, n)
    if c % g != 0:
        return None
    e1 = e // g
    c1 = c // g
    m = n // g
    r = (pow(e1, -1, m) * c1) % m
    return (m, r)


def count_crt_system(congruences: list[tuple[int, int]], n: int) -> int:
    """Count solutions in Z_n to a ≡ r_i (mod m_i)."""
    if not congruences:
        return n
    m0, r0 = congruences[0]
    M = m0
    R = r0
    for m, r in congruences[1:]:
        g = math.gcd(M, m)
        if (r - R) % g != 0:
            return 0
        l = M // g * m
        # merge congruences
        t = ((r - R) // g) * pow(M // g, -1, m // g) % (m // g)
        R = (R + M * t) % l
        M = l
    # Solutions in Z_n are residues congruent to R mod M
    return n // M


def bad_set_formula_for_speed(e: int, b: int, n: int, L: int):
    """Return bad-a set via residue-class branch formula."""
    N = n * L
    x = (e * b) % N
    u = x // L
    d = x % L

    branches = [(-u) % n]
    if d > 0:
        branches.append((-u - 1) % n)

    aset = set()
    for c in branches:
        sr = solve_linear_residue(e, c, n)
        if sr is None:
            continue
        m, r = sr
        for a in range(r, n, m):
            aset.add(a)
    return aset, branches


def bad_set_direct_for_speed(e: int, b: int, n: int, L: int):
    N = n * L
    lo = L
    hi = (n - 1) * L
    aset = set()
    for a in range(n):
        k = a * L + b
        v = (e * k) % N
        if v < lo or v > hi:
            aset.add(a)
    return aset


def fiber_moments_from_sets(speed_sets: list[set[int]], n: int):
    I = P = T = 0
    for a in range(n):
        q = sum(1 for s in speed_sets if a in s)
        I += q
        P += q * (q - 1) // 2
        T += q * (q - 1) * (q - 2) // 6
    return I, P, T


def fiber_moments_direct(E_non: list[int], b: int, n: int, L: int):
    N = n * L
    lo = L
    hi = (n - 1) * L
    I = P = T = 0
    for a in range(n):
        k = a * L + b
        q = 0
        for e in E_non:
            v = (e * k) % N
            if v < lo or v > hi:
                q += 1
        I += q
        P += q * (q - 1) // 2
        T += q * (q - 1) * (q - 2) // 6
    return I, P, T


def branch_intersection_count(branch_data: list[tuple[int, list[int]]], pick: tuple[int, ...], n: int) -> int:
    """Pick one branch c_i per selected speed and count CRT solutions."""
    congruences = []
    for idx, branch_choice in enumerate(pick):
        e, branches = branch_data[idx]
        if branch_choice >= len(branches):
            return 0
        c = branches[branch_choice]
        sr = solve_linear_residue(e, c, n)
        if sr is None:
            return 0
        congruences.append(sr)
    return count_crt_system(congruences, n)


def analyze_tuple(E: tuple[int, ...], n: int, sample_b_limit: int | None = None):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]
    if sample_b_limit is not None and len(B_div) > sample_b_limit:
        B_div = random.sample(B_div, sample_b_limit)

    for b in B_div:
        # per-speed bad set equivalence
        speed_sets = []
        branch_data = []
        for e in E_non:
            s_form, branches = bad_set_formula_for_speed(e, b, n, L)
            s_dir = bad_set_direct_for_speed(e, b, n, L)
            if s_form != s_dir:
                return False, {
                    "fail": "speed_badset_mismatch",
                    "n": n,
                    "E": E,
                    "L": L,
                    "b": b,
                    "e": e,
                    "formula": sorted(s_form),
                    "direct": sorted(s_dir),
                }
            speed_sets.append(s_form)
            branch_data.append((e, branches))

        # I,P,T from set-system vs direct
        I1, P1, T1 = fiber_moments_from_sets(speed_sets, n)
        I2, P2, T2 = fiber_moments_direct(E_non, b, n, L)
        if (I1, P1, T1) != (I2, P2, T2):
            return False, {
                "fail": "moment_mismatch",
                "n": n,
                "E": E,
                "L": L,
                "b": b,
                "set_mom": (I1, P1, T1),
                "dir_mom": (I2, P2, T2),
            }

        # Pair/triple CRT branch counts
        # compare branch sum vs direct intersection size
        for i, j in combinations(range(len(E_non)), 2):
            A = speed_sets[i] & speed_sets[j]
            cnt_dir = len(A)
            cnt = 0
            ei, bi = branch_data[i]
            ej, bj = branch_data[j]
            # branch products are disjoint by construction per speed
            for xi in range(len(bi)):
                for xj in range(len(bj)):
                    cnt += branch_intersection_count([(ei, bi), (ej, bj)], (xi, xj), n)
            if cnt != cnt_dir:
                return False, {
                    "fail": "pair_crt_mismatch",
                    "n": n,
                    "E": E,
                    "L": L,
                    "b": b,
                    "pair": (E_non[i], E_non[j]),
                    "crt": cnt,
                    "direct": cnt_dir,
                }

        for i, j, k in combinations(range(len(E_non)), 3):
            A = speed_sets[i] & speed_sets[j] & speed_sets[k]
            cnt_dir = len(A)
            cnt = 0
            ei, bi = branch_data[i]
            ej, bj = branch_data[j]
            ek, bk = branch_data[k]
            for xi in range(len(bi)):
                for xj in range(len(bj)):
                    for xk in range(len(bk)):
                        cnt += branch_intersection_count([(ei, bi), (ej, bj), (ek, bk)], (xi, xj, xk), n)
            if cnt != cnt_dir:
                return False, {
                    "fail": "triple_crt_mismatch",
                    "n": n,
                    "E": E,
                    "L": L,
                    "b": b,
                    "triple": (E_non[i], E_non[j], E_non[k]),
                    "crt": cnt,
                    "direct": cnt_dir,
                }

    return True, {
        "n": n,
        "E": E,
        "L": L,
        "checked_b": len(B_div),
    }


def main() -> None:
    random.seed(0)
    rows = []
    summary_lines = ["# Case-2 Residue/CRT Identity Checker (v1)", "", "Validated identities:", "- per-speed bad-a set = union of <=2 linear congruence classes mod n", "- fiber moments I_b,P_b,T_b from set-system match direct counting", "- pair/triple intersections from branch CRT counts match direct intersections", ""]

    # exhaustive small-n
    summary_lines.append("## Exhaustive blocks")
    summary_lines.append("| n | tuples checked | status |")
    summary_lines.append("|---:|---:|---:|")
    for n, max_e in EXHAUSTIVE_MAX.items():
        checked = 0
        ok = True
        fail = None
        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            checked += 1
            good, info = analyze_tuple(E, n)
            if not good:
                ok = False
                fail = info
                break
        summary_lines.append(f"| {n} | {checked} | {'OK' if ok else 'FAIL'} |")
        rows.append({"mode": "exhaustive", "n": n, "checked": checked, "ok": int(ok), "detail": str(fail) if fail else ""})

    # random higher-n
    summary_lines.append("")
    summary_lines.append("## Random higher-n blocks")
    summary_lines.append("| n | sampled tuples | max_e | sample_b_limit | status |")
    summary_lines.append("|---:|---:|---:|---:|---:|")
    for n, samples, max_e in RANDOM_PLAN:
        checked = 0
        tries = 0
        ok = True
        fail = None
        while checked < samples and tries < samples * 200:
            tries += 1
            E = tuple(random.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            L = math.lcm(*E)
            if L > 1800:
                continue
            checked += 1
            good, info = analyze_tuple(E, n, sample_b_limit=40)
            if not good:
                ok = False
                fail = info
                break
        summary_lines.append(f"| {n} | {checked} | {max_e} | 40 | {'OK' if ok else 'FAIL'} |")
        rows.append({"mode": "random", "n": n, "checked": checked, "ok": int(ok), "detail": str(fail) if fail else ""})

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["mode", "n", "checked", "ok", "detail"])
        w.writeheader()
        w.writerows(rows)

    summary_lines.append("")
    summary_lines.append("Artifacts:")
    summary_lines.append(f"- rows: `{OUT_ROWS}`")
    summary_lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(summary_lines) + "\n")

    print("FINAL")
    print("rows", OUT_ROWS)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
