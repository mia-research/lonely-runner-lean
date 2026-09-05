from __future__ import annotations

import argparse
import random
from collections import defaultdict
from itertools import combinations
from math import gcd, lcm


def bad_set(e: int, b: int, L: int, n: int) -> set[int]:
    t = (e * b) // L
    rho = e % n
    return {
        r
        for r in range(n)
        if (rho * r + t) % n == 0 or (rho * r + t + 1) % n == 0
    }


def multiplicities(E_non: list[int], b: int, L: int, n: int) -> dict[int, list[int]]:
    cover: dict[int, list[int]] = defaultdict(list)
    for e in E_non:
        for r in bad_set(e, b, L, n):
            cover[r].append(e)
    return dict(cover)


def grouped_events(
    E_non: list[int], b0: int, b_upper: int, L: int
) -> list[tuple[int, list[tuple[int, int]]]]:
    buckets: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for e in E_non:
        t0 = (e * b0) // L
        t_upper = (e * b_upper) // L
        for t in range(t0 + 1, t_upper + 1):
            b = (t * L) // e
            if b0 < b <= b_upper and (e * b) % L == 0:
                buckets[b].append((e, t))
    return sorted(buckets.items())


def analyze_start(E: tuple[int, ...], n: int, r0: int, e0: int) -> dict | None:
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    b_upper = ((n - 1) * L) // n
    E_non = [e for e in E if e % n != 0]

    current_r = r0
    current_e = e0
    depth = 0
    transfer = None

    for b, _ in grouped_events(E_non, b0, b_upper, L):
        cover = multiplicities(E_non, b, L, n)
        if len(cover) < n:
            safe = (b, sorted(set(range(n)) - set(cover.keys())))
            break

        cover_list = cover.get(current_r, [])
        if len(cover_list) == 1 and cover_list[0] != current_e:
            current_e = cover_list[0]
            depth += 1
            transfer = (b, current_r, current_e)
    else:
        return None

    if depth == 0:
        return {
            "good": True,
            "depth": 0,
            "safe": safe,
            "companion_readd": False,
        }

    transfer_b, transfer_r, transfer_e = transfer
    companion = next(r for r in sorted(bad_set(transfer_e, transfer_b, L, n)) if r != transfer_r)

    companion_readd = False
    coincident_companion_readd = False
    for b, evs in grouped_events(E_non, transfer_b, safe[0], L):
        before_b = b - 1 if b > transfer_b else transfer_b
        adds = []
        for e, _ in evs:
            before = bad_set(e, before_b, L, n)
            after = bad_set(e, b, L, n)
            if companion not in before and companion in after:
                adds.append(e)
        if adds:
            companion_readd = True
            if len(evs) > 1:
                coincident_companion_readd = True

    return {
        "good": not companion_readd,
        "depth": depth,
        "safe": safe,
        "companion_readd": companion_readd,
        "coincident_companion_readd": coincident_companion_readd,
    }


def thin_rows(E: tuple[int, ...], n: int) -> tuple[list[dict], int, int]:
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    E_non = [e for e in E if e % n != 0]
    cover = multiplicities(E_non, b0, L, n)

    rows = []
    for r, runners in cover.items():
        if len(runners) != 1:
            continue
        e = runners[0]
        q = e // n
        rho = e % n
        inv = pow(rho, -1, n)
        a_low = (-q * inv) % n
        a_high = (-(q + 1) * inv) % n
        pos = "low" if r == a_low else ("high" if r == a_high else "other")
        rows.append(
            {
                "r": r,
                "e": e,
                "n": n,
                "q": q,
                "rho": rho,
                "pos": pos,
            }
        )
    return rows, L, b0


def choose_row(rows: list[dict], rule: str) -> dict:
    if rule == "min_e":
        return min(rows, key=lambda row: (row["e"], row["r"]))
    if rule == "min_q":
        return min(rows, key=lambda row: (row["q"], row["e"], row["r"]))
    if rule == "min_e_high":
        return min(rows, key=lambda row: (row["e"], 0 if row["pos"] == "high" else 1, row["r"]))
    if rule == "min_e_low":
        return min(rows, key=lambda row: (row["e"], 0 if row["pos"] == "low" else 1, row["r"]))
    if rule == "high_min_e":
        highs = [row for row in rows if row["pos"] == "high"]
        if highs:
            return min(highs, key=lambda row: (row["e"], row["r"]))
        return min(rows, key=lambda row: (row["e"], row["r"]))
    if rule == "high_max_hold":
        highs = [row for row in rows if row["pos"] == "high"]
        if highs:
            return min(
                highs,
                key=lambda row: (
                    row["e"] / (2 * row["n"] - row["rho"]),
                    row["e"],
                    row["r"],
                ),
            )
        return min(rows, key=lambda row: (row["e"], row["r"]))
    raise ValueError(f"unknown rule: {rule}")


def exhaustive_prime_cases(n: int, max_speed: int) -> list[tuple[int, ...]]:
    out = []
    for E in combinations(range(1, max_speed + 1), n - 1):
        if gcd(*E) != 1:
            continue
        if not any(e % n == 0 for e in E):
            continue
        E_non = [e for e in E if e % n != 0]
        if set(range(1, n)) - {e % n for e in E_non}:
            out.append(E)
    return out


def random_prime_cases(n: int, max_speed: int, samples: int, seed: int) -> list[tuple[int, ...]]:
    rng = random.Random(seed)
    speeds = list(range(1, max_speed + 1))
    out = []
    seen = set()
    attempts = 0

    while len(out) < samples and attempts < 500000:
        attempts += 1
        E = tuple(sorted(rng.sample(speeds, n - 1)))
        if E in seen:
            continue
        seen.add(E)
        if gcd(*E) != 1:
            continue
        if not any(e % n == 0 for e in E):
            continue
        E_non = [e for e in E if e % n != 0]
        if set(range(1, n)) - {e % n for e in E_non}:
            out.append(E)
    return out


def run_scan(cases: list[tuple[int, ...]], n: int, rule: str) -> dict:
    full_cover = 0
    successes = 0
    depth_hist: dict[int, int] = defaultdict(int)
    failures = []

    for E in cases:
        rows, L, b0 = thin_rows(E, n)
        E_non = [e for e in E if e % n != 0]
        if len(multiplicities(E_non, b0, L, n)) < n:
            continue
        full_cover += 1
        chosen = choose_row(rows, rule)
        result = analyze_start(E, n, chosen["r"], chosen["e"])
        if result is None:
            continue
        depth_hist[result["depth"]] += 1
        if result["good"]:
            successes += 1
        elif len(failures) < 10:
            failures.append(
                {
                    "E": E,
                    "chosen": chosen,
                    "result": result,
                    "rows": rows,
                }
            )

    return {
        "n": n,
        "rule": rule,
        "full_cover": full_cover,
        "successes": successes,
        "depth_hist": dict(depth_hist),
        "failures": failures,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exhaustive", "random"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--max-speed", type=int, required=True)
    parser.add_argument("--rule", default="min_e")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    if args.mode == "exhaustive":
        cases = exhaustive_prime_cases(args.n, args.max_speed)
    else:
        cases = random_prime_cases(args.n, args.max_speed, args.samples, args.seed)

    result = run_scan(cases, args.n, args.rule)
    print(
        {
            "mode": args.mode,
            "n": args.n,
            "max_speed": args.max_speed,
            "rule": args.rule,
            "cases": len(cases),
            "full_cover": result["full_cover"],
            "successes": result["successes"],
            "depth_hist": result["depth_hist"],
            "failures": result["failures"][:5],
        }
    )


if __name__ == "__main__":
    main()
