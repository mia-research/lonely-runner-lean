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


def floor_reset_events(E_non: list[int], b0: int, b_upper: int, L: int) -> list[tuple[int, int, int]]:
    events: list[tuple[int, int, int]] = []
    for e in E_non:
        t_start = (e * b0) // L
        t_end = (e * b_upper) // L
        for t in range(t_start + 1, t_end + 1):
            b_event = (t * L) // e
            if b0 < b_event <= b_upper and (e * b_event) % L == 0:
                events.append((b_event, e, t))
    return sorted(events)


def grouped_events(
    E_non: list[int], b0: int, b_upper: int, L: int
) -> list[tuple[int, list[tuple[int, int]]]]:
    buckets: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for b, e, t in floor_reset_events(E_non, b0, b_upper, L):
        buckets[b].append((e, t))
    return sorted(buckets.items())


def first_thin_chain(E: tuple[int, ...], n: int) -> dict | None:
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    b_upper = ((n - 1) * L) // n
    E_non = [e for e in E if e % n != 0]

    cover0 = multiplicities(E_non, b0, L, n)
    if len(cover0) < n:
        return None

    thin = [(r, runners[0]) for r, runners in sorted(cover0.items()) if len(runners) == 1]
    if not thin:
        return None

    r_star, e_star = thin[0]
    chain = [(b0, r_star, e_star)]
    current_r = r_star
    current_e = e_star

    for b_ev, _, _ in floor_reset_events(E_non, b0, b_upper, L):
        cover_after = multiplicities(E_non, b_ev, L, n)
        if len(cover_after) < n:
            missing = sorted(set(range(n)) - set(cover_after.keys()))
            return {
                "E": E,
                "n": n,
                "L": L,
                "b0": b0,
                "b_upper": b_upper,
                "E_non": E_non,
                "initial_thin": (r_star, e_star),
                "chain": chain,
                "safe_b": b_ev,
                "safe_missing": missing,
                "depth": len(chain) - 1,
            }

        cover_list_after = cover_after.get(current_r, [])
        if len(cover_list_after) == 1:
            new_e = cover_list_after[0]
            if new_e != current_e:
                chain.append((b_ev, current_r, new_e))
                current_e = new_e

    return None


def analyze_post_transfer(case: dict) -> dict | None:
    if case["depth"] != 1:
        return None

    n = case["n"]
    L = case["L"]
    E_non = case["E_non"]
    transfer_b, r_star, e_transfer = case["chain"][1]
    safe_b = case["safe_b"]

    bad_at_transfer = sorted(bad_set(e_transfer, transfer_b, L, n))
    if r_star not in bad_at_transfer or len(bad_at_transfer) != 2:
        return {
            "status": "unexpected_badset",
            "bad_at_transfer": bad_at_transfer,
        }

    companion = next(r for r in bad_at_transfer if r != r_star)

    event_rows = []
    any_add = False
    any_coincident = False
    any_coincident_add = False
    add_rows = []
    coincident_rows = []

    for b, evs in grouped_events(E_non, transfer_b, safe_b, L):
        row = {
            "b": b,
            "events": evs,
            "coincident": len(evs) > 1,
            "adds_companion": [],
        }
        before_b = b - 1 if b > transfer_b else transfer_b
        for e, _ in evs:
            before = bad_set(e, before_b, L, n)
            after = bad_set(e, b, L, n)
            if companion not in before and companion in after:
                row["adds_companion"].append(e)

        if row["coincident"]:
            any_coincident = True
            coincident_rows.append(row)
        if row["adds_companion"]:
            any_add = True
            add_rows.append(row)
        if row["coincident"] and row["adds_companion"]:
            any_coincident_add = True

        event_rows.append(row)

    return {
        "status": "ok",
        "transfer_b": transfer_b,
        "r_star": r_star,
        "e_transfer": e_transfer,
        "companion": companion,
        "safe_b": safe_b,
        "safe_missing": case["safe_missing"],
        "event_rows": event_rows,
        "any_add": any_add,
        "any_coincident": any_coincident,
        "any_coincident_add": any_coincident_add,
        "add_rows": add_rows,
        "coincident_rows": coincident_rows,
    }


def exhaustive_prime_cases(n: int, max_speed: int) -> list[tuple[int, ...]]:
    speeds = list(range(1, max_speed + 1))
    out = []
    for combo in combinations(speeds, n - 1):
        if gcd(*combo) != 1:
            continue
        if not any(e % n == 0 for e in combo):
            continue
        E_non = [e for e in combo if e % n != 0]
        R_non = {e % n for e in E_non}
        units = set(range(1, n))
        if units - R_non:
            out.append(combo)
    return out


def random_prime_cases(n: int, max_speed: int, samples: int, seed: int) -> list[tuple[int, ...]]:
    rng = random.Random(seed)
    speeds = list(range(1, max_speed + 1))
    out = []
    seen = set()
    attempts = 0
    while len(out) < samples and attempts < 200000:
        attempts += 1
        combo = tuple(sorted(rng.sample(speeds, n - 1)))
        if combo in seen:
            continue
        seen.add(combo)
        if gcd(*combo) != 1:
            continue
        if not any(e % n == 0 for e in combo):
            continue
        E_non = [e for e in combo if e % n != 0]
        R_non = {e % n for e in E_non}
        units = set(range(1, n))
        if units - R_non:
            out.append(combo)
    return out


def run_probe(cases: list[tuple[int, ...]], n: int) -> dict:
    analyzed = []
    depth_hist: dict[int, int] = defaultdict(int)
    depth1_rows = []

    for E in cases:
        case = first_thin_chain(E, n)
        if case is None:
            continue
        depth_hist[case["depth"]] += 1
        analyzed.append(case)
        if case["depth"] == 1:
            row = analyze_post_transfer(case)
            depth1_rows.append({"case": case, "post": row})

    return {
        "n": n,
        "cases_analyzed": len(analyzed),
        "depth_hist": dict(depth_hist),
        "depth1_rows": depth1_rows,
    }


def print_summary(label: str, result: dict) -> None:
    depth1_rows = result["depth1_rows"]
    coinc = sum(1 for row in depth1_rows if row["post"] and row["post"]["any_coincident"])
    add = sum(1 for row in depth1_rows if row["post"] and row["post"]["any_add"])
    coinc_add = sum(1 for row in depth1_rows if row["post"] and row["post"]["any_coincident_add"])

    print(f"== {label} ==")
    print(f"n={result['n']}")
    print(f"cases_analyzed={result['cases_analyzed']}")
    print(f"depth_hist={result['depth_hist']}")
    print(f"depth1_count={len(depth1_rows)}")
    print(f"depth1_any_coincident={coinc}")
    print(f"depth1_any_companion_add={add}")
    print(f"depth1_any_coincident_companion_add={coinc_add}")

    for row in depth1_rows[:5]:
        case = row["case"]
        post = row["post"]
        print(
            {
                "E": case["E"],
                "chain": case["chain"],
                "safe_b": case["safe_b"],
                "safe_missing": case["safe_missing"],
                "companion": None if not post else post["companion"],
                "any_coincident": None if not post else post["any_coincident"],
                "any_add": None if not post else post["any_add"],
                "any_coincident_add": None if not post else post["any_coincident_add"],
                "events": [] if not post else post["event_rows"],
            }
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exhaustive", "random"], required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--max-speed", type=int, required=True)
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    if args.mode == "exhaustive":
        cases = exhaustive_prime_cases(args.n, args.max_speed)
        label = f"exhaustive n={args.n} max_speed={args.max_speed}"
    else:
        cases = random_prime_cases(args.n, args.max_speed, args.samples, args.seed)
        label = f"random n={args.n} max_speed={args.max_speed} samples={len(cases)} seed={args.seed}"

    result = run_probe(cases, args.n)
    print_summary(label, result)


if __name__ == "__main__":
    main()
