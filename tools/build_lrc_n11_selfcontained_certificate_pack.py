#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
from itertools import combinations
from math import comb
from pathlib import Path

N = 11
RUNNERS = 9
DATE_TAG = "2026-03-30"

ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "reports" / "proofs" / f"lrc_n11_selfcontained_certificate_{DATE_TAG}"

LOCAL_ROWS = OUT_DIR / f"lrc_n11_local_profile_rows_{DATE_TAG}.csv"
BAD_ROWS = OUT_DIR / f"lrc_n11_local_bad_profile_rows_{DATE_TAG}.csv"
ACTUAL_WITNESSES = OUT_DIR / f"lrc_n11_actual_bad_state_witnesses_{DATE_TAG}.csv"
IMPOSSIBLE_ROWS = OUT_DIR / f"lrc_n11_impossible_bad_profile_rows_{DATE_TAG}.csv"
SUMMARY_MD = OUT_DIR / f"lrc_n11_selfcontained_certificate_appendix_{DATE_TAG}.md"
MANIFEST_JSON = OUT_DIR / f"lrc_n11_selfcontained_certificate_manifest_{DATE_TAG}.json"


RAW_WITNESS_ROWS = """
2 2 2 2 2 1 1 1 1 1 1,1 4 5 10 18 20 30 44 60 90
2 2 2 2 2 2 1 1 1 1 1,1 2 3 4 5 15 18 36 66 90
2 2 2 2 2 2 2 1 1 1 1,1 2 3 4 5 15 18 36 66 90
3 2 2 1 1 1 1 1 1 1 1,2 3 5 9 11 15 20 36 60 90
3 2 2 2 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
3 2 2 2 2 1 1 1 1 1 1,1 2 3 10 12 18 30 33 36 60
3 2 2 2 2 2 1 1 1 1 1,1 5 6 9 10 12 15 60 90 99
3 3 1 1 1 1 1 1 1 1 1,3 8 18 20 24 36 45 60 120 220
3 3 2 1 1 1 1 1 1 1 1,1 6 12 15 18 20 30 36 90 165
3 3 2 2 1 1 1 1 1 1 1,1 4 6 10 12 20 30 36 180 198
3 3 2 2 2 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
3 3 3 1 1 1 1 1 1 1 1,6 9 12 15 20 30 36 45 90 165
3 3 3 2 1 1 1 1 1 1 1,1 5 6 9 10 12 15 60 90 99
4 1 1 1 1 1 1 1 1 1 1,3 5 6 9 12 15 20 33 45 90
4 2 1 1 1 1 1 1 1 1 1,5 6 20 21 30 36 66 72 120 126
4 2 2 1 1 1 1 1 1 1 1,1 2 6 10 12 18 30 66 90 180
4 2 2 2 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
4 2 2 2 2 1 1 1 1 1 1,3 4 9 10 12 18 30 33 36 45
4 3 1 1 1 1 1 1 1 1 1,1 7 45 56 66 70 105 140 168 180
4 3 2 1 1 1 1 1 1 1 1,5 6 9 12 15 18 20 60 90 132
4 3 2 2 1 1 1 1 1 1 1,5 9 10 12 15 36 60 90 99 180
4 3 3 1 1 1 1 1 1 1 1,6 9 12 15 20 30 36 45 90 165
4 4 1 1 1 1 1 1 1 1 1,2 3 14 24 40 70 84 90 140 198
4 4 2 1 1 1 1 1 1 1 1,2 3 5 6 9 36 45 55 90 180
5 1 1 1 1 1 1 1 1 1 1,1 7 15 130 180 429 468 728 780 819
5 2 1 1 1 1 1 1 1 1 1,15 21 35 40 42 63 70 90 154 168
5 2 2 1 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
5 2 2 2 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
5 3 1 1 1 1 1 1 1 1 1,1 2 3 5 8 18 20 30 40 44
5 3 2 1 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
5 4 1 1 1 1 1 1 1 1 1,6 8 12 15 18 20 42 63 132 210
6 1 1 1 1 1 1 1 1 1 1,2 3 5 20 26 30 36 195 660 780
6 2 1 1 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
6 2 2 1 1 1 1 1 1 1 1,3 4 9 10 12 18 30 33 36 45
6 3 1 1 1 1 1 1 1 1 1,2 3 8 9 12 15 18 30 60 198
7 1 1 1 1 1 1 1 1 1 1,2 3 5 6 7 12 15 84 140 198
7 2 1 1 1 1 1 1 1 1 1,1 4 9 15 30 36 44 45 60 90
8 1 1 1 1 1 1 1 1 1 1,7 9 11 15 18 24 36 63 105 120
""".strip()


def canon(values: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(values, reverse=True))


def cover(profile: tuple[int, ...]) -> int:
    return sum(1 for value in profile if value > 0)


def total_branches(profile: tuple[int, ...]) -> int:
    return sum(profile)


def odd_bonf_ub(profile: tuple[int, ...], k_odd: int = 9) -> int:
    total = 0
    for t in range(1, k_odd + 1):
        vt = 0
        for value in profile:
            if value >= t:
                vt += comb(value, t)
        total += vt if (t % 2 == 1) else -vt
    return total


def enumerate_local_profiles() -> set[tuple[int, ...]]:
    states = {canon((0,) * N)}
    for _ in range(RUNNERS):
        new_states: set[tuple[int, ...]] = set()
        for state in states:
            base = list(state)
            for i in range(N):
                child = base.copy()
                child[i] += 1
                new_states.add(canon(child))
            for i, j in combinations(range(N), 2):
                child = base.copy()
                child[i] += 1
                child[j] += 1
                new_states.add(canon(child))
        states = new_states
    return states


def parse_actual_witness_rows() -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    rows: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for raw_line in RAW_WITNESS_ROWS.splitlines():
        profile_raw, witness_raw = raw_line.split(",")
        profile = tuple(int(x) for x in profile_raw.split())
        witness = tuple(int(x) for x in witness_raw.split())
        rows.append((profile, witness))
    return rows


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def build_rows() -> tuple[list[dict[str, object]], list[dict[str, object]], list[dict[str, object]], list[dict[str, object]], dict[str, object]]:
    actual_witness_map = {profile: witness for profile, witness in parse_actual_witness_rows()}
    profiles = sorted(
        enumerate_local_profiles(),
        key=lambda p: (cover(p), total_branches(p), p),
        reverse=True,
    )

    local_rows: list[dict[str, object]] = []
    bad_rows: list[dict[str, object]] = []
    impossible_rows: list[dict[str, object]] = []
    actual_rows: list[dict[str, object]] = []

    cover_histogram: dict[int, int] = {}

    for profile in profiles:
        cov = cover(profile)
        total = total_branches(profile)
        ub5 = odd_bonf_ub(profile, 5)
        ub9 = odd_bonf_ub(profile, 9)
        cap_solv = total
        min_bN_capsolv = min(N, cap_solv, ub9)
        local_lb = max(0, N - min_bN_capsolv)
        required_singleton_mass = max(0, 18 - total)
        is_bad = cov == N
        is_actual_bad = is_bad and profile[0] >= required_singleton_mass
        witness = actual_witness_map.get(profile, ())

        local_rows.append(
            {
                "profile": " ".join(map(str, profile)),
                "q1": profile[0],
                "total_branches": total,
                "cover": cov,
                "ub5": ub5,
                "ub9": ub9,
                "cap_solv": cap_solv,
                "min_bN_capsolv": min_bN_capsolv,
                "local_lb_min_bN_capsolv": local_lb,
                "required_singleton_mass": required_singleton_mass,
                "is_fully_covered": int(is_bad),
                "is_actual_bad": int(is_actual_bad),
                "has_witness": int(bool(witness)),
                "witness_tuple": " ".join(map(str, witness)),
            }
        )

        cover_histogram[cov] = cover_histogram.get(cov, 0) + 1

        if is_bad:
            row = {
                "profile": " ".join(map(str, profile)),
                "total_branches": total,
                "q1": profile[0],
                "ub5": ub5,
                "ub9": ub9,
                "required_singleton_mass": required_singleton_mass,
                "singleton_collapse_condition": int(profile[0] >= required_singleton_mass),
                "actual_bad": int(is_actual_bad),
                "witness_tuple": " ".join(map(str, witness)),
            }
            bad_rows.append(row)
            if is_actual_bad:
                actual_rows.append(
                    {
                        "profile": " ".join(map(str, profile)),
                        "witness_tuple": " ".join(map(str, witness)),
                        "total_branches": total,
                        "q1": profile[0],
                        "required_singleton_mass": required_singleton_mass,
                    }
                )
            else:
                impossible_rows.append(row)

    metadata = {
        "total_local_profiles": len(local_rows),
        "fully_covered_profiles": len(bad_rows),
        "actual_bad_profiles": len(actual_rows),
        "impossible_bad_profiles": len(impossible_rows),
        "profiles_with_positive_local_lb": sum(
            1 for row in local_rows if int(row["local_lb_min_bN_capsolv"]) > 0
        ),
        "cover_histogram": cover_histogram,
    }

    return local_rows, bad_rows, actual_rows, impossible_rows, metadata


def write_summary(metadata: dict[str, object]) -> None:
    lines = []
    lines.append("# `n = 11` Self-Contained Certificate Appendix")
    lines.append("")
    lines.append("This appendix packages the exact finite data currently available for the actual")
    lines.append("exactly-one-divisible `n = 11` branch.")
    lines.append("")
    lines.append("## Exact Objects Frozen Here")
    lines.append("")
    lines.append("- The full local multiplicity-profile kernel for `9` singleton/pair contributors on `Z_11`.")
    lines.append("- The `45` fully covered local profiles inside that kernel.")
    lines.append("- The exact singleton-collapse classifier for actual bad profiles.")
    lines.append("- Explicit witness tuples for each of the `38` actual bad local profiles.")
    lines.append("")
    lines.append("## Exact Counts")
    lines.append("")
    lines.append(f"- Total reachable local profiles: `{metadata['total_local_profiles']}`")
    lines.append(f"- Fully covered local profiles: `{metadata['fully_covered_profiles']}`")
    lines.append(f"- Actual bad profiles: `{metadata['actual_bad_profiles']}`")
    lines.append(f"- Impossible bad profiles: `{metadata['impossible_bad_profiles']}`")
    lines.append(
        f"- Profiles with positive local `min_bN_capsolv` lower bound: `{metadata['profiles_with_positive_local_lb']}`"
    )
    lines.append("")
    lines.append("## Exact Classifier")
    lines.append("")
    lines.append("Let `q^down = (q_1,...,q_11)` be a fully covered local profile and let")
    lines.append("`T = sum_i q_i`. Then the singleton-collapse theorem gives:")
    lines.append("")
    lines.append("```text")
    lines.append("q^down is actual bad  <=>  q_1 >= 18 - T.")
    lines.append("```")
    lines.append("")
    lines.append("This separates the `45` fully covered local profiles into `38` actual bad")
    lines.append("profiles and `7` impossible profiles.")
    lines.append("")
    lines.append("## Exact Limitation")
    lines.append("")
    lines.append("This packet closes the local-state layer, but it does **not** by itself prove")
    lines.append("the final weighted occupancy inequality needed for a self-contained proof of")
    lines.append("the full actual exactly-one-divisible branch.")
    lines.append("")
    lines.append("The remaining theorem target is still:")
    lines.append("")
    lines.append("```text")
    lines.append("sum_j N_j <= B_div - 10")
    lines.append("```")
    lines.append("")
    lines.append("on the actual bad-event decomposition along `B_div`.")
    lines.append("")
    lines.append("## Files")
    lines.append("")
    lines.append(f"- `{LOCAL_ROWS.name}`")
    lines.append(f"- `{BAD_ROWS.name}`")
    lines.append(f"- `{ACTUAL_WITNESSES.name}`")
    lines.append(f"- `{IMPOSSIBLE_ROWS.name}`")
    lines.append(f"- `{MANIFEST_JSON.name}`")
    SUMMARY_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_manifest(metadata: dict[str, object], files: list[Path]) -> None:
    payload = {
        "name": "lrc_n11_selfcontained_certificate_pack",
        "date": DATE_TAG,
        "exact_scope": {
            "n": N,
            "branch": "actual exactly-one-divisible local profile layer",
            "model": "9 singleton/pair contributors on Z_11",
        },
        "builder_script": {
            "file": Path(__file__).name,
            "sha256": sha256(Path(__file__)),
        },
        "counts": metadata,
        "files": [],
    }
    for path in files:
        payload["files"].append(
            {
                "file": path.name,
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
        )
    MANIFEST_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    local_rows, bad_rows, actual_rows, impossible_rows, metadata = build_rows()

    write_csv(
        LOCAL_ROWS,
        [
            "profile",
            "q1",
            "total_branches",
            "cover",
            "ub5",
            "ub9",
            "cap_solv",
            "min_bN_capsolv",
            "local_lb_min_bN_capsolv",
            "required_singleton_mass",
            "is_fully_covered",
            "is_actual_bad",
            "has_witness",
            "witness_tuple",
        ],
        local_rows,
    )
    write_csv(
        BAD_ROWS,
        [
            "profile",
            "total_branches",
            "q1",
            "ub5",
            "ub9",
            "required_singleton_mass",
            "singleton_collapse_condition",
            "actual_bad",
            "witness_tuple",
        ],
        bad_rows,
    )
    write_csv(
        ACTUAL_WITNESSES,
        [
            "profile",
            "witness_tuple",
            "total_branches",
            "q1",
            "required_singleton_mass",
        ],
        actual_rows,
    )
    write_csv(
        IMPOSSIBLE_ROWS,
        [
            "profile",
            "total_branches",
            "q1",
            "ub5",
            "ub9",
            "required_singleton_mass",
            "singleton_collapse_condition",
            "actual_bad",
            "witness_tuple",
        ],
        impossible_rows,
    )
    write_summary(metadata)
    write_manifest(metadata, [LOCAL_ROWS, BAD_ROWS, ACTUAL_WITNESSES, IMPOSSIBLE_ROWS, SUMMARY_MD])

    print(OUT_DIR)
    for path in [LOCAL_ROWS, BAD_ROWS, ACTUAL_WITNESSES, IMPOSSIBLE_ROWS, SUMMARY_MD, MANIFEST_JSON]:
        print(path)


if __name__ == "__main__":
    main()
