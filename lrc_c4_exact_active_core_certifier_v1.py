from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Iterable, Sequence

try:
    from lrc_n11_c4_finite_transition_probe_v2 import (
        L_C4,
        R_C4,
        RELEASED,
        folded_state_cells,
        format_fraction,
        minimal_covers_by_size,
        unique_low_nonempty_states,
    )
except ModuleNotFoundError:
    FALLBACK_ROOT = Path("/Users/trentpalelei/Documents/Claude Library")
    if str(FALLBACK_ROOT) not in sys.path:
        sys.path.insert(0, str(FALLBACK_ROOT))
    from lrc_n11_c4_finite_transition_probe_v2 import (
        L_C4,
        R_C4,
        RELEASED,
        folded_state_cells,
        format_fraction,
        minimal_covers_by_size,
        unique_low_nonempty_states,
    )


ELEVEN = Fraction(11)
HALF_ELEVEN = Fraction(11, 2)
ACTIVE_THRESHOLD = Fraction(40, 9)
FOLDED_CELLS = folded_state_cells()
FOLDED_BOUNDARIES = tuple(
    sorted({left for left, _, _ in FOLDED_CELLS} | {right for _, right, _ in FOLDED_CELLS})
)


def frac_floor(x: Fraction) -> int:
    return x.numerator // x.denominator


def frac_ceil(x: Fraction) -> int:
    return -frac_floor(-x)


def frac_str(x: Fraction) -> str:
    return format_fraction(x)


def state_str(state: Sequence[int]) -> str:
    if not state:
        return "[]"
    return "[" + ",".join(str(x) for x in state) + "]"


def interval_str(iv: tuple[Fraction, Fraction]) -> str:
    return f"({frac_str(iv[0])},{frac_str(iv[1])})"


def fold_mod_11(y: Fraction) -> Fraction:
    q = y.numerator // (y.denominator * 11)
    r = y - ELEVEN * q
    if r > HALF_ELEVEN:
        r = ELEVEN - r
    return r


def active_in_C4(lam: Fraction) -> bool:
    return lam >= ACTIVE_THRESHOLD


def service_state_at_a(a: Fraction) -> tuple[int, ...]:
    return tuple(
        m for m in RELEASED if ((a * m) % ELEVEN) < 1 or ((a * m) % ELEVEN) > 10
    )


def service_state_at_x(lam: Fraction, x: Fraction) -> tuple[int, ...]:
    return service_state_at_a(fold_mod_11(lam * x))


def runner_breakpoints_in_C4(lam: Fraction) -> list[Fraction]:
    pts = {L_C4, R_C4}
    lo_y = lam * L_C4
    hi_y = lam * R_C4
    max_beta = FOLDED_BOUNDARIES[-1]
    k_lo = frac_floor((lo_y - max_beta) / ELEVEN) - 2
    k_hi = frac_ceil((hi_y + max_beta) / ELEVEN) + 2

    for k in range(k_lo, k_hi + 1):
        kk = ELEVEN * k
        for beta in FOLDED_BOUNDARIES:
            for num in (kk + beta, kk - beta):
                if num < 0:
                    continue
                x = num / lam
                if L_C4 <= x <= R_C4:
                    pts.add(x)
    return sorted(pts)


def induced_x_partition(lambdas: Sequence[Fraction]) -> list[tuple[Fraction, Fraction]]:
    pts = {L_C4, R_C4}
    for lam in lambdas:
        pts.update(runner_breakpoints_in_C4(lam))
    ordered = sorted(pts)
    return [(a, b) for a, b in zip(ordered, ordered[1:]) if a < b]


def partition_profiles(
    lambdas: Sequence[Fraction],
) -> list[dict[str, object]]:
    partition = induced_x_partition(lambdas)
    out: list[dict[str, object]] = []
    for left, right in partition:
        mid = (left + right) / 2
        runner_states = tuple(service_state_at_x(lam, mid) for lam in lambdas)
        covered = tuple(sorted(set().union(*map(set, runner_states))))
        uncovered = tuple(sorted(set(RELEASED) - set(covered)))
        out.append(
            {
                "interval": (left, right),
                "mid": mid,
                "runner_states": runner_states,
                "covered": covered,
                "uncovered": uncovered,
            }
        )
    return out


def gap_intervals(lambdas: Sequence[Fraction]) -> list[dict[str, object]]:
    return [row for row in partition_profiles(lambdas) if row["uncovered"]]


def has_full_cover(lambdas: Sequence[Fraction]) -> bool:
    return not gap_intervals(lambdas)


def minimal_active_cores(lambdas: Sequence[Fraction]) -> list[tuple[int, ...]]:
    active_indices = tuple(i for i, lam in enumerate(lambdas) if active_in_C4(lam))
    minimal: list[tuple[int, ...]] = []
    for size in range(1, len(active_indices) + 1):
        for combo in combinations(active_indices, size):
            if any(set(prev).issubset(combo) for prev in minimal):
                continue
            if has_full_cover([lambdas[i] for i in combo]):
                minimal.append(combo)
    return minimal


def core_signature(lambdas: Sequence[Fraction], core: Sequence[int]) -> tuple[tuple[object, ...], ...]:
    core_lambdas = [lambdas[i] for i in core]
    signature: list[tuple[object, ...]] = []
    for row in partition_profiles(core_lambdas):
        interval = row["interval"]
        runner_states = row["runner_states"]
        covered = row["covered"]
        assert isinstance(interval, tuple)
        assert isinstance(runner_states, tuple)
        assert isinstance(covered, tuple)
        signature.append(
            (
                frac_str(interval[0]),
                frac_str(interval[1]),
                tuple(state_str(state) for state in runner_states),
                tuple(str(x) for x in covered),
            )
        )
    return tuple(signature)


def witness_ok(speeds: Sequence[int], t: Fraction, threshold: Fraction = Fraction(1, 11)) -> bool:
    for speed in speeds:
        pos = (Fraction(speed) * t) % 1
        if pos < threshold or pos > 1 - threshold:
            return False
    return True


def bounded_witnesses(
    speeds: Sequence[int],
    *,
    q_max: int = 5,
    threshold: Fraction = Fraction(1, 11),
) -> list[tuple[Fraction, int, int]]:
    out: list[tuple[Fraction, int, int]] = []
    for q in range(1, q_max + 1):
        denom = 11 * q
        for p in range(1, denom):
            t = Fraction(p, denom)
            if witness_ok(speeds, t, threshold=threshold):
                out.append((t, p, q))
    return out


def abstract_folded_summary() -> dict[str, object]:
    cells = FOLDED_CELLS
    low_states = unique_low_nonempty_states(cells)
    cover_counts = {
        size: len(covers)
        for size, covers in minimal_covers_by_size(cells, sizes=(3, 4, 5, 6)).items()
    }
    return {
        "active_threshold": frac_str(ACTIVE_THRESHOLD),
        "total_cells": len(cells),
        "low_cells": sum(1 for _, _, state in cells if len(state) <= 2),
        "high_cells": sum(1 for _, _, state in cells if len(state) >= 3),
        "unique_low_nonempty_states": [list(state) for state in low_states],
        "minimal_cover_counts": cover_counts,
    }


def state_mask(state: Sequence[int]) -> int:
    mask = 0
    for label in state:
        mask |= 1 << (label - 5)
    return mask


def bounded_global_cache(max_speed: int = 17) -> dict[str, object]:
    active_lams = tuple(Fraction(v, 1) for v in range(2, max_speed + 1) if active_in_C4(Fraction(v, 1)))
    cells = induced_x_partition(active_lams)
    mask_by_lambda: dict[Fraction, tuple[int, ...]] = {}
    state_by_lambda: dict[Fraction, tuple[tuple[int, ...], ...]] = {}
    for lam in active_lams:
        masks: list[int] = []
        states: list[tuple[int, ...]] = []
        for left, right in cells:
            mid = (left + right) / 2
            state = service_state_at_x(lam, mid)
            states.append(state)
            masks.append(state_mask(state))
        mask_by_lambda[lam] = tuple(masks)
        state_by_lambda[lam] = tuple(states)
    return {
        "active_lams": active_lams,
        "cells": cells,
        "mask_by_lambda": mask_by_lambda,
        "state_by_lambda": state_by_lambda,
        "full_mask": state_mask(RELEASED),
    }


def integer_lambda_cache(min_speed: int, max_speed: int) -> dict[str, object]:
    active_lams = tuple(Fraction(v, 1) for v in range(min_speed, max_speed + 1) if active_in_C4(Fraction(v, 1)))
    cells = induced_x_partition(active_lams)
    mask_by_lambda: dict[Fraction, tuple[int, ...]] = {}
    state_by_lambda: dict[Fraction, tuple[tuple[int, ...], ...]] = {}
    for lam in active_lams:
        masks: list[int] = []
        states: list[tuple[int, ...]] = []
        for left, right in cells:
            mid = (left + right) / 2
            state = service_state_at_x(lam, mid)
            states.append(state)
            masks.append(state_mask(state))
        mask_by_lambda[lam] = tuple(masks)
        state_by_lambda[lam] = tuple(states)
    return {
        "active_lams": active_lams,
        "cells": cells,
        "mask_by_lambda": mask_by_lambda,
        "state_by_lambda": state_by_lambda,
        "full_mask": state_mask(RELEASED),
    }


def bounded_has_full_cover(subset: Sequence[int], cache: dict[str, object]) -> bool:
    cells = cache["cells"]
    mask_by_lambda = cache["mask_by_lambda"]
    full_mask = cache["full_mask"]
    assert isinstance(cells, list)
    assert isinstance(mask_by_lambda, dict)
    assert isinstance(full_mask, int)
    active_lams = [Fraction(v, 1) for v in subset if active_in_C4(Fraction(v, 1))]

    for cell_index in range(len(cells)):
        mask = 0
        for lam in active_lams:
            mask |= mask_by_lambda[lam][cell_index]
            if mask == full_mask:
                break
        if mask != full_mask:
            return False
    return True


def bounded_minimal_active_cores(
    subset: Sequence[int],
    cache: dict[str, object],
) -> list[tuple[int, ...]]:
    active_positions = tuple(i for i, v in enumerate(subset) if active_in_C4(Fraction(v, 1)))
    cells = cache["cells"]
    mask_by_lambda = cache["mask_by_lambda"]
    full_mask = cache["full_mask"]
    assert isinstance(cells, list)
    assert isinstance(mask_by_lambda, dict)
    assert isinstance(full_mask, int)

    minimal: list[tuple[int, ...]] = []
    for size in range(1, len(active_positions) + 1):
        for combo in combinations(active_positions, size):
            if any(set(prev).issubset(combo) for prev in minimal):
                continue
            combo_lams = [Fraction(subset[i], 1) for i in combo]
            ok = True
            for cell_index in range(len(cells)):
                mask = 0
                for lam in combo_lams:
                    mask |= mask_by_lambda[lam][cell_index]
                    if mask == full_mask:
                        break
                if mask != full_mask:
                    ok = False
                    break
            if ok:
                minimal.append(combo)
    return minimal


def bounded_core_signature(
    subset: Sequence[int],
    core: Sequence[int],
    cache: dict[str, object],
) -> tuple[tuple[object, ...], ...]:
    cells = cache["cells"]
    state_by_lambda = cache["state_by_lambda"]
    assert isinstance(cells, list)
    assert isinstance(state_by_lambda, dict)

    core_lams = [Fraction(subset[i], 1) for i in core]
    signature: list[tuple[object, ...]] = []
    for cell_index, (left, right) in enumerate(cells):
        runner_states = tuple(state_by_lambda[lam][cell_index] for lam in core_lams)
        covered = tuple(sorted(set().union(*map(set, runner_states))))
        signature.append(
            (
                frac_str(left),
                frac_str(right),
                tuple(state_str(state) for state in runner_states),
                tuple(str(x) for x in covered),
            )
        )
    return tuple(signature)


def enumerate_full_cover_subsets_v1_eq_1(max_speed: int = 17) -> dict[str, object]:
    cache = bounded_global_cache(max_speed=max_speed)
    results: dict[str, object] = {
        "total_subsets": 0,
        "full_cover_subsets": 0,
        "gap_subsets": 0,
        "with_11_and_full_cover": 0,
        "with_11_and_full_cover_all_have_q_le_5_witness": True,
        "witness_counter": Counter(),
        "minimal_core_counter": Counter(),
        "signature_counter": Counter(),
        "example_core_witnesses": defaultdict(list),
        "full_cover_rows": [],
    }

    for subset in combinations(range(2, max_speed + 1), 9):
        results["total_subsets"] += 1
        lambdas = [Fraction(v, 1) for v in subset]
        full_cover = bounded_has_full_cover(subset, cache)
        if not full_cover:
            results["gap_subsets"] += 1
            continue

        results["full_cover_subsets"] += 1
        has_11 = 11 in subset
        cores = bounded_minimal_active_cores(subset, cache)
        witnesses = bounded_witnesses((1,) + subset, q_max=5)

        if has_11:
            results["with_11_and_full_cover"] += 1
            if not witnesses:
                results["with_11_and_full_cover_all_have_q_le_5_witness"] = False

        row = {
            "subset": subset,
            "has_11": has_11,
            "minimal_cores": [],
            "witnesses": [(frac_str(t), p, q) for t, p, q in witnesses],
        }

        for core in cores:
            core_speeds = tuple(subset[i] for i in core)
            results["minimal_core_counter"][core_speeds] += 1
            sig = bounded_core_signature(subset, core, cache)
            results["signature_counter"][sig] += 1
            row["minimal_cores"].append(core_speeds)
            if witnesses:
                results["example_core_witnesses"][core_speeds].append((subset, witnesses[0]))

        if witnesses:
            results["witness_counter"][(witnesses[0][1], witnesses[0][2])] += 1
        results["full_cover_rows"].append(row)

    return results


def active_core_catalogue_up_to_30() -> dict[str, object]:
    cache = integer_lambda_cache(5, 30)
    cells = cache["cells"]
    mask_by_lambda = cache["mask_by_lambda"]
    full_mask = cache["full_mask"]
    assert isinstance(cells, list)
    assert isinstance(mask_by_lambda, dict)
    assert isinstance(full_mask, int)

    full_cover_sets: list[tuple[int, ...]] = []
    for combo in combinations(range(5, 31), 6):
        ok = True
        combo_lams = [Fraction(v, 1) for v in combo]
        for cell_index in range(len(cells)):
            mask = 0
            for lam in combo_lams:
                mask |= mask_by_lambda[lam][cell_index]
                if mask == full_mask:
                    break
            if mask != full_mask:
                ok = False
                break
        if ok:
            full_cover_sets.append(combo)
    return {
        "count": len(full_cover_sets),
        "sets": full_cover_sets,
    }


def calibration_report() -> dict[str, object]:
    abstract = abstract_folded_summary()
    bounded = enumerate_full_cover_subsets_v1_eq_1(max_speed=17)

    common_witnesses_by_core: dict[tuple[int, ...], list[tuple[str, int, int]]] = {}
    for core, examples in bounded["example_core_witnesses"].items():
        candidate_intersection: set[tuple[str, int, int]] | None = None
        for subset, _ in examples:
            witnesses = {
                (frac_str(t), p, q)
                for t, p, q in bounded_witnesses((1,) + subset, q_max=5)
            }
            if candidate_intersection is None:
                candidate_intersection = witnesses
            else:
                candidate_intersection &= witnesses
        common_witnesses_by_core[core] = sorted(candidate_intersection or set())

    return {
        "abstract": abstract,
        "bounded_v1_eq_1_max17": {
            "total_subsets": bounded["total_subsets"],
            "full_cover_subsets": bounded["full_cover_subsets"],
            "gap_subsets": bounded["gap_subsets"],
            "with_11_and_full_cover": bounded["with_11_and_full_cover"],
            "with_11_all_have_q_le_5_witness": bounded[
                "with_11_and_full_cover_all_have_q_le_5_witness"
            ],
            "witness_counter": {
                f"p={p},q={q}": count for (p, q), count in bounded["witness_counter"].items()
            },
            "minimal_core_counter": {
                str(core): count for core, count in bounded["minimal_core_counter"].items()
            },
            "distinct_signature_count": len(bounded["signature_counter"]),
            "common_witnesses_by_core": {
                str(core): vals for core, vals in common_witnesses_by_core.items()
            },
        },
    }


def report_with_six_runner_catalogue() -> dict[str, object]:
    report = calibration_report()
    catalogue = active_core_catalogue_up_to_30()
    report["exact_six_runner_catalogue_up_to_30"] = {
        "count": catalogue["count"],
        "sets": [list(row) for row in catalogue["sets"]],
    }
    return report


def print_report(report: dict[str, object], *, include_six_runner_catalogue: bool = False) -> None:
    abstract = report["abstract"]
    bounded = report["bounded_v1_eq_1_max17"]
    assert isinstance(abstract, dict)
    assert isinstance(bounded, dict)

    print("# C4 exact active-core certifier report")
    print()
    print("## Abstract folded layer")
    print(f"- active threshold: {abstract['active_threshold']}")
    print(f"- total folded cells: {abstract['total_cells']}")
    print(f"- low-service cells: {abstract['low_cells']}")
    print(f"- high-service cells: {abstract['high_cells']}")
    print(
        "- minimal abstract cover counts: "
        + ", ".join(
            f"size {k} -> {v}" for k, v in sorted(abstract["minimal_cover_counts"].items())
        )
    )
    print()
    print("## Exact bounded calibration (`v1=1`, speeds in `{2,...,17}`)")
    print(f"- total 9-subsets: {bounded['total_subsets']}")
    print(f"- full `C4` cover subsets: {bounded['full_cover_subsets']}")
    print(f"- gap subsets: {bounded['gap_subsets']}")
    print(f"- with runner `11` and full `C4` cover: {bounded['with_11_and_full_cover']}")
    print(
        "- all full-cover + runner-`11` subsets have a `q<=5` witness: "
        f"{bounded['with_11_all_have_q_le_5_witness']}"
    )
    print(f"- distinct exact core signatures: {bounded['distinct_signature_count']}")
    print("- exact minimal active cores and how often they occur:")
    for core, count in sorted(
        bounded["minimal_core_counter"].items(), key=lambda item: (-item[1], item[0])
    ):
        print(f"  - {core}: {count}")
    print("- common bounded witness families by minimal active core:")
    for core, vals in sorted(bounded["common_witnesses_by_core"].items()):
        preview = ", ".join(f"{t} (p={p}, q={q})" for t, p, q in vals[:8])
        print(f"  - {core}: {preview if preview else 'none'}")

    if include_six_runner_catalogue:
        six = report["exact_six_runner_catalogue_up_to_30"]
        assert isinstance(six, dict)
        print()
        print("## Exact 6-runner active-core catalogue up to `30`")
        print(f"- count: {six['count']}")
        for row in six["sets"]:
            print(f"  - {row}")


def write_report_json(path: Path) -> None:
    report = calibration_report()
    with path.open("w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--include-six-runner-catalogue",
        action="store_true",
        help="also run the heavier exact 6-runner catalogue sweep up to 30",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        help="optional path for a JSON report",
    )
    args = parser.parse_args()

    report = (
        report_with_six_runner_catalogue()
        if args.include_six_runner_catalogue
        else calibration_report()
    )
    if args.json_out is not None:
        with args.json_out.open("w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2, sort_keys=True)
    print_report(report, include_six_runner_catalogue=args.include_six_runner_catalogue)
