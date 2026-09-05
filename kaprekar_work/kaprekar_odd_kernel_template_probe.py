#!/usr/bin/env python3
"""
Odd primitive-kernel template probe for base-10 Kaprekar cycles.

This is a structural probe, not a theorem certifier. It pulls the currently
verified odd primitive kernels A..H from the cycle-grammar inventory and
measures:

1. pair-core / asymmetry coordinates on complementary digit pairs,
2. per-phase positive-gap multiplicities,
3. cycle-sum staircase laws,
4. the shared layer-increment multiset on the period-5 side,
5. the period-3 rotor pattern on H.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
import importlib.util


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_odd_kernel_template_probe_2026-04-24.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def gap_count_vector(cnt: list[int]) -> list[int]:
    desc: list[int] = []
    for d in range(9, -1, -1):
        desc.extend([d] * cnt[d])
    asc = list(reversed(desc))
    gaps = [a - b for a, b in zip(desc, asc)][: (len(desc) + 1) // 2]
    c = Counter(x for x in gaps if x > 0)
    return [c.get(k, 0) for k in range(1, 10)]


def pair_core_extra(cnt: list[int]) -> tuple[list[int], list[int]]:
    pairs = [
        (cnt[0], cnt[9]),
        (cnt[1], cnt[8]),
        (cnt[2], cnt[7]),
        (cnt[3], cnt[6]),
        (cnt[4], cnt[5]),
    ]
    core = [min(a, b) for a, b in pairs]
    extra = [b - a for a, b in pairs]
    return core, extra


def family_rows(mod, name: str) -> list[list[int]]:
    return getattr(mod, f"{name}_states")(0)


def staircase_sum_law(rows: list[list[int]]) -> list[int]:
    total = [0] * 9
    for row in rows:
        gc = gap_count_vector(row)
        total = [a + b for a, b in zip(total, gc)]
    return total


def best_link_diffs(src: list[list[int]], dst: list[list[int]]) -> dict[str, object]:
    src_g = [gap_count_vector(s) for s in src]
    dst_g = [gap_count_vector(s) for s in dst]
    best = None
    for shift in range(len(dst_g)):
        diffs = []
        score = 0
        for i in range(len(src_g)):
            diff = [dst_g[(i + shift) % len(dst_g)][j] - src_g[i][j] for j in range(9)]
            diffs.append(diff)
            score += sum(abs(v) for v in diff)
        uniq = sorted({tuple(d) for d in diffs})
        cand = {"shift": shift, "score": score, "diffs": diffs, "unique_diffs": uniq}
        if best is None or score < best["score"]:
            best = cand
    assert best is not None
    return best


def rotor_check(rows: list[list[int]]) -> dict[str, object]:
    vectors = [gap_count_vector(s) for s in rows]
    base = [1, 1, 0, 1, 1, 1, 1, 1, 1]
    extras = []
    ok = True
    for v in vectors:
        diff = [a - b for a, b in zip(v, base)]
        extras.append(diff)
        if sum(diff) != 1 or max(diff) != 1 or min(diff) < 0:
            ok = False
    hot_positions = [next((i + 1 for i, x in enumerate(diff) if x == 1), None) for diff in extras]
    return {"base": base, "extras": extras, "hot_positions": hot_positions, "ok": ok}


def summarize_family(name: str, rows: list[list[int]]) -> dict[str, object]:
    phase_rows = []
    core_total = [0] * 5
    extra_hist = Counter()
    gap_sum = [0] * 9
    for phase, row in enumerate(rows):
        core, extra = pair_core_extra(row)
        gaps = gap_count_vector(row)
        core_total = [a + b for a, b in zip(core_total, core)]
        gap_sum = [a + b for a, b in zip(gap_sum, gaps)]
        extra_hist[tuple(extra)] += 1
        phase_rows.append({"phase": phase, "counts": row, "core": core, "extra": extra, "gap_counts": gaps})
    return {
        "period": len(rows),
        "dimension": sum(rows[0]),
        "phase_rows": phase_rows,
        "core_total": core_total,
        "extra_histogram": {str(k): v for k, v in extra_hist.items()},
        "gap_sum": gap_sum,
    }


def main() -> None:
    mod = load_inventory()

    families = {name: family_rows(mod, name) for name in "ABCDEFGH"}
    summary = {name: summarize_family(name, rows) for name, rows in families.items()}

    staircase_links = {
        "A_to_C": best_link_diffs(families["A"], families["C"]),
        "C_to_F": best_link_diffs(families["C"], families["F"]),
        "D_to_E": best_link_diffs(families["D"], families["E"]),
        "F_to_G": best_link_diffs(families["F"], families["G"]),
    }

    payload = {
        "families": summary,
        "period5_staircase_main": {
            "chain": ["A", "C", "F", "G"],
            "gap_sum_vectors": {name: summary[name]["gap_sum"] for name in ["A", "C", "F", "G"]},
        },
        "period5_staircase_companion": {
            "chain": ["D", "E"],
            "gap_sum_vectors": {name: summary[name]["gap_sum"] for name in ["D", "E"]},
        },
        "staircase_links": staircase_links,
        "H_rotor": rotor_check(families["H"]),
        "B_boundary": summarize_family("B", families["B"]),
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for name in ["A", "C", "D", "E", "F", "G", "H"]:
        row = summary[name]
        print(f"{name}: period={row['period']} d={row['dimension']} gap_sum={row['gap_sum']}")
    for name, row in staircase_links.items():
        print(f"{name}: shift={row['shift']} score={row['score']} unique_diffs={row['unique_diffs']}")
    print(f"H_rotor: ok={payload['H_rotor']['ok']} hot_positions={payload['H_rotor']['hot_positions']}")


if __name__ == "__main__":
    main()
