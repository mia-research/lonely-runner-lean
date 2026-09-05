#!/usr/bin/env python3
"""
Force the raw count-space staircase pieces N_0,...,N_4 from the odd automaton.

The point of this probe is to avoid reading the raw count pieces off the
verified family differences A->C->F->G directly. Instead, we treat the
gap-space staircase pieces M_0,...,M_4 and the odd asymmetry alphabet as
primary, and ask:

    among minimal two-digit raw-count lifts, which deltas can realize each M_j
    on every relevant source phase while staying inside the odd staircase
    asymmetry alphabet?

The answer comes back unique for each j.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from itertools import product
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_staircase_count_piece_forcing_2026-04-26.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def rotate(rows: list[list[int]], k: int) -> list[list[int]]:
    n = len(rows)
    return [rows[(i + k) % n] for i in range(n)]


def gap_count_vector(cnt: list[int]) -> tuple[int, ...]:
    desc: list[int] = []
    for d in range(9, -1, -1):
        desc.extend([d] * cnt[d])
    asc = list(reversed(desc))
    gaps = [a - b for a, b in zip(desc, asc)][: (len(desc) + 1) // 2]
    c = Counter(x for x in gaps if x > 0)
    return tuple(c.get(k, 0) for k in range(1, 10))


def asymmetry(cnt: list[int]) -> tuple[int, ...]:
    return (
        cnt[9] - cnt[0],
        cnt[8] - cnt[1],
        cnt[7] - cnt[2],
        cnt[6] - cnt[3],
        cnt[5] - cnt[4],
    )


def add(u: list[int], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def main() -> None:
    mod = load_inventory()

    # Canonical odd staircase gauge and companion slice.
    M = [
        (0, 0, 0, 0, 0, 0, 1, 0, 0),   # M0 = +L7
        (0, 0, 0, 0, 1, 0, 0, 0, 0),   # M1 = +L5
        (1, 0, 0, 0, 0, 0, 0, 0, 0),   # M2 = +L1
        (0, 0, 0, 0, 0, 1, 0, -1, 1),  # M3 = +L79
        (0, 0, 1, 0, 0, -1, 0, 1, 0),  # M4 = +L3
    ]

    expected_N = [
        (0, 1, 0, 0, 0, 0, 0, 0, 1, 0),    # +18
        (0, 0, 1, 0, 0, 0, 0, 1, 0, 0),    # +27
        (0, 0, 0, 0, 1, 1, 0, 0, 0, 0),    # +45
        (1, -1, 1, 0, 0, 0, 0, 0, 1, 0),   # +09 -18 +27
        (0, 1, -1, 1, 0, 0, 1, 0, -1, 1),  # +1369 -28
    ]

    # The odd staircase asymmetry alphabet from the earlier template note.
    U = (1, 0, 0, 0, 0)
    V = (2, -2, 1, 0, 0)
    W = (0, 2, -1, 0, 0)
    allowed_asym = {U, V, W}

    # Build all source rows where each gap-piece M_j occurs:
    # A->C, C->F, F->G, and companion D->E.
    occurrences: dict[int, list[dict[str, object]]] = {j: [] for j in range(5)}
    for m in range(0, 9):
        A = rotate(mod.A_states(m), 0)
        C = rotate(mod.C_states(m), 3)
        F = rotate(mod.F_states(m), 1)
        D = rotate(mod.D_states(m), 0)

        levels = {1: A, 2: C, 3: F}
        for r in (1, 2, 3):
            src = levels[r]
            for i, row in enumerate(src):
                j = (i + r - 1) % 5
                occurrences[j].append(
                    {"family": {1: "A", 2: "C", 3: "F"}[r], "m": m, "phase": i, "row": row}
                )

        # Companion slice D->E uses the same pieces with phase offset +3.
        for i, row in enumerate(D):
            j = (i + 3) % 5
            occurrences[j].append({"family": "D", "m": m, "phase": i, "row": row})

    candidate_deltas = [delta for delta in product((-1, 0, 1), repeat=10) if sum(delta) == 2]
    forcing_rows = []
    failures = 0

    for j in range(5):
        valid: list[tuple[int, ...]] = []
        witness_rows: list[dict[str, object]] = []

        for delta in candidate_deltas:
            ok = True
            for item in occurrences[j]:
                row = item["row"]  # type: ignore[index]
                new = add(row, delta)
                if min(new) < 0:
                    ok = False
                    break
                if asymmetry(new) not in allowed_asym:
                    ok = False
                    break
                gap_delta = tuple(a - b for a, b in zip(gap_count_vector(new), gap_count_vector(row)))
                if gap_delta != M[j]:
                    ok = False
                    break
            if ok:
                valid.append(delta)

        forced = valid[0] if len(valid) == 1 else None
        ok = forced == expected_N[j]
        if not ok:
            failures += 1

        # One representative source row for readable output.
        sample = occurrences[j][0]
        witness_rows.append(
            {
                "family": sample["family"],
                "m": sample["m"],
                "phase": sample["phase"],
                "row": sample["row"],
            }
        )

        forcing_rows.append(
            {
                "piece_index": j,
                "gap_piece": M[j],
                "expected_count_piece": expected_N[j],
                "candidate_count": len(valid),
                "candidates": valid,
                "forced_count_piece": forced,
                "ok": ok,
                "sample_source": witness_rows[0],
            }
        )

    payload = {
        "allowed_asymmetry_alphabet": [U, V, W],
        "gap_layer_pieces": M,
        "expected_count_layer_pieces": expected_N,
        "m_range": [0, 8],
        "source_occurrence_counts": {str(j): len(occurrences[j]) for j in range(5)},
        "forcing_rows": forcing_rows,
        "forcing_failures": failures,
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"forcing_failures={failures}")
    for row in forcing_rows:
        print(
            f"piece {row['piece_index']}: candidates={row['candidate_count']} forced={row['forced_count_piece']}"
        )


if __name__ == "__main__":
    main()
