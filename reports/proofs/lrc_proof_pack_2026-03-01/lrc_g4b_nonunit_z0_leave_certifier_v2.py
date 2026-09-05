#!/usr/bin/env python3
"""
Run-scoped non-unit z=0 leave-witness certifier (v2).

Core witness at interior run end b* (first safe fiber after run):
  Leave_e(b*) = B_e(b*-1) \ B_e(b*)
  U_-e(b*)    = union_{f!=e} B_f(b*)
  Witness     = Leave_e(b*) \ U_-e(b*)

No selection bias: every filtered event is recorded, even if leave set is empty.

Outputs:
  /tmp/lrc_g4b_nonunit_z0_leave_rows_v2.csv
  /tmp/lrc_g4b_nonunit_z0_leave_summary_v2.md
"""
from __future__ import annotations

import csv
import math
import random
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

SEED = 20260305
CONFIGS = [
    # (n, mode, max_e, sample_size, L_cap)
    (6,  "exhaustive", 10, None, 840),
    (8,  "exhaustive", 11, None, 840),
    (10, "sample",     14, 600, 840),
]

OUT_ROWS = Path("/tmp/lrc_g4b_nonunit_z0_leave_rows_v2.csv")
OUT_SUMM = Path("/tmp/lrc_g4b_nonunit_z0_leave_summary_v2.md")


def bad_a_set(e: int, b: int, L: int, n: int, cache: Dict[Tuple[int, int], frozenset[int]]) -> frozenset[int]:
    key = (e, b % L)
    if key in cache:
        return cache[key]
    N = n * L
    bb = b % L
    out: Set[int] = set()
    for a in range(n):
        x = (e * (a * L + bb)) % N
        if x < L or x > (n - 1) * L:
            out.add(a)
    fz = frozenset(out)
    cache[key] = fz
    return fz


def union_bad(E_non: Sequence[int], b: int, L: int, n: int,
              cache: Dict[Tuple[int, int], frozenset[int]],
              exclude: Optional[int] = None) -> Set[int]:
    u: Set[int] = set()
    for e in E_non:
        if exclude is not None and e == exclude:
            continue
        u |= bad_a_set(e, b, L, n, cache)
    return u


def build_b_div(E_div: Sequence[int], L: int, n: int) -> List[int]:
    N = n * L
    lo = L
    hi = (n - 1) * L
    out: List[int] = []
    for b in range(L):
        ok = True
        for e in E_div:
            x = (e * b) % N
            if not (lo <= x <= hi):
                ok = False
                break
        if ok:
            out.append(b)
    return out


def split_components(sorted_b: Sequence[int]) -> List[List[int]]:
    if not sorted_b:
        return []
    comps: List[List[int]] = []
    cur = [sorted_b[0]]
    for b in sorted_b[1:]:
        if b == cur[-1] + 1:
            cur.append(b)
        else:
            comps.append(cur)
            cur = [b]
    comps.append(cur)
    return comps


def obstruction_runs(component: Sequence[int], delta: Dict[int, int]) -> List[Tuple[int, int, int, int]]:
    out: List[Tuple[int, int, int, int]] = []
    in_run = False
    s = -1
    rid = 0
    for i, b in enumerate(component):
        obs = (delta[b] == 0)
        if obs and not in_run:
            in_run = True
            s = i
        if in_run:
            end_now = (not obs) or (i == len(component) - 1)
            if end_now:
                e = i - 1 if not obs else i
                out.append((rid, s, e, e - s + 1))
                rid += 1
                in_run = False
    return out


def gen_templates(n: int, mode: str, max_e: int, sample_size: Optional[int]) -> Iterable[Tuple[int, ...]]:
    all_tups = list(combinations(range(1, max_e + 1), n - 1))
    if mode == "exhaustive" or sample_size is None or sample_size >= len(all_tups):
        return all_tups
    rng = random.Random(SEED + n + max_e)
    return rng.sample(all_tups, sample_size)


@dataclass
class Counters:
    tuples_seen: int = 0
    tuples_in_scope: int = 0
    components: int = 0
    runs_total: int = 0
    runs_interior: int = 0
    interior_nonunit_events: int = 0
    interior_nonunit_pass: int = 0
    interior_nonunit_leave_empty: int = 0
    interior_nonunit_imp_fail: int = 0

    interior_pure_nonunit_events: int = 0
    interior_pure_nonunit_pass: int = 0
    interior_pure_nonunit_leave_empty: int = 0
    interior_pure_nonunit_imp_fail: int = 0


def analyze(rows: List[dict], c: Counters) -> None:
    tuple_id = 0
    for n, mode, max_e, sample_size, L_cap in CONFIGS:
        for E in gen_templates(n, mode, max_e, sample_size):
            c.tuples_seen += 1
            tuple_id += 1

            if math.gcd(*E) != 1:
                continue
            E_div = [e for e in E if e % n == 0]
            if not E_div:
                continue
            L = math.lcm(*E)
            if L <= 2 * n or L > L_cap:
                continue

            c.tuples_in_scope += 1

            E_non = [e for e in E if e % n != 0]
            E_nonunit = [e for e in E_non if math.gcd(e, n) > 1]
            E_unit = [e for e in E_non if math.gcd(e, n) == 1]

            cache: Dict[Tuple[int, int], frozenset[int]] = {}
            b_div = build_b_div(E_div, L, n)
            if not b_div:
                continue
            comps = split_components(b_div)

            for comp_id, comp in enumerate(comps):
                c.components += 1
                b_hi = comp[-1]

                delta: Dict[int, int] = {}
                for b in comp:
                    delta[b] = n - len(union_bad(E_non, b, L, n, cache))

                runs = obstruction_runs(comp, delta)
                c.runs_total += len(runs)

                for run_id, idx_s, idx_e, run_len in runs:
                    b_start = comp[idx_s]
                    b_end = comp[idx_e]
                    is_boundary_end = int(idx_e == len(comp) - 1)
                    if is_boundary_end:
                        continue
                    c.runs_interior += 1

                    b_star = comp[idx_e + 1]   # first safe fiber
                    b_prev = b_end             # last obstructed fiber

                    z0_nonunit = [e for e in E_nonunit if (e * b_star) % L == 0]
                    z0_unit = [e for e in E_unit if (e * b_star) % L == 0]

                    if not z0_nonunit:
                        # keep a structural row for run diagnostics
                        rows.append({
                            "n": n,
                            "tuple_id": tuple_id,
                            "e_tuple": " ".join(map(str, E)),
                            "L": L,
                            "component_id": comp_id,
                            "run_id": run_id,
                            "run_start_b": b_start,
                            "run_end_b": b_end,
                            "run_len": run_len,
                            "b_prev": b_prev,
                            "b_star": b_star,
                            "is_boundary_end": 0,
                            "e_target": -1,
                            "g_e": 0,
                            "z0_nonunit_at_bstar": 0,
                            "z0_unit_at_bstar": len(z0_unit),
                            "leave_size": -1,
                            "witness_count": -1,
                            "witness_r": "",
                            "D_prev": delta[b_prev],
                            "D_star": delta[b_star],
                            "leave_pass": -1,
                            "implication_ok": -1,
                            "filtered_nonunit_event": 0,
                            "filtered_pure_nonunit_event": 0,
                        })
                        continue

                    for e in z0_nonunit:
                        c.interior_nonunit_events += 1

                        Be_prev = set(bad_a_set(e, b_prev, L, n, cache))
                        Be_star = set(bad_a_set(e, b_star, L, n, cache))

                        leave = sorted(Be_prev - Be_star)
                        U_minus = union_bad(E_non, b_star, L, n, cache, exclude=e)
                        w = sorted(set(leave) - U_minus)

                        leave_pass = int(len(w) > 0)
                        implication_ok = int((len(w) == 0) or (delta[b_star] >= 1))

                        if leave_pass:
                            c.interior_nonunit_pass += 1
                        if len(leave) == 0:
                            c.interior_nonunit_leave_empty += 1
                        if implication_ok == 0:
                            c.interior_nonunit_imp_fail += 1

                        pure_nonunit = int(len(z0_unit) == 0)
                        if pure_nonunit:
                            c.interior_pure_nonunit_events += 1
                            if leave_pass:
                                c.interior_pure_nonunit_pass += 1
                            if len(leave) == 0:
                                c.interior_pure_nonunit_leave_empty += 1
                            if implication_ok == 0:
                                c.interior_pure_nonunit_imp_fail += 1

                        rows.append({
                            "n": n,
                            "tuple_id": tuple_id,
                            "e_tuple": " ".join(map(str, E)),
                            "L": L,
                            "component_id": comp_id,
                            "run_id": run_id,
                            "run_start_b": b_start,
                            "run_end_b": b_end,
                            "run_len": run_len,
                            "b_prev": b_prev,
                            "b_star": b_star,
                            "is_boundary_end": 0,
                            "e_target": e,
                            "g_e": math.gcd(e, n),
                            "z0_nonunit_at_bstar": len(z0_nonunit),
                            "z0_unit_at_bstar": len(z0_unit),
                            "leave_size": len(leave),
                            "witness_count": len(w),
                            "witness_r": " ".join(map(str, w[:8])),
                            "D_prev": delta[b_prev],
                            "D_star": delta[b_star],
                            "leave_pass": leave_pass,
                            "implication_ok": implication_ok,
                            "filtered_nonunit_event": 1,
                            "filtered_pure_nonunit_event": pure_nonunit,
                        })


def write_rows(path: Path, rows: List[dict]) -> None:
    if not rows:
        return
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def pct(a: int, b: int) -> str:
    if b == 0:
        return "n/a"
    return f"{(100.0 * a / b):.1f}%"


def write_summary(path: Path, rows: List[dict], c: Counters) -> None:
    # sample failing rows
    flt = [r for r in rows if int(r["filtered_nonunit_event"]) == 1]
    flt_fail = [r for r in flt if int(r["leave_pass"]) == 0]
    pure = [r for r in rows if int(r["filtered_pure_nonunit_event"]) == 1]
    pure_fail = [r for r in pure if int(r["leave_pass"]) == 0]

    lines: List[str] = []
    lines.append("# Non-Unit z=0 Leave-Witness Certifier v2")
    lines.append("Date: 2026-03-05")
    lines.append("")
    lines.append("## Scope")
    lines.append("- Run-scoped interior obstruction-run exits on `B_div`.")
    lines.append("- Event fiber `b*` = first safe fiber after run; `b_prev` = last obstructed fiber.")
    lines.append("- Witness: `Leave_e(b*) = B_e(b_prev)\\B_e(b*)`; require `Leave\\U_-e(b*) != emptyset`.")
    lines.append(f"- Configs: {CONFIGS}")
    lines.append("")
    lines.append("## Counts")
    lines.append(f"- tuples_seen: {c.tuples_seen}")
    lines.append(f"- tuples_in_scope: {c.tuples_in_scope}")
    lines.append(f"- components: {c.components}")
    lines.append(f"- runs_total: {c.runs_total}")
    lines.append(f"- runs_interior: {c.runs_interior}")
    lines.append("")
    lines.append("## Profile A: all interior non-unit z=0 events")
    lines.append(f"- events: {c.interior_nonunit_events}")
    lines.append(f"- leave-pass: {c.interior_nonunit_pass} ({pct(c.interior_nonunit_pass, c.interior_nonunit_events)})")
    lines.append(f"- leave-empty: {c.interior_nonunit_leave_empty} ({pct(c.interior_nonunit_leave_empty, c.interior_nonunit_events)})")
    lines.append(f"- implication fails (pass but D*=0): {c.interior_nonunit_imp_fail}")
    lines.append("")
    lines.append("## Profile B: pure non-unit z=0 events (no simultaneous unit z=0 at b*)")
    lines.append(f"- events: {c.interior_pure_nonunit_events}")
    lines.append(f"- leave-pass: {c.interior_pure_nonunit_pass} ({pct(c.interior_pure_nonunit_pass, c.interior_pure_nonunit_events)})")
    lines.append(f"- leave-empty: {c.interior_pure_nonunit_leave_empty} ({pct(c.interior_pure_nonunit_leave_empty, c.interior_pure_nonunit_events)})")
    lines.append(f"- implication fails (pass but D*=0): {c.interior_pure_nonunit_imp_fail}")
    lines.append("")

    lines.append("## Failure samples (Profile A)")
    if not flt_fail:
        lines.append("- none")
    else:
        for r in flt_fail[:10]:
            lines.append(
                "- "
                f"n={r['n']} E=({r['e_tuple']}) comp={r['component_id']} run={r['run_id']} "
                f"b_prev={r['b_prev']} b*={r['b_star']} e={r['e_target']} g={r['g_e']} "
                f"|Leave|={r['leave_size']} w={r['witness_count']} D*= {r['D_star']} "
                f"unit_z0={r['z0_unit_at_bstar']}"
            )

    lines.append("")
    lines.append("## Failure samples (Profile B)")
    if not pure_fail:
        lines.append("- none")
    else:
        for r in pure_fail[:10]:
            lines.append(
                "- "
                f"n={r['n']} E=({r['e_tuple']}) comp={r['component_id']} run={r['run_id']} "
                f"b_prev={r['b_prev']} b*={r['b_star']} e={r['e_target']} g={r['g_e']} "
                f"|Leave|={r['leave_size']} w={r['witness_count']} D*= {r['D_star']}"
            )

    path.write_text("\n".join(lines) + "\n")


def main() -> int:
    random.seed(SEED)
    rows: List[dict] = []
    c = Counters()
    analyze(rows, c)
    write_rows(OUT_ROWS, rows)
    write_summary(OUT_SUMM, rows, c)
    print(f"wrote rows: {OUT_ROWS} ({len(rows)} rows)")
    print(f"wrote summary: {OUT_SUMM}")
    print(f"nonunit events: {c.interior_nonunit_events}, pass: {c.interior_nonunit_pass}")
    print(f"pure nonunit events: {c.interior_pure_nonunit_events}, pass: {c.interior_pure_nonunit_pass}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
