#!/usr/bin/env python3
"""
Gap-2 D.2 triage analyzer.

Reads multi-divisible batch checks CSV and summarizes how the current
component-wise D.2 diagnostic behaves per template.

Purpose:
- Identify which templates cross d2_lb_floor >= phi_n within the checked window.
- Quantify crossing delays / non-crossing templates for theorem refinement.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple


@dataclass
class TriageRow:
    template_id: str
    n: int
    d: int
    fixed: str
    e_div: str
    checks: int
    m_min: int
    m_max: int
    phi_n: int
    d2_min: int
    d2_max: int
    d2_at_mmax: int
    slope_est: str
    first_m_d2_ge_phi: int
    crossed_in_window: int


def parse_int(x: str) -> int:
    return int(x.strip())


def analyze_template(rows: List[dict]) -> TriageRow:
    rows = sorted(rows, key=lambda r: parse_int(r["M"]))

    n = parse_int(rows[0]["n"])
    d = parse_int(rows[0]["d"])
    fixed = rows[0]["fixed"]
    e_div = rows[0]["e_div"]
    phi_n = parse_int(rows[0]["phi_n"])
    tid = rows[0]["template_id"]

    ms = [parse_int(r["M"]) for r in rows]
    d2 = [parse_int(r["d2_lb_floor"]) for r in rows]

    first = -1
    for m, v in zip(ms, d2):
        if v >= phi_n:
            first = m
            break

    slope = ""
    if len(ms) >= 2 and ms[-1] != ms[0]:
        num = d2[-1] - d2[0]
        den = ms[-1] - ms[0]
        slope = f"{num}/{den}"

    return TriageRow(
        template_id=tid,
        n=n,
        d=d,
        fixed=fixed,
        e_div=e_div,
        checks=len(rows),
        m_min=min(ms),
        m_max=max(ms),
        phi_n=phi_n,
        d2_min=min(d2),
        d2_max=max(d2),
        d2_at_mmax=d2[-1],
        slope_est=slope,
        first_m_d2_ge_phi=first,
        crossed_in_window=int(first != -1),
    )


def write_outputs(out_dir: Path, tag: str, triage_rows: List[TriageRow]) -> Tuple[Path, Path]:
    rows_csv = out_dir / f"lrc_case2_multidiv_d2_triage_rows_{tag}.csv"
    summary_md = out_dir / f"lrc_case2_multidiv_d2_triage_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        fieldnames = list(TriageRow.__dataclass_fields__.keys())
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in sorted(triage_rows, key=lambda x: (x.n, x.d, x.template_id)):
            w.writerow(asdict(r))

    grouped: Dict[Tuple[int, int], List[TriageRow]] = {}
    for r in triage_rows:
        grouped.setdefault((r.n, r.d), []).append(r)

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# Multi-Divisible D.2 Triage Summary\n\n")
        f.write("- Interpretation: this analyzes the **current** D.2 diagnostic lower bound only.\n")
        f.write("- Non-crossing templates indicate where theorem constants need tightening.\n\n")

        for (n, d), arr in sorted(grouped.items()):
            crossed = [x for x in arr if x.crossed_in_window == 1]
            not_crossed = [x for x in arr if x.crossed_in_window == 0]
            firsts = [x.first_m_d2_ge_phi for x in crossed]
            f.write(f"## n={n}, |E_div|={d}\n")
            f.write(f"- templates: {len(arr)}\n")
            f.write(f"- crossed in window: {len(crossed)}\n")
            f.write(f"- not crossed in window: {len(not_crossed)}\n")
            f.write(f"- d2(M_max) min: {min(x.d2_at_mmax for x in arr)}\n")
            f.write(f"- d2(M_max) max: {max(x.d2_at_mmax for x in arr)}\n")
            if firsts:
                f.write(f"- first crossing M stats: min={min(firsts)}, max={max(firsts)}\n")
            f.write("\n")

        f.write("## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, summary_md


def main() -> None:
    ap = argparse.ArgumentParser(description="Analyze D.2 diagnostic crossing behavior")
    ap.add_argument("--checks-csv", type=str, required=True)
    ap.add_argument("--tag", type=str, default="v1")
    ap.add_argument("--out-dir", type=str, default=".")
    args = ap.parse_args()

    by_template: Dict[str, List[dict]] = {}
    with Path(args.checks_csv).open(newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            by_template.setdefault(row["template_id"], []).append(row)

    triage_rows = [analyze_template(rows) for rows in by_template.values()]

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv, summary_md = write_outputs(out_dir, args.tag, triage_rows)

    print(f"templates={len(triage_rows)}")
    print(f"rows: {rows_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
