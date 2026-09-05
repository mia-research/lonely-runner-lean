#!/usr/bin/env python3
"""Run strict precision-ladder reproducibility on queued numeric claims.

For each selected claim:
- Extract numeric values from source artifact
- Compute metric bundle in float64 / decimal128 / mpmath
- Compare float64 vs mpmath and decimal128 vs mpmath
- Write per-claim artifacts and a batch summary
- Update queue with execution status and artifact pointers
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

NUM_RE = re.compile(r"(?<![A-Za-z0-9_])[-+]?(?:\d+\.\d+|\d+|\.\d+)(?:[eE][-+]?\d+)?")


@dataclass
class Thresholds:
    stable: float
    sensitive: float


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run precision ladder for queued numeric claims")
    p.add_argument("--queue", required=True, help="Path to promotion queue CSV")
    p.add_argument("--claims", required=True, help="Path to claims CSV")
    p.add_argument("--triage", required=True, help="Path to numeric triage CSV")
    p.add_argument("--output-root", required=True, help="Root output directory for per-claim artifacts")
    p.add_argument("--summary", required=True, help="Batch summary markdown path")
    p.add_argument("--batch-json", required=True, help="Batch summary JSON path")
    p.add_argument("--queue-out", required=True, help="Updated queue CSV path")
    p.add_argument("--limit", type=int, default=10, help="Number of numeric_test items to execute")
    p.add_argument(
        "--max-values",
        type=int,
        default=50000,
        help="Max numeric values per claim; use 0 for uncapped full extraction",
    )
    p.add_argument("--sample-values", type=int, default=12, help="Sample values to store in input summary")
    return p.parse_args()


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]]) -> None:
    if not rows:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("", encoding="utf-8")
        return
    fieldnames: List[str] = []
    seen = set()
    for r in rows:
        for k in r.keys():
            if k not in seen:
                seen.add(k)
                fieldnames.append(k)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            chunk = f.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def extract_numbers_from_text(text: str, max_values: int) -> List[str]:
    vals: List[str] = []
    for m in NUM_RE.finditer(text):
        token = m.group(0)
        vals.append(token)
        if max_values > 0 and len(vals) >= max_values:
            break
    return vals


def extract_numeric_tokens(source_path: Path, max_values: int) -> Tuple[List[str], Dict[str, object]]:
    suffix = source_path.suffix.lower()
    method = "regex_text"
    total_scanned = 0

    if suffix == ".csv":
        method = "csv_cells_plus_regex"
        values: List[str] = []
        with source_path.open(newline="", encoding="utf-8", errors="replace") as f:
            reader = csv.reader(f)
            for row in reader:
                total_scanned += 1
                for cell in row:
                    cell = cell.strip()
                    if not cell:
                        continue
                    if cell.lower() in {"true", "false", "yes", "no", "nan", "null", "none"}:
                        continue
                    # Handles plain numbers and embedded lists/tuples in cells.
                    matches = NUM_RE.findall(cell)
                    if not matches:
                        continue
                    for tok in matches:
                        values.append(tok)
                        if max_values > 0 and len(values) >= max_values:
                            break
                    if max_values > 0 and len(values) >= max_values:
                        break
                if max_values > 0 and len(values) >= max_values:
                    break
        return values, {
            "method": method,
            "rows_scanned": total_scanned,
            "truncated": (max_values > 0 and len(values) >= max_values),
        }

    text = source_path.read_text(encoding="utf-8", errors="replace")
    values = extract_numbers_from_text(text, max_values)
    return values, {
        "method": method,
        "chars_scanned": len(text),
        "truncated": (max_values > 0 and len(values) >= max_values),
    }


def to_float64_values(tokens: Sequence[str]) -> List[float]:
    out: List[float] = []
    for t in tokens:
        try:
            v = float(t)
        except ValueError:
            continue
        if not math.isfinite(v):
            continue
        out.append(v)
    return out


def to_decimal_values(tokens: Sequence[str]) -> List[Decimal]:
    out: List[Decimal] = []
    with localcontext() as ctx:
        ctx.prec = 34  # decimal128 precision
        for t in tokens:
            try:
                d = Decimal(t)
            except InvalidOperation:
                continue
            if not d.is_finite():
                continue
            out.append(+d)
    return out


def to_mpmath_values(tokens: Sequence[str], dps: int = 80) -> List[mp.mpf]:
    mp.mp.dps = dps
    out: List[mp.mpf] = []
    for t in tokens:
        try:
            x = mp.mpf(t)
        except (ValueError, TypeError):
            continue
        if not mp.isfinite(x):
            continue
        out.append(x)
    return out


def metrics_float(values: Sequence[float]) -> Dict[str, str]:
    n = len(values)
    if n == 0:
        return {"n": "0"}
    total = math.fsum(values)
    mean = total / n
    # Welford variance for numeric stability.
    m = 0.0
    s = 0.0
    for i, x in enumerate(values, start=1):
        delta = x - m
        m += delta / i
        s += delta * (x - m)
    variance = s / n
    abs_sum = math.fsum(abs(x) for x in values)
    l2 = math.sqrt(math.fsum(x * x for x in values))

    alt = 0.0
    sign = 1.0
    for x in sorted(values, key=lambda y: abs(y), reverse=True):
        alt += sign * x
        sign *= -1.0

    eps = 1e-30
    eps_probe = math.fsum((x + eps) - x for x in values)

    return {
        "n": str(n),
        "sum": f"{total:.17e}",
        "mean": f"{mean:.17e}",
        "variance": f"{variance:.17e}",
        "abs_sum": f"{abs_sum:.17e}",
        "l2_norm": f"{l2:.17e}",
        "min": f"{min(values):.17e}",
        "max": f"{max(values):.17e}",
        "alt_sum_desc_abs": f"{alt:.17e}",
        "epsilon_probe": f"{eps_probe:.17e}",
    }


def metrics_decimal(values: Sequence[Decimal]) -> Dict[str, str]:
    n = len(values)
    if n == 0:
        return {"n": "0"}
    with localcontext() as ctx:
        ctx.prec = 34
        total = sum(values, Decimal(0))
        mean = total / Decimal(n)
        m = Decimal(0)
        s = Decimal(0)
        for i, x in enumerate(values, start=1):
            i_d = Decimal(i)
            delta = x - m
            m = m + (delta / i_d)
            s = s + delta * (x - m)
        variance = s / Decimal(n)
        abs_sum = sum((abs(x) for x in values), Decimal(0))
        l2 = (sum((x * x for x in values), Decimal(0))).sqrt()

        alt = Decimal(0)
        sign = Decimal(1)
        for x in sorted(values, key=lambda y: abs(y), reverse=True):
            alt += sign * x
            sign = -sign

        eps = Decimal("1e-30")
        eps_probe = sum(((x + eps) - x for x in values), Decimal(0))

        return {
            "n": str(n),
            "sum": format(total, "E"),
            "mean": format(mean, "E"),
            "variance": format(variance, "E"),
            "abs_sum": format(abs_sum, "E"),
            "l2_norm": format(l2, "E"),
            "min": format(min(values), "E"),
            "max": format(max(values), "E"),
            "alt_sum_desc_abs": format(alt, "E"),
            "epsilon_probe": format(eps_probe, "E"),
        }


def metrics_mpmath(values: Sequence[mp.mpf], dps: int = 80) -> Dict[str, str]:
    mp.mp.dps = dps
    n = len(values)
    if n == 0:
        return {"n": "0"}
    total = mp.fsum(values)
    mean = total / n
    m = mp.mpf("0")
    s = mp.mpf("0")
    for i, x in enumerate(values, start=1):
        delta = x - m
        m += delta / i
        s += delta * (x - m)
    variance = s / n
    abs_sum = mp.fsum(abs(x) for x in values)
    l2 = mp.sqrt(mp.fsum(x * x for x in values))

    alt = mp.mpf("0")
    sign = mp.mpf("1")
    for x in sorted(values, key=lambda y: abs(y), reverse=True):
        alt += sign * x
        sign = -sign

    eps = mp.mpf("1e-30")
    eps_probe = mp.fsum((x + eps) - x for x in values)

    return {
        "n": str(n),
        "sum": mp.nstr(total, 40),
        "mean": mp.nstr(mean, 40),
        "variance": mp.nstr(variance, 40),
        "abs_sum": mp.nstr(abs_sum, 40),
        "l2_norm": mp.nstr(l2, 40),
        "min": mp.nstr(min(values), 40),
        "max": mp.nstr(max(values), 40),
        "alt_sum_desc_abs": mp.nstr(alt, 40),
        "epsilon_probe": mp.nstr(eps_probe, 40),
    }


def metric_keys(m: Dict[str, str]) -> List[str]:
    return sorted(k for k in m.keys() if k != "n")


def status_for(rel: float, th: Thresholds) -> str:
    if rel <= th.stable:
        return "stable"
    if rel <= th.sensitive:
        return "precision_sensitive"
    return "unstable"


def compare_metrics(
    baseline: Dict[str, str],
    high: Dict[str, str],
    thresholds: Thresholds,
) -> Tuple[List[Dict[str, str]], float, str]:
    rows: List[Dict[str, str]] = []
    max_rel = 0.0
    worst_status = "stable"
    ignored_for_global = {"epsilon_probe"}

    for k in metric_keys(baseline):
        if k not in high:
            continue
        try:
            b = mp.mpf(baseline[k])
            h = mp.mpf(high[k])
        except (TypeError, ValueError):
            continue
        abs_diff = abs(b - h)
        denom = max(abs(b), abs(h), mp.mpf("1e-40"))
        rel = float(abs_diff / denom)
        st = status_for(rel, thresholds)
        if k not in ignored_for_global:
            if st == "unstable":
                worst_status = "unstable"
            elif st == "precision_sensitive" and worst_status != "unstable":
                worst_status = "precision_sensitive"
            max_rel = max(max_rel, rel)
        rows.append(
            {
                "metric": k,
                "baseline": str(b),
                "high_precision": str(h),
                "abs_diff": str(abs_diff),
                "rel_diff": f"{rel:.12e}",
                "status": st,
            }
        )
    if max_rel == 0.0 and rows:
        # If all global metrics were exact/ignored, keep a tiny non-zero for traceability.
        max_rel = 0.0
    return rows, max_rel, worst_status


def write_compare_csv(path: Path, rows: Sequence[Dict[str, str]], global_status: str, max_rel: float) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["metric", "baseline", "high_precision", "abs_diff", "rel_diff", "status"])
        for r in rows:
            w.writerow([r["metric"], r["baseline"], r["high_precision"], r["abs_diff"], r["rel_diff"], r["status"]])
        w.writerow([])
        w.writerow(["GLOBAL_STATUS", global_status])
        w.writerow(["MAX_REL_DIFF", f"{max_rel:.12e}"])


def load_map(rows: Sequence[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def parse_thresholds(triage_row: Dict[str, str] | None) -> Thresholds:
    if not triage_row:
        return Thresholds(stable=1e-9, sensitive=1e-6)
    try:
        stable = float(triage_row.get("stable_threshold", "1e-9"))
    except ValueError:
        stable = 1e-9
    try:
        sensitive = float(triage_row.get("sensitive_threshold", "1e-6"))
    except ValueError:
        sensitive = 1e-6
    if sensitive < stable:
        sensitive = stable
    return Thresholds(stable=stable, sensitive=sensitive)


def claim_folder(root: Path, claim_id: str) -> Path:
    return root / claim_id


def write_json(path: Path, obj: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


def select_first_numeric(queue_rows: Sequence[Dict[str, str]], limit: int) -> List[Dict[str, str]]:
    candidates = [
        r
        for r in queue_rows
        if (r.get("promotion_track") or "") == "numeric_test"
        and (r.get("queue_status") or "queued") in {"queued", "retry"}
    ]
    candidates.sort(key=lambda r: (r.get("promotion_id", ""), r.get("claim_id", "")))
    return candidates[:limit]


def main() -> int:
    args = parse_args()
    queue_path = Path(args.queue)
    claims_path = Path(args.claims)
    triage_path = Path(args.triage)
    output_root = Path(args.output_root)

    queue_rows = read_csv(queue_path)
    claims_map = load_map(read_csv(claims_path), "claim_id")
    triage_map = load_map(read_csv(triage_path), "claim_id")

    selected = select_first_numeric(queue_rows, args.limit)
    if not selected:
        raise SystemExit("no-numeric-queue-items")

    batch_started = utc_now()
    batch_results: List[Dict[str, object]] = []

    for item in selected:
        claim_id = item.get("claim_id", "")
        source_path_str = (item.get("source_path") or claims_map.get(claim_id, {}).get("source_path") or "").strip()
        claim_dir = claim_folder(output_root, claim_id)
        claim_dir.mkdir(parents=True, exist_ok=True)

        result_row: Dict[str, object] = {
            "claim_id": claim_id,
            "promotion_id": item.get("promotion_id", ""),
            "status": "error",
            "message": "",
            "artifact_dir": str(claim_dir),
        }

        try:
            if not source_path_str:
                raise FileNotFoundError("missing_source_path")
            source_path = Path(source_path_str)
            if not source_path.exists():
                raise FileNotFoundError(f"missing_source_file:{source_path}")

            tokens, extract_meta = extract_numeric_tokens(source_path, args.max_values)
            fvals = to_float64_values(tokens)
            dvals = to_decimal_values(tokens)
            mvals = to_mpmath_values(tokens, dps=80)
            usable_n = min(len(fvals), len(dvals), len(mvals))

            if usable_n < 5:
                raise ValueError(f"insufficient_numeric_values:{usable_n}")

            fvals = fvals[:usable_n]
            dvals = dvals[:usable_n]
            mvals = mvals[:usable_n]

            m_float = metrics_float(fvals)
            m_dec = metrics_decimal(dvals)
            m_mp = metrics_mpmath(mvals, dps=80)

            triage_row = triage_map.get(claim_id)
            th = parse_thresholds(triage_row)

            cmp_float, max_rel_float, status_float = compare_metrics(m_float, m_mp, th)
            cmp_dec, max_rel_dec, status_dec = compare_metrics(m_dec, m_mp, th)

            # Final verdict uses the better of decimal/mpmath alignment and float comparison.
            if status_float == "stable" and status_dec == "stable":
                final_status = "stable"
            elif status_dec == "stable" and status_float != "stable":
                final_status = "precision_sensitive"
            elif status_dec == "precision_sensitive" or status_float == "precision_sensitive":
                final_status = "precision_sensitive"
            else:
                final_status = "unstable"

            input_summary = {
                "claim_id": claim_id,
                "promotion_id": item.get("promotion_id", ""),
                "source_path": str(source_path),
                "source_sha256": sha256_file(source_path),
                "source_bytes": source_path.stat().st_size,
                "extraction": extract_meta,
                "tokens_extracted": len(tokens),
                "usable_values": usable_n,
                "sample_values": tokens[: args.sample_values],
                "thresholds": {"stable": th.stable, "sensitive": th.sensitive},
                "created_utc": utc_now(),
            }
            write_json(claim_dir / "input_summary.json", input_summary)
            write_json(claim_dir / "metrics_float64.json", m_float)
            write_json(claim_dir / "metrics_decimal128.json", m_dec)
            write_json(claim_dir / "metrics_mpmath.json", m_mp)

            write_compare_csv(
                claim_dir / "compare_float64_vs_mpmath.csv",
                cmp_float,
                status_float,
                max_rel_float,
            )
            write_compare_csv(
                claim_dir / "compare_decimal128_vs_mpmath.csv",
                cmp_dec,
                status_dec,
                max_rel_dec,
            )

            verdict = {
                "claim_id": claim_id,
                "promotion_id": item.get("promotion_id", ""),
                "final_status": final_status,
                "float64_vs_mpmath": {
                    "global_status": status_float,
                    "max_rel_diff": max_rel_float,
                },
                "decimal128_vs_mpmath": {
                    "global_status": status_dec,
                    "max_rel_diff": max_rel_dec,
                },
                "notes": [
                    "Strict ladder executed: float64, decimal128 (prec=34), mpmath (dps=80).",
                    "Use decimal/mpmath agreement as high-precision anchor.",
                ],
                "created_utc": utc_now(),
            }
            write_json(claim_dir / "repro_verdict.json", verdict)

            result_row.update(
                {
                    "status": "executed",
                    "message": "ok",
                    "usable_values": usable_n,
                    "final_status": final_status,
                    "max_rel_float_vs_mpmath": max_rel_float,
                    "max_rel_decimal_vs_mpmath": max_rel_dec,
                    "artifact_dir": str(claim_dir),
                }
            )

        except Exception as e:  # noqa: BLE001 - batch runner should continue per claim.
            err = str(e)
            result_row.update(
                {
                    "status": "error",
                    "message": err,
                    "final_status": "error",
                    "usable_values": 0,
                    "max_rel_float_vs_mpmath": None,
                    "max_rel_decimal_vs_mpmath": None,
                }
            )
            write_json(
                claim_dir / "repro_verdict.json",
                {
                    "claim_id": claim_id,
                    "promotion_id": item.get("promotion_id", ""),
                    "final_status": "error",
                    "error": err,
                    "created_utc": utc_now(),
                },
            )

        batch_results.append(result_row)

    # Update queue rows with execution metadata.
    executed_map = {str(r["claim_id"]): r for r in batch_results}
    queue_updated: List[Dict[str, str]] = []
    completed_utc = utc_now()
    for row in queue_rows:
        cid = row.get("claim_id", "")
        ex = executed_map.get(cid)
        if ex:
            row = dict(row)
            row["queue_status"] = "executed" if ex["status"] == "executed" else "error"
            row["executed_utc"] = completed_utc
            row["artifact_dir"] = str(ex.get("artifact_dir", ""))
            row["ladder_status"] = str(ex.get("final_status", ""))
            row["ladder_max_rel_float_vs_mpmath"] = (
                "" if ex.get("max_rel_float_vs_mpmath") is None else f"{float(ex['max_rel_float_vs_mpmath']):.12e}"
            )
            row["ladder_max_rel_decimal_vs_mpmath"] = (
                "" if ex.get("max_rel_decimal_vs_mpmath") is None else f"{float(ex['max_rel_decimal_vs_mpmath']):.12e}"
            )
            row["execution_note"] = str(ex.get("message", ""))
        queue_updated.append(row)

    write_csv(Path(args.queue_out), queue_updated)

    # Batch artifacts.
    status_counts: Dict[str, int] = {}
    for r in batch_results:
        k = str(r.get("final_status", "unknown"))
        status_counts[k] = status_counts.get(k, 0) + 1

    serial_runtime_min = 0
    for row in selected:
        try:
            serial_runtime_min += int(float(row.get("runtime_estimate_min", "0") or 0))
        except ValueError:
            pass

    batch_json = {
        "batch_started_utc": batch_started,
        "batch_completed_utc": completed_utc,
        "queue_input": str(queue_path),
        "queue_output": str(Path(args.queue_out)),
        "selected_count": len(selected),
        "result_count": len(batch_results),
        "status_counts": status_counts,
        "serial_runtime_estimate_min": serial_runtime_min,
        "results": batch_results,
    }
    write_json(Path(args.batch_json), batch_json)

    lines = [
        "# Numeric Ladder Batch Summary",
        "",
        f"Started: {batch_started}",
        f"Completed: {completed_utc}",
        "",
        "## Core Metrics",
        f"- selected_numeric_tests: {len(selected)}",
        f"- executed_results: {len(batch_results)}",
        f"- serial_runtime_estimate_min: {serial_runtime_min}",
        "",
        "## Status Counts",
    ]
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")

    lines += ["", "## Per-Claim Results"]
    for r in batch_results:
        lines.append(
            "- "
            + f"{r.get('promotion_id','')} {r.get('claim_id','')}: "
            + f"status={r.get('status','')} final={r.get('final_status','')} "
            + f"usable_values={r.get('usable_values',0)} "
            + f"artifact_dir={r.get('artifact_dir','')}"
        )

    summary_path = Path(args.summary)
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_queue_out={args.queue_out}")
    print(f"wrote_summary={args.summary}")
    print(f"wrote_batch_json={args.batch_json}")
    print(f"selected={len(selected)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
