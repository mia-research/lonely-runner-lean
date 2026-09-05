#!/usr/bin/env python3
"""Deterministic first-pass catalog extraction from claim seed queue.

Produces registry/claims.csv with one atomic candidate claim per seeded artifact.
This is a controlled Phase 1 pass intended for downstream review and refinement.
"""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

TEXT_TYPES = {"text", "markdown", "python", "javascript", "json", "csv", "html", "latex", "sh", "swift"}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Extract first-pass claims from seeded artifacts")
    p.add_argument("--seed-queue", required=True, help="Path to registry/claim_seed_queue.csv")
    p.add_argument("--manifest", required=True, help="Path to registry/corpus_manifest.csv")
    p.add_argument("--output", required=True, help="Path to registry/claims.csv")
    p.add_argument("--report", required=True, help="Path to reports catalog extraction summary")
    p.add_argument("--max-chars", type=int, default=5000, help="Max chars to sample from source text")
    return p.parse_args()


def clean_name(name: str) -> str:
    base = Path(name).stem
    base = base.replace("_", " ")
    base = re.sub(r"\s+", " ", base).strip()
    return base


def read_manifest(path: Path) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    with path.open(newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            out[row.get("artifact_id", "")] = row
    return out


def read_text_file(path: Path, max_chars: int) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="ignore")[:max_chars]
    except Exception:
        return ""


def html_to_text(s: str) -> str:
    s = re.sub(r"<script[\s\S]*?</script>", " ", s, flags=re.I)
    s = re.sub(r"<style[\s\S]*?</style>", " ", s, flags=re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def read_doc_like(path: Path, max_chars: int) -> str:
    """Use macOS textutil for docx/rtf extraction."""
    try:
        proc = subprocess.run(
            ["textutil", "-convert", "txt", str(path), "-stdout"],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode == 0:
            return proc.stdout[:max_chars]
    except Exception:
        pass
    return ""


def first_sentence(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return ""
    parts = re.split(r"(?<=[.!?])\s+", text)
    for p in parts:
        p = p.strip()
        if len(p) >= 35:
            return p[:240]
    return text[:240]


def detect_claim_type(name: str, text: str, ftype: str) -> str:
    s = f"{name} {text}".lower()

    if any(k in s for k in ["theorem", "proof", "structural reduction", "formal proof"]):
        return "theorem_claim"
    if "conjecture" in s:
        return "conjecture"
    if any(k in s for k in ["empirical", "validation", "results", "dataset", "csv", "experiment", "test"]):
        return "empirical_claim"
    if any(k in s for k in ["algorithm", "method", "procedure", "engine", "implementation"]):
        return "algorithmic_claim"
    if any(k in s for k in ["definition", "define", "let "]):
        return "definition"

    if ftype in {"csv", "json"}:
        return "empirical_claim"
    return "candidate_claim"


def initial_status(claim_type: str, excerpt: str) -> Tuple[str, float]:
    if not excerpt:
        return "U-Unresolved Frontier", 0.35

    # Conservative first pass.
    if claim_type in {"theorem_claim", "conjecture", "algorithmic_claim", "definition", "candidate_claim"}:
        return "C-Underspecified", 0.58
    return "C-Underspecified", 0.62


def source_path_from_manifest(row: Dict[str, str]) -> Path:
    folder = row.get("source_folder", "~/Downloads")
    folder = folder.replace("~", str(Path.home()))
    return Path(folder) / row.get("filename", "")


def extract_excerpt(file_path: Path, file_type: str, max_chars: int) -> Tuple[str, str]:
    file_type = (file_type or "").lower()

    if not file_path.exists():
        return "", "missing_source"

    if file_type in TEXT_TYPES:
        text = read_text_file(file_path, max_chars)
        if file_type == "html":
            text = html_to_text(text)
        return text, "text_read"

    if file_type in {"docx", "rtf"}:
        text = read_doc_like(file_path, max_chars)
        return text, "textutil_extract" if text else "doc_extract_failed"

    if file_type == "pdf":
        # Filename-only fallback for pdf in this deterministic pass.
        return "", "filename_only_pdf"

    return "", "unsupported_type"


def write_claims(
    seeds: List[Dict[str, str]],
    manifest: Dict[str, Dict[str, str]],
    out_path: Path,
    report_path: Path,
    max_chars: int,
) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)

    rows_out: List[List[str]] = []

    stats = {
        "total_seeded": 0,
        "claims_written": 0,
        "missing_manifest": 0,
        "missing_source": 0,
        "text_extracted": 0,
        "filename_only": 0,
    }
    claim_type_counts: Dict[str, int] = {}
    status_counts: Dict[str, int] = {}

    created_utc = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    for s in seeds:
        stats["total_seeded"] += 1
        seed_id = s.get("claim_id", "")
        artifact_id = s.get("source_artifact_id", "")
        filename = s.get("filename", "")
        track = s.get("track", "")
        priority_note = s.get("priority_note", "")

        m = manifest.get(artifact_id)
        if not m:
            stats["missing_manifest"] += 1
            source_path = ""
            file_type = "unknown"
            excerpt = ""
            method = "missing_manifest"
        else:
            file_type = m.get("file_type", "unknown")
            src = source_path_from_manifest(m)
            source_path = str(src)
            excerpt, method = extract_excerpt(src, file_type, max_chars)
            if method == "missing_source":
                stats["missing_source"] += 1
            if method in {"text_read", "textutil_extract"} and excerpt:
                stats["text_extracted"] += 1
            if method.startswith("filename_only"):
                stats["filename_only"] += 1

        claim_type = detect_claim_type(filename, excerpt, file_type)
        status, conf = initial_status(claim_type, excerpt)

        short_stmt = first_sentence(excerpt)
        if not short_stmt:
            short_stmt = clean_name(filename)

        assumptions = "explicit assumptions pending extraction review"
        source_excerpt = re.sub(r"\s+", " ", excerpt).strip()[:320]

        claim_type_counts[claim_type] = claim_type_counts.get(claim_type, 0) + 1
        status_counts[status] = status_counts.get(status, 0) + 1

        rows_out.append(
            [
                f"CLAIM-{track}-{len(rows_out)+1:06d}",
                seed_id,
                artifact_id,
                filename,
                track,
                priority_note,
                file_type,
                claim_type,
                short_stmt,
                assumptions,
                status,
                f"{conf:.2f}",
                source_path,
                source_excerpt,
                method,
                created_utc,
            ]
        )

    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "claim_id",
                "seed_id",
                "source_artifact_id",
                "filename",
                "track",
                "priority_note",
                "file_type",
                "claim_type",
                "short_statement",
                "assumptions",
                "status",
                "confidence",
                "source_path",
                "source_excerpt",
                "extraction_method",
                "created_utc",
            ]
        )
        w.writerows(rows_out)

    stats["claims_written"] = len(rows_out)

    lines = [
        "# Catalog Extraction Summary",
        "",
        f"Generated: {created_utc}",
        "",
        "## Core Metrics",
        f"- total_seeded: {stats['total_seeded']}",
        f"- claims_written: {stats['claims_written']}",
        f"- missing_manifest: {stats['missing_manifest']}",
        f"- missing_source: {stats['missing_source']}",
        f"- text_extracted: {stats['text_extracted']}",
        f"- filename_only: {stats['filename_only']}",
        "",
        "## Claim Type Counts",
    ]
    for k in sorted(claim_type_counts):
        lines.append(f"- {k}: {claim_type_counts[k]}")
    lines.append("")
    lines.append("## Status Counts")
    for k in sorted(status_counts):
        lines.append(f"- {k}: {status_counts[k]}")

    report_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    seed_path = Path(args.seed_queue)
    manifest_path = Path(args.manifest)
    out_path = Path(args.output)
    report_path = Path(args.report)

    with seed_path.open(newline="", encoding="utf-8") as f:
        seeds = list(csv.DictReader(f))

    manifest = read_manifest(manifest_path)
    write_claims(seeds, manifest, out_path, report_path, args.max_chars)

    print(f"wrote_claims={out_path} rows={len(seeds)}")
    print(f"wrote_report={report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
