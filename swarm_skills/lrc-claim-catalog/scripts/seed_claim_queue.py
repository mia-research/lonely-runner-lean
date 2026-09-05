#!/usr/bin/env python3
"""Seed deterministic claim queues from registry track_map.csv."""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

DOC_TYPES = {"docx", "pdf", "markdown", "text", "rtf", "latex"}
DATA_TYPES = {"csv", "json"}
CODE_TYPES = {"python", "html", "javascript", "swift", "sh"}

PRIORITY_TERMS = [
    "formal proof",
    "structural reduction",
    "complete proof",
    "source of truth",
    "lonely runner",
    "conjecture",
    "theorem",
    "empirical validation",
    "boundary",
    "detector",
    "isolation",
]


@dataclass
class Row:
    artifact_id: str
    filename: str
    track: str
    track_confidence: float
    file_type: str
    queue: str
    score: float = 0.0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Seed claim queue from track map")
    p.add_argument("--track-map", required=True, help="Path to track_map.csv")
    p.add_argument("--output", required=True, help="Output claim_seed_queue.csv path")
    p.add_argument("--track", default="LRC", help="Track to seed")
    p.add_argument("--batch-size", type=int, default=80, help="Rows to seed")
    p.add_argument("--min-confidence", type=float, default=0.65, help="Min track confidence")
    p.add_argument("--dry-run", action="store_true", help="Preview without writing")
    return p.parse_args()


def score_row(r: Row) -> float:
    name = r.filename.lower()
    ft = r.file_type.lower()
    score = 0.0

    for t in PRIORITY_TERMS:
        if t in name:
            score += 12.0

    if "proof" in name:
        score += 20.0
    if "structural reduction" in name:
        score += 20.0
    if "lonely runner" in name or "lrc" in name:
        score += 14.0
    if "empirical" in name or "validation" in name:
        score += 8.0
    if "boundary" in name or "detector" in name or "alignment" in name:
        score += 8.0

    if ft in DOC_TYPES:
        score += 10.0
    elif ft in DATA_TYPES:
        score += 8.0
    elif ft in CODE_TYPES:
        score += 6.0

    score += r.track_confidence * 10.0
    return score


def read_rows(path: Path, track: str, min_conf: float) -> List[Row]:
    items: List[Row] = []
    with path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for d in reader:
            try:
                conf = float(d.get("track_confidence", ""))
            except ValueError:
                continue
            if d.get("track") != track:
                continue
            if d.get("queue") != "track_assigned":
                continue
            if conf < min_conf:
                continue
            items.append(
                Row(
                    artifact_id=d.get("artifact_id", ""),
                    filename=d.get("filename", ""),
                    track=d.get("track", ""),
                    track_confidence=conf,
                    file_type=d.get("file_type", ""),
                    queue=d.get("queue", ""),
                )
            )
    return items


def select_balanced(rows: List[Row], batch_size: int) -> List[Row]:
    for r in rows:
        r.score = score_row(r)

    docs = sorted((r for r in rows if r.file_type.lower() in DOC_TYPES), key=lambda x: (-x.score, x.filename))
    data = sorted((r for r in rows if r.file_type.lower() in DATA_TYPES), key=lambda x: (-x.score, x.filename))
    code = sorted((r for r in rows if r.file_type.lower() in CODE_TYPES), key=lambda x: (-x.score, x.filename))
    other = sorted(
        (r for r in rows if r.file_type.lower() not in DOC_TYPES | DATA_TYPES | CODE_TYPES),
        key=lambda x: (-x.score, x.filename),
    )

    # Default split similar to current LRC kickoff profile.
    targets: Dict[str, int] = {
        "docs": int(batch_size * 0.44),
        "data": int(batch_size * 0.38),
        "code": int(batch_size * 0.18),
    }

    selected: List[Row] = []
    seen = set()

    def take(src: List[Row], n: int) -> None:
        count = 0
        for r in src:
            if r.artifact_id in seen:
                continue
            selected.append(r)
            seen.add(r.artifact_id)
            count += 1
            if count >= n:
                break

    take(docs, targets["docs"])
    take(data, targets["data"])
    take(code, targets["code"])

    for src in (docs, data, code, other):
        for r in src:
            if len(selected) >= batch_size:
                break
            if r.artifact_id in seen:
                continue
            selected.append(r)
            seen.add(r.artifact_id)
        if len(selected) >= batch_size:
            break

    return selected[:batch_size]


def priority_note(score: float) -> str:
    if score >= 85.0:
        return "P1_core_proof_or_primary_evidence"
    if score >= 70.0:
        return "P2_supporting_or_replication"
    return "P3_context_or_auxiliary"


def main() -> int:
    args = parse_args()
    track_map = Path(args.track_map)
    out = Path(args.output)

    rows = read_rows(track_map, args.track, args.min_confidence)
    selected = select_balanced(rows, args.batch_size)

    if args.dry_run:
        print(f"track={args.track} eligible={len(rows)} selected={len(selected)}")
        for i, r in enumerate(selected[:12], 1):
            print(f"{i:03d} {r.artifact_id} | {r.file_type} | {r.filename}")
        return 0

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["claim_id", "source_artifact_id", "filename", "track", "priority_note"])
        for i, r in enumerate(selected, 1):
            w.writerow([
                f"SEED-{args.track}-{i:06d}",
                r.artifact_id,
                r.filename,
                r.track,
                priority_note(r.score),
            ])

    print(f"wrote={out} rows={len(selected)} track={args.track}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
