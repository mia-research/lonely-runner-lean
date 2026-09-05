"""
lrc_case_r_boundary_campaign_status_v1.py
==========================================
Read-only status reporter for the LRC Case R> boundary campaign.

Usage:
    python3 tools/lrc_case_r_boundary_campaign_status_v1.py \\
        --output-root reports/investigations/INV-CASE-R-BOUNDARY-001

Prints:
    - Completed chunks / total chunks
    - Configs done / configs remaining
    - Throughput estimate (from per-chunk runtimes)
    - ETA
    - Per-family coverage table
"""

import argparse
import gzip
import json
import os
import sys
import time
from collections import defaultdict


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def _manifest_path(root):
    return os.path.join(root, "manifest.json")

def _progress_path(root):
    return os.path.join(root, "checkpoints", "progress.json")

def _chunk_path(root, chunk_id):
    return os.path.join(root, "chunks", f"chunk_{chunk_id:06d}.jsonl.gz")


def _load_json(path):
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def _chunk_stats(root, chunk_id):
    """Return (count, witness_count, total_runtime_s, family_counts) for a chunk."""
    path = _chunk_path(root, chunk_id)
    if not os.path.exists(path):
        return 0, 0, 0.0, {}
    count = 0
    witnesses = 0
    total_rt = 0.0
    fam_counts = defaultdict(int)
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
                count += 1
                if r.get("witness_found"):
                    witnesses += 1
                total_rt += r.get("runtime_s", 0.0)
                fam = r.get("config_family", "?")
                fam_counts[fam] += 1
            except Exception:
                pass
    return count, witnesses, total_rt, dict(fam_counts)


def _eta_str(seconds):
    if seconds <= 0 or seconds == float("inf"):
        return "?"
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    s = int(seconds % 60)
    if h > 0:
        return f"{h}h {m:02d}m"
    elif m > 0:
        return f"{m}m {s:02d}s"
    else:
        return f"{s}s"


# ─────────────────────────────────────────────────────────────────────────────
# Main status report
# ─────────────────────────────────────────────────────────────────────────────

def status_report(output_root: str):
    root = os.path.abspath(output_root)

    manifest = _load_json(_manifest_path(root))
    if manifest is None:
        print(f"[error] No manifest found at {root}. Has the campaign been started?")
        sys.exit(1)

    progress = _load_json(_progress_path(root))
    if progress is None:
        print("[error] No progress checkpoint found. Campaign may not have started yet.")
        sys.exit(1)

    target_configs   = manifest.get("target_configs", "?")
    chunk_size       = manifest.get("chunk_size", "?")
    master_seed      = manifest.get("master_seed", "?")
    workers          = manifest.get("workers", "?")
    created_at       = manifest.get("created_at", "?")
    family_filter    = manifest.get("family_filter") or "all"

    completed_ids    = sorted(progress.get("completed_chunk_ids", []))
    configs_done     = progress.get("configs_done", 0)
    last_updated     = progress.get("last_updated", "?")

    # Derive total chunks from target + chunk_size
    if isinstance(target_configs, int) and isinstance(chunk_size, int):
        import math
        total_chunks_est = math.ceil(target_configs / chunk_size)
    else:
        total_chunks_est = "?"

    configs_remaining = (
        target_configs - configs_done
        if isinstance(target_configs, int) else "?"
    )

    # Throughput: sum runtime from completed chunks (sample last 10 for recency)
    sample_ids = completed_ids[-10:] if len(completed_ids) > 10 else completed_ids
    total_sample_rt = 0.0
    total_sample_ct = 0
    total_witnesses = 0
    fam_totals = defaultdict(int)
    fam_witnesses = defaultdict(int)

    for cid in completed_ids:
        cnt, wct, rt, fc = _chunk_stats(root, cid)
        total_witnesses += wct
        for fam, n in fc.items():
            fam_totals[fam] += n
            # witnesses per fam: we don't break it down here (would need re-scan)

    for cid in sample_ids:
        cnt, wct, rt, fc = _chunk_stats(root, cid)
        total_sample_rt += rt
        total_sample_ct += cnt

    # configs/sec = total_sample_ct / total_sample_rt (serial core-time)
    # adjusted for parallelism: divide by workers
    w = workers if isinstance(workers, int) else 1
    if total_sample_rt > 0 and total_sample_ct > 0:
        serial_rate = total_sample_ct / total_sample_rt   # per worker-second
        wall_rate   = serial_rate * w                     # per wall-second (approx)
    else:
        serial_rate = 0.0
        wall_rate   = 0.0

    if isinstance(configs_remaining, int) and wall_rate > 0:
        eta_seconds = configs_remaining / wall_rate
    else:
        eta_seconds = float("inf")

    witness_rate = (
        total_witnesses / configs_done * 100
        if configs_done > 0 else 0.0
    )

    # ── Print ──────────────────────────────────────────────────────────────────
    sep = "─" * 60
    print(sep)
    print("LRC Case R> Boundary Campaign — Status")
    print(sep)
    print(f"  Output root   : {root}")
    print(f"  Created at    : {created_at}")
    print(f"  Last updated  : {last_updated}")
    print(f"  Master seed   : {master_seed}")
    print(f"  Family filter : {family_filter}")
    print(f"  Workers       : {workers}")
    print(sep)
    print(f"  Chunks completed : {len(completed_ids):,} / {total_chunks_est}")
    print(f"  Configs done     : {configs_done:,} / {target_configs:,}")
    print(f"  Configs remaining: {configs_remaining:,}" if isinstance(configs_remaining, int) else f"  Configs remaining: {configs_remaining}")
    print(f"  Witness rate     : {witness_rate:.4f}%  ({total_witnesses:,} witnesses)")
    print(sep)
    if wall_rate > 0:
        print(f"  Throughput (approx) : {wall_rate:.1f} configs/s (wall-clock, {w} workers)")
        print(f"  ETA                 : {_eta_str(eta_seconds)}")
    else:
        print("  Throughput: insufficient data")
    print(sep)

    if fam_totals:
        print("  Per-family coverage:")
        print(f"    {'Family':<20} {'Configs':>10}")
        for fam in sorted(fam_totals):
            print(f"    {fam:<20} {fam_totals[fam]:>10,}")

    print(sep)


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def _parse_args():
    parser = argparse.ArgumentParser(
        description="Status reporter for LRC Case R> boundary campaign"
    )
    parser.add_argument(
        "--output-root", type=str,
        default="reports/investigations/INV-CASE-R-BOUNDARY-001",
        help="Campaign output directory"
    )
    return parser.parse_args()


if __name__ == "__main__":
    args = _parse_args()
    status_report(args.output_root)
