#!/usr/bin/env python3
"""
verify_lrc_n11.py
=================
Event-complete boundary-set verification of the n=11 Lonely Runner Conjecture.

For each random speed configuration in the commensurable large-ratio regime
(a_1 in (0,1), a_j in (j-1, j+1) for j=2..9, a_10 = 10 fixed), this script
searches for a witness time t in the reference window

    W_ref = [1 / (11 * a_1),  10 / (11 * a_1)]

at which every runner i satisfies  min(frac(a_i * t), 1 - frac(a_i * t)) >= 1/11.

The search is event-complete via the boundary-set method: boundary times are the
set of t in W_ref where some runner crosses the isolation threshold 1/11 exactly.
Between consecutive boundary times the isolation status of every runner is
constant, so evaluating midpoints of inter-boundary intervals is exhaustive.

Evidence storage
----------------
  runs/<run_id>/batches.jsonl   -- one JSON record per batch
  runs/<run_id>/evidence.db     -- SQLite mirror for querying
  runs/<run_id>/summary.json    -- final statistics
  runs/<run_id>/config.json     -- full run parameters

Usage
-----
  python3 verify_lrc_n11.py [options]

  --target INT        Total configurations to test       (default 10_000_000)
  --batch-size INT    Configs per work batch              (default 5_000)
  --workers INT       Parallel worker processes           (default cpu_count)
  --seed INT          Master random seed                  (default 42)
  --output-dir PATH   Root directory for evidence output  (default ./runs)
  --run-id STR        Name for this run                   (default auto timestamp)
  --resume            Resume from existing run_id         (default False)

Reproducibility
---------------
  Each batch uses seed = master_seed + batch_index, so results are fully
  deterministic and individual batches can be re-run independently.

Author: Trent Palelei  (verification harness)
Date  : 2026-03-30
"""

import argparse
import json
import os
import signal
import sqlite3
import sys
import time
from datetime import datetime, timezone
from multiprocessing import Pool, cpu_count
from pathlib import Path
from typing import Optional

import numpy as np

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

N_RUNNERS  = 11           # number of runners (including runner 0 at origin)
N_SPEEDS   = 10           # a_1 .. a_10
THETA      = 1.0 / N_RUNNERS   # isolation threshold = 1/11
THETA_EPS  = 1e-11        # numerical tolerance for threshold comparisons

# ---------------------------------------------------------------------------
# Core verification functions
# ---------------------------------------------------------------------------

def _boundary_times_in_window(a: np.ndarray, w_left: float, w_right: float) -> np.ndarray:
    """
    Return all boundary times in [w_left, w_right] for the given speed vector.

    A boundary time for runner i is a t where  a_i * t ≡ THETA  or  1-THETA (mod 1),
    i.e.  t = (k + THETA) / a_i  or  t = (k + 1 - THETA) / a_i  for integer k >= 0.

    Parameters
    ----------
    a        : speed vector, shape (N_SPEEDS,)
    w_left   : left boundary of W_ref
    w_right  : right boundary of W_ref

    Returns
    -------
    Sorted 1-D array of boundary times in [w_left, w_right].
    """
    times = []
    for a_i in a:
        if a_i < 1e-15:
            continue
        # Range of k: a_i * t = k + offset, so k = a_i * t - offset
        k_min = max(0, int(np.floor(a_i * w_left)))
        k_max = int(np.ceil(a_i * w_right)) + 1

        for k in range(k_min, k_max + 1):
            t1 = (k + THETA) / a_i
            t2 = (k + 1.0 - THETA) / a_i
            if w_left - THETA_EPS <= t1 <= w_right + THETA_EPS:
                times.append(t1)
            if w_left - THETA_EPS <= t2 <= w_right + THETA_EPS:
                times.append(t2)

    if not times:
        return np.array([])
    return np.unique(np.array(times, dtype=np.float64))


def _is_isolated(a: np.ndarray, t: float) -> tuple[bool, float]:
    """
    Check whether all runners are isolated at time t.

    Returns (isolated: bool, min_margin: float).
    min_margin = min over i of (dist_i - THETA), where dist_i = min(frac, 1-frac).
    A positive min_margin means all runners are strictly isolated.
    """
    frac = np.mod(a * t, 1.0)
    dists = np.minimum(frac, 1.0 - frac)
    min_dist = float(np.min(dists))
    return min_dist >= THETA - THETA_EPS, min_dist - THETA


def find_witness(a: np.ndarray) -> tuple[bool, Optional[float], float, int]:
    """
    Boundary-set witness search in W_ref.

    Returns
    -------
    (found, t_witness, min_margin, n_boundaries)
      found      : True if a witness was found
      t_witness  : witness time (or None)
      min_margin : margin at best candidate (negative if no witness)
      n_boundaries: number of boundary points evaluated
    """
    w_left  = 1.0  / (N_RUNNERS * a[0])
    w_right = 10.0 / (N_RUNNERS * a[0])

    if w_right <= w_left:
        return False, None, -1.0, 0

    boundaries = _boundary_times_in_window(a, w_left, w_right)
    n_bound = len(boundaries)

    if n_bound == 0:
        # No boundaries in window: check a single interior point
        t_mid = 0.5 * (w_left + w_right)
        ok, margin = _is_isolated(a, t_mid)
        return ok, (t_mid if ok else None), margin, 0

    best_margin = -np.inf
    best_t = None

    # Check midpoints of every inter-boundary interval (event-complete).
    # Also include the window endpoints themselves.
    eval_times = [w_left]
    for i in range(len(boundaries) - 1):
        eval_times.append(0.5 * (boundaries[i] + boundaries[i + 1]))
    eval_times.append(w_right)
    # Also include boundary times themselves (runner may be exactly at threshold)
    eval_times.extend(boundaries.tolist())

    for t in eval_times:
        if not (w_left - THETA_EPS <= t <= w_right + THETA_EPS):
            continue
        ok, margin = _is_isolated(a, t)
        if margin > best_margin:
            best_margin = margin
            best_t = t
        if ok:
            return True, t, margin, n_bound

    return False, best_t, best_margin, n_bound


# ---------------------------------------------------------------------------
# Batch generation and processing
# ---------------------------------------------------------------------------

def _generate_batch(batch_size: int, seed: int) -> np.ndarray:
    """
    Generate a batch of random speed configurations in the large-ratio regime.

    Layout: configs[:, 0] = a_1 in (0, 1), uniform.
            configs[:, j-1] = a_j in (j-1, j+1) for j = 2..9, random sign class.
            configs[:, 9]   = 10.0 (fixed).

    The sign class for each a_j is chosen uniformly: with probability 1/2,
    a_j is drawn from (j-1, j) (sigma = -1) and with probability 1/2 from
    (j, j+1) (sigma = +1).  This ensures all 2^8 = 256 sign classes are
    sampled proportionally.
    """
    rng = np.random.default_rng(seed)
    configs = np.empty((batch_size, N_SPEEDS), dtype=np.float64)

    # a_1: avoid the boundary values 0 and 1 strictly
    u = rng.random(batch_size)
    configs[:, 0] = 0.001 + 0.998 * u   # in (0.001, 0.999)

    # a_2 .. a_9
    for col_idx in range(1, 9):    # col_idx = j - 1, so j = col_idx + 1
        j = col_idx + 1            # runner index
        sigma = rng.integers(0, 2, batch_size)   # 0 → sigma=-1, 1 → sigma=+1
        lo = np.where(sigma == 0, float(j - 1), float(j))
        hi = np.where(sigma == 0, float(j),     float(j + 1))
        configs[:, col_idx] = lo + rng.random(batch_size) * (hi - lo)

    # a_10 = 10 (normalised)
    configs[:, 9] = 10.0

    return configs


def _process_single_config(args):
    """Top-level picklable function for Pool.imap."""
    config, = args
    a = np.asarray(config, dtype=np.float64)
    found, t_wit, margin, n_bound = find_witness(a)
    return {
        "found":    found,
        "margin":   float(margin),
        "n_bound":  int(n_bound),
        "t_witness": float(t_wit) if t_wit is not None else None,
        "failure_speeds": None if found else config.tolist(),
    }


def _process_batch(args) -> dict:
    """
    Process one batch of configurations.

    Parameters
    ----------
    args : (batch_index, batch_size, master_seed, n_workers_unused)

    Returns a dict with aggregated statistics for this batch.
    """
    batch_index, batch_size, master_seed, _ = args
    seed = master_seed + batch_index
    configs = _generate_batch(batch_size, seed)

    n_passed   = 0
    n_failed   = 0
    total_bound = 0
    min_margin = np.inf
    max_margin = -np.inf
    failures   = []

    for i in range(batch_size):
        a = configs[i]
        found, t_wit, margin, n_bound = find_witness(a)

        total_bound += n_bound
        if margin < min_margin:
            min_margin = margin
        if margin > max_margin:
            max_margin = margin

        if found:
            n_passed += 1
        else:
            n_failed += 1
            if len(failures) < 5:
                failures.append({
                    "speeds": a.tolist(),
                    "margin": float(margin),
                    "n_bound": n_bound,
                })

    return {
        "batch_index":       batch_index,
        "seed":              seed,
        "n_tested":          batch_size,
        "n_passed":          n_passed,
        "n_failed":          n_failed,
        "total_boundaries":  total_bound,
        "min_margin":        float(min_margin),
        "max_margin":        float(max_margin),
        "mean_boundaries":   total_bound / batch_size if batch_size > 0 else 0.0,
        "failures":          failures,
    }


# ---------------------------------------------------------------------------
# Evidence storage
# ---------------------------------------------------------------------------

class EvidenceStore:
    """JSONL + SQLite store for batch results."""

    SCHEMA = """
    CREATE TABLE IF NOT EXISTS batches (
        batch_index     INTEGER PRIMARY KEY,
        seed            INTEGER,
        n_tested        INTEGER,
        n_passed        INTEGER,
        n_failed        INTEGER,
        total_boundaries INTEGER,
        min_margin      REAL,
        max_margin      REAL,
        mean_boundaries REAL,
        elapsed_s       REAL,
        timestamp       TEXT
    );
    CREATE TABLE IF NOT EXISTS failures (
        id              INTEGER PRIMARY KEY AUTOINCREMENT,
        batch_index     INTEGER,
        speeds_json     TEXT,
        margin          REAL,
        n_bound         INTEGER,
        FOREIGN KEY(batch_index) REFERENCES batches(batch_index)
    );
    CREATE TABLE IF NOT EXISTS run_meta (
        key   TEXT PRIMARY KEY,
        value TEXT
    );
    """

    def __init__(self, run_dir: Path):
        self.run_dir = run_dir
        self.run_dir.mkdir(parents=True, exist_ok=True)
        self.jsonl_path = run_dir / "batches.jsonl"
        self.db_path    = run_dir / "evidence.db"
        self._conn = sqlite3.connect(str(self.db_path))
        self._conn.executescript(self.SCHEMA)
        self._conn.commit()

    def write_meta(self, key: str, value):
        self._conn.execute(
            "INSERT OR REPLACE INTO run_meta(key, value) VALUES (?, ?)",
            (key, json.dumps(value))
        )
        self._conn.commit()

    def append_batch(self, record: dict, elapsed_s: float):
        ts = datetime.now(timezone.utc).isoformat()
        record["elapsed_s"] = elapsed_s
        record["timestamp"] = ts

        # JSONL append
        with open(self.jsonl_path, "a") as f:
            f.write(json.dumps({
                k: v for k, v in record.items() if k != "failures"
            }) + "\n")

        # SQLite insert
        self._conn.execute(
            """INSERT OR REPLACE INTO batches
               (batch_index, seed, n_tested, n_passed, n_failed,
                total_boundaries, min_margin, max_margin, mean_boundaries,
                elapsed_s, timestamp)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (
                record["batch_index"], record["seed"],
                record["n_tested"], record["n_passed"], record["n_failed"],
                record["total_boundaries"],
                record["min_margin"], record["max_margin"],
                record["mean_boundaries"],
                elapsed_s, ts,
            )
        )

        for f in record.get("failures", []):
            self._conn.execute(
                "INSERT INTO failures(batch_index, speeds_json, margin, n_bound) VALUES (?,?,?,?)",
                (record["batch_index"], json.dumps(f["speeds"]),
                 f["margin"], f["n_bound"])
            )

        self._conn.commit()

    def cumulative_stats(self) -> dict:
        row = self._conn.execute(
            """SELECT COUNT(*), SUM(n_tested), SUM(n_passed), SUM(n_failed),
                      SUM(total_boundaries), MIN(min_margin), MAX(max_margin),
                      SUM(elapsed_s)
               FROM batches"""
        ).fetchone()
        return {
            "n_batches":         row[0] or 0,
            "n_tested":          row[1] or 0,
            "n_passed":          row[2] or 0,
            "n_failed":          row[3] or 0,
            "total_boundaries":  row[4] or 0,
            "global_min_margin": row[5],
            "global_max_margin": row[6],
            "total_elapsed_s":   row[7] or 0.0,
        }

    def last_batch_index(self) -> int:
        row = self._conn.execute(
            "SELECT MAX(batch_index) FROM batches"
        ).fetchone()
        return row[0] if row[0] is not None else -1

    def close(self):
        self._conn.close()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def parse_args():
    p = argparse.ArgumentParser(
        description="Event-complete LRC n=11 verification via boundary-set method."
    )
    p.add_argument("--target",     type=int, default=10_000_000,
                   help="Total configurations to test (default 10^7).")
    p.add_argument("--batch-size", type=int, default=5_000,
                   help="Configurations per batch (default 5000).")
    p.add_argument("--workers",    type=int, default=None,
                   help="Worker processes (default: all CPU cores).")
    p.add_argument("--seed",       type=int, default=42,
                   help="Master random seed (default 42).")
    p.add_argument("--output-dir", type=str, default="runs",
                   help="Root directory for evidence output.")
    p.add_argument("--run-id",     type=str, default=None,
                   help="Run identifier (default: auto timestamp).")
    p.add_argument("--resume",     action="store_true",
                   help="Resume an existing run-id from last completed batch.")
    return p.parse_args()


def main():
    args = parse_args()

    n_workers  = args.workers or cpu_count()
    batch_size = args.batch_size
    target     = args.target
    n_batches  = (target + batch_size - 1) // batch_size
    master_seed = args.seed

    run_id = args.run_id or datetime.now(timezone.utc).strftime("run_%Y%m%d_%H%M%S")
    run_dir = Path(args.output_dir) / run_id
    store   = EvidenceStore(run_dir)

    # --- Resume support ---
    start_batch = 0
    if args.resume:
        start_batch = store.last_batch_index() + 1
        print(f"Resuming from batch {start_batch}.")
    else:
        # Write config
        config = {
            "run_id":     run_id,
            "target":     target,
            "batch_size": batch_size,
            "n_batches":  n_batches,
            "n_workers":  n_workers,
            "seed":       master_seed,
            "theta":      THETA,
            "n_runners":  N_RUNNERS,
            "method":     "boundary_set_event_complete",
            "started_at": datetime.now(timezone.utc).isoformat(),
            "python":     sys.version,
            "numpy":      np.__version__,
        }
        with open(run_dir / "config.json", "w") as f:
            json.dump(config, f, indent=2)
        store.write_meta("config", config)

    # --- Graceful shutdown ---
    interrupted = [False]
    def _handler(sig, frame):
        interrupted[0] = True
        print("\nInterrupted — saving current state.", flush=True)
    signal.signal(signal.SIGINT,  _handler)
    signal.signal(signal.SIGTERM, _handler)

    print("=" * 70)
    print("LRC n=11 Verification — Boundary-Set Method (Event-Complete)")
    print(f"  Target : {target:,} configurations")
    print(f"  Batches: {n_batches:,}  x  {batch_size:,} configs/batch")
    print(f"  Workers: {n_workers}")
    print(f"  Seed   : {master_seed}")
    print(f"  Run ID : {run_id}")
    print(f"  Output : {run_dir.resolve()}")
    print("=" * 70, flush=True)

    wall_start = time.monotonic()
    last_checkpoint = wall_start

    # Chunk batches for Pool.map to reduce scheduling overhead
    chunk = max(1, min(n_workers * 2, 20))

    batch_args = [
        (b, batch_size, master_seed, n_workers)
        for b in range(start_batch, n_batches)
    ]

    with Pool(processes=n_workers) as pool:
        for idx, result in enumerate(
            pool.imap_unordered(_process_batch, batch_args, chunksize=chunk)
        ):
            if interrupted[0]:
                break

            elapsed = time.monotonic() - wall_start
            store.append_batch(result, elapsed_s=elapsed)

            # --- Immediate failure alert ---
            if result["n_failed"] > 0:
                print(f"\n!!! FAILURE in batch {result['batch_index']}: "
                      f"{result['n_failed']} config(s) without witness !!!")
                for fail in result.get("failures", []):
                    print(f"    speeds : {[f'{x:.6f}' for x in fail['speeds']]}")
                    print(f"    margin : {fail['margin']:.8f}")

            # --- Progress every 10 batches ---
            done_batches = idx + 1
            if done_batches % 10 == 0 or done_batches == 1:
                stats = store.cumulative_stats()
                rate  = stats["n_tested"] / elapsed if elapsed > 0 else 0
                remaining = max(0, target - stats["n_tested"])
                eta_s = remaining / rate if rate > 0 else 0
                eta_h = eta_s / 3600
                print(
                    f"  Batch {done_batches:,}/{n_batches:,} | "
                    f"tested {stats['n_tested']:,} | "
                    f"failed {stats['n_failed']} | "
                    f"min_margin {stats['global_min_margin']:.6f} | "
                    f"rate {rate:.0f}/s | "
                    f"ETA {eta_h:.1f}h",
                    flush=True,
                )

    # --- Final summary ---
    stats = store.cumulative_stats()
    total_time = time.monotonic() - wall_start

    summary = {
        "run_id":             run_id,
        "completed_at":       datetime.now(timezone.utc).isoformat(),
        "interrupted":        interrupted[0],
        "n_tested":           stats["n_tested"],
        "n_passed":           stats["n_passed"],
        "n_failed":           stats["n_failed"],
        "n_batches_completed": stats["n_batches"],
        "total_boundaries_evaluated": stats["total_boundaries"],
        "global_min_margin":  stats["global_min_margin"],
        "global_max_margin":  stats["global_max_margin"],
        "total_time_s":       total_time,
        "configs_per_second": stats["n_tested"] / total_time if total_time > 0 else 0,
        "success_rate":       (stats["n_passed"] / stats["n_tested"]
                               if stats["n_tested"] > 0 else None),
        # 95% confidence upper bound on failure probability (rule of three)
        "p_failure_upper_95": (3.0 / stats["n_tested"]
                               if stats["n_failed"] == 0 and stats["n_tested"] > 0
                               else None),
    }

    with open(run_dir / "summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    store.write_meta("summary", summary)
    store.close()

    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)
    print(f"  Configurations tested : {stats['n_tested']:,}")
    print(f"  Witnesses found       : {stats['n_passed']:,}")
    print(f"  Failures              : {stats['n_failed']}")
    if stats["n_tested"] > 0:
        print(f"  Success rate          : {100*stats['n_passed']/stats['n_tested']:.6f}%")
    print(f"  Global min margin     : {stats['global_min_margin']:.8f}")
    print(f"  Total boundaries eval : {stats['total_boundaries']:,}")
    print(f"  Elapsed               : {total_time:.1f}s ({total_time/3600:.2f}h)")
    if stats["n_tested"] > 0:
        print(f"  Throughput            : {stats['n_tested']/total_time:.0f} configs/s")

    if stats["n_failed"] == 0 and stats["n_tested"] > 0:
        p_up = 3.0 / stats["n_tested"]
        print(f"\n  95%% confidence: failure rate < {p_up:.2e}  "
              f"(< 1 per {1/p_up:.0f} configs)")
        print(f"\n  OUTCOME: No counterexample detected in {stats['n_tested']:,} "
              f"event-complete trials.")
    else:
        print(f"\n  OUTCOME: {stats['n_failed']} failure(s) detected — inspect evidence.db.")

    print(f"\n  Evidence stored at: {run_dir.resolve()}")
    print("=" * 70)


if __name__ == "__main__":
    main()
