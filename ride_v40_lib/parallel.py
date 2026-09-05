# ride_v40_lib/parallel.py — multiprocessing backend for v40
# v1.0 — 2026-04-15
#
# Parallelism is at the (space, rung, run_id) level — each SA run is one
# worker task. Rungs and spaces are constructed in the parent and passed
# to workers via pickle. numpy arrays (target_perm, source, target) pickle
# cheaply and read-only usage in workers means no synchronisation needed.

from __future__ import annotations

import os
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, replace
from typing import Iterable

import numpy as np

from .core import Perm, mismatch_ratio
from .sa_kernel import SAConfig, SAResult, run_sa


@dataclass
class WorkItem:
    space_name: str
    rung_name: str
    target_perm: Perm
    n: int
    run_id: int
    sa_config: SAConfig


def _build_space(name: str, n: int):
    # Imported inside worker to avoid circular-import cost at module load
    from .spaces import (
        CycleArcSpace,
        CycleGeometrySpace,
        HybridScheduleSpace,
        RawFYSeedSpace,
    )
    if name == "raw_fy_seed":
        return RawFYSeedSpace(n)
    if name == "cycle_geometry":
        return CycleGeometrySpace(n)
    if name == "hybrid_schedule":
        return HybridScheduleSpace(n)
    if name == "cycle_arc":
        return CycleArcSpace(n)
    raise ValueError(f"unknown space: {name}")


def _run_one_work_item(item: WorkItem) -> tuple[str, str, SAResult]:
    """Top-level function (picklable) that a worker runs."""
    space = _build_space(item.space_name, item.n)
    local_config = replace(item.sa_config,
                           rng_seed=item.sa_config.rng_seed + item.run_id)
    # Workers log with their own prefix so the console is readable under -j>1
    pid = os.getpid()
    def _log(msg: str) -> None:
        print(f"[pid:{pid}] {msg}", flush=True)
    result = run_sa(space, item.target_perm, local_config,
                    energy_fn=mismatch_ratio, run_id=item.run_id,
                    log_fn=_log)
    return item.space_name, item.rung_name, result


def run_parallel(work_items: Iterable[WorkItem], max_workers: int | None = None,
                 ) -> list[tuple[str, str, SAResult]]:
    """
    Execute a batch of work items across a process pool.
    Returns list of (space_name, rung_name, SAResult) in completion order.
    """
    items = list(work_items)
    if max_workers is None:
        max_workers = min(len(items), max(1, (os.cpu_count() or 2) - 1))
    print(f"[parallel] running {len(items)} work items with {max_workers} workers")

    results: list[tuple[str, str, SAResult]] = []
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(_run_one_work_item, item) for item in items]
        for fut in as_completed(futures):
            space_name, rung_name, result = fut.result()
            results.append((space_name, rung_name, result))
    return results
