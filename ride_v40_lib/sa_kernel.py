# ride_v40_lib/sa_kernel.py — generic simulated-annealing kernel
# v1.0 — 2026-04-15
#
# Extracted from /Users/trentpalelei/Desktop/TSP/lambda_function_37_original.py
# (rsn_refinement v7.2 "Path Annealing"): temperature schedule, Metropolis
# acceptance, best-path tracking. The original is tightly coupled to TSP
# routes with 2-opt moves; here we strip the inner-loop route manipulation
# and parameterise by a generic ThetaSpace and energy callback so the SAME
# SA control logic drives cycle-geometry, hybrid-schedule, cycle-arc, or
# raw-FY-seed searches interchangeably.

from __future__ import annotations

import json
import math
import random
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Optional

from .core import Perm, ThetaSpace, mismatch_ratio


# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

@dataclass
class SAConfig:
    """Matches the shape of lambda_function_37 SA parameters, generalised."""
    initial_temp: float = 1.0
    cooling_rate: float = 0.9995           # per-iteration exponential decay
    min_temp: float = 1e-9
    max_iterations: int = 20_000
    wallclock_budget_sec: float = 900.0    # 15 min default per (space, rung, run)
    restart_patience: int = 3_000          # iters without improvement before restart
    restart_keep_best: bool = True         # restart at best-θ (True) vs fresh sample (False)
    rng_seed: int = 0                      # run-level seed for reproducibility
    log_every: int = 250                   # iterations between log lines
    early_stop_mismatch: float = 0.0       # stop if mismatch_ratio <= this (0 = only on exact)


@dataclass
class SAResult:
    """One completed SA run."""
    space_name: str
    run_id: int
    n_iterations: int
    wallclock_sec: float
    initial_energy: float
    best_energy: float
    best_theta_json: dict
    best_iteration: int
    metropolis_accepts: int
    improvements: int
    restarts: int
    energy_trace: list[tuple[int, float]] = field(default_factory=list)  # (iter, energy)
    exact_match: bool = False  # hash oracle outcome (filled by caller if checked)


# --------------------------------------------------------------------------
# Main kernel
# --------------------------------------------------------------------------

def run_sa(
    space: ThetaSpace,
    target_perm: Perm,
    config: SAConfig,
    energy_fn: Optional[Callable[[Perm, Perm], float]] = None,
    run_id: int = 0,
    log_fn: Optional[Callable[[str], None]] = None,
) -> SAResult:
    """
    Run SA over `space` trying to match `target_perm`.

    energy_fn(current, target) defaults to mismatch_ratio (float in [0,1]).
    """
    if energy_fn is None:
        energy_fn = mismatch_ratio

    log = log_fn or print
    rng = random.Random(config.rng_seed + run_id * 104729)

    log(f"[SA:{space.name}:{run_id}] start  n={space.n:,}  T0={config.initial_temp:.3f}  "
        f"cool={config.cooling_rate}  budget={config.wallclock_budget_sec:.0f}s  "
        f"max_iter={config.max_iterations:,}")

    # Initial sample
    theta = space.sample(rng)
    sigma = space.construct(theta)
    energy = float(energy_fn(sigma, target_perm))
    initial_energy = energy

    best_theta = theta
    best_energy = energy
    best_iteration = 0

    temperature = config.initial_temp
    metropolis_accepts = 0
    improvements = 0
    restarts = 0
    since_last_improve = 0
    energy_trace: list[tuple[int, float]] = [(0, energy)]

    t_start = time.time()
    last_log_t = t_start

    for iteration in range(1, config.max_iterations + 1):
        # Neighbour proposal
        theta_prime = space.neighbor(theta, temperature / config.initial_temp, rng)
        sigma_prime = space.construct(theta_prime)
        energy_prime = float(energy_fn(sigma_prime, target_perm))

        # Metropolis (extracted from lambda_function_37:680-694)
        delta = energy_prime - energy
        accept = False
        if delta <= 0:
            accept = True
        elif temperature > config.min_temp:
            prob = math.exp(-delta / temperature)
            if rng.random() < prob:
                accept = True
                metropolis_accepts += 1

        if accept:
            theta = theta_prime
            energy = energy_prime
            if energy < best_energy:
                best_energy = energy
                best_theta = theta_prime
                best_iteration = iteration
                improvements += 1
                since_last_improve = 0
            else:
                since_last_improve += 1
        else:
            since_last_improve += 1

        # Cool
        temperature *= config.cooling_rate

        # Restart logic (stagnation)
        if since_last_improve >= config.restart_patience:
            restarts += 1
            if config.restart_keep_best:
                theta = best_theta
                energy = best_energy
            else:
                theta = space.sample(rng)
                energy = float(energy_fn(space.construct(theta), target_perm))
            temperature = config.initial_temp * 0.5   # partial reheat
            since_last_improve = 0

        # Early stop
        if best_energy <= config.early_stop_mismatch:
            log(f"[SA:{space.name}:{run_id}] early_stop iter={iteration:,} "
                f"best_energy={best_energy:.6f}")
            energy_trace.append((iteration, energy))
            break

        # Wallclock budget
        now = time.time()
        if now - t_start > config.wallclock_budget_sec:
            log(f"[SA:{space.name}:{run_id}] budget_reached iter={iteration:,}")
            break

        # Periodic logging
        if iteration % config.log_every == 0 or now - last_log_t > 10.0:
            energy_trace.append((iteration, energy))
            log(f"[SA:{space.name}:{run_id}] iter={iteration:>7,d}  "
                f"E={energy:.4f}  best={best_energy:.4f}  "
                f"T={temperature:.3e}  metro={metropolis_accepts}  "
                f"imp={improvements}  restarts={restarts}  "
                f"elapsed={now - t_start:.1f}s")
            last_log_t = now

        if temperature < config.min_temp:
            log(f"[SA:{space.name}:{run_id}] T_frozen iter={iteration:,} T={temperature:.2e}")
            break

    wallclock = time.time() - t_start
    final_iter = iteration  # noqa: F823 (last iteration executed)
    energy_trace.append((final_iter, energy))

    log(f"[SA:{space.name}:{run_id}] done  iters={final_iter:,}  "
        f"best={best_energy:.6f}  initial={initial_energy:.6f}  "
        f"improve={(initial_energy - best_energy):.6f}  "
        f"wall={wallclock:.1f}s")

    return SAResult(
        space_name=space.name,
        run_id=run_id,
        n_iterations=final_iter,
        wallclock_sec=wallclock,
        initial_energy=initial_energy,
        best_energy=best_energy,
        best_theta_json=space.to_json(best_theta),
        best_iteration=best_iteration,
        metropolis_accepts=metropolis_accepts,
        improvements=improvements,
        restarts=restarts,
        energy_trace=energy_trace,
    )


def result_to_json(result: SAResult) -> dict:
    """JSON-safe dict of a SAResult for log files."""
    return {
        "space_name": result.space_name,
        "run_id": result.run_id,
        "n_iterations": result.n_iterations,
        "wallclock_sec": round(result.wallclock_sec, 2),
        "initial_energy": result.initial_energy,
        "best_energy": result.best_energy,
        "best_theta": result.best_theta_json,
        "best_iteration": result.best_iteration,
        "metropolis_accepts": result.metropolis_accepts,
        "improvements": result.improvements,
        "restarts": result.restarts,
        "energy_trace": [[int(i), float(e)] for i, e in result.energy_trace],
        "exact_match": result.exact_match,
    }


def save_results(results: list[SAResult], out_path: Path, meta: dict) -> None:
    payload = {
        "meta": meta,
        "results": [result_to_json(r) for r in results],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        json.dump(payload, f, indent=2)
