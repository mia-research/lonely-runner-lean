#!/usr/bin/env python3
"""
RIDE V24 - Order-family harness.

Exploratory comparison of four order generators on the same target after the
same K-materialisation + frequency-patch front end:

  1. fixed Fisher-Yates orbit
  2. affine index orbit
  3. lane/block orbit
  4. cycle-arc orbit

For each family we apply 1, 2, and 3 stages and measure the residual order:
  - mile          : minimum transpositions still needed
  - fixed         : positions already correct
  - mismatch      : positions still wrong
  - mean_span     : average displacement of the exact target->source map
  - max_span      : worst displacement

This is an exploratory harness, not a codec. The goal is to identify which
order family burns residual structure fastest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from ride_v10_whole_file_tsp_addr import candidate_lane_strides, exact_cycle_stats, merge_lanes, split_lanes
from ride_v13_canterbury_recipe_bench import build_perm_target_to_source
from ride_v16_whole_file_orbit_steps import PCG32
from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v21_block_move_rsn import block_move_plan
from ride_v23_cycle_arc_compiler import CycleArcPlan, compile_cycle_to_arc_macros, replay_cycle_arc_plan, sorted_non_trivial_cycles


K_CANDIDATES = (1, 2, 3, 4, 5, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256)
LANE_K_CANDIDATES = (1, -1, 2, -2, 4, -4, 8, -8, 16, -16)
LANE_STRIDE_LIMIT = 10
AFFINE_FAMILY_COUNT = 12
AFFINE_TOP_KS = 6
FY_TOP_KS = 8
CYCLE_TOP_COUNT = 4
CYCLE_PREFIX_CANDIDATES = (1, 2, 4)
SCHEDULE_SEARCH_DEFAULT_ITERS = 0
SCHEDULE_SEARCH_DEFAULT_TEMP = 18.0
SCHEDULE_SEARCH_DEFAULT_COOLING = 0.93


@dataclass
class ResidualStats:
    mile: int
    cycles: int
    fixed: int
    mismatch: int
    mean_span: float
    max_span: int


@dataclass
class StageResult:
    stage: int
    improved: bool
    stats: ResidualStats
    meta: dict[str, Any]


def parse_schedule(spec: str | None) -> list[str]:
    if spec is None:
        return ["affine_index", "lane_block"]
    parts = [item.strip() for item in spec.split(",") if item.strip()]
    return parts if parts else ["affine_index", "lane_block"]


def parse_name_list(spec: str | None) -> list[str]:
    if spec is None:
        return []
    return [item.strip() for item in spec.split(",") if item.strip()]


def require_known_names(names: list[str], known: list[str], label: str) -> list[str]:
    unknown = [name for name in names if name not in known]
    if unknown:
        raise SystemExit(f"unknown {label}: {', '.join(unknown)}; known: {', '.join(known)}")
    return names


def expand_schedule(seed_schedule: list[str], max_stages: int) -> list[str]:
    if max_stages <= 0:
        return []
    base = list(seed_schedule) if seed_schedule else ["affine_index", "lane_block"]
    out: list[str] = []
    while len(out) < max_stages:
        out.extend(base)
    return out[:max_stages]


def raw_hash_seed(raw: bytes, salt: bytes = b"") -> int:
    digest = hashlib.sha256(salt + raw).hexdigest()
    return int(digest[:16], 16)


def state_hash(state: list[int]) -> str:
    return hashlib.sha256(bytes(state)).hexdigest()


def residual_stats(current: list[int], target: list[int]) -> ResidualStats:
    stats = exact_cycle_stats(target, current)
    fixed = int(stats["fixed_points"])
    mismatch = len(target) - fixed
    return ResidualStats(
        mile=int(stats["mile"]),
        cycles=int(stats["cycles"]),
        fixed=fixed,
        mismatch=mismatch,
        mean_span=float(stats["mean_span"]),
        max_span=int(stats["max_span"]),
    )


def stats_key(stats: ResidualStats) -> tuple[int, int, int, int, int]:
    return (
        stats.mile,
        stats.mismatch,
        int(round(stats.mean_span * 1000.0)),
        stats.max_span,
        -stats.fixed,
    )


def better(new_stats: ResidualStats, old_stats: ResidualStats) -> bool:
    return stats_key(new_stats) < stats_key(old_stats)


def stats_energy(stats: ResidualStats) -> float:
    return (
        float(stats.mile)
        + 0.05 * float(stats.mismatch)
        + 0.01 * float(stats.mean_span)
        + 0.001 * float(stats.max_span)
        - 0.01 * float(stats.fixed)
    )


def apply_output_to_source_perm(state: list[int], perm: list[int]) -> list[int]:
    return [state[source_index] for source_index in perm]


def decompose_perm(perm: list[int]) -> list[list[int]]:
    n = len(perm)
    seen = [False] * n
    cycles: list[list[int]] = []
    for start in range(n):
        if seen[start]:
            continue
        cycle: list[int] = []
        cur = start
        while not seen[cur]:
            seen[cur] = True
            cycle.append(cur)
            cur = perm[cur]
        cycles.append(cycle)
    return cycles


def perm_power(perm: list[int], cycles: list[list[int]], k: int) -> list[int]:
    if k == 0:
        return list(range(len(perm)))
    out = [0] * len(perm)
    for cycle in cycles:
        length = len(cycle)
        shift = k % length
        for index, position in enumerate(cycle):
            out[position] = cycle[(index + shift) % length]
    return out


def apply_perm_power(state: list[int], perm: list[int], cycles: list[list[int]], k: int) -> list[int]:
    return apply_output_to_source_perm(state, perm_power(perm, cycles, k))


def fisher_yates_sigma(n: int, seed: int) -> list[int]:
    rng = PCG32(seed)
    sigma = list(range(n))
    for index in range(n - 1, 0, -1):
        swap_index = rng.next_uniform(index + 1)
        sigma[index], sigma[swap_index] = sigma[swap_index], sigma[index]
    return sigma


def coprime_multiplier(rng: PCG32, n: int) -> int:
    if n <= 2:
        return 1
    candidate = rng.next_uniform(max(2, n - 1)) + 1
    while candidate > 1 and math.gcd(candidate, n) != 1:
        candidate += 1
        if candidate >= n:
            candidate = 1
    return candidate


def affine_sigma(n: int, a: int, b: int) -> list[int]:
    return [((a * index) + b) % n for index in range(n)]


def lane_rotate_state(state: list[int], stride: int, k: int) -> list[int]:
    lanes = split_lanes(state, stride)
    out_lanes: list[list[int]] = []
    for lane_index, lane in enumerate(lanes):
        if not lane:
            out_lanes.append([])
            continue
        shift_seed = lane_index * 7 + len(lane) // 5 + 1
        shift = (k * shift_seed) % len(lane)
        rotated = list(lane[shift:]) + list(lane[:shift])
        out_lanes.append(rotated)
    return merge_lanes(out_lanes, len(state))


def apply_block_or_swap(state: list[int], op: tuple) -> list[int]:
    out = list(state)
    tag = op[0]
    if tag == "S":
        _, a, b = op
        out[a], out[b] = out[b], out[a]
        return out
    if tag == "M":
        _, src, dst, length = op
        block = out[src:src + length]
        del out[src:src + length]
        if src < dst:
            dst -= length
        out[dst:dst] = block
        return out
    raise ValueError(f"unknown block op tag: {tag}")


class FisherOrbitFamily:
    def __init__(self, n: int, raw: bytes):
        self.seed = raw_hash_seed(raw, b"fy-orbit")
        self.sigma = fisher_yates_sigma(n, self.seed)
        self.cycles = decompose_perm(self.sigma)
        cycle_lengths = sorted((len(cycle) for cycle in self.cycles), reverse=True)[:6]
        extra = {
            value
            for length in cycle_lengths
            for value in (length // 4, length // 2, (3 * length) // 4, length - 1)
            if value > 0
        }
        self.k_values = sorted(set(K_CANDIDATES) | extra)

    def candidates(self, current: list[int], target: list[int], current_stats: ResidualStats) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        candidates: list[tuple[list[int], ResidualStats, dict[str, Any]]] = []
        for k in self.k_values:
            if k == 0:
                continue
            candidate = apply_perm_power(current, self.sigma, self.cycles, k)
            candidate_stats = residual_stats(candidate, target)
            meta = {"family": "fixed_fy", "seed": self.seed, "k": k}
            candidates.append((candidate, candidate_stats, meta))
        candidates.sort(key=lambda item: stats_key(item[1]))
        return candidates

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        best_state = current
        best_stats = current_stats
        best_meta: dict[str, Any] = {"family": "fixed_fy", "seed": self.seed, "k": 0}

        for candidate, candidate_stats, meta in self.candidates(current, target, current_stats):
            if better(candidate_stats, best_stats):
                best_state = candidate
                best_stats = candidate_stats
                best_meta = meta

        return best_state, best_meta


class AffineOrbitFamily:
    def __init__(self, n: int, raw: bytes):
        self.seed = raw_hash_seed(raw, b"affine-orbit")
        rng = PCG32(self.seed)
        self.orbits: list[dict[str, Any]] = []
        for _ in range(AFFINE_FAMILY_COUNT):
            a = coprime_multiplier(rng, n)
            b = rng.next_uniform(n) if n > 0 else 0
            sigma = affine_sigma(n, a, b)
            cycles = decompose_perm(sigma)
            cycle_lengths = sorted((len(cycle) for cycle in cycles), reverse=True)[:4]
            k_values = sorted(
                set(K_CANDIDATES)
                | {
                    value
                    for length in cycle_lengths
                    for value in (length // 4, length // 2, (3 * length) // 4, length - 1)
                    if value > 0
                }
            )
            self.orbits.append({"a": a, "b": b, "sigma": sigma, "cycles": cycles, "k_values": k_values})

    def candidates(self, current: list[int], target: list[int], current_stats: ResidualStats) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        candidates: list[tuple[list[int], ResidualStats, dict[str, Any]]] = []
        for orbit in self.orbits:
            for k in orbit["k_values"][:AFFINE_TOP_KS]:
                if k == 0:
                    continue
                candidate = apply_perm_power(current, orbit["sigma"], orbit["cycles"], k)
                candidate_stats = residual_stats(candidate, target)
                meta = {"family": "affine", "a": orbit["a"], "b": orbit["b"], "k": k}
                candidates.append((candidate, candidate_stats, meta))
        candidates.sort(key=lambda item: stats_key(item[1]))
        return candidates

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        best_state = current
        best_stats = current_stats
        best_meta: dict[str, Any] = {"family": "affine", "a": None, "b": None, "k": 0}

        for candidate, candidate_stats, meta in self.candidates(current, target, current_stats):
            if better(candidate_stats, best_stats):
                best_state = candidate
                best_stats = candidate_stats
                best_meta = meta

        return best_state, best_meta


class LaneBlockOrbitFamily:
    def candidates(self, current: list[int], target: list[int], current_stats: ResidualStats) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        candidates: list[tuple[list[int], ResidualStats, dict[str, Any]]] = []

        base_stats = exact_cycle_stats(target, current)
        strides = candidate_lane_strides(base_stats)[:LANE_STRIDE_LIMIT]
        for stride in strides:
            for k in LANE_K_CANDIDATES:
                if k == 0:
                    continue
                candidate = lane_rotate_state(current, stride, k)
                candidate_stats = residual_stats(candidate, target)
                meta = {"family": "lane_block", "mode": "lane", "stride": stride, "k": k}
                candidates.append((candidate, candidate_stats, meta))

        perm = list(build_perm_target_to_source(bytearray(target), bytearray(current)))
        plan = block_move_plan(perm, focus_window=128, min_block=8, max_probe=2048)
        for op in plan["ops"][:8]:
            candidate = apply_block_or_swap(current, op)
            candidate_stats = residual_stats(candidate, target)
            meta = {"family": "lane_block", "mode": "block", "op": list(op)}
            candidates.append((candidate, candidate_stats, meta))

        candidates.sort(key=lambda item: stats_key(item[1]))
        return candidates

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        best_state = current
        best_stats = current_stats
        best_meta: dict[str, Any] = {"family": "lane_block", "mode": "none"}

        for candidate, candidate_stats, meta in self.candidates(current, target, current_stats):
            if better(candidate_stats, best_stats):
                best_state = candidate
                best_stats = candidate_stats
                best_meta = meta

        return best_state, best_meta


class CycleArcOrbitFamily:
    def candidates(self, current: list[int], target: list[int], current_stats: ResidualStats) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        perm = list(build_perm_target_to_source(bytearray(target), bytearray(current)))
        cycles = sorted_non_trivial_cycles(perm)[:CYCLE_TOP_COUNT]
        candidates: list[tuple[list[int], ResidualStats, dict[str, Any]]] = []

        for cycle_index, cycle in enumerate(cycles):
            plan = compile_cycle_to_arc_macros(cycle, perm)
            if not plan.macros:
                continue
            for prefix_len in CYCLE_PREFIX_CANDIDATES:
                if prefix_len > len(plan.macros):
                    continue
                prefix_plan = CycleArcPlan(
                    pivot=plan.pivot,
                    sorted_members=plan.sorted_members,
                    macros=plan.macros[:prefix_len],
                    swaps=plan.swaps,
                    covered_by_long_macros=plan.covered_by_long_macros,
                    long_macro_count=plan.long_macro_count,
                )
                candidate = list(current)
                replay_cycle_arc_plan(candidate, prefix_plan)
                candidate_stats = residual_stats(candidate, target)
                meta = {
                    "family": "cycle_arc",
                    "cycle_index": cycle_index,
                    "pivot": plan.pivot,
                    "prefix_macros": prefix_len,
                }
                candidates.append((candidate, candidate_stats, meta))

        candidates.sort(key=lambda item: stats_key(item[1]))
        return candidates

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        best_state = current
        best_stats = current_stats
        best_meta: dict[str, Any] = {"family": "cycle_arc", "mode": "none"}

        for candidate, candidate_stats, meta in self.candidates(current, target, current_stats):
            if better(candidate_stats, best_stats):
                best_state = candidate
                best_stats = candidate_stats
                best_meta = meta

        return best_state, best_meta


class HybridOrbitFamily:
    def __init__(self, schedule: list[str], family_map: dict[str, Any]):
        self.schedule = list(schedule)
        self.family_map = family_map
        self.stage_index = 0

    def reset(self) -> None:
        self.stage_index = 0

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        family_name = self.schedule[min(self.stage_index, len(self.schedule) - 1)]
        self.stage_index += 1
        family = self.family_map[family_name]
        best_state, meta = family.stage(current, target, current_stats)
        return best_state, {
            "family": "hybrid",
            "stage_family": family_name,
            "schedule": self.schedule,
            "inner": meta,
        }


class AnnealedHybridFamily:
    def __init__(
        self,
        schedule: list[str],
        family_map: dict[str, Any],
        raw: bytes,
        initial_temp: float = 50.0,
        cooling_rate: float = 0.82,
        candidates_per_family: int = 3,
    ):
        self.schedule = list(schedule)
        self.family_map = family_map
        self.seed = raw_hash_seed(raw, b"annealed-hybrid")
        self.initial_temp = initial_temp
        self.cooling_rate = cooling_rate
        self.candidates_per_family = candidates_per_family
        self.reset()

    def reset(self) -> None:
        self.stage_index = 0
        self.temperature = self.initial_temp
        self.rng = PCG32(self.seed)

    def _family_candidates(
        self,
        family_name: str,
        current: list[int],
        target: list[int],
        current_stats: ResidualStats,
    ) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        family = self.family_map[family_name]
        if hasattr(family, "candidates"):
            return family.candidates(current, target, current_stats)[: self.candidates_per_family]
        next_state, meta = family.stage(current, target, current_stats)
        next_stats = residual_stats(next_state, target)
        return [(next_state, next_stats, meta)]

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        pool = self.schedule or list(self.family_map.keys())
        candidates: list[tuple[str, list[int], ResidualStats, dict[str, Any]]] = []
        for family_name in pool:
            for candidate_state, candidate_stats, meta in self._family_candidates(family_name, current, target, current_stats):
                candidates.append((family_name, candidate_state, candidate_stats, meta))

        if not candidates:
            return current, {
                "family": "annealed_hybrid",
                "schedule": self.schedule,
                "accepted": False,
                "reason": "no_candidates",
                "temperature": self.temperature,
            }

        current_energy = stats_energy(current_stats)
        candidates.sort(key=lambda item: stats_energy(item[2]))
        chosen_family, chosen_state, chosen_stats, chosen_meta = candidates[0]
        chosen_energy = stats_energy(chosen_stats)
        accepted = False
        reason = "best"

        if chosen_state != current and chosen_energy <= current_energy:
            accepted = True
        else:
            uphill = [item for item in candidates if item[1] != current]
            if uphill:
                probe = uphill[self.rng.next_uniform(len(uphill))]
                probe_energy = stats_energy(probe[2])
                delta_energy = probe_energy - current_energy
                if delta_energy <= 0:
                    chosen_family, chosen_state, chosen_stats, chosen_meta = probe
                    chosen_energy = probe_energy
                    accepted = True
                    reason = "alternative_nonworse"
                elif self.temperature > 1e-12:
                    accept_prob = math.exp(-delta_energy / max(self.temperature, 1e-12))
                    threshold = self.rng.next() / 0xFFFFFFFF
                    if threshold < accept_prob:
                        chosen_family, chosen_state, chosen_stats, chosen_meta = probe
                        chosen_energy = probe_energy
                        accepted = True
                        reason = "metropolis"

        meta = {
            "family": "annealed_hybrid",
            "schedule": self.schedule,
            "chosen_family": chosen_family,
            "accepted": accepted,
            "reason": reason,
            "temperature": self.temperature,
            "current_energy": round(current_energy, 6),
            "chosen_energy": round(chosen_energy, 6),
            "inner": chosen_meta,
        }
        self.stage_index += 1
        self.temperature *= self.cooling_rate
        return (chosen_state if accepted else current), meta


def policy_unit(current_stats: ResidualStats) -> float:
    return max(1.0, min(48.0, math.sqrt(max(1, current_stats.mile)) / 12.0))


def macro_micro_bias(stage_index: int, family_name: str, meta: dict[str, Any], current_stats: ResidualStats) -> float:
    """
    Negative bias is a bonus (preferred), positive bias is a penalty.

    Learned from the current experiments:
      - early global affine moves help most
      - lane rotations are strong mid-bridges
      - block swaps matter later as repair
      - Fisher-Yates can occasionally help as a pivot, but shouldn't dominate
      - cycle-arc is currently weak on page-scale document/binary probes
    """
    unit = policy_unit(current_stats)
    stage = min(stage_index, 3)

    if family_name == "affine_index":
        return (-2.0, -1.5, -1.0, -0.4)[stage] * unit

    if family_name == "lane_block":
        mode = meta.get("mode")
        if mode == "lane":
            return (-1.2, -1.3, -0.8, -0.6)[stage] * unit
        if mode == "block":
            return (1.5, 0.8, -0.3, -1.4)[stage] * unit
        return 0.0

    if family_name == "fixed_fisher_yates":
        return (-0.4, -0.3, 0.0, 0.5)[stage] * unit

    if family_name == "cycle_arc":
        return (2.5, 2.0, 1.3, 0.7)[stage] * unit

    return 0.0


class AnnealedHybridV2Family:
    def __init__(
        self,
        family_map: dict[str, Any],
        raw: bytes,
        initial_temp: float = 40.0,
        cooling_rate: float = 0.84,
        candidates_per_family: int = 3,
    ):
        self.family_map = family_map
        self.seed = raw_hash_seed(raw, b"annealed-hybrid-v2")
        self.initial_temp = initial_temp
        self.cooling_rate = cooling_rate
        self.candidates_per_family = candidates_per_family
        self.reset()

    def reset(self) -> None:
        self.stage_index = 0
        self.temperature = self.initial_temp
        self.rng = PCG32(self.seed)

    def _family_candidates(
        self,
        family_name: str,
        current: list[int],
        target: list[int],
        current_stats: ResidualStats,
    ) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
        family = self.family_map[family_name]
        if hasattr(family, "candidates"):
            return family.candidates(current, target, current_stats)[: self.candidates_per_family]
        next_state, meta = family.stage(current, target, current_stats)
        next_stats = residual_stats(next_state, target)
        return [(next_state, next_stats, meta)]

    def stage(self, current: list[int], target: list[int], current_stats: ResidualStats) -> tuple[list[int], dict[str, Any]]:
        candidates: list[tuple[float, float, str, list[int], ResidualStats, dict[str, Any]]] = []
        current_energy = stats_energy(current_stats)

        for family_name in self.family_map:
            for candidate_state, candidate_stats, meta in self._family_candidates(family_name, current, target, current_stats):
                base_energy = stats_energy(candidate_stats)
                bias = macro_micro_bias(self.stage_index, family_name, meta, current_stats)
                guided_energy = base_energy + bias
                candidates.append((guided_energy, base_energy, family_name, candidate_state, candidate_stats, meta))

        if not candidates:
            return current, {
                "family": "annealed_hybrid_v2",
                "accepted": False,
                "reason": "no_candidates",
                "temperature": self.temperature,
                "stage_index": self.stage_index,
            }

        candidates.sort(key=lambda item: (item[0], item[1]))
        best_guided, best_base, chosen_family, chosen_state, chosen_stats, chosen_meta = candidates[0]
        chosen_energy = best_base
        chosen_bias = best_guided - best_base
        accepted = False
        reason = "guided_best"

        if chosen_state != current and chosen_energy <= current_energy:
            accepted = True
        else:
            uphill = [item for item in candidates if item[3] != current]
            if uphill:
                probe = uphill[self.rng.next_uniform(len(uphill))]
                probe_guided, probe_base, probe_family, probe_state, probe_stats, probe_meta = probe
                delta_energy = probe_base - current_energy
                if delta_energy <= 0:
                    chosen_family, chosen_state, chosen_stats, chosen_meta = probe_family, probe_state, probe_stats, probe_meta
                    chosen_energy = probe_base
                    chosen_bias = probe_guided - probe_base
                    accepted = True
                    reason = "alternative_nonworse"
                elif self.temperature > 1e-12:
                    accept_prob = math.exp(-delta_energy / max(self.temperature, 1e-12))
                    threshold = self.rng.next() / 0xFFFFFFFF
                    if threshold < accept_prob:
                        chosen_family, chosen_state, chosen_stats, chosen_meta = probe_family, probe_state, probe_stats, probe_meta
                        chosen_energy = probe_base
                        chosen_bias = probe_guided - probe_base
                        accepted = True
                        reason = "metropolis"

        meta = {
            "family": "annealed_hybrid_v2",
            "accepted": accepted,
            "reason": reason,
            "temperature": self.temperature,
            "stage_index": self.stage_index,
            "chosen_family": chosen_family,
            "current_energy": round(current_energy, 6),
            "chosen_energy": round(chosen_energy, 6),
            "chosen_bias": round(chosen_bias, 6),
            "inner": chosen_meta,
        }
        self.stage_index += 1
        self.temperature *= self.cooling_rate
        return (chosen_state if accepted else current), meta


def simulate_schedule(
    schedule: list[str],
    family_map: dict[str, Any],
    source: list[int],
    target: list[int],
    max_stages: int,
) -> tuple[list[StageResult], ResidualStats]:
    current = list(source)
    current_stats = residual_stats(current, target)
    results: list[StageResult] = []

    for stage_index in range(max_stages):
        family_name = schedule[min(stage_index, len(schedule) - 1)]
        family = family_map[family_name]
        next_state, inner_meta = family.stage(current, target, current_stats)
        next_stats = residual_stats(next_state, target)
        improved = next_state != current and better(next_stats, current_stats)
        if improved:
            current = next_state
            current_stats = next_stats
        results.append(
            StageResult(
                stage=stage_index + 1,
                improved=improved,
                stats=current_stats,
                meta={
                    "family": "schedule_search_stage",
                    "stage_family": family_name,
                    "inner": inner_meta,
                },
            )
        )

    return results, current_stats


def mutate_schedule(schedule: list[str], family_names: list[str], rng: PCG32) -> tuple[list[str], dict[str, Any]]:
    if not schedule:
        return list(schedule), {"mutation": "noop"}

    out = list(schedule)
    mutation = rng.next_uniform(4)

    if mutation == 0:
        index = rng.next_uniform(len(out))
        replacement = family_names[rng.next_uniform(len(family_names))]
        out[index] = replacement
        return out, {"mutation": "replace", "index": index, "replacement": replacement}

    if mutation == 1 and len(out) > 1:
        left = rng.next_uniform(len(out))
        right = rng.next_uniform(len(out))
        while right == left:
            right = rng.next_uniform(len(out))
        out[left], out[right] = out[right], out[left]
        return out, {"mutation": "swap", "left": left, "right": right}

    if mutation == 2 and len(out) > 2:
        start = rng.next_uniform(len(out) - 1)
        stop = start + 1 + rng.next_uniform(len(out) - start)
        segment = out[start:stop]
        if len(segment) > 1:
            shift = 1 + rng.next_uniform(len(segment) - 1)
            out[start:stop] = segment[shift:] + segment[:shift]
            return out, {"mutation": "rotate", "start": start, "stop": stop, "shift": shift}

    start = rng.next_uniform(len(out))
    span = 1 + rng.next_uniform(len(out) - start)
    replacement = family_names[rng.next_uniform(len(family_names))]
    for index in range(start, start + span):
        out[index] = replacement
    return out, {"mutation": "flood", "start": start, "span": span, "replacement": replacement}


def anneal_schedule_search(
    seed_schedule: list[str],
    family_map: dict[str, Any],
    source: list[int],
    target: list[int],
    max_stages: int,
    raw: bytes,
    iterations: int,
    initial_temp: float,
    cooling_rate: float,
    progress: bool = False,
) -> dict[str, Any]:
    family_names = list(family_map.keys())
    current_schedule = expand_schedule(seed_schedule, max_stages)
    current_results, current_stats = simulate_schedule(current_schedule, family_map, source, target, max_stages)
    current_energy = stats_energy(current_stats)

    best_schedule = list(current_schedule)
    best_results = list(current_results)
    best_stats = current_stats
    best_energy = current_energy
    best_iteration = 0

    accepted_moves = 0
    temperature = initial_temp
    rng = PCG32(raw_hash_seed(raw, b"annealed-schedule-search"))

    if progress:
        print(
            f"[search] start energy={current_energy:.4f} schedule={','.join(current_schedule)}",
            flush=True,
        )

    for iteration in range(1, iterations + 1):
        candidate_schedule, mutation_meta = mutate_schedule(current_schedule, family_names, rng)
        candidate_results, candidate_stats = simulate_schedule(candidate_schedule, family_map, source, target, max_stages)
        candidate_energy = stats_energy(candidate_stats)
        delta_energy = candidate_energy - current_energy

        accept = False
        reason = "reject"
        if delta_energy < 0:
            accept = True
            reason = "improve"
        elif temperature > 1e-12:
            accept_prob = math.exp(-delta_energy / max(temperature, 1e-12))
            threshold = rng.next() / 0xFFFFFFFF
            if threshold < accept_prob:
                accept = True
                reason = "metropolis"

        if accept:
            accepted_moves += 1
            current_schedule = candidate_schedule
            current_results = candidate_results
            current_stats = candidate_stats
            current_energy = candidate_energy

        if candidate_energy < best_energy:
            best_schedule = list(candidate_schedule)
            best_results = list(candidate_results)
            best_stats = candidate_stats
            best_energy = candidate_energy
            best_iteration = iteration
            if progress:
                print(
                    f"[search] best iter={iteration} energy={best_energy:.4f} "
                    f"mile={best_stats.mile} schedule={','.join(best_schedule)}",
                    flush=True,
                )

        if progress and (
            iteration == 1
            or iteration == iterations
            or iteration % max(1, iterations // 8) == 0
        ):
            print(
                f"[search] iter={iteration} accepted={reason if accept else 'no'} "
                f"temp={temperature:.4f} current={current_energy:.4f} best={best_energy:.4f} "
                f"mutation={json.dumps(mutation_meta, separators=(',', ':'))}",
                flush=True,
            )

        temperature *= cooling_rate

    return {
        "schedule": best_schedule,
        "results": best_results,
        "stats": best_stats,
        "meta": {
            "seed_schedule": expand_schedule(seed_schedule, max_stages),
            "best_schedule": best_schedule,
            "iterations": iterations,
            "accepted_moves": accepted_moves,
            "best_iteration": best_iteration,
            "initial_temp": initial_temp,
            "cooling_rate": cooling_rate,
            "best_energy": round(best_energy, 6),
        },
    }


def run_family(name: str, family: Any, source: list[int], target: list[int], max_stages: int, progress: bool = False) -> list[StageResult]:
    current = list(source)
    current_stats = residual_stats(current, target)
    results: list[StageResult] = []
    if hasattr(family, "reset"):
        family.reset()

    for stage in range(1, max_stages + 1):
        next_state, meta = family.stage(current, target, current_stats)
        next_stats = residual_stats(next_state, target)
        improved = next_state != current and better(next_stats, current_stats)
        if improved:
            current = next_state
            current_stats = next_stats
        row = StageResult(stage=stage, improved=improved, stats=current_stats, meta=meta)
        results.append(row)
        if progress:
            print(
                f"[{name}] stage={stage} improved={'yes' if improved else 'no'} "
                f"mile={row.stats.mile} fixed={row.stats.fixed} mismatch={row.stats.mismatch}",
                flush=True,
            )
    return results


def load_raw(args: argparse.Namespace) -> bytes:
    if args.text is not None:
        return args.text.encode("utf-8")
    if args.file is not None:
        raw = Path(args.file).expanduser().read_bytes()
        if args.byte_limit is not None:
            return raw[: args.byte_limit]
        return raw
    sample = "Hello World, Hello Kimi".encode("utf-8")
    return sample


def print_stage_table(name: str, initial: ResidualStats, stages: list[StageResult]) -> None:
    print(f"\n{name}", flush=True)
    print("  stage | improved | mile | fixed | mismatch | mean_span | max_span | meta", flush=True)
    print(
        f"      0 |       -  | {initial.mile:>4} | {initial.fixed:>5} | {initial.mismatch:>8} | "
        f"{initial.mean_span:>9.2f} | {initial.max_span:>8} | initial",
        flush=True,
    )
    for row in stages:
        meta = json.dumps(row.meta, separators=(",", ":"))
        print(
            f"      {row.stage} | {'yes' if row.improved else ' no':>8} | "
            f"{row.stats.mile:>4} | {row.stats.fixed:>5} | {row.stats.mismatch:>8} | "
            f"{row.stats.mean_span:>9.2f} | {row.stats.max_span:>8} | {meta}",
            flush=True,
        )


def maybe_write_report(report: dict[str, Any], json_out: str | None) -> None:
    if not json_out:
        return
    json_path = Path(json_out).expanduser()
    json_path.write_text(json.dumps(report, indent=2))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Compare RIDE order families on one target")
    parser.add_argument("--file", help="Raw file to probe")
    parser.add_argument("--text", help="UTF-8 text to probe")
    parser.add_argument("--byte-limit", type=int, help="Optional raw-byte slice when using --file")
    parser.add_argument("--stages", type=int, default=3, help="Stages to apply per family")
    parser.add_argument(
        "--families",
        help="Comma-separated top-level families to run. Default is all available families.",
    )
    parser.add_argument(
        "--hybrid-schedule",
        default="affine_index,lane_block",
        help="Comma-separated family schedule for the hybrid run",
    )
    parser.add_argument(
        "--schedule-search-families",
        help="Comma-separated base families available to annealed schedule search. Default is all base families.",
    )
    parser.add_argument(
        "--schedule-search-iters",
        type=int,
        default=SCHEDULE_SEARCH_DEFAULT_ITERS,
        help="Optional annealed search iterations for a stage schedule over the base families",
    )
    parser.add_argument(
        "--schedule-search-temp",
        type=float,
        default=SCHEDULE_SEARCH_DEFAULT_TEMP,
        help="Initial temperature for annealed schedule search",
    )
    parser.add_argument(
        "--schedule-search-cooling",
        type=float,
        default=SCHEDULE_SEARCH_DEFAULT_COOLING,
        help="Cooling rate for annealed schedule search",
    )
    parser.add_argument("--progress", action="store_true", help="Print per-stage progress during long runs")
    parser.add_argument("--json-out", help="Optional path to write JSON report")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    raw = load_raw(args)
    if args.progress:
        print("[progress] loaded raw input; starting K-materialisation front end...", flush=True)
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    if args.progress:
        print("[progress] K-materialisation + frequency patch complete.", flush=True)
    initial = residual_stats(source_digits, target_digits)

    print("╔══════════════════════════════════════════════════════════════╗", flush=True)
    print("║  RIDE V24 - ORDER FAMILY HARNESS                            ║", flush=True)
    print("║  compare residual-order burn across deterministic families  ║", flush=True)
    print("╚══════════════════════════════════════════════════════════════╝", flush=True)
    print(f"\nRaw bytes: {len(raw):,}", flush=True)
    print(f"Target digits: {len(target_digits):,}", flush=True)
    print(f"K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}", flush=True)
    print(f"Frequency delta L1: {l1:,}", flush=True)
    print(f"Initial target hash: {state_hash(target_digits)}", flush=True)

    base_families = {
        "fixed_fisher_yates": FisherOrbitFamily(len(target_digits), raw),
        "affine_index": AffineOrbitFamily(len(target_digits), raw),
        "lane_block": LaneBlockOrbitFamily(),
        "cycle_arc": CycleArcOrbitFamily(),
    }

    base_names = list(base_families.keys())
    hybrid_schedule = parse_schedule(args.hybrid_schedule)
    require_known_names(hybrid_schedule, base_names, "hybrid schedule family")

    schedule_search_names = parse_name_list(args.schedule_search_families) or base_names
    require_known_names(schedule_search_names, base_names, "schedule-search family")
    schedule_search_family_map = {name: base_families[name] for name in schedule_search_names}

    all_families: dict[str, Any] = dict(base_families)
    all_families["hybrid_schedule"] = HybridOrbitFamily(hybrid_schedule, base_families)
    all_families["annealed_hybrid"] = AnnealedHybridFamily(hybrid_schedule, base_families, raw)
    all_families["annealed_hybrid_v2"] = AnnealedHybridV2Family(base_families, raw)

    all_names = list(all_families.keys()) + ["annealed_schedule_search"]
    requested_families = parse_name_list(args.families) or all_names
    require_known_names(requested_families, all_names, "family")

    families = {name: all_families[name] for name in requested_families if name in all_families}

    report: dict[str, Any] = {
        "raw_bytes": len(raw),
        "target_digits": len(target_digits),
        "k_params": list(params),
        "frequency_delta_l1": l1,
        "hybrid_schedule": hybrid_schedule,
        "requested_families": requested_families,
        "schedule_search_families": schedule_search_names,
        "initial": asdict(initial),
        "families": {},
    }

    for name, family in families.items():
        stages = run_family(name, family, source_digits, target_digits, args.stages, progress=args.progress)
        print_stage_table(name, initial, stages)
        report["families"][name] = [asdict(stage) for stage in stages]
        maybe_write_report(report, args.json_out)

    if args.schedule_search_iters > 0 and "annealed_schedule_search" in requested_families:
        if args.progress:
            print("[progress] starting annealed stage-schedule search...", flush=True)
        searched = anneal_schedule_search(
            seed_schedule=hybrid_schedule,
            family_map=schedule_search_family_map,
            source=source_digits,
            target=target_digits,
            max_stages=args.stages,
            raw=raw,
            iterations=args.schedule_search_iters,
            initial_temp=args.schedule_search_temp,
            cooling_rate=args.schedule_search_cooling,
            progress=args.progress,
        )
        print_stage_table("annealed_schedule_search", initial, searched["results"])
        report["families"]["annealed_schedule_search"] = [asdict(stage) for stage in searched["results"]]
        report["annealed_schedule_search"] = {
            "meta": searched["meta"],
            "stats": asdict(searched["stats"]),
        }
        maybe_write_report(report, args.json_out)

    if args.json_out:
        json_path = Path(args.json_out).expanduser()
        print(f"\nJSON report written to {json_path}", flush=True)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
