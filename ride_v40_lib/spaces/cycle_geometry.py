# ride_v40_lib/spaces/cycle_geometry.py
# v1.0 — 2026-04-15
#
# Cycle-geometry θ-space: engineer σ(θ) to match v18's few-huge-cycles
# geometry (JPEG: 13 cycles, cantrbry.zip: 16, LRC PDF: 11) where cycle
# membership on long cycles follows a geometric gap distribution with
# p ≈ 0.377 (v27 measurement on LRC PDF).
#
# θ = (n_cycles, size_head, size_decay, p_geo, lane_width, phase_seed).
#
# Constructor partitions [0..n) into n_cycles disjoint subsets:
#   - head cycle gets `size_head` fraction of n,
#   - each subsequent cycle gets `size_decay` × previous,
#   - within each cycle, positions are drawn by walking the index line with
#     geometric-distributed gaps (parameter `p_geo`), modulo n, offset by a
#     per-cycle phase derived from phase_seed.
#   - lane_width controls interleaving: indices get bucketed into lanes of
#     that width before drawing, so cycles sit in different lane strata.
# Each cycle becomes a single long rotation (i_0 -> i_1 -> ... -> i_k -> i_0).
#
# This is NOT tuned to the exact target. It's a structural prior — the SA
# kernel searches θ for the configuration whose cycle GEOMETRY best matches
# π_target's cycle geometry.

from __future__ import annotations

import random
from dataclasses import dataclass

import numpy as np

from ..core import Perm, ThetaSpace


# Observed bounds from v18/v27 on real files: 11-16 cycles, head 37.8%/36.7%
# of total, geometric p between 0.30 and 0.45. Bounds widen these to be safe.
N_CYCLES_MIN, N_CYCLES_MAX = 6, 24
SIZE_HEAD_MIN, SIZE_HEAD_MAX = 0.20, 0.55
SIZE_DECAY_MIN, SIZE_DECAY_MAX = 0.30, 0.95
P_GEO_MIN, P_GEO_MAX = 0.20, 0.55
LANE_WIDTH_MIN, LANE_WIDTH_MAX = 1, 8192


@dataclass(frozen=True)
class CycleGeomTheta:
    n_cycles: int
    size_head: float        # fraction of n for cycle 0
    size_decay: float       # each next cycle = decay × previous size
    p_geo: float            # geometric gap parameter
    lane_width: int
    phase_seed: int         # uint32


class CycleGeometrySpace(ThetaSpace):

    name = "cycle_geometry"

    def sample(self, rng: random.Random) -> CycleGeomTheta:
        return CycleGeomTheta(
            n_cycles=rng.randint(N_CYCLES_MIN, N_CYCLES_MAX),
            size_head=rng.uniform(SIZE_HEAD_MIN, SIZE_HEAD_MAX),
            size_decay=rng.uniform(SIZE_DECAY_MIN, SIZE_DECAY_MAX),
            p_geo=rng.uniform(P_GEO_MIN, P_GEO_MAX),
            lane_width=rng.randint(LANE_WIDTH_MIN, min(LANE_WIDTH_MAX, self.n // 4)),
            phase_seed=rng.randrange(0, 2**32),
        )

    def neighbor(self, theta: CycleGeomTheta, temperature: float,
                 rng: random.Random) -> CycleGeomTheta:
        # Perturb one coordinate; step size scales with temperature.
        t = max(0.05, min(1.0, temperature))
        choice = rng.randrange(6)
        n_cycles = theta.n_cycles
        size_head = theta.size_head
        size_decay = theta.size_decay
        p_geo = theta.p_geo
        lane_width = theta.lane_width
        phase_seed = theta.phase_seed

        if choice == 0:
            step = max(1, int(round(4 * t)))
            delta = rng.randint(-step, step)
            n_cycles = max(N_CYCLES_MIN, min(N_CYCLES_MAX, n_cycles + delta))
        elif choice == 1:
            step = 0.08 * t
            size_head = float(max(SIZE_HEAD_MIN,
                                  min(SIZE_HEAD_MAX, size_head + rng.uniform(-step, step))))
        elif choice == 2:
            step = 0.12 * t
            size_decay = float(max(SIZE_DECAY_MIN,
                                   min(SIZE_DECAY_MAX, size_decay + rng.uniform(-step, step))))
        elif choice == 3:
            step = 0.08 * t
            p_geo = float(max(P_GEO_MIN,
                              min(P_GEO_MAX, p_geo + rng.uniform(-step, step))))
        elif choice == 4:
            factor = 2.0 ** rng.uniform(-2 * t, 2 * t)
            lane_width = max(LANE_WIDTH_MIN,
                             min(LANE_WIDTH_MAX, max(1, int(round(lane_width * factor)))))
        else:
            # Phase seed: hot = resample, cool = bit flip
            if t > 0.5:
                phase_seed = rng.randrange(0, 2**32)
            else:
                phase_seed = phase_seed ^ (1 << rng.randint(0, 31))

        return CycleGeomTheta(
            n_cycles=n_cycles,
            size_head=size_head,
            size_decay=size_decay,
            p_geo=p_geo,
            lane_width=lane_width,
            phase_seed=phase_seed,
        )

    def construct(self, theta: CycleGeomTheta) -> Perm:
        n = self.n
        rng_np = np.random.default_rng(theta.phase_seed)

        # 1. Cycle sizes via geometric decay, renormalised to sum to n.
        raw_sizes = np.empty(theta.n_cycles, dtype=np.float64)
        current = theta.size_head
        for i in range(theta.n_cycles):
            raw_sizes[i] = current
            current *= theta.size_decay
        raw_sizes = raw_sizes / raw_sizes.sum()
        cycle_sizes = np.floor(raw_sizes * n).astype(np.int64)
        # Dump any rounding remainder into the head cycle.
        cycle_sizes[0] += n - int(cycle_sizes.sum())
        # Each cycle needs length >= 2 to be non-trivial; if rounding broke
        # one, collapse it into the head.
        for i in range(1, len(cycle_sizes)):
            if cycle_sizes[i] < 2:
                cycle_sizes[0] += cycle_sizes[i]
                cycle_sizes[i] = 0
        cycle_sizes = cycle_sizes[cycle_sizes >= 2]
        # Degenerate safety: at least one cycle covers everything.
        if len(cycle_sizes) == 0:
            cycle_sizes = np.array([n], dtype=np.int64)

        # 2. For each cycle, sample geometric-gap positions within the
        #    available index pool. We walk a shuffled index line in lanes.
        # Build a lane ordering: stable, deterministic from phase_seed.
        lanes: list[np.ndarray] = []
        lw = max(1, min(theta.lane_width, n))
        for start in range(0, n, lw):
            end = min(start + lw, n)
            lanes.append(np.arange(start, end, dtype=np.int64))
        # Shuffle lane order (not contents) so cycles interleave structurally.
        lane_order = np.arange(len(lanes))
        rng_np.shuffle(lane_order)
        pool = np.concatenate([lanes[i] for i in lane_order])
        # `pool` is a permutation of [0..n) whose structure is lane-striped.

        # 3. Carve `pool` into cycles, drawing each cycle by skipping
        #    geometric(p_geo) items from the remaining pool.
        sigma = np.arange(n, dtype=np.int64)  # identity baseline
        # `available` tracks which pool indices are still unassigned.
        available_mask = np.ones(n, dtype=bool)
        pool_idx = np.arange(n, dtype=np.int64)  # positions within pool

        for cyc_len in cycle_sizes:
            cyc_len = int(cyc_len)
            # Draw `cyc_len` positions from the pool by geometric skipping.
            remaining = pool_idx[available_mask]
            if len(remaining) < cyc_len:
                # Not enough left for a full cycle — just take what's there.
                cyc_len = len(remaining)
                if cyc_len < 2:
                    break

            # Draw `cyc_len` DISTINCT positions from `remaining` by
            # geometric skipping. Wrap-around is allowed but we advance the
            # cursor one extra step if we land on an already-taken slot.
            taken_in_cycle = np.zeros(len(remaining), dtype=bool)
            chosen_positions: list[int] = []
            cursor = 0
            while len(chosen_positions) < cyc_len:
                # Advance past already-taken slots (at most len(remaining) steps)
                guard = 0
                while taken_in_cycle[cursor] and guard < len(remaining):
                    cursor = (cursor + 1) % len(remaining)
                    guard += 1
                if guard >= len(remaining):
                    break  # no free slots left (shouldn't happen given masks)
                taken_in_cycle[cursor] = True
                chosen_positions.append(int(remaining[cursor]))
                gap = 1 + int(rng_np.geometric(max(0.01, min(0.99, theta.p_geo))))
                cursor = (cursor + gap) % len(remaining)

            if len(chosen_positions) < 2:
                continue
            chosen = np.array(chosen_positions, dtype=np.int64)
            # Mark them as consumed.
            available_mask[chosen] = False
            # Build the single-cycle rotation: chosen[k] -> chosen[(k+1) % L]
            # i.e. for position chosen[k], sigma[chosen[k]] = chosen[(k+1) % L]
            # sigma encodes target[i] = source[sigma[i]]; rotating the cycle
            # means source index chosen[k+1] lands at target position chosen[k].
            next_positions = np.roll(chosen, -1)
            sigma[chosen] = next_positions

        return sigma

    def to_json(self, theta: CycleGeomTheta) -> dict:
        return {
            "n_cycles": int(theta.n_cycles),
            "size_head": float(theta.size_head),
            "size_decay": float(theta.size_decay),
            "p_geo": float(theta.p_geo),
            "lane_width": int(theta.lane_width),
            "phase_seed": int(theta.phase_seed),
        }
