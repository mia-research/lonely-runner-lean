# ride_v40_lib/spaces/cycle_arc.py
# v1.0 — 2026-04-15
#
# Cycle-arc θ-space. θ = a small collection of arcs; each arc is
# (anchor, length, stride, direction). σ(θ) is built by placing these
# arcs into [0..n) and composing them as rotations.
#
# This fights v23's known wall head-on (state doc §10: cycle-arc encoding
# costs 6.5x the file on the PDF). Included per the "throw ideas at the
# wall" directive — if v40 can't beat v30 here, that's also data.

from __future__ import annotations

import random
from dataclasses import dataclass
from typing import Tuple

import numpy as np

from ..core import Perm, ThetaSpace


N_ARCS_MIN, N_ARCS_MAX = 4, 24


@dataclass(frozen=True)
class Arc:
    anchor: int          # start index in [0..n)
    length: int          # number of positions in arc, >= 2
    stride: int          # gap between consecutive arc positions
    direction: int       # +1 or -1 (rotation direction)


@dataclass(frozen=True)
class CycleArcTheta:
    arcs: Tuple[Arc, ...]


class CycleArcSpace(ThetaSpace):

    name = "cycle_arc"

    def sample(self, rng: random.Random) -> CycleArcTheta:
        n_arcs = rng.randint(N_ARCS_MIN, N_ARCS_MAX)
        arcs = tuple(self._sample_arc(rng) for _ in range(n_arcs))
        return CycleArcTheta(arcs=arcs)

    def _sample_arc(self, rng: random.Random) -> Arc:
        n = self.n
        return Arc(
            anchor=rng.randrange(0, n),
            length=rng.randint(2, max(3, min(n // 4, 2048))),
            stride=rng.randint(1, max(2, min(n // 16, 1024))),
            direction=rng.choice([-1, 1]),
        )

    def neighbor(self, theta: CycleArcTheta, temperature: float,
                 rng: random.Random) -> CycleArcTheta:
        t = max(0.05, min(1.0, temperature))
        arcs = list(theta.arcs)

        op = rng.choice(["perturb", "replace", "add", "drop"])
        if op == "add" and len(arcs) < N_ARCS_MAX:
            arcs.append(self._sample_arc(rng))
        elif op == "drop" and len(arcs) > N_ARCS_MIN:
            del arcs[rng.randrange(len(arcs))]
        elif op == "replace":
            arcs[rng.randrange(len(arcs))] = self._sample_arc(rng)
        else:  # perturb
            i = rng.randrange(len(arcs))
            a = arcs[i]
            step = max(1, int(round(self.n * 0.05 * t)))
            arcs[i] = Arc(
                anchor=(a.anchor + rng.randint(-step, step)) % self.n,
                length=max(2, a.length + rng.randint(-max(1, int(a.length * 0.2 * t)),
                                                     max(1, int(a.length * 0.2 * t)))),
                stride=max(1, a.stride + rng.randint(-max(1, int(a.stride * 0.2 * t)),
                                                     max(1, int(a.stride * 0.2 * t)))),
                direction=a.direction if rng.random() > 0.1 * t else -a.direction,
            )
        return CycleArcTheta(arcs=tuple(arcs))

    def construct(self, theta: CycleArcTheta) -> Perm:
        n = self.n
        sigma = np.arange(n, dtype=np.int64)
        for arc in theta.arcs:
            # Build the arc's position sequence.
            positions = [(arc.anchor + k * arc.stride) % n for k in range(arc.length)]
            # Deduplicate in case stride * length wraps onto itself.
            seen = set()
            unique_positions = []
            for p in positions:
                if p not in seen:
                    seen.add(p)
                    unique_positions.append(p)
            if len(unique_positions) < 2:
                continue
            seq = np.array(unique_positions, dtype=np.int64)
            if arc.direction < 0:
                seq = seq[::-1]
            # Apply as a cycle: position seq[k] -> seq[(k+1) % L]
            next_seq = np.roll(seq, -1)
            # Compose onto current sigma: the arc operates on CURRENT sigma,
            # meaning sigma[seq[k]] := sigma_old[next_seq[k]]. Use a copy
            # to avoid in-place aliasing surprises.
            old = sigma.copy()
            sigma[seq] = old[next_seq]
        return sigma

    def to_json(self, theta: CycleArcTheta) -> dict:
        return {
            "arcs": [
                {"anchor": int(a.anchor), "length": int(a.length),
                 "stride": int(a.stride), "direction": int(a.direction)}
                for a in theta.arcs
            ]
        }
