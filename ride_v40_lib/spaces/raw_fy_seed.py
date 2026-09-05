# ride_v40_lib/spaces/raw_fy_seed.py
# v1.0 — 2026-04-15
#
# Matched-budget baseline: the v30 regime, re-expressed under the v40
# harness so it gets the same SA kernel, same budget, same logging as the
# designed-seed spaces. This is how we know whether any designed-seed
# space actually beats random seeds, or whether improvements are just
# harness artefacts.
#
# θ = (seed: uint32). construct(θ) = Fisher–Yates shuffle with that seed.
# neighbor(θ, T) = bit-flip perturbation whose magnitude scales with T.

from __future__ import annotations

import random
from dataclasses import dataclass

import numpy as np

from ..core import Perm, ThetaSpace


@dataclass(frozen=True)
class FYTheta:
    seed: int  # uint32


class RawFYSeedSpace(ThetaSpace):
    """v30 baseline: a single 32-bit Fisher–Yates seed."""

    name = "raw_fy_seed"

    def sample(self, rng: random.Random) -> FYTheta:
        return FYTheta(seed=rng.randrange(0, 2**32))

    def neighbor(self, theta: FYTheta, temperature: float, rng: random.Random) -> FYTheta:
        # Hot: resample. Warm: flip multiple bits. Cold: single-bit flip.
        if temperature > 0.66:
            return FYTheta(seed=rng.randrange(0, 2**32))
        if temperature > 0.33:
            mask = 0
            for _ in range(rng.randint(2, 5)):
                mask |= 1 << rng.randint(0, 31)
            return FYTheta(seed=theta.seed ^ mask)
        return FYTheta(seed=theta.seed ^ (1 << rng.randint(0, 31)))

    def construct(self, theta: FYTheta) -> Perm:
        r = np.random.default_rng(theta.seed)
        return r.permutation(self.n).astype(np.int64)

    def to_json(self, theta: FYTheta) -> dict:
        return {"seed": int(theta.seed)}
