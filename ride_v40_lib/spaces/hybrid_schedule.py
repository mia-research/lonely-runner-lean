# ride_v40_lib/spaces/hybrid_schedule.py
# v1.0 — 2026-04-15
#
# Hybrid-schedule θ-space: generalises v24's annealed_hybrid. θ is an
# ordered schedule of (family, params) tuples. σ(θ) = composition of each
# family's generated permutation.
#
# Families implemented:
#   - affine: σ(i) = (a*i + b) mod n,          params = (a, b)
#   - lane:   rotate each lane of width w by k, params = (w, k)
#   - rev:    reverse the whole array,          params = ()
#   - fy:     Fisher–Yates with seed s,         params = (s,)
#
# Schedule length in [1, 8]. SA mutates: add a stage, drop a stage, swap
# adjacent stages, resample a stage's params, change a stage's family.
# Bounded length stops the search from silently encoding per-byte data
# in the parameter stream.

from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Tuple

import numpy as np

from ..core import Perm, ThetaSpace, compose


SCHEDULE_MIN, SCHEDULE_MAX = 1, 8
FAMILIES = ("affine", "lane", "rev", "fy")
FAMILY_WEIGHTS = (0.35, 0.30, 0.05, 0.30)  # sampling prior


def _sample_family_params(family: str, n: int, rng: random.Random) -> tuple:
    if family == "affine":
        # a coprime with n; pick odd a for safety (not exhaustive but cheap)
        while True:
            a = rng.randrange(1, n)
            if _gcd(a, n) == 1:
                break
        b = rng.randrange(0, n)
        return (a, b)
    if family == "lane":
        w = 1 << rng.randint(4, min(13, max(4, (n.bit_length() - 1))))  # 16..8192
        w = min(w, max(1, n // 2))
        k = rng.randrange(1, max(2, w))
        return (w, k)
    if family == "rev":
        return ()
    if family == "fy":
        return (rng.randrange(0, 2**32),)
    raise ValueError(family)


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


@dataclass(frozen=True)
class Stage:
    family: str
    params: tuple


@dataclass(frozen=True)
class ScheduleTheta:
    stages: Tuple[Stage, ...]


class HybridScheduleSpace(ThetaSpace):

    name = "hybrid_schedule"

    def sample(self, rng: random.Random) -> ScheduleTheta:
        length = rng.randint(SCHEDULE_MIN, SCHEDULE_MAX)
        stages = tuple(self._sample_stage(rng) for _ in range(length))
        return ScheduleTheta(stages=stages)

    def _sample_stage(self, rng: random.Random) -> Stage:
        # weighted choice
        r = rng.random()
        acc = 0.0
        fam = FAMILIES[-1]
        for f, w in zip(FAMILIES, FAMILY_WEIGHTS):
            acc += w
            if r < acc:
                fam = f
                break
        return Stage(family=fam, params=_sample_family_params(fam, self.n, rng))

    def neighbor(self, theta: ScheduleTheta, temperature: float,
                 rng: random.Random) -> ScheduleTheta:
        stages = list(theta.stages)
        t = max(0.05, min(1.0, temperature))
        # Moves: resample one stage's params (cool), change one stage's
        # family (warm), add/drop stage (warm), swap adjacent (cool).
        if t > 0.5 and rng.random() < 0.5:
            op = rng.choice(["add", "drop", "family"]
                            if len(stages) > SCHEDULE_MIN and len(stages) < SCHEDULE_MAX
                            else (["add", "family"] if len(stages) < SCHEDULE_MAX
                                  else ["drop", "family"]))
        else:
            op = rng.choice(["params", "swap"]) if len(stages) >= 2 else "params"

        if op == "add" and len(stages) < SCHEDULE_MAX:
            pos = rng.randint(0, len(stages))
            stages.insert(pos, self._sample_stage(rng))
        elif op == "drop" and len(stages) > SCHEDULE_MIN:
            pos = rng.randrange(len(stages))
            del stages[pos]
        elif op == "family":
            pos = rng.randrange(len(stages))
            new_fam = rng.choice([f for f in FAMILIES if f != stages[pos].family])
            stages[pos] = Stage(family=new_fam,
                                params=_sample_family_params(new_fam, self.n, rng))
        elif op == "swap" and len(stages) >= 2:
            i = rng.randrange(len(stages) - 1)
            stages[i], stages[i + 1] = stages[i + 1], stages[i]
        else:  # params
            pos = rng.randrange(len(stages))
            stages[pos] = Stage(family=stages[pos].family,
                                params=_sample_family_params(stages[pos].family, self.n, rng))

        return ScheduleTheta(stages=tuple(stages))

    def construct(self, theta: ScheduleTheta) -> Perm:
        sigma = np.arange(self.n, dtype=np.int64)
        for stage in theta.stages:
            sigma = compose(self._build_stage(stage), sigma)
        return sigma

    def _build_stage(self, stage: Stage) -> Perm:
        n = self.n
        if stage.family == "affine":
            a, b = stage.params
            i = np.arange(n, dtype=np.int64)
            return (a * i + b) % n
        if stage.family == "lane":
            w, k = stage.params
            out = np.arange(n, dtype=np.int64)
            for start in range(0, n, w):
                end = min(start + w, n)
                L = end - start
                if L <= 1:
                    continue
                shift = k % L
                out[start:end] = np.concatenate([out[start + shift:end],
                                                 out[start:start + shift]])
            return out
        if stage.family == "rev":
            return np.arange(n - 1, -1, -1, dtype=np.int64)
        if stage.family == "fy":
            (seed,) = stage.params
            r = np.random.default_rng(seed)
            return r.permutation(n).astype(np.int64)
        raise ValueError(stage.family)

    def to_json(self, theta: ScheduleTheta) -> dict:
        return {
            "stages": [
                {"family": s.family, "params": [int(p) if isinstance(p, (int, np.integer))
                                                else p for p in s.params]}
                for s in theta.stages
            ]
        }
