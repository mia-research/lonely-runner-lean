# ride_v40_lib/core.py — core types and θ-space interface
# v1.0 — 2026-04-15
"""
Core types and the abstract ThetaSpace interface.

A ThetaSpace is a configuration space whose points θ deterministically
construct permutations σ(θ) of length n. The SA kernel searches over θ;
every ThetaSpace must provide sample / neighbor / construct so the kernel
is space-agnostic.

Semantics of permutations here match ride_v13_canterbury_recipe_bench.py:
    target[i] = source[perm[i]]
i.e. perm is an index map from target positions to source positions, and
apply_perm(source, perm) produces target.
"""

from __future__ import annotations

import hashlib
import random
from abc import ABC, abstractmethod
from array import array
from dataclasses import dataclass
from typing import Any

import numpy as np


Perm = np.ndarray  # dtype=int64 or int32, shape (n,), values in [0, n)


# --------------------------------------------------------------------------
# Metrics (all O(n) or better)
# --------------------------------------------------------------------------

def mismatch_count(current: Perm, target_perm: Perm) -> int:
    """Number of positions where current != target_perm. O(n)."""
    return int(np.sum(current != target_perm))


def mismatch_ratio(current: Perm, target_perm: Perm) -> float:
    """Mismatch as a fraction in [0, 1]. O(n)."""
    return float(np.sum(current != target_perm)) / len(target_perm)


def mile(current: Perm, target_perm: Perm) -> tuple[int, int]:
    """
    Minimum transpositions needed to transform current into target_perm,
    via cycle decomposition of the residual. Returns (mile, n_cycles).
    O(n).
    """
    n = len(current)
    # residual π such that π(current) = target_perm
    # i.e. for each position i, we need to map current[i] -> target_perm[i]
    # residual permutation on value-space:
    # build a map current_value -> position_in_current, then walk
    # Simpler: residual on index space where we ask "where does current[i]
    # need to go". Here we use the standard cycle-mile of the permutation
    # π defined by π[i] = position in current whose value is target_perm[i].
    # But with potentially duplicated values this is ambiguous, so we use
    # the direct index-level mile: mile = n - (# fixed points if treated as
    # permutation of positions). We treat current and target_perm as both
    # permutations of [0..n), so the relevant residual is:
    pos_of = np.empty(n, dtype=np.int64)
    pos_of[current] = np.arange(n, dtype=np.int64)
    # residual[i] = where target_perm[i] currently sits in current
    residual = pos_of[target_perm]
    # cycle decomposition of residual
    visited = np.zeros(n, dtype=bool)
    cycles = 0
    for i in range(n):
        if visited[i]:
            continue
        cycles += 1
        j = i
        while not visited[j]:
            visited[j] = True
            j = int(residual[j])
    return n - cycles, cycles


def file_hash(data: bytes) -> str:
    """SHA-256 of raw bytes. Used as the stopping oracle."""
    return hashlib.sha256(data).hexdigest()


def apply_perm_np(source: np.ndarray, perm: Perm) -> np.ndarray:
    """Vectorized: out[i] = source[perm[i]]."""
    return source[perm]


# --------------------------------------------------------------------------
# Abstract θ-space interface
# --------------------------------------------------------------------------

@dataclass
class ThetaSample:
    """A point in a θ-space, paired with its derived σ."""
    theta: Any
    sigma: Perm


class ThetaSpace(ABC):
    """
    Abstract base for a configuration space searchable by the SA kernel.

    Implementations must be:
    - deterministic: construct(θ) always yields the same σ,
    - seeded: sample(rng) and neighbor(θ, T, rng) take explicit rng,
    - finite-dim: θ is JSON-serialisable (for logging and restart).
    """

    name: str  # short identifier, appears in logs and result tables

    def __init__(self, n: int):
        self.n = n

    @abstractmethod
    def sample(self, rng: random.Random) -> Any:
        """Draw an initial θ."""
        ...

    @abstractmethod
    def neighbor(self, theta: Any, temperature: float, rng: random.Random) -> Any:
        """
        Produce θ' in the neighbourhood of θ. Higher temperature should
        yield larger perturbations; the kernel passes temperature / T0 in
        [0, 1]-ish scale so implementations can branch on it.
        """
        ...

    @abstractmethod
    def construct(self, theta: Any) -> Perm:
        """Deterministically build σ(θ) as a numpy array of length self.n."""
        ...

    @abstractmethod
    def to_json(self, theta: Any) -> dict:
        """JSON-serialisable dict for logging."""
        ...

    # Optional hook — default implementation is no-op; useful if the
    # constructor allocates reusable buffers.
    def close(self) -> None:
        pass


# --------------------------------------------------------------------------
# Helpers for θ-space implementors
# --------------------------------------------------------------------------

def validate_permutation(sigma: Perm, n: int) -> None:
    """Raise ValueError if sigma is not a valid permutation of [0..n)."""
    if sigma.shape != (n,):
        raise ValueError(f"sigma shape {sigma.shape} != ({n},)")
    if sigma.dtype.kind != "i" and sigma.dtype.kind != "u":
        raise ValueError(f"sigma dtype {sigma.dtype} not integer")
    if int(sigma.min()) < 0 or int(sigma.max()) >= n:
        raise ValueError(f"sigma values out of range [0, {n})")
    # O(n) uniqueness check
    seen = np.zeros(n, dtype=bool)
    seen[sigma] = True
    if not seen.all():
        raise ValueError("sigma is not a permutation (has duplicates)")


def identity_perm(n: int) -> Perm:
    return np.arange(n, dtype=np.int64)


def compose(outer: Perm, inner: Perm) -> Perm:
    """Return (outer ∘ inner)[i] = outer[inner[i]]."""
    return outer[inner]


def invert(sigma: Perm) -> Perm:
    n = len(sigma)
    inv = np.empty(n, dtype=sigma.dtype)
    inv[sigma] = np.arange(n, dtype=sigma.dtype)
    return inv


def perm_to_array(sigma: Perm) -> array:
    """Convert numpy perm to stdlib array('I') for v13 helpers."""
    out = array("I", [0]) * len(sigma)
    for i, v in enumerate(sigma):
        out[i] = int(v)
    return out
