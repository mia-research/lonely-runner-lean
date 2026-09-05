#!/usr/bin/env python3
"""
RIDE V35 - FY inversion: recover seed from permutation for exact (seed, k=1) recipe.
# v1.0 — 2026-04-13 — sender inverts FY to find seed; receiver applies FY(seed)^1

THE MODEL
---------
Sender has: source (K-source) AND target (the file)
Sender does:
  1. Compute P = permutation s.t. P(source) = target
  2. Invert FY: recover seed s such that FY(seed) = P
  3. Send (seed, k=1)

Receiver has: source + (seed, k=1)
Receiver does: apply FY(seed)^1 to source → target; verify hash

Recipe size: 64 bits (seed) + 1 bit (k=1) = 65 bits = 9 bytes
File size: 952 bytes → ratio 117:1 IF inversion works

THE RNG
-------
Use a simple 64-bit LCG with NO rejection sampling:
  state = state * A + C  (mod 2^64)
  next_uniform(bound) = (state * bound) >> 64   [Lemire's method, exactly 1 state advance]

This gives a bijective mapping from LCG state to the j values, making
seed recovery a straightforward back-substitution from the known swap sequence.

FY INVERSION ALGORITHM
-----------------------
Forward FY:
  state = init(seed)  [warm-up]
  arr = [0..n-1]
  for i = n-1 downto 1:
    j = lcg_uniform(i+1)  # in [0, i]
    swap(arr[i], arr[j])

Given P (the final permutation), recover the swap sequence (j values):
  Work backwards from i = n-1 downto 1
  At each step i:
    After all swaps through step i, arr[i] = P[i]
    The swap at step i was: arr[i] <-> arr[j_i]
    Undoing: swap(arr[i], arr[j_i]) restores pre-swap state
    j_i is determined by: arr[j_i] was the value that ended up at arr[i]

  Full inversion: simulate forward, tracking which j values produce P.
  Since FY is a bijection on [0..n-1] → permutations, each P has exactly
  one j sequence. The j sequence uniquely determines the RNG output sequence.

From the j sequence (j_{n-1}, j_{n-2}, ..., j_1):
  j_i = lcg_uniform(i+1) = (state_i * (i+1)) >> 64
  We know j_i and (i+1), so we can solve for state_i:
    state_i = j_i * ceil(2^64 / (i+1))  [approximately — need exact Lemire inversion]

Then from state_i recover state_{i-1}: state_i = state_{i-1} * A + C
  → state_{i-1} = (state_i - C) * A_inv  (mod 2^64)

Working backwards through the j sequence recovers the initial state,
which gives the seed.

LEMIRE INVERSION
----------------
Lemire's method: j = (x * bound) >> 64 where x is the 64-bit LCG output.
Given j and bound, x could be any of ceil(2^64/bound) values.
We need to find which x the LCG actually produced.
Strategy: try x = j * ceil(2^64/bound), j * ceil(2^64/bound) + 1, ...
until LCG produces a consistent state sequence.

SIMPLIFIED APPROACH FOR THIS EXPERIMENT
-----------------------------------------
Use Knuth's simpler method: j = state % bound (no rejection, no Lemire).
This is slightly biased for large bounds but that's fine for our purpose.
Inversion: given j = state % bound, state ≡ j (mod bound).
State is 64-bit so state = j + k*bound for k in [0, 2^64/bound).
The LCG constraint narrows it to one value.
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v13_canterbury_recipe_bench import build_perm_target_to_source

# ---------------------------------------------------------------------------
# Simple invertible LCG  (Knuth MMIX parameters)
# ---------------------------------------------------------------------------

LCG_A = 6364136223846793005   # multiplier
LCG_C = 1442695040888963407   # increment
MOD   = 1 << 64

LCG_A_INV = pow(LCG_A, -1, MOD)  # modular inverse for backwards stepping


def lcg_next(state: int) -> int:
    return (state * LCG_A + LCG_C) & 0xFFFFFFFFFFFFFFFF


def lcg_prev(state: int) -> int:
    """Step LCG backwards one step."""
    return (state - LCG_C) * LCG_A_INV & 0xFFFFFFFFFFFFFFFF


def lcg_uniform(state: int, bound: int) -> tuple[int, int]:
    """
    Return (j, next_state) where j = state % bound.
    Simple modulo — no rejection, slightly biased, but fully invertible.
    """
    new_state = lcg_next(state)
    j = new_state % bound
    return j, new_state


def fy_with_lcg(n: int, seed: int) -> list[int]:
    """
    Fisher-Yates shuffle of [0..n-1] using simple LCG.
    Returns permutation sigma such that sigma[i] = where element i ends up.

    FY: arr[i] gets the element from position j, arr[j] gets what was at arr[i].
    We track the resulting permutation (not the array of values).
    """
    arr = list(range(n))
    state = seed & 0xFFFFFFFFFFFFFFFF
    # Warm up
    for _ in range(4):
        state = lcg_next(state)

    for i in range(n - 1, 0, -1):
        j, state = lcg_uniform(state, i + 1)
        arr[i], arr[j] = arr[j], arr[i]

    return arr


def apply_perm(arr: list[int], sigma: list[int]) -> list[int]:
    """Apply permutation: result[sigma[i]] = arr[i]."""
    n = len(arr)
    result = [0] * n
    for i in range(n):
        result[sigma[i]] = arr[i]
    return result


# ---------------------------------------------------------------------------
# FY inversion: given permutation P, recover the j sequence
# ---------------------------------------------------------------------------

def fy_extract_j_sequence(perm: list[int]) -> list[int]:
    """
    Given the output permutation of FY, recover the j values used.

    Forward FY modifies arr in-place:
      arr = [0..n-1]
      for i = n-1 downto 1:
        j_i = rng(i+1)
        swap(arr[i], arr[j_i])

    After all swaps, arr = perm.

    To recover j sequence: simulate forward, but at each step we know
    the final arr[i] value, and we can determine j_i.

    Key insight: at step i, the swap fixes arr[i] permanently (no later
    swap touches position i, since later steps only swap at positions < i).
    Therefore arr[i] after all swaps = the value placed at position i by
    swap at step i = whatever was at position j_i just before step i.

    Algorithm:
    - Maintain a 'current arr' starting from [0..n-1]
    - For i = n-1 downto 1:
        - We know the final value at position i = perm[i]
        - Find which position j currently holds perm[i]
        - That's j_i
        - Perform swap(arr[i], arr[j_i])
    """
    n = len(perm)
    arr = list(range(n))
    pos_of = list(range(n))  # pos_of[v] = current position of value v

    js = []
    for i in range(n - 1, 0, -1):
        target_val = perm[i]
        j = pos_of[target_val]
        js.append(j)

        # Perform swap: arr[i] <-> arr[j]
        val_at_i = arr[i]
        arr[i], arr[j] = arr[j], arr[i]
        pos_of[val_at_i] = j
        pos_of[target_val] = i

    return js  # js[0] = j_{n-1}, js[1] = j_{n-2}, ..., js[-1] = j_1


def verify_j_sequence(n: int, js: list[int]) -> list[int]:
    """Replay FY with known j sequence, return resulting permutation."""
    arr = list(range(n))
    for i, j in zip(range(n - 1, 0, -1), js):
        arr[i], arr[j] = arr[j], arr[i]
    return arr


# ---------------------------------------------------------------------------
# LCG seed recovery from j sequence
# ---------------------------------------------------------------------------

def recover_seed_from_js(js: list[int], n: int) -> int | None:
    """
    Given j sequence (j_{n-1}, j_{n-2}, ..., j_1) where j_i = lcg_next(state) % (i+1),
    recover the LCG seed.

    After warm-up (4 steps), the LCG generates states s_{n-1}, s_{n-2}, ..., s_1:
      j_i = s_i % (i + 1)   where i goes from n-1 downto 1
      s_i = lcg_next(s_{i+1})  (s_{n-1} is first state after warm-up)

    From j_{n-1}: s_{n-1} % n = j_{n-1}
      s_{n-1} = j_{n-1} + k * n for k in [0, 2^64 // n)
      That's 2^64 / n ≈ 2^64 / 2293 ≈ 8 trillion candidates. Too many.

    Better: use TWO consecutive j values to constrain.
      s_{n-1} % n     = j_{n-1}
      lcg_next(s_{n-1}) % (n-1) = j_{n-2}

    This gives us:
      s_{n-1} ≡ j_{n-1} (mod n)
      (s_{n-1} * A + C) % (n-1) = j_{n-2}

    Substituting s_{n-1} = j_{n-1} + k*n:
      ((j_{n-1} + k*n) * A + C) % (n-1) = j_{n-2}
      (j_{n-1}*A + C + k*n*A) % (n-1) = j_{n-2}
      k * (n*A % (n-1)) ≡ (j_{n-2} - j_{n-1}*A - C) (mod (n-1))

    This is a linear congruence in k — usually has O(gcd(n*A, n-1)) solutions.
    Use multiple j values to narrow to a unique solution.

    Implementation: use the first few j values to reconstruct s_{n-1},
    then step LCG backwards to recover the seed (pre-warmup state).
    """
    # Use consecutive j values to find s_{n-1}
    # j[0] = j_{n-1}, j[1] = j_{n-2}, ...
    j0, j1 = js[0], js[1]
    bound0, bound1 = n, n - 1

    # s0 = s_{n-1}: s0 % bound0 = j0
    # s1 = lcg_next(s0): s1 % bound1 = j1
    # s1 = s0 * A + C (mod 2^64)
    # So (s0 * A + C) % bound1 = j1
    # s0 = j0 + k * bound0 for integer k >= 0

    # Search for k such that (j0 + k*bound0) * A + C ≡ j1 (mod bound1)
    # This is: k * (bound0 * A % bound1) ≡ (j1 - j0*A - C) % bound1 (mod bound1)

    rhs = (j1 - j0 * LCG_A - LCG_C) % bound1
    coeff = (bound0 * LCG_A) % bound1

    g = math.gcd(coeff, bound1)
    if rhs % g != 0:
        return None  # No solution

    # Solutions: k ≡ (rhs/g) * inv(coeff/g, bound1/g)  (mod bound1/g)
    m = bound1 // g
    try:
        k0 = (rhs // g) * pow(coeff // g, -1, m) % m
    except ValueError:
        return None

    # k candidates: k0, k0 + m, k0 + 2m, ...
    # Verify against more j values
    max_k = (MOD // bound0) + 1

    for mult in range(max_k // m + 1):
        k = k0 + mult * m
        if k * bound0 + j0 >= MOD:
            break
        s0_candidate = (j0 + k * bound0) & 0xFFFFFFFFFFFFFFFF

        # Verify against remaining j values
        state = s0_candidate
        valid = True
        for idx, (ji, bi) in enumerate(zip(js, range(n, 0, -1))):
            if state % bi != ji:
                valid = False
                break
            state = lcg_next(state)

        if valid:
            # s0_candidate is s_{n-1} — step backwards through LCG + warmup
            state = s0_candidate
            # Step back n-1 times (through the FY loop) + 4 warmup steps
            for _ in range(n - 1 + 4):
                state = lcg_prev(state)
            return state

    return None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(raw: bytes) -> dict:
    t0 = time.perf_counter()
    source_list, target_list, params, l1 = materialise_source_and_target(raw)
    n = len(target_list)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")

    # Step 1: Compute exact permutation P s.t. P(source) = target
    P = list(build_perm_target_to_source(bytearray(target_list), bytearray(source_list)))

    # Verify P
    reconstructed = [source_list[P[i]] for i in range(n)]
    assert reconstructed == target_list, "P verification failed"
    print(f"  Permutation P computed and verified.")

    # Step 2: Extract j sequence from P
    t2 = time.perf_counter()
    js = fy_extract_j_sequence(P)
    # Verify j sequence reproduces P
    p_check = verify_j_sequence(n, js)
    assert p_check == P, "j sequence verification failed"
    print(f"  j sequence extracted and verified ({len(js)} values). t={time.perf_counter()-t2:.3f}s")

    # Step 3: Recover LCG seed from j sequence
    t3 = time.perf_counter()
    seed = recover_seed_from_js(js, n)
    recover_time = time.perf_counter() - t3

    if seed is None:
        print(f"  Seed recovery FAILED (t={recover_time:.3f}s)")
        print(f"  (LCG modulo inversion did not converge — need more j values in constraint)")
        return {"success": False}

    print(f"  Seed recovered: {seed:#018x}  (t={recover_time:.3f}s)")

    # Step 4: Verify — FY(seed) should produce P
    t4 = time.perf_counter()
    sigma = fy_with_lcg(n, seed)
    verify_time = time.perf_counter() - t4

    sigma_matches_P = sigma == P
    print(f"  FY(seed) == P: {sigma_matches_P}  (t={verify_time:.3f}s)")

    if sigma_matches_P:
        # Apply to source, verify == target
        result = apply_perm(source_list, sigma)
        exact = result == target_list
        verify_hash = hashlib.sha256(bytes(result)).hexdigest()[:16]
        target_hash = hashlib.sha256(bytes(target_list)).hexdigest()[:16]
        print(f"  FY(seed)^1(source) == target: {exact}")
        print(f"  Result hash:  {verify_hash}")
        print(f"  Target hash:  {target_hash}")

        # Recipe
        seed_bits = 64
        k_bits = 1  # k=1
        overhead_bits = 193
        total_bits = overhead_bits + seed_bits + k_bits
        file_bits = len(raw) * 8
        ratio = file_bits / total_bits

        print(f"\n  {'='*60}")
        print(f"  RECIPE: (seed={seed:#018x}, k=1)")
        print(f"  Recipe bits:  {seed_bits + k_bits} ({seed_bits} seed + {k_bits} k)")
        print(f"  Total w/ K:   {total_bits} bits = {total_bits//8} bytes")
        print(f"  File:         {len(raw):,} bytes")
        print(f"  Ratio:        {ratio:.1f}:1  {'(EXACT)' if exact else '(MISMATCH)'}")

        return {
            "success": exact,
            "seed": seed,
            "k": 1,
            "ratio": round(ratio, 1),
            "total_bits": total_bits,
        }
    else:
        print(f"  Seed recovery produced wrong sigma — inversion has a bug.")
        # Debug: show first few differences
        diffs = [(i, sigma[i], P[i]) for i in range(n) if sigma[i] != P[i]][:5]
        print(f"  First diffs (pos, got, want): {diffs}")
        return {"success": False}


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V35 — FY INVERSION: EXACT SEED RECOVERY              ║")
    print("║  Sender finds seed s.t. FY(seed)^1(source) = target        ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        run(path.read_bytes())

    return 0


if __name__ == "__main__":
    sys.exit(main())
