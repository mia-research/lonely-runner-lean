#!/usr/bin/env python3
"""
Reset thread B (easy): was the key generator a standard MT19937 (Python `random`)
seeded with a CURVE PARAMETER (or a common constant), rather than a name/date at
second resolution (the only seeds prior sweeps tried)?

For each (seed, recipe) we regenerate keys for the contiguous run 1..70 and count
EXACT key matches + the longest exact prefix. Even a 4-5 key exact prefix is a
strong hit (chance ~ 2^-(sum of low-bit widths)). Matched null: the same recipe
seeded by 200 random 64-bit seeds -> the exact-match distribution under "no link".
Positive control: a planted seed must be recovered 70/70.

Exact integers only; the PRNG bits are the object under test, no float anywhere.
"""
import hashlib, random
from reset_common import load_solved, contiguous_run
from ecc_secp256k1 import N_ORDER as n, P as p, Gx, Gy

solved = load_solved()
RUN = contiguous_run(solved, 1)                     # 1..70
ACTUAL = {N: solved[N]["d"] for N in RUN}

def keys_from_random(seed, recipe, order):
    """Generate {N: key} for N in `order` from a fresh Random(seed) via `recipe`."""
    r = random.Random(seed)
    out = {}
    for N in order:
        w = N - 1
        if recipe == "getrandbits_seq":
            low = r.getrandbits(w) if w > 0 else 0
        elif recipe == "getrandbits256_trunc":
            g = r.getrandbits(256); low = g & ((1 << w) - 1) if w > 0 else 0
        elif recipe == "randrange_low":
            low = r.randrange(1 << w) if w > 0 else 0
        elif recipe == "randrange_full":
            out[N] = r.randrange(1 << (N - 1), 1 << N); continue
        else:
            raise ValueError(recipe)
        out[N] = (1 << (N - 1)) | low
    return out

def score(gen):
    """exact matches over the run, and longest exact prefix from N=1."""
    matches = sum(1 for N in RUN if gen.get(N) == ACTUAL[N])
    prefix = 0
    for N in RUN:
        if gen.get(N) == ACTUAL[N]:
            prefix += 1
        else:
            break
    return matches, prefix

# ---- seed candidates ----
def h_int(x):
    """sha256 of the 32-byte big-endian encoding -> int seed."""
    b = int(x).to_bytes((int(x).bit_length() + 7) // 8 or 1, "big")
    return int(hashlib.sha256(b).hexdigest(), 16)

def h_str(s):
    return int(hashlib.sha256(s.encode()).hexdigest(), 16)

SEEDS = {
    # raw curve constants
    "n": n, "p": p, "Gx": Gx, "Gy": Gy, "t": p + 1 - n,
    # hashes of curve constants
    "sha(n)": h_int(n), "sha(p)": h_int(p), "sha(Gx)": h_int(Gx), "sha(Gy)": h_int(Gy),
    # string hashes
    "sha('secp256k1')": h_str("secp256k1"),
    "sha('bitcoin')": h_str("bitcoin"),
    "sha('puzzle')": h_str("puzzle"),
    "sha('lonely')": h_str("lonely"),
    # common integer seeds
    "0": 0, "1": 1, "42": 42, "2015": 2015, "1231006505": 1231006505,
    # low 64 bits of curve constants (a 2015 coder might seed with a truncation)
    "n&2^64": n & ((1 << 64) - 1), "p&2^64": p & ((1 << 64) - 1),
    "Gx&2^64": Gx & ((1 << 64) - 1),
}
RECIPES = ["getrandbits_seq", "getrandbits256_trunc", "randrange_low", "randrange_full"]
ORDERS = {"forward": RUN, "reverse": list(reversed(RUN))}

print("=== Thread B: curve-parameter / constant seeds x MT19937 ===")
print(f"run = 1..{RUN[-1]}  ({len(RUN)} keys)\n")

# ---- positive control ----
CTRL_SEED, CTRL_RECIPE = 20150115, "getrandbits_seq"
planted = keys_from_random(CTRL_SEED, CTRL_RECIPE, RUN)
# temporarily treat planted as actual to verify recovery
_saved = dict(ACTUAL)
ACTUAL.update(planted)
m, pre = score(keys_from_random(CTRL_SEED, CTRL_RECIPE, RUN))
print(f"[CTRL] planted seed {CTRL_SEED} recipe {CTRL_RECIPE}: matches {m}/{len(RUN)}, prefix {pre}  -> {'FIRES' if m==len(RUN) else 'FAILED'}")
# and a wrong seed should NOT match
mw, prew = score(keys_from_random(CTRL_SEED + 1, CTRL_RECIPE, RUN))
print(f"[CTRL] wrong seed {CTRL_SEED+1}: matches {mw}, prefix {prew}  (expect ~0)\n")
ACTUAL.clear(); ACTUAL.update(_saved)

# ---- real search ----
best = (0, 0, None)
hits = []
for sname, sval in SEEDS.items():
    for recipe in RECIPES:
        for oname, order in ORDERS.items():
            gen = keys_from_random(sval, recipe, order)
            m, pre = score(gen)
            if m > 0 or pre > 0:
                hits.append((m, pre, sname, recipe, oname))
            if (m, pre) > (best[0], best[1]):
                best = (m, pre, f"{sname}/{recipe}/{oname}")

hits.sort(reverse=True)
print("seed/recipe combos with ANY exact match or prefix:")
if not hits:
    print("  (none)")
for m, pre, sname, recipe, oname in hits[:20]:
    print(f"  matches {m:>2}  prefix {pre:>2}  <- {sname} / {recipe} / {oname}")

print(f"\nBEST over {len(SEEDS)}x{len(RECIPES)}x{len(ORDERS)} = "
      f"{len(SEEDS)*len(RECIPES)*len(ORDERS)} combos: "
      f"matches {best[0]}, prefix {best[1]}  ({best[2]})")

# ---- matched null: how many exact matches does a random seed give? ----
import statistics
null_matches = []
for s in range(200):
    gen = keys_from_random(0xBEEF0000 + s, "getrandbits_seq", RUN)
    m, _ = score(gen)
    null_matches.append(m)
print(f"\nnull (200 random seeds, getrandbits_seq): "
      f"max matches {max(null_matches)}, mean {statistics.mean(null_matches):.3f}")
print("scope: MT19937/Python-random only, 22 seeds x 4 recipes x 2 orders; "
      "other PRNG families (MWC1616/glibc/LCG) tested in thread D.")
