# PREREG — Difference-set quadratic-character sum `S_diff` (v1)

**Status:** FROZEN before apply. Pre-registration gate: `experiment-designer` (isolated,
context-free). Date: 2026-07-26. Applied result: [RESULT_diffset_sdiff_v1.md].

---

## Object
```
S_diff = Σ_{1 ≤ j < k ≤ 82} χ₂(x_j − x_k)   over F_P,  P = secp256k1 field prime (P ≡ 3 mod 4)
```
- `x_1..x_82` = affine X-coordinates of the 82 solved-puzzle pubkeys, **ascending bit-length
  order** (all 82 bit-lengths distinct ⇒ total order, no tiebreak).
- `χ₂(z)` = integer Legendre symbol `(z|P)` = `pow(z,(P−1)//2,P)` mapped `{1→+1, P−1→−1}`.
- Source: `solved_puzzles_xy.csv` col `X`.

## Feature / target disjointness
Feature = character sum of X-*differences*; target = which key fills each bit-slot. Disjoint in
construction; `S_diff` does not encode bit-length (the only structure the control preserves). **Not
a residue-vs-component tautology.**

## Antisymmetry + forced-info (decidable, before data)
- `P ≡ 3 mod 4 ⇒ χ₂(−1) = −1 ⇒ χ₂(x_k−x_j) = −χ₂(x_j−x_k)`: each term **antisymmetric** under index
  swap ⇒ `S_diff` is **ordering-dependent** ⇒ ordering **frozen** (ascending bit-length).
- `Σ` over **ordered** pairs `≡ 0` for every set (forced, zero info); `#QR` over ordered pairs =
  `3321` constant (forced). The signed `j<k` sum is the **unforced** part.
- `3321` terms ⇒ `S_diff` is always **ODD** (support constraint).

## Matched control (null)
10,000 resamples of size 82 from `constructed_keys_1to160_100k.csv` (known-MT generator, same
select-bitlen→curve pipeline), one key per matching real bit-length. **Preserves** n, bit-length
multiset, pipeline, frozen ordering, forced bit-1 slot (= generator x). **Destroys** only the
puzzle-specific identity of which key fills each bit-slot.

Empirical null: `mean −2.31, σ 57.69` (= √3321 analytic; shared-index dependence does **not**
inflate), median −3, range [−313, +223]. ≈98% of variance from the 72 high-bit keys (bits 11–130);
only bit-1 fully forced (pool = 1).

## Planted control — FIRES
Per-pair QR-bias `ε` injected in the frozen orientation: reject rate **0.046 at ε=0** (calibrated ≈
α), 0.50 at ε=0.034, 0.83 at ε=0.05, 0.94 at ε=0.06. Null is calibrated and the region is exitable.

## Power
`σ_null = 57.69` ⇒ **50% power at |E[S]| ≈ 113** (ε ≈ 0.034 ≈ 3.4 pts), **80% at ε ≈ 0.048**.

## Falsification (FROZEN, integer order statistics)
Reject the no-leakage null iff
```
S_diff_real < −115   OR   S_diff_real > +111
```
`L = 250th-smallest, U = 9751st-smallest` of the seed-20260726 null; tail counts `227 / 230 ≤ 250`
⇒ two-sided false-positive `≤ 0.0457`. Apply-time two-sided rank p =
`(1 + 2·min(#{null≤S}, #{null≥S})) / 10001`. **Seed jitter:** endpoints wander ±2 across seeds ⇒
`|S_diff| ∈ [111,115]` = **MARGINAL**, not decisive.

## Scope
82 solved puzzles, bit-lengths `{1–70, 75–130}`; control pool = 100,023-row constructed set;
secp256k1 P; ascending-bit ordering; seed 20260726; N=10,000. **No number generalizes past this
scope.**

## Subspace caveat (load-bearing)
`S_diff` is **one projection**. By `χ₂(−1) = −1`, orientation-**symmetric** difference-set structure
is identically 0 here — **invisible, not bounded**. A null bounds only this frozen-orientation
projection, never the symmetric / other-orientation / higher-order difference-set subspace.

## Reproducibility artifacts (this directory)
- `diffset_sdiff_null_v1.py` — matched-control null generator.
- `diffset_sdiff_apply_v1.py` — exact-integer apply harness (int `pow` Legendre).
- `diffset_sdiff_frozen_null_v1.txt` — frozen null, seed 20260726, 10,000 sorted odd ints.
