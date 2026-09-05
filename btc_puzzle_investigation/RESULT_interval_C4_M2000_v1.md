# RESULT — C.4: the interval channel at `M = 2000`. A quantified BOUND (18.5× tighter), not a null.

**Date:** 2026-08-01. **Script:** `interval_C4_M2000_v1.py`. **Log:** `item3_C4_M2000.log`.
**Grade:** `[EMPIRICAL — BOUND, power measured]`. **This does NOT close the channel.**

## 0. Why C.4 was run

At `M = 96` the measured floor was ≳35–50% of the set carrying coherent bias — nearly vacuous, since
a sparse 96-element subset of a `2^128` interval cannot show a 35% coherent bias unless ECDLP is
trivially broken. That non-detection was an **insufficient-power result**, and calling it a null was
retracted. C.4 raises `M` to 2000: pairs go `4560 → 1,999,000`, a 438× increase.

## 1. ⚠ The power number the script printed is an ARTIFACT — do not read it

The run reports `DETECTION FLOOR at M=2000 : 100% coherent bias`, i.e. **worse** than `M = 96`'s 35%.
That is **not** the instrument getting weaker. It is a **plant-construction artifact**:

> The greedy plant selects `M` points from a pool of `NP` by maximising same-class pairs. At
> `M/NP = 96/400 = 24%` it has room to be selective; at `2000/5000 = 40%` it has taken most of the
> pool and its advantage is exhausted. **"Fraction of the SET planted" is confounded with `M` and is
> not comparable across `M`.**

Recording this prominently because reading it at face value would have **inverted the conclusion** —
it would have said raising `M` made the test worse.

## 2. The power measurement that IS comparable: fraction of PAIRS biased

The statistic depends only on the pair-class multiset, so the clean question is *what fraction of
pairs must carry a bias to be detected.* Measured by binary search against each `M`'s own null 99th:

| `M` | # pairs | null `E3` 99th | detection floor |
|---|---|---|---|
| 96 | 4,560 | 20,181 | **2.575%** of pairs |
| 400 | 79,800 | 386,679 | 0.749% |
| **2000** | **1,999,000** | **9,573,316** | **0.139%** of pairs |

> **18.5× improvement**, against the `√438 ≈ 21×` predicted by the `1/√(#pairs)` scaling. C.4
> delivers the power increase it was run for.

## 2b. ⚠ CORRECTION — the floor differs per readout; "0.14% across all three" was a shortcut

§2 measured the floor against `E3` only, with the bias concentrated on class 0, and the bound was
then stated "across all three readouts." **That is an analytical shortcut.** The floor depends on the
readout *and* on how the bias is distributed among classes — `χ₂` is maximally biased by
concentrating on `{0,2,4}`, `χ₃` by `{0,3}`, `χ₆` by a single class. Measured exactly
(null = multinomial, `R = 4000`, 99th percentile):

| `M` | bias | `E2` floor | `E3` floor | `E6` floor |
|---|---|---|---|---|
| 96 | class-0 | 3.786% | 2.295% | 3.931% |
| 96 | readout-optimal | 2.594% | 3.040% | 2.260% |
| 400 | class-0 | 1.050% | 0.901% | 1.172% |
| 400 | readout-optimal | 0.586% | 0.585% | 1.074% |
| **2000** | **class-0** | **0.177%** | **0.146%** | **0.153%** |
| **2000** | **readout-optimal** | **0.142%** | **0.196%** | **0.097%** |

**Range at `M = 2000`: 0.097%–0.196%.** For a *given* bias direction the effective floor is the
**minimum** over readouts (any one firing suffices); a bound claimed to hold for **all** the tested
directions must use the **weakest** cell, `0.196%`.

**Improvement over `M = 96` is 16–26×** depending on readout (`E3` class-0 15.7×, `E2` class-0 21.4×,
`E6` class-0 25.7×), bracketing the predicted ~21× — so the single "18.5×" figure should be read as a
range, not a constant.

## 3. Result at `M = 2000`

Pool `NP = 5000`, `R = 200` null draws, arms `k ∈ {64, 128, 135, 160}`:

- **SUM object `x(Pᵢ+Pⱼ)`**: no cell fires; highest `k=160, E2` at 197/200 (98.5th).
- **GROUP difference `x(Pᵢ−Pⱼ)`**: no cell fires; highest `k=160, E2` at 181/200.
- **24 arm cells, zero fires.**
- **C-NEG (n ≥ 20 standing repair):** SUM 3/60 above the 95th (≈3 expected), **0/60 above the 99th**;
  GROUP 3/60 and **0/60**. Quiet on both.

## 4. What this establishes — stated as a bound

> **At `M = 2000`, `k ∈ {64, 128, 135, 160}`, on both the swap-invariant sum object and the group-law
> difference: no class bias of the tested shapes exceeding ≈0.20% of pairs is present** (the weakest
> readout/direction cell). Per-readout floors run **0.097%–0.196%** — see §2b; the earlier blanket
> "0.14%" was the `E3`/class-0 cell generalised without measurement.

That is **18.5× tighter** than the previous constraint and is real progress. It is **a bound, not an
absence**: whether a genuine interval-channel leak would produce a ≥0.14% pair-class bias is unknown,
so **the channel is not closed.** The correct reading is "leakage of this shape and above this
magnitude is excluded at these bit-lengths," nothing more.

## 5. Scope

secp256k1, constructed scalars, `μ₆`-class readouts `E2/E3/E6`, `M = 2000`, pool 5000, `R = 200`,
`k ∈ {64, 128, 135, 160}`, one seed. Untouched: `k` outside that set, other readouts, **C.5**
(triples / higher-order objects, non-dyadic intervals, non-uniform sampling within an interval), and
any bias below the 0.14% pair floor.

## 6. Method note

A control that is **confounded with the parameter being varied** is worse than no control: it
produces a number that looks like a power measurement and points the wrong way. The fix was to move
the power question to a quantity (fraction of **pairs**) that does not depend on how the plant is
constructed.
