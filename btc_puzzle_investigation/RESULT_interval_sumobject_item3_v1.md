# RESULT — ITEM 3: the two never-run interval readouts. ⚠ "NULL" RETRACTED — INSUFFICIENT POWER.

> ## ⚠⚠ RETRACTION (same day, before this file was cited anywhere)
>
> The first revision reported these arms as **NULL**. **That is withdrawn.** In the same document I
> measured the detection floor at **≳35–50% of the set carrying a coherent class bias** and then
> called a non-detection a null. Those are not compatible.
>
> A 96-element sparse subset of a `2^128` interval will not exhibit a >35% coherent structural bias
> unless ECDLP is trivially broken. **The instrument cannot see anything short of that, so its
> silence carries almost no information about the channel.**
>
> **Correct statement:** *this test, at `M = 96`, lacks the statistical power to bound
> interval-channel leakage. It excludes only a bias affecting ≳35% of the set — a nearly vacuous
> constraint.* It is an **insufficient-power result, not a null.**
>
> Conflating "the instrument did not trigger" with "there is nothing there" is exactly the unbounded
> closure this project polices, committed one paragraph after stating the power floor that refutes it.

**Date:** 2026-08-01. **Script:** `interval_sumobject_v1.py` (passes `check_no_float.py`).
**Log:** `item3_run_v1.log`. **Grade:** `[EMPIRICAL — SCOPED NULL]`, power measured.

## 0. What was unrun, and why

`NEXT_SESSION_PROMPT_2026-08-01_v2.md` §C:

- **C.1 — the swap-invariant SUM object `x(Pᵢ+Pⱼ)`.** On a **negation-closed** index set (field
  differences) every odd character is ill-posed unordered and identically zero symmetrized, so `χ₃`
  is the only legal readout there. The **sum** set is swap-invariant, so the full `χ₂/χ₃/χ₆` family
  is legal. **Never run.**
- **C.2 — `χ₂` and `χ₆` on the GROUP-LAW difference.** Also legal (`x(−Q) = x(Q)` removes the sign
  ambiguity), and **computed all along but discarded**, because `interval_multireadout_v3.py` printed
  them under a `[parity-void]` tag that the same analysis file's own scope correction shows is wrong
  for the group arm.

Both are `x([dᵢ ± dⱼ]G)` — the scalar sumset / difference set mapped through `d ↦ x([d]G)`.

**Pre-screen applied before running** (parity × index-set parity): the sum set is swap-invariant and
`x(−Q)=x(Q)` on the group arm, so all three readouts are well-posed on both. The new singular-value
pre-screen does **not** apply here — these are direct character sums over a pair-class multiset, not
singular values of a readout × phase matrix.

## 1. Result — NO DETECTION (see the retraction: this is not a null)

`M = 96` points per set, pool `NP = 400`, `R = 400` null draws (random point subsets), arms drawn
from the dyadic interval `[2^{k−1}, 2^k)`:

| object | arm cells | ≥ 99th (FIRE) | ≥ 95th |
|---|---|---|---|
| SUM `x(Pᵢ+Pⱼ)` | 21 (7 `k` × 3 readouts) | **0** | **0** |
| GROUP DIFF `x(Pᵢ−Pⱼ)` | 21 | **0** | **0** |

**42 arm cells, zero reach even the 95th percentile** (≈2.1 expected) — but see §2's power floor: a non-detection at this power is close to uninformative. Highest single cell:
379/400 at `k=64`, `E2`, group arm — just under the 95th. This includes **`k = 128` and `k = 135`,
the puzzle's native scale.**

## 2. Controls

- **C-PLANT: fires 400/400 on all three readouts, both objects.**
- **C-NEG (standing `n ≥ 20` repair applied):** 20 draws × 3 readouts = 60 cells.
  SUM: 5 above the 95th (≈3 expected), **0 above the 99th**. GROUP: 2 above the 95th, **0 above the
  99th**. Quiet.
- **Power curve** (fraction of the set carrying planted structure):

| planted | SUM fires on | GROUP fires on |
|---|---|---|
| 100% | E2, E3, E6 | E2, E3, E6 |
| 75% | E2, E3, E6 | E3, E6 |
| 50% | E3, E6 | E3 |
| 35% | E6 | — |
| 25% | — | — |

> **POWER: detects ≳35% (sum, via `E6`) / ≳50% (group, via `E3`) of the set carrying a coherent
> class bias. BLIND below ~25–35%.** A coarse instrument, stated as such.

## 3. The GLV forcing — now PROVED, not read off a script

⚠ The first revision banked this as an empirical "structural finding" from the `C-GLV` control line.
That was an empirical reversion: it is an elementary algebraic identity and should have been derived.

**Theorem.** On a GLV(μ₃)-closed point set the value multiset `{x(Pᵢ ± Pⱼ)}` is a union of complete
μ₃-orbits `{v, βv, β²v}` — because `λ(P±Q) = λP ± λQ` and `x(λR) = βx(R)`, so each pair
`(λ^aP, λ^bQ)` sweeps a full orbit as `a` varies. Summing a character over one orbit gives
`χ(v)·(1 + χ(β) + χ(β)²)`. Hence:

- **`χ₂(β) = 1` necessarily**, since `χ₂(β)³ = χ₂(β³) = 1` and `χ₂(β) ∈ {±1}`.
  The orbit sum is `3·χ₂(v)` — **`χ₂` can never annihilate a μ₃-orbit, for any curve or prime.**
- **`χ₃(β)`, `χ₆(β)` are primitive cube roots** exactly when `β ∉ ker χ`, i.e. `β` is not a cube,
  i.e. **`9 ∤ (P−1)`**. Then `1 + ω + ω² = 0` — **exact annihilation.**

**secp256k1:** `P − 1 ≡ 6 (mod 9)`, so `9 ∤ P−1`; verified `χ₂(β) = 1`, `χ₃(β)` a primitive cube
root, `1 + χ₃(β) + χ₃(β)² ≡ 0 (mod P)` exactly, `μ₆(β) = 4`, and the sum multiset is a union of
complete μ₃-orbits (400 values checked). `E2 = 2916 ≠ 0`, `E3 = E6 = 0` — as the theorem requires.

**The condition is `9 ∤ (P−1)`, and it is checkable in one line.** On a prime with `9 | (P−1)`, `β`
would be a cube, `χ₃(β) = 1`, and `E3`/`E6` would NOT be annihilated. The forcing is not universal.

## 3b. Original (empirical) statement, retained for provenance

**C-GLV, both objects:** `E3 = 0` **exactly** and `E6 = 0` **exactly**; `E2` is **not** forced
(31329 on the sum object, 81 on the group arm).

The record had this only for the group difference (`ANALYSIS_diffset_readout_parity_void_v1.md`
scope-correction table: group-law difference `E₃ = 0 exact`, `E₆ = 0 exact`). It now holds for the
**sum** object as well, and the **non-forcing of `E2` is established for both**.

> **Pre-screen consequence: on any GLV-closed (μ₃-closed) point set, `E3` and `E6` carry zero
> information and only `E2` is informative.** Anything testing a `μ₃`-structured set with `E3` or
> `E6` is reading a forced zero.

## 4. What this settles

The `[parity-void]` mis-tagging is resolved **by measurement, not by argument**: the group-arm
`E2`/`E6` were legal all along, and they are null. The swap-invariant sum object — the one readout
axis the analysis file said "actually exists" and had never been exercised — is null on the full
`χ₂/χ₃/χ₆` family.

## 5. Scope and what remains in §C

`M = 96`, pool 400, `R = 400`, secp256k1, constructed scalars, `μ₆`-class readouts, `k ∈ {40, 64,
96, 128, 135, 160, 200}`. Untouched: **C.4** `M = 2000` (detectable marginal excess falls like `1/M`,
the coherent-block floor like `1/√M`), **C.5** triples / higher-order objects and non-dyadic
intervals or non-uniform sampling within an interval.
