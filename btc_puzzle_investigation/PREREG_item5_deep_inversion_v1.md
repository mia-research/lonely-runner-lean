# PRE-REGISTRATION — Item 5 deep run: pointwise inversion at 2^128, `M = 6.25×10⁶`

**Written BEFORE the run. Frozen.** `experiment-designer` gate: **OWED, not run** — recorded per
`CLAUDE.md §2a`; this file is the substance of the spec, not a substitute for the gate.
**No grade may be promoted on this run until the gate clears.**

## 1. Object

`S = Σ_i a_i b_i`, `a_i = χ₂(x_{[d_i]G})`, `b_i = χ₂(x_{[d_i⁻¹]G})`, secp256k1.

## 2. Arms (fixed now)

| arm | `d` drawn from | M |
|---|---|---|
| k=128 | `[2^127, 2^128)` | 6 250 000 |
| k=135 | `[2^134, 2^135)` | 6 250 000 |
| k=160 | `[2^159, 2^160)` | 6 250 000 |
| CONTROL | `[1, n)` full range | 6 250 000 |

Seed for the primary run: `20260801`. Seeds `11111…55555` are **reserved for OOS** and must not be
inspected first.

## 3. Statistic and decision rule (fixed now)

- Statistic: `S`, **two-sided**.
- Null: the **exact permutation moments** of a fixed-vector inner product —
  `E[S] = (Σa)(Σb)/M`, `Var[S] = [Σ(aᵢ−ā)²][Σ(bᵢ−b̄)²]/(M−1)` — with a normal reference (valid at
  this `M` by CLT). **Validated against 500 explicit shuffles on a subsample; if the analytic sd and
  the empirical sd disagree by >2%, the run is VOID.**
- **FIRE = |z| ≥ 3.0.** With 4 arms, a *claim* requires **|z| ≥ 3.4** (Bonferroni).
- **Any arm that fires must replicate on 5 fresh seeds at the same `M` before it is named.**
  Statistic and direction are fixed by this document. Failure to replicate ⇒ dead, recorded as such.

## 4. Controls — each must measure BOTH sides

- **C-BALANCE** — marginals of `a` and of `b`, reported separately.
- **C-DUP** — sampled `d` sharing a μ₆ class (would force ties). Expected 0; reported.
- **C-FIX** — `d` with `d = ±d⁻¹` (summand forced to `+1` regardless of data). **Excluded**, count reported.
- **C-NULLSD** — analytic sd vs empirical shuffle sd (§3). *This is the check that would have caught
  the `√2` fault in item 4.*
- **C-PLANT** — dilution curve at the achieved `M`; the floor is **measured**, never assumed.

## 5. Pre-committed prediction

Threshold scaling is `f > 2.5/√M`. At `M = 6.25×10⁶` the predicted floor is **0.10%**, against the
2% achieved at `M = 20000`. **If the measured dilution floor is not within a factor 2 of 0.10%, the
scaling model is wrong and that is itself the finding.**

## 6. What a null result will and will not mean

A non-detection bounds the pointwise inversion correlation below the **measured** floor at these
bit-lengths. It is **a bound, not an absence**, and does not close the channel. The retraction in
`RESULT_interval_sumobject_item3_v1.md` applies verbatim: an instrument's silence is only as
informative as its measured floor.

## 7. Self-audit — sections this pre-registration does NOT cover

- **Object/disjointness:** `a` and `b` come from the same curve and the same readout; they are
  disjointly *indexed* (`d` vs `d⁻¹`) but not disjointly *constructed*. Unaudited.
- **Scope:** one readout (`χ₂` of `x`), one map (`k = −1`); `χ₃`/`χ₆` and `d ↦ d^k` for other
  `k ≡ ±1 mod 6` are outside.
- **Falsification:** the rule fires on `|z|`; it has no power against structure that leaves the
  first moment intact (e.g. a variance-only or higher-order effect).
