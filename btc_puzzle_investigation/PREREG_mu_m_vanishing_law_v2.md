# PREREG v2 — the `μ_m` vanishing law (SUPERSEDES v1; v1's design was tautological)

**Written 2026-08-02. No script for this question has been executed.** v1 was gated by
`experiment-designer` before freezing; it returned 16 findings, **5 blocking**, including one
**critical**. v1 is retained unmodified. Amendments marked `[G:Fn]`.

---

## 0. Why v1 was void — stated first, because it changes what the run can conclude

> **`[G:F1]` CRITICAL — v1's P1 was unfalsifiable by the instrument that measured it.**
>
> v1 §1 defined `p`-rank as *"the stable rank of `𝒞` on `H⁰(C,Ω¹)`"*, and v1 §3 **constructs** `𝒞` by
> a recipe that writes column `(a,b)` only into block `m − k_b`. The matrix is therefore block-graded
> **by construction**, and by v1's own (correct) linear algebra any such matrix has stable rank `≤ S`.
> So `p`-rank`_measured ≤ S` would have held for **every `f`, every `p ≡ −1 (mod m)`, and every
> coefficient value — including wrong ones.**
>
> Gate artifact: 4000 random fills of the allowed blocks, per row — max stable rank `= S` at all 8
> rows (ungraded random matrices reach the full genus, so the cap is the grading, not the fill).
> Worse: at `p ≡ −1`, `b·p⁻¹ ≡ b·p ≡ m−b`, so the grading is insensitive **even to a sign error in
> the `k_b` recipe** — a corrupted target `c = b·p` gives the identical maximum at all 8 rows.
>
> The statistic and the bound were the same object twice. This is the shared-construction tautology
> already logged on this project (`feedback_residue_vs_component_tautology_2026_07_14`).

**The v2 fix, and it is structural, not cosmetic:**

> **P1 is measured against the POINT-COUNT `p`-rank only** — the Newton polygon of the
> `L`-polynomial built from `#C(F_{p^n})`. The Cartier stable rank **cannot test P1** and is demoted
> to a descriptive quantity. Consequently **rows without point-count coverage carry ZERO independent
> weight** and are reported as *instrument-internal*, not as evidence `[G:F2, F14]`.

---

## 1. Object amendments

- **`new part` DEFINED `[G:F8]`** — v1 used it six times without defining it for general `m`.
  **`new part := ⊕_{gcd(b,m)=1} V_b`**, the primitive part. It is `𝒞`-stable, since
  `gcd(b·p⁻¹, m) = gcd(b,m)`. **At `m` prime the new part is all of `Jac C`** — so for `m = 5` it is
  4-dimensional, not a 2-dimensional analogue of `A_new`.
- **`V_b` renamed `[G:F15]`** — it is the **degree-`b` piece of the `ℤ/m`-grading** of
  `F_p(x)[w]/(w^m − f)` as an `F_p(x)`-algebra (an `F_p`-subspace, which is what makes the whole
  construction `F_p`-rational). It becomes the `μ_m`-eigenspace only after base change to
  `F_p(ζ_m)`; at `p ≡ −1 (mod m)`, `m > 2`, `ζ_m ∉ F_p`.
- **`S_new(m,d) := Σ_{gcd(b,m)=1} min(⌊bd/m⌋, ⌊(m−b)d/m⌋)`**, the new-part bound.

## 2. Predictions — with the new-part column v1 omitted `[G:F8]`

| `(m,d)` | genus | `S` | **`S_new`** | `S_old` | point-count coverage (§4) |
|---|---|---|---|---|---|
| **(4,3)** | 3 | 1 | **0** | 1 | anchor, not out-of-sample |
| (5,3) | 4 | 2 | **2** | 0 | yes |
| (3,4) | 3 | 2 | **2** | 0 | yes |
| (3,5) | 4 | 2 | **2** | 0 | yes |
| (4,5) | 6 | 4 | **2** | 2 | yes (`p=7`, `7⁶ = 117 649`) |
| (8,3) | 7 | 3 | **2** | 1 | yes (`p=7`, `7⁷ = 823 543`) |
| (7,3) | 6 | 2 | **2** | 0 | marginal (`p=13`, `13⁶ = 4.8·10⁶`) |
| (5,4) | 6 | 2 | **2** | 0 | **NO** — instrument-internal, zero independent weight |

**`[G:F9]` P3 CORRECTED — v1's "unlike `m = 4`" is contradicted by v1's own table.** `(4,5)` has
`S_new = 2 > 0`. **`(4,3)` is the only row in the table with `S_new = 0`.** So the vanishing is
**`d`-dependent, not `m`-dependent**: `⌊d/m⌋ = 0 ⟺ d < m`. Derived characterization, pre-registered:

> `S_new = 0` **⟺** `min(b, m−b)·d < m` for every `b` coprime to `m`.

Executed check: `(6,5)` also gives `S_new = 0`, so the `(4,3)` phenomenon **recurs** and is not unique.
P3 is restated as: *at `(5,3)` the new part is not uniformly supersingular, **unlike `(4,3)`***.

**`[G:F10]` P3's object corrected.** `ℤ[ζ₅]` is a domain — no nontrivial idempotents — so the `{2,3}`
grouping is **not** an abelian subvariety and "ordinary" does not apply to it. At `p ≡ −1 (mod 5)`, `p`
splits into two primes of residue degree 2 in `ℚ(ζ₅)`, whose Frobenius orbits on characters are
`{1,4}` and `{2,3}`; so the **`p`-divisible group** of `Jac C` splits accordingly. The claim is:
*the `{2,3}` summand of the `p`-divisible group is generically ordinary (`p`-rank 2 = its dimension);
the `{1,4}` summand is supersingular.*

> **Pre-registered binarity `[G:F10]`:** `dim V₂ = dim V₃ = 1`, so both composites are `1×1` and the
> `{2,3}` stable rank is **`0` or `2`, never `1`.** A binary readout — stronger than v1 claimed.

## 3. Controls — v1's four were one forced, one unrunnable, one half-forced, one decided in advance

| id | type | statement | pass condition |
|---|---|---|---|
| **C1** | **control — now PRIMARY** | Point-count `p`-rank: build `L_C(T)` from `#C(F_{p^n})`, `n = 1…g`, read the Newton polygon. **This is the only instrument that can test P1.** | `p`-rank `≤ S` at every covered row; **a violation refutes the pairing mechanism** |
| **C2** | control `[G:F3]` | Wrong-pairing arm, `p ≢ ±1 (mod m)`. **Structurally impossible at `m ∈ {3,4}`** — every unit mod 3 and 4 is `±1`. Eligible cells and their true bound `S′` are **pre-registered here**: `(5,3) r∈{2,3} → S′=0`; `(5,4) r∈{2,3} → S′=0`; `(7,3) r∈{3,5} → S′=0`; `(7,3) r∈{2,4} → S′=3`; `(8,3) r=5 → S′=5`; **`(8,3) r=3 → S′=S=3`, a PREDICTED COINCIDENCE, not a failure.** | **all 5 forced cells** (`S′ = 0 < S`) must mispredict; denominator is the 10 eligible cells only |
| **C4a** | **control (new) `[G:F4]`** | Regression: the generalized-`m` code must reproduce `anew_m_support_v2.sage`'s Cartier matrix **entrywise** at `m = 4`, on a frozen `(p,f)` list | exact entrywise match; else **VOID** |
| **C4b** | anchor `[G:F4]` | `(4,3)`: `p`-rank ∈ {0,1}, and `= 1` **exactly on rows where `a_p(E) ≢ 0 mod p`**, `a_p` computed independently. **The supersingular-`E` exception is named in advance** — it occurs for 4.7–18% of cubics, and v1's C4 would have VOIDed the run for that correct reason | both |
| **K-plant** | **control (new) `[G:F7]`** | Hand-build a graded matrix of chosen stable rank `r`, require the readout to report `r`, for every `(m,d)` and every `r ∈ 0…S` | all reported; else **VOID** |
| **K-attain** | **control (new) `[G:F7]`** | The pipeline must **reach** stable rank `= S` on ≥1 row per `(m,d)`. If it never attains `S` at some `(m,d)`, that `(m,d)` is **instrument-suspect, not a P2 datum** | ≥1 attaining row per `(m,d)` |
| G-spread | **guard** (was "C3") `[G:F5]` | ≥3 distinct `S`; some `min=0`, some all-`min>0`. **Satisfied by the §2 table at write time — cannot fail.** Relabelled | design check only |

## 4. Sampling plan — v1 had none `[G:F6]`

v1 fixed no prime range, no `n_f`, no distribution, no seed, no exclusion rule, no P2 threshold — a
regression against `PREREG_anew_m_support_v2.md`, written the same day.

- **Seed `20260805`.** Per `(m,d)`: all primes `p ≡ −1 (mod m)`, `p > d`, `p ≤ 200`; **40 seeded-random
  separable `f` of degree `d`** per prime, rejecting `disc f ≡ 0 mod p` (exclusions derived from the
  sample and reported with `N`).
- **Point-count coverage (C1), budget `p^g ≤ 5·10⁶`, fixed now**: the per-row column in §2.
  **C1 runs on the first 8 seeded-random `f` per covered `(m,d,p)`** (the `#C(F_{p^n})` count is
  `O(p^g)` *per `f`*, so it cannot run on all 40); the remaining `f` receive the Cartier readout only,
  which is **descriptive and carries no P1 weight** (§0). `(5,4)` is **not covered at all** — its
  smallest eligible prime is `p = 19` with `19⁶ ≈ 4.7·10⁷` — and is reported as instrument-internal.
- **P2 threshold, operational:** for each `(m,d)`, the fraction of non-excluded `f` with
  `p`-rank `= S`; pre-committed to reporting it as a fraction with its denominator, **per `(m,d)`,
  never pooled**. "Generic" means `≥ 0.5`; below that is reported as a rate, not a failure.
- **Exactness `[G:F16]`:** point counting uses `numpy int64` / Sage finite fields — exact integers, no
  float. An overflow guard is asserted per `(p,n)` on the largest intermediate. **The sole float in
  the run is any reported rate**; no float in the signal path.

## 5. Permitted conclusions

| outcome | permitted | forbidden |
|---|---|---|
| no C1 violation | *"point-count `p`-rank `≤ S` at every covered row (`N` stated); the pairing mechanism is independently confirmed at the covered `(m,d)`."* | **extending it to uncovered rows** — `(5,4)`, and `(7,3)` if the budget is not met `[G:F14]` |
| **a C1 violation** | **the pairing mechanism is REFUTED**; name the row; re-open Step 3′ **and** the downstream in §6 | refuting on the Cartier readout alone — it cannot violate `S` `[G:F1]` |
| Cartier stable rank `≤ S` | **nothing.** Forced by construction; reported as a consistency check on the code, never as evidence | quoting it as support for P1 |
| P2 rate per `(m,d)` | the fraction with its denominator | calling it a law |
| **P3 at `(5,3)`**: `{2,3}` stable rank `= 2` | *"the `{2,3}` summand of the `p`-divisible group is ordinary at `(p,f) = …`; the new part is not uniformly supersingular at `(5,3)`, unlike `(4,3)`."* | any hardness or ECDLP reading (§6) |
| **uniform shortfall** — `p`-rank `< S` for **all** `f` at some `(m,d)` `[G:F11]` | *"a SECOND vanishing beyond the pairing"*; name the pair(s) with zero stable rank; `[VERIFIED-INSTANCE]`; **re-opens `S` as the complete bound** | filing it as "a low P2 rate" |
| per-pair stable ranks deviate from §2 `[G:F11]` | report per-pair; this is a distinct outcome from the total matching | — |
| C1, C4a, C4b, K-plant fail | **VOID-and-investigate** `[G:F11]` | any conclusion |
| K-attain fails at some `(m,d)` | that `(m,d)` is **instrument-suspect**; its P2 datum is withdrawn | reporting its rate |

## 6. Scope `[G:F12, F13]`

- **The downstream v1 omitted.** A C1 violation would unseat the reviewed status of Step 3′ and
  therefore the current support for `Hom(E,A_new) = 0` / **P13** / **Route 2's "blocked" grade**;
  those would revert to their pre-`RESULT_v2` grade and need re-deriving. **No other outcome touches
  them.** N4 / Route 3 is untouched by every outcome.
- **`[G:F13]` v1's §6 supplied the bridge it forbade**, paraphrasing "not uniformly supersingular" as
  *"not uniformly easy"* — which asserts supersingular = easy, the exact translation the section
  exists to block. Struck. The object-level statement is: **the `{2,3}` summand has `p`-rank 2.** No
  hardness reading is named, not even to forbid it.
- Pure curve arithmetic. Nothing reaches `p = 2²⁵⁶−2³²−977`. Nothing about the `a ≠ 0` uniformity gap,
  nothing about any `d`-side object.

*Frozen at first v2 script execution. Deviations → `PREREG_mu_m_vanishing_law_v2_DEVIATIONS.md`.*
