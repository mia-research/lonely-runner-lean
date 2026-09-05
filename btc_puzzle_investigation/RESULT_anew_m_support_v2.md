# RESULT v2 — `m`-support: anti-suppression audit of the filters, and the CM census upgraded to an exact multiplicity law

*2026-08-02. Supersedes `RESULT_anew_m_support_v1.md`, retained unmodified. Same run, same log
(`anew_m_support_v2.log`); v2 adds a filter audit and corrects an **under-statement in v1's own
reporting**. Artifact: `audit_phase1_filters_v1.sage` / `.log`. No new sweep was run.*

**Carried unchanged from v1:** §1 rows 2/3/10, §2 controls, §3 EXPLORATORY, §4 scope, §5 ledger.

---

## 1. Anti-suppression audit of the Phase 1 filters

Question asked: **can any filter in `anew_m_support_v2.sage` drop or hide an `m = −1` cover instead of
reporting it?** This is the project's documented one-way failure mode (converting positives to nulls
before testing them), so the headline null had to be audited for it rather than trusted.

| filter | audit | result |
|---|---|---|
| **random-draw rejection loop** (`disc = 0`, capped at 4000 tries) — could silently under-draw and shrink `N` | replayed the seeded stream over all 96 primes | **3840 draws, exactly `96 × 40`; zero primes short.** No under-draw |
| **CM/non-CM split** (`is_cm_type`) — could misroute a class out of the census | counted random draws that land CM-type | **exactly 3** — which reconciles the log exactly: `380 (exhaustive) + 3 = 383` CM rows, `3840 − 3 = 3837` non-CM rows |
| **`m` UNDEFINED gate** (`p ∤ b₂`) | an `m = −1` row has `b₂ = −p`, divisible; and v1 §1 reports 0 UNDEFINED rows on the MAIN arm | cannot hide `m = −1` |
| **`extract_m` parity path** (`"PARITY_FAIL"`) | is a non-`None` value, so it lands in the tally *and* trips outcome 7; outcome 7 reported 0 | cannot hide a row |
| **class dedup** (`cover_class`) — merging two covers of different `m` would hide one | in-sample check "labels with mixed `m`" | **0** across 4220 MAIN + 4600 CONTROL rows — soundness verified **at the actual sweep primes**, stronger than K4′'s brute force at `p ∈ {11,19,23}` |
| **full reporting path** | pushed a synthetic `m = −1` row end-to-end | tallied under key `−1`; **appears in the LOCK-VALUE readout**; `extract_m` on a true `m = −1` count vector returns `−1` |

> **No suppression path exists in the code.** The null on `m = −1` is a property of the family, not an
> artifact of a filter.

---

## 2. CORRECTION to v1 — the CM finding was under-reported

v1 §1 row 4 stated the CM-type result as *"the realized support of `m` is exactly `{−2, 1, 2}`"*. That
is true and **weaker than the data**. The census is exactly regular:

> **`[VERIFIED — complete census, 96 primes, zero deviation]`**
>
> | | CM classes per prime | `m` census | **exact per-prime multiplicity** |
> |---|---|---|---|
> | `p ≡ 11 mod 12` (**49** primes) | 2 | `m = +2`: 98 | **`2 × (m = +2)`** |
> | `p ≡ 7 mod 12` (**47** primes) | 6 | `m = −2`: 94; `m = +1`: 188 | **`2 × (m = −2)` and `4 × (m = +1)`** |
>
> `49 × 2 = 98`; `47 × 2 = 94`; `47 × 4 = 188`. **Zero deviation at any of the 96 primes.**

This is a **multiplicity law**, not a support set: at every prime `≡ 7 mod 12` the six CM classes split
`2 : 4` between `m = −2` and `m = +1`, and at every prime `≡ 11 mod 12` both classes carry `m = +2`.

**Why it is stronger than what the record had.** The `m`-law H1/H2 was measured on the curated
`B ∈ {7, 2, 11}`. This enumerates **every** CM class at every sampled prime, so it is a census, and the
`2 : 4` split matches the index-6 structure of `(F_p*)³ ∩ (F_p*)⁴` — the subgroup that governs
`w⁴ = x³+B ≅ w⁴ = x³+B'` — with 2 of the 6 classes cubic-residue and 4 non-residue, exactly the
branch condition the anchor's table uses.

**Grade unchanged, scope unchanged.** Still `[VERIFIED]`, still 96 primes in `(1039, 2500)`, still the
`a = 0` fibre, still nothing reaching secp. This corrects **how the same data was stated**, not what
was measured. No law-fit beyond the sampled primes is claimed and no out-of-sample retest of the
multiplicity law has been run.

---

## 3. Why this correction was needed — recorded plainly

v1 reported the CM stratum at the strength of a *support set* when the data supported an *exact
multiplicity law*. The direction of the error is the documented one: **a positive flattened toward a
weaker statement.** It is the same direction as the project's logged core bias, appearing in the
reporting layer rather than in the test design — which is where the filter audit above would not have
caught it, and did not; the user asked for the review that did.

The audit found **no defect in the code**. The defect was in the write-up, and only in the direction
of under-claiming.
