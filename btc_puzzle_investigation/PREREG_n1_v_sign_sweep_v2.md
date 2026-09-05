# PREREG v2 — is `v = sinθ₁·sinθ₂ ≤ 0` for the N1 twisted sheaf?

**Date:** 2026-07-25 · **Supersedes `PREREG_n1_v_sign_sweep_v1.md`, which was NEVER run** — pre-data
revision after the mandated `experiment-designer` audit. The audit found **seven defects**, two of them
verified by me independently before acting (F2 and F6 below). v1's arms were correctly held.
Still no multi-prime data has been collected; the 6 existing cells (p=13, 43) remain **in-sample**.

**Audit thesis verdict on v1:** *"Not yet — the `O(p²)` instrument is sound and the design is repairable,
but as written the spec applies an inverted criterion to 14 of its 40 primes."* All seven fixes are
folded in below.

**What survived:** the `O(p²)` instrument is **well-defined** — no character of `E(F_{p²})` is needed,
because `L_{χ_a}` is the Lang torsor with trace function `χ_a ∘ Tr_{k/1}` and `L_{χ₂(y)}` has
`χ₂ ∘ N`, both forced by base change. Newton `e₂=(P₁²−P₂)/2` is correct. The auditor reproduced the
record's cells independently (p=13 `|V₁|/√p = 0.27735`; p=43 all five μ₆ classes to `1e−4`).

---

## F1 — sign of `P₂` (v1 was wrong)

Lefschetz gives `V_k = −Σαᵢᵏ` for **every** `k`, so `P₂(a) = −V₂(a)`, not `+V₂(a)`:

> **`e₂ = (P₁² − P₂)/2 = (V₁(a)² + V₂(a))/2`**

v1 implemented literally returns `v ≡ −0.25` at every `a` at p=43. **Load-bearing.**

## F2 — ★ the dictionary is STRATUM-DEPENDENT and the criterion INVERTS (verified by me)

| stratum | closure | `α·(pair)` | `L` factor | `e₂` | criterion | `e₃` |
|---|---|---|---|---|---|---|
| **`p ≡ 3 mod 4`** (SIN, **secp**) | `α↦−ᾱ` | `−p` | `(1−At−pt²)` | `−2p − 4p·v` | **`v ≤ 0 ⟺ e₂ ≥ −2p`** | `−p·e₁` |
| **`p ≡ 1 mod 4`** (COS) | `α↦ᾱ` | `+p` | `(1−At+pt²)` | `+2p + 4p·v` | **`v ≤ 0 ⟺ e₂ ≤ +2p`** | `+p·e₁` |

**Verified at p=13** (exact `e₂ = −12`): cos dictionary → `v = −0.72997` (instrument: `−0.7300`) ✓;
v1's sin dictionary → `−0.2700` ✗. v1 applied the sin criterion to **14 of its 40 primes**.

## F3 — M1 reference values must be EXACT (v1's tolerance was unachievable)

v1's references were transcribed to 4 dp from printed phases; exact `v` at p=43's maximising class is
`−0.14526827783269782` vs the transcribed `−0.1451` — a `1.7e−4` gap, `10⁵×` the stated `1e−9`, so
**M1 as written FAILS and v1 §2 then forbids the sweep.** Exact references:

- **p=13:** `e₂ = −12` (rational, `(n−1)/6 = 1`), **`v = −19/26`** exactly.
- **p=43:** the five μ₆-class `e₂` are the roots of
  `m₄₃(Y) = Y⁵ − 60Y⁴ − 2032Y³ + 224768Y² − 5515008Y + 42288128 ∈ ℤ[Y]` (irreducible), via
  `v = −(Y+2p)/(4p)`. *(Auditor-computed; M1 re-derives it — if it disagrees, M1 fails and the sweep
  does not run.)*

M1 now demands **exact equality**, not a tolerance.

## F4 — M3 was UNRUNNABLE; replaced by four checks computable from `(V₁,V₂)` alone

v1's M3 required `e₃` (needs `P₃`, `O(p³)`) and `e₄` (needs `P₄`, `O(p⁴)`) — the design computes only
`P₁,P₂`, so v1 §5's gate "surviving M1/M3" was ungated. Replacements, all exact-integer:

- **M3a** `Im V₂(a) = 0` — forced (`χ₂^{(2)}(−1) = (−1)^{(p²−1)/2} = +1` ∀ odd `p`); exact form `h₂[d] = h₂[−d]`.
- **M3b** `conj V_k(a) = χ₂^{(k)}(−1)·V_k(a)` — the record's own identity, stratum-uniform.
- **★ M3c** `|u| ≤ 1 + v` (forced by weight-1). **This couples `V₁` to `V₂` and FIRES ON THE F1 BUG**
  (p=43, a=2: `|u| = 0.777645 > 1+v = 0.750000`). This is the check v1 most needed.
- **M3d** `u² ≥ 4v` and `|u| ≤ 2` (reality of `sinθᵢ`).

## F5 — the plant must run INSIDE the pipeline; plus an adjudication gate

- **M2a** (v1's M2, relabelled): synthetic `P₁,P₂` → validates **the Newton/dictionary arithmetic only**.
  It exercises none of the `E(F_{p²})` enumeration, `χ₂∘N`, trace map, dlog, or the `P_k=−V_k`
  convention — **it passes identically with the F1 bug present.**
- **★ M2b — MUTATION BATTERY on the real pipeline (required).** Re-run M1 with each of:
  (i) `P₂ := +V₂`; (ii) `χ₂` exponent `(p−1)/2` instead of `(p²−1)/2`; (iii) trace `P` instead of
  `P + Frob P`; (iv) a `v=+0.36` tuple injected at the **histogram** level (Galois-consistent: since
  `V₂(ca) = σ_c(V₂(a))`, a plant must move a whole orbit, not one cell).
  **Each mutation MUST make M1 or M3c fail. Any that passes names an unguarded component.**
- **Adjudication (§5):** a cell reporting `v>0` is filed as a counterexample only after
  (a) exact `ℤ[ζ_n]` recomputation with certified enclosure, (b) M3a–M3d at that cell, (c) the `O(p⁴)`
  instrument at that `(p,a)` if `p ≤ 61`.

## F6 — strata (verified by me: v1's second stratum was a 100% subset of the first)

`p ≡ 1 mod 3` is **forced** (else `E` is supersingular, `#E = p+1` even) — v1 never stated it.
The frozen 40-list (`#E` prime, `p > 100`) spans **[127, 4513]**: **26 are `p ≡ 7 mod 12` (SIN/secp)**,
14 are `p ≡ 1 mod 12` (COS). v1's "smallest 10 above 2000" are **all already among the 40** — zero new
primes, ten double-counted (verified). **Replacement second stratum:** the smallest 10 with `#E` prime
**above 4513** — `[4549, 4597, 4831, 5107, 5197, 5281, 5791, 5923, 5953, 6007]` (5 of them `p≡3 mod 4`).
**Report strata separately; never pool.**

## F7 — the count unit is μ₆ classes, not raw `a`

`σ_c(e₂(a)) = e₂(ca)` exactly, so the `n−1` values are **Galois conjugates of one algebraic integer**,
collapsing to `(n−1)/6`. Report `#{μ₆ classes with v>0}` out of `(n−1)/6`. Frozen totals for the
40-list: **14,168 μ₆ classes (9,888 SIN / 4,280 COS)** — not 85,008 raw `a`-cells.

## D5 — no bare double decides a sign (v1 had no power number)

`|V₂| ≤ 4p` is forced while `Σ_d|h₂[d]| = O(p²)`, so cancellation is `≈p/4`; at `p=4513`, 53-bit
doubles retain `≈12.9` decimal digits ⇒ **the sign of `v` is decidable in double precision only for
`|v| ≳ 10⁻¹³`** — and by the record's `S_y→2 ⟺ v→0` identification, **the deciding cells are exactly
the smallest-`|v|` ones.** Rule: the sign is decided by **certified enclosure** (Arb / `mpmath.iv`) on
the exact integer coefficient vector of `V₁²+V₂ ∈ ℤ[ζ_n]`, precision doubled until the enclosure
excludes 0; if it does not by 512 bits, test exact algebraic equality on the reduced vector mod `Φ_n` — **`e₂ + 2p = 0` (SIN) / `2p − e₂ = 0`
(COS)**, the same stratum split as the ADDITION, *not* a common `∓` — and report `v = 0` or **ABSTAIN**.

## ★ ADDITION — restate the per-prime test as TOTAL POSITIVITY of one algebraic integer

Per prime, compute `e₂(1) ∈ (1/2)ℤ[ζ_n]` once (`O(n²)`), form its minimal polynomial
`m_p(Y) ∈ ℤ[Y]` of degree `(n−1)/6`, and test by **Sturm sequence on the integer polynomial
`m_p(X ∓ 2p)` — no floats anywhere** — whether it has a root on the wrong side of `∓2p`.

> **The whole claim at `p` becomes: the STRATUM-CORRECT quantity below is a TOTALLY NON-NEGATIVE
> algebraic integer of the μ₆-fixed subfield of `ℚ(ζ_n)`:**
> - **SIN (`p≡3 mod 4`, secp):** `e₂ + 2p ≥ 0`  → Sturm on `m_p(X − 2p)` has no negative root
> - **COS (`p≡1 mod 4`):**       `2p − e₂ ≥ 0`  → Sturm on `m_p(X + 2p)`, reversed orientation

> ⚠⚠ **CORRECTED 2026-07-25, BEFORE ANY RUN — I reintroduced F2's defect in this very ADDITION.**
> v2 first wrote both strata as `∓(e₂+2p)`. For COS that reads `−(e₂+2p) ≥ 0 ⟺ e₂ ≤ −2p`, but the
> correct COS condition is `e₂ ≤ +2p`. **Wrong sign AND wrong constant — it inverts the criterion on
> the cos stratum, exactly the defect F2 was raised to fix.** Verified at `p=13` (`e₂=−12`, true
> `v=−19/26 ≤ 0`): correct `2p−e₂ = 38 ≥ 0` ✓; the erroneous form gives `−14 < 0` ⇒ would have reported
> `v>0` and manufactured a false counterexample. **The two quantities are `(e₂+2p)` and `(2p−e₂)` — NOT
> a common `∓(e₂+2p)`.** Found by running the audit's own load-bearing check inline after the
> `experiment-designer` re-audit STALLED and returned nothing.

This makes the sign test exact by construction (retiring D5), fixes the count unit automatically (F7),
collapses `n−1` float decisions into one integer-polynomial question, and **hands the proof programme a
sharper target than §3 of the RESULT reached for** — total positivity of a single algebraic integer,
which is the shape integrality arguments actually attack. Verified implementable at p=43: roots
`−61.014, 16.796, 30.772, 33.972, 39.474`, all `≥ −2p = −86`.

## Unchanged from v1

§4 outcomes (all four legitimate; `v>0` ⇒ **route dead, inequality NOT refuted**), §5 falsification
logic (deterministic universal claim: one counterexample decides, no multiple-comparison correction,
counts are scope not significance — now with the F5 adjudication gate), §6 scope (`v ≤ 0` sufficient not
necessary; secp banner #5 — all primes here are `O(10²–10³)` against secp's `2²⁵⁶`).

## Deviations: `PREREG_n1_v_sign_sweep_v2_DEVIATIONS.md`, at first deviation.
