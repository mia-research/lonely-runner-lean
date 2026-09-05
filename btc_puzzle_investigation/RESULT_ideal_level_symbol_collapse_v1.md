# Two ideal-level refinements of the ℓ≥5 bridge question collapse — forced algebra, no new test
### (the QUESTION stays open; what collapses is the refinement, see §3's correction)

**Date:** 2026-07-25 · Scripts (in-repo, `scripts_bridge_programme/`): `ideal_symbol_build_v1.py`,
`ideal_symbol_structure_v1.py`, `ideal_symbol_units_v1.py`. Exact integers throughout.
**Status: OBJECT BUILD + FORCED-IDENTITY CHECKS. No inferential test was run; no association statistic
was computed.** An `experiment-designer` prereg gates any inferential arm (CLAUDE.md §2).

**Why this was opened.** `RESULT_ell_ge5_mutual_information_v1` and `RESULT_ell_ge5_conditional_MI_v1`
bound the **rational-exponent** shadow of the reciprocity bridge at ℓ=5,7,11,13 (marginally, and
conditionally on `w=(t−1)/ℓ mod ℓ`). Both pre-committed the same remaining scope: *"a null on the
rational exponents does not establish 'no ℓ-th power reciprocity in `ℚ(ζ_ℓ)`'; the general law operates
on symbols with a choice of prime ideals, and the rational projection can wash an ideal-level relation
into rational independence."* This builds that ideal-level object.

---

## 0. The construction

Curve `E: y²=x³+7` / `F_p`, CM by `ℤ[ω]`, prime order `n=p+1−t`, `4p=t²+3v²`. Record's setup
(`RESULT_cubic_sextic_bridge_v1`): `π=(t+v)/2+vω` with `N(π)=p`, and **`ν=1−π`** with `N(ν)=n`.
Since `3∣n−1` (record's L3), `n` splits in the CM ring and `ℤ[ω]/(ν) ≅ F_n`; since `n≡1 mod ℓ`,
elements of `F_n` carry an ℓ-th power residue symbol. Because `p=π·π̄`:

> `χ_ℓ(p mod n) = χ_ℓ(π mod ν) · χ_ℓ(π̄ mod ν)`

The rational symbol already bounded is the **product**; the CM-factor symbols are *a priori* finer.
That was the hypothesis: a relation between factors could cancel in the product.

## 1. The refinement is empty — five forced facts (**all instrument checks, not evidence**)

Each was **derived before it was run**, so per the drill protocol ("count only UNFORCED hits") a pass
confirms the implementation and carries **no** evidential weight. The content is the *consequence*.

| # | forced fact | ℓ=5,7,11,13 |
|---|---|---|
| **F1** | `π ≡ 1 (mod ν)` — immediate from `ν=1−π` ⇒ **`χ_ℓ(π mod ν) = 1` identically** | **250/250** each |
| **F2** | ⇒ **`χ_ℓ(p mod n) = χ_ℓ(π̄ mod ν)`** — the rational symbol **IS** a single CM-factor symbol | **250/250** each |
| **F3** | mirror: `ν ≡ 1 (mod π)` ⇒ **`χ_ℓ(n mod p) = χ_ℓ(ν̄ mod π)`** | **250/250** each |
| **F4a** | conjugate primes: exponent w.r.t. `ζ^c` is `m·c⁻¹ (mod ℓ)` | **60/60** each |
| **F4b** | ⇒ **product over all `ℓ−1` conjugate primes = 1**, since `Σ_{c∈(ℤ/ℓ)*} c⁻¹ ≡ 0` | **60/60** each |

**⇒ The proposed refinement is empty.** One CM factor is *trivially* 1 (F1), so the factorization does
not split the rational symbol into two informative pieces — it **equals** the surviving factor (F2/F3).
And the symbol of the *ideal* `(ν)` in the compositum `L=ℚ(ζ_{3ℓ})` — a product over the full Galois
orbit of `ℓ−1` primes — is **forced to 1** (F4b), so it carries no information at all; every bit of
content sits in the **individual** conjugate exponent `m`, which by F2 is exactly the rational exponent
already measured and bounded. **This ideal-level route collapses back onto the rational one by forced
algebra, not by an empirical null.**

## 2. Why ℓ=3 escapes — the unit/supplement layer, with ℓ=3 as a live control

The ℓ=3 bridge's correction `c₃ = s·(e(π̄′)−e(ν′))` is carried entirely by **primarizing units** of
`ℤ[ω]` (unit group `μ₆`) plus the **ω-supplement** `χ_λ(ω)`, a separate classical input.

> **Derived before running:** for `u ∈ μ₆`, `χ_ℓ(u)⁶ = χ_ℓ(u⁶) = 1` and `χ_ℓ(u) ∈ μ_ℓ` of prime order
> `ℓ`; `gcd(6,ℓ)=1` for every prime `ℓ≥5` ⇒ **`χ_ℓ(u) = 1` FORCED**.

| ℓ | `χ_ℓ(ω)=1` | `χ_ℓ(−1)=1` | all six units trivial |
|---|---|---|---|
| **3** | **63/200** | 200/200 | **63/200** ← **live** (supplement carries the bridge) |
| 5 / 7 / 11 / 13 | 200/200 | 200/200 | **200/200** ← forced trivial |

ℓ=3 is a **discriminating control on the same code**: the layer is live there (`≈1/3`, as `χ₃(ω)` takes
all three values) and dead at ℓ≥5. So the triviality at ℓ≥5 is a property of the object, not a dead
instrument. **The entire layer that carries the ℓ=3 correction is invisible to `χ_ℓ` for ℓ≥5.**

## 3. Grade

> **Two ideal-level refinements of the ℓ≥5 bridge question — (a) splitting the rational symbol along
> the CM factorization `p=ππ̄`, and (b) passing to the FULL-ORBIT ideal symbol in `ℚ(ζ_{3ℓ})` — both
> collapse: (a) to the rational symbol itself, (b) to the constant 1.** `[PROVED — forced algebra,
> confirmed 250/250 and 60/60]`

⚠ **Scope of (b):** the *full-orbit ideal symbol* is **my own formulation**, not the record's open item.
The prior RESULTs named *"the symbol in `ℚ(ζ_ℓ)` **with a choice of prime ideals**"* — i.e. the
**individual** symbol, which is (a)/F2, not the orbit product. So (b) being trivial **refutes a
formulation introduced here**, and must not be reported as refuting the record's item. (Guarding the
strawman failure mode: refuting a claim never made.)

**What this does and does NOT re-type.** It says these two constructions yield **no NEW test** — the
ideal-level object is the rational object (F2/F3), so it **inherits the existing bound *and its power
floor* (~6% copy-fraction)**, nothing better. It does **not** say the ℓ≥5 bridge question is
structurally void.

> ⚠ **Correction (self-audit).** An earlier draft of this section read *"re-types the null from
> 'empirically absent at our power' toward 'structurally degenerate': nothing for a test to find at any
> sample size."* **That is wrong** — the exact `enlarge-a-null-into-a-closure` reflex
> ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]). F2/F3 **re-express both sides** of the bridge;
> they do not show that no relation between `χ_ℓ(π̄ mod ν)` and `χ_ℓ(ν̄ mod π)` exists. Such a relation
> would still appear as association **in exactly the test already run, at exactly the power already
> had**. What is degenerate is the **factorization** (one factor trivially 1), **not the question.**

Dissolution of a *proposed refinement* is still a positive outcome (drill protocol): it removes a route
that looked like it offered new resolution and did not.

## 4. ⚠ WHAT IS **NOT** ESTABLISHED — pending the source

- **The mechanism is NOT claimed.** The tempting conclusion — *"ℓ-th power reciprocity is therefore
  vacuous for CM data at ℓ≥5, which explains the null"* — rests on a step this file does **not**
  establish: exactly **what the classical law constrains** (the ideal symbol? primary elements of
  `ℤ[ζ_ℓ]` only? a Hilbert-symbol expression?). `π̄, ν ∈ ℤ[ω] ⊄ ℤ[ζ_ℓ]` for ℓ≥5, so whether the law
  even *applies* to them is a source question. A `citation-verifier` pass on **Lemmermeyer Ch. 7** (the
  ledger's ★ overdue item) is running; **the mechanism stays UNGRADED until its statement is in hand.**
  Refuting/《confirming》a mechanism is separate from the forced facts above, which stand either way.
- **Other ideal-level constructions are untouched.** Nothing here bounds symbols of *other* elements of
  `ℤ[ω]` at `ν` beyond units and the CM generators (F1–F3 cover `π, π̄`; §2 covers `μ₆`); nor
  non-CM-generated ideals; nor `ℓ` dividing the class number / non-PID `ℓ≥23`.
- **Scope inherited:** 26-bit `p`, `D=−3`, one twist per `p`. The forced facts are algebraic (scale-free
  by derivation), but the counts were taken at this scale.

## 5. What this opens

- **The one surviving ideal-level lever named so far:** symbols `χ_ℓ(α mod ν)` for `α ∈ ℤ[ω]`
  **outside** `{π, π̄, units}` — these are not covered by F1–F3 or §2 and are not obviously forced.
  Which `α` are canonical (not fished) is the design question; `1−ω` (the ramified prime above 3) and
  `v` are the candidates with curve meaning.
- **The mechanism**, once the source lands: if the law's object really is the orbit-product, the ℓ≥5
  null becomes *structural*, and the correct statement is a theorem, not a bound.
- Untouched by this file: the conditional mediators (`v mod ℓ`, second ℓ-adic digit) from
  `RESULT_ell_ge5_conditional_MI_v1` §4.

## 6. Prior art

No novelty claimed. `ν=1−π`, `π≡1 mod ν`, Eisenstein cubic reciprocity, the ω-supplement, and the
triviality of `μ₆` under `χ_ℓ` for `gcd(6,ℓ)=1` are elementary/classical. The ledger's ★ literature
sweep (Lemmermeyer Ch. 7) is **in progress and was never previously done**. Public data only; no
leakage / ECDLP content.
