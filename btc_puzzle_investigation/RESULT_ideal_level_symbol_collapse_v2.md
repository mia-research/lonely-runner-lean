# The CM route to an ideal-level ℓ≥5 bridge reduces to a rational symbol — forced algebra

**Supersedes `RESULT_ideal_level_symbol_collapse_v1.md`** (which is retained: it carries the audit trail
of two corrections made to it). v2 adds §1b (the reduction R1–R4) and folds in both corrections.
**Date:** 2026-07-25 · Scripts (in-repo, `scripts_bridge_programme/`): `ideal_symbol_build_v1.py`,
`ideal_symbol_structure_v1.py`, `ideal_symbol_units_v1.py`, `ideal_symbol_reduction_v1.py`.
Exact integers throughout.

**Status: OBJECT BUILD + FORCED-IDENTITY CHECKS. No inferential test was run; no association statistic
was computed.** An `experiment-designer` prereg gates any inferential arm (CLAUDE.md §2).

**Why opened.** `RESULT_ell_ge5_mutual_information_v1` and `RESULT_ell_ge5_conditional_MI_v1` bound the
**rational-exponent** shadow of the reciprocity bridge at ℓ=5,7,11,13 (marginal, and conditional on
`w=(t−1)/ℓ mod ℓ`). Both pre-committed the same remaining scope: *a rational-exponent null does not
establish "no ℓ-th power reciprocity in `ℚ(ζ_ℓ)`", since the law operates on symbols with a choice of
prime ideals and the rational projection can wash an ideal-level relation into rational independence.*

---

## 0a. ⚠ PROCESS STATUS (added on challenge — read before citing anything here)

- **NO `experiment-designer` pre-registration was written for this work.** CLAUDE.md §2 makes it
  mandatory before any "test, sweep, scan, or anomaly drill". I proceeded on an unstated judgment that
  forced-identity checks of derived algebra are none of those. **That judgment was self-authorized and
  never checked.** It is defensible only to the extent every count here is a FORCED identity derived
  before running (§1) — i.e. an instrument check, carrying no evidential weight, which is exactly how
  they are graded. **Any inferential arm still requires a prereg.**
- **Controls: one, and it does fire.** ℓ=3 is a live discriminating control on the same code (units
  non-trivial 63/200) against ℓ≥5 (trivial 200/200) — so the ℓ≥5 triviality is not a dead instrument.
  There is **no** planted-negative control for the R1–R4 reductions; they are exact identities, so a
  plant is not well-defined — but that also means nothing here would fire if the *parametrization* were
  wrong. The independent check that it is not: `e₃`, `e₄` reproduce the record's separately-verified
  forced identities.

## 0. Construction

`E: y²=x³+7 / F_p`, CM by `ℤ[ω]`, prime order `n=p+1−t`, `4p=t²+3v²`. Record's setup
(`RESULT_cubic_sextic_bridge_v1`): `π=(t+v)/2+vω`, `N(π)=p`; **`ν=1−π`**, `N(ν)=n`. Since `3∣n−1`
(record's L3), `ℤ[ω]/(ν) ≅ F_n`; since `n≡1 mod ℓ`, its elements carry an ℓ-th power symbol. As
`p=π·π̄`:  `χ_ℓ(p mod n) = χ_ℓ(π mod ν)·χ_ℓ(π̄ mod ν)`. Hypothesis: a relation between the CM factors
could cancel in the product, so the factors would be finer than the rational symbol already bounded.

## 1. Nine forced facts — **all instrument checks, not evidence**

Every one was **derived before it was run**, so per the drill protocol ("count only UNFORCED hits") a
pass confirms the implementation and carries **no** evidential weight. The content is the consequence.

| # | forced fact | ℓ=5,7,11,13 |
|---|---|---|
| **F1** | `π ≡ 1 (mod ν)` (from `ν=1−π`) ⇒ **`χ_ℓ(π mod ν) = 1` identically** | 250/250 each |
| **F2** | ⇒ **`χ_ℓ(p mod n) = χ_ℓ(π̄ mod ν)`** | 250/250 each |
| **F3** | mirror: `ν ≡ 1 (mod π)` ⇒ **`χ_ℓ(n mod p) = χ_ℓ(ν̄ mod π)`** | 250/250 each |
| **F4a** | conjugate primes: exponent w.r.t. `ζ^c` is `m·c⁻¹ (mod ℓ)` | 60/60 each |
| **F4b** | ⇒ product over all `ℓ−1` conjugate primes = 1 (`Σc⁻¹ ≡ 0`) | 60/60 each |
| **R1** | **`π̄ ≡ t−1 (mod ν)` ELEMENT-WISE in `ℤ[ω]`** | **250/250 each** |
| **R2** | **`ν̄ ≡ 1−t (mod π)` ELEMENT-WISE** | **250/250 each** |
| **R3** | ⇒ `χ_ℓ(p mod n) = χ_ℓ((t−1) mod n)` | 250/250 each |
| **R4** | ⇒ `χ_ℓ(n mod p) = χ_ℓ((1−t) mod p)` | 250/250 each |

### 1a. The factorization is degenerate

One CM factor is *trivially* 1 (F1), so `p=π·π̄` does not split the rational symbol into two informative
pieces — it **equals** the surviving factor (F2/F3). And the symbol of the *ideal* `(ν)` in
`L=ℚ(ζ_{3ℓ})`, a product over the full Galois orbit, is **forced to 1** (F4b).

### 1b. And the surviving factor is RATIONAL

`π̄ = t−π = t−(1−ν) = (t−1)+ν ≡ t−1 (mod ν)`, verified element-wise (R1). So the CM generator's residue
is a **rational integer**, and with `U=|t−1|`:

> **`χ_ℓ(p mod n) = χ_ℓ(U mod n)`  and  `χ_ℓ(n mod p) = χ_ℓ(−U mod p)`**

**Both sides of the bridge are ℓ-th power symbols of the SAME rational integer `U`, in two different
fields.** There is no ideal-level content in this route to find — not because a test returned null, but
because the CM elements reduce to rationals. (Consistent with, and sharper than, the record's
`p ≡ (t−1) mod n` / `n ≡ −(t−1) mod p`, verified 300/300 in `ell_condmi_verify_designer_v1.py`.)

## 2. Why ℓ=3 escapes — the unit layer, with ℓ=3 as a live control

The ℓ=3 correction `c₃ = s·(e(π̄′)−e(ν′))` is carried by **primarizing units** of `ℤ[ω]` (`μ₆`) plus the
**ω-supplement** `χ_λ(ω)`, a separate classical input.

> **Derived before running:** for `u∈μ₆`, `χ_ℓ(u)⁶=1` and `χ_ℓ(u)∈μ_ℓ` of prime order `ℓ`;
> `gcd(6,ℓ)=1` for every prime `ℓ≥5` ⇒ **`χ_ℓ(u)=1` FORCED**.

| ℓ | `χ_ℓ(ω)=1` | all six units trivial |
|---|---|---|
| **3** | **63/200** | **63/200** ← live (the supplement carries the bridge) |
| 5 / 7 / 11 / 13 | 200/200 | **200/200** ← forced trivial |

ℓ=3 is a discriminating control **on the same code**, so the ℓ≥5 triviality is a property of the object,
not a dead instrument. The layer carrying the ℓ=3 correction is invisible to `χ_ℓ` for ℓ≥5.

## 3. Grade

> **The CM route to an ideal-level ℓ≥5 bridge collapses to a rational symbol:** the factorization
> `p=ππ̄` is degenerate (one factor ≡1), the full-orbit ideal symbol in `ℚ(ζ_{3ℓ})` is ≡1, and the
> surviving factor reduces element-wise to the rational integer `U=|t−1|`.
> `[PROVED — forced algebra, confirmed 250/250 and 60/60]`

**What this does and does NOT re-type.** These constructions yield **no NEW test** — the ideal-level
object is the rational object, so it **inherits the existing bound and its power floor (~6%
copy-fraction)**, nothing better. It does **not** show the ℓ≥5 bridge question is void: R1–R4
*re-express* both sides; a relation between `χ_ℓ(U mod n)` and `χ_ℓ(−U mod p)` could still exist and
would appear in exactly the test already run, at exactly the power already had. **The factorization is
degenerate; the question is not.**

⚠ **Scope of the full-orbit item (F4b):** that formulation is **my own**, not the record's open item.
The prior RESULTs named the symbol *"with a choice of prime ideals"* — the **individual** symbol, which
is F2/R1. F4b being trivial refutes a formulation introduced here and must not be reported as refuting
the record's item.

## 4. Where this leaves the bridge question

Combining R1–R4 with the completed probes, the ℓ≥5 question is now stated exactly:

> Is there a relation between `χ_ℓ(U mod n)` and `χ_ℓ(−U mod p)`, `U=|t−1|`?

That is precisely the **shared-`U` congruence channel** the `experiment-designer` audit identified and
that **C-cong** was built to isolate. Measured (`RESULT_ell_ge5_conditional_MI_v1` §1): natural C-cong
**null** (`Tcond p=0.370`, N=2500, per-stratum min 475) with a **planted positive that fires**
(`p=0.0000`) — so that control had power. Marginal and conditional arms are likewise null OOS.
**Consistent picture, all at the stated power floor; not a proof of non-existence.**

## 5. ⚠ NOT established — pending the source

- **The mechanism is NOT claimed.** The tempting statement — *"ℓ-th power reciprocity is therefore
  vacuous for CM data at ℓ≥5, which explains the null"* — needs **what the classical law actually
  constrains** (ideal symbol? primary elements of `ℤ[ζ_ℓ]` only? a Hilbert-symbol expression?).
  `π̄,ν ∈ ℤ[ω] ⊄ ℤ[ζ_ℓ]` for ℓ≥5, so whether the law even *applies* is a source question.
  ⚠⚠ **The `citation-verifier` pass on Lemmermeyer Ch. 7 (the ledger's overdue item) was ATTEMPTED
  2026-07-25 and FAILED — the agent terminated early on a session limit. IT DID NOT COMPLETE. No
  statement of the law was obtained; no artifact was produced. It must be RE-RUN.** **The mechanism
  stays UNGRADED.** The forced facts (§1) stand either way — none of them depends on the source.
  - **Unverified LEAD from the failed run** (a fragment, not a finding, and not to be cited as one):
    it reported that Silverman–Stange cites **Lemmermeyer Thm 7.10, sextic reciprocity in `ℚ(ω)`** —
    relevant because `ℚ(ω)` is this curve's CM field, i.e. a law stated for **our** ring rather than
    `ℤ[ζ_ℓ]`. **Unchecked**: neither the theorem's statement nor the Silverman–Stange citation was
    verified before the agent died. Treat as a pointer to check, nothing more.
- **This closes the CM route only.** The classical law's own object — symbols of elements of `ℤ[ζ_ℓ]`,
  with a choice of prime ideal over `p,n` — is *not* covered by R1–R4, which concern `ℤ[ω]`-elements.
- **Untouched:** conditional mediators `v mod ℓ` and the second ℓ-adic digit
  (`RESULT_ell_ge5_conditional_MI_v1` §4); `ℓ≥17`; `h≥3`; non-PID `ℓ≥23`; secp's factors `149,631,…`.
- **Scope:** 26-bit `p`, `D=−3`, one twist per `p`. The facts are algebraic (scale-free by derivation);
  the counts were taken at this scale.

## 6. Prior art

No novelty claimed. `ν=1−π`, `π≡1 mod ν`, `π̄≡t−1 mod ν`, Eisenstein cubic reciprocity, the
ω-supplement, and the triviality of `μ₆` under `χ_ℓ` when `gcd(6,ℓ)=1` are elementary/classical. The
ledger's literature sweep (Lemmermeyer Ch. 7) is in progress and was never previously done.
Public data only; no leakage / ECDLP content.
