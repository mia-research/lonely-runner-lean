# PREREG — the cubic/sextic reciprocity bridge `χ^{(n)}(p) ↔ χ^{(p)}(1−t)`

**Date:** 2026-07-24 · **Frozen BEFORE any run.** Follow-on to `RESULT_ord_n_residue_structure_v1.md`
(which left the cubic analogue of (L1) as the named next probe). Exact integers only; no float.

Object: `j=0` curve `/F_p`, `p ≡ 1 mod 3`, prime order `n = p+1−t`. `ℤ[ω]`, `ω = (−1+√−3)/2`.

---

## 0. Setup fixed now (so no choice is made after seeing data)

`4p = t²+3v²` with `t, v` odd ⇒ `π := (t+v)/2 + vω ∈ ℤ[ω]`, `N(π) = p`, `tr(π) = t`.
`ν := 1−π`, `N(ν) = 1−t+p = n`. `π̄ = (t−v)/2 − vω`, `N(π̄) = p`.

Canonical identifications (**not** free choices — forced by the ideal):
`ν = A+Bω ⇒ ω_n ≡ −A·B⁻¹ (mod n)`;  `π̄ = C+Dω ⇒ ω_p ≡ −C·D⁻¹ (mod p)`.
Characters are read as exponents: `χ₃^{(n)}(p) = ω_n^{j}`, `χ₃^{(p)}(1−t) = ω_p^{k}`, `j,k ∈ {0,1,2}`.

Primary normalization = Ireland–Rosen: `λ = A+Bω` primary iff `A ≡ 2 (mod 3)`, `B ≡ 0 (mod 3)`;
exactly one of the six unit multiples is primary when `3 ∤ N(λ)`.

## 1. Controls that MUST fire before any arm is believed

| # | control | required |
|---|---|---|
| **K0** | **Eisenstein cubic reciprocity** `χ_{ν}(π̄') = χ_{π̄}(ν')` for the primarized `ν', π̄'` | **100%.** This is a theorem; a single failure means my `ℤ[ω]` arithmetic is broken and **every arm below is void.** |
| **K1** | **Gauss:** `2` is a cubic residue mod `n` ⟺ `n = a²+27b²` | **100%** (independent check of the character machinery against a classical criterion) |
| **K2** | `χ₃^{(n)}(p) = 1` base rate over the family | `≈ 1/3`, matched to a random-base control mod the same `n` |
| **K3** | `ω_n² + ω_n + 1 ≡ 0 (mod n)` and `ω_p² + ω_p + 1 ≡ 0 (mod p)` | **100%**, per instance |

**If K0 or K1 fails, the run is reported as a machinery failure and nothing else is reported.**

## 2. Arm A — the cubic bridge (the structural target)

`π ≡ 1 (mod ν)` ⇒ `χ_ν(p) = χ_ν(π)χ_ν(π̄) = χ_ν(π̄)`. And `π ≡ t (mod π̄)` ⇒ `ν = 1−π ≡ 1−t (mod π̄)`,
so `χ_{π̄}(ν) = χ₃^{(p)}(1−t)`. Reciprocity applies to *primarized* arguments, so the two differ by
unit factors `χ_ν(u₂)`, `χ_{π̄}(u₁)`.

> **H-bridge:** `j − k mod 3` is a **deterministic function** of the primarization data
> `(u₁, u₂)` together with the residues `(A,B) mod 3`, `(C,D) mod 3`, `t mod 3`, `v mod 3` — and of
> nothing else.

**Protocol against post-hoc fitting (pre-committed):**
1. **TRAIN** on `p < 2¹⁸`: tabulate `j−k` against the frozen variable list above. Read off a rule.
2. **FREEZE** the rule verbatim into `RESULT_…` before step 3.
3. **TEST** out-of-sample on **disjoint** `p ∈ [2¹⁸, 2²²]`, then at 32/64/128/256 bits.
   Required: **100%**, zero violations. Any violation ⇒ H-bridge **FALSE as stated**.

**Falsified if:** no rule on the frozen variables predicts `j−k` on TRAIN (i.e. the same variable-cell
contains both values), or a TRAIN-fitted rule fails out-of-sample.
**Explicitly permitted outcome:** the rule needs a variable *not* on the frozen list ⇒ report as
`[OPEN — variable set insufficient]`, **not** as a discovered rule.

## 3. Arm B — unconditional cubic forcing (direct analogue of (L1))

`χ₃(−1) = 1` always, so `χ₃^{(n)}(p) = χ₃^{(n)}(|t−1|)`. With `U := |t−1| = c³·m`, `m` cubefree:

> **(i)** `m = 1 ⇒ χ₃^{(n)}(p) = 1` **forced** — required rate **exactly 1.0000**, 0 violations.
> **(ii)** density of `{U ≤ 2√p : U a cube}` `≍ (2√p)^{−2/3} ∝ p^{−1/3}` — **faster decay than (L1)'s
> `p^{−1/4}`**, so at `2²⁵⁶` it is `~2^{−85}`: predicted **absent**, and absent by derivation.
> **(iii)** excess of `χ₃ = 1` over `1/3` equals `(2/3)·P[U a cube]`, no free parameter.

## 4. Arm C — sextic closure of the original ledger item

`2 ∣ n−1` always and `3 ∣ n−1` always (**L3**, proved), so `χ₆` mod `n` is always defined and
`c_p = 6 ⟺ χ₆^{(n)}(p) = 1 ⟺ [χ₂ = 1] ∧ [χ₃ = 1]`.

> **H-sextic-bridge:** combining (L1)'s quadratic identity with Arm A gives `χ₆^{(n)}(p)` as an
> explicit function of `χ₆^{(p)}(1−t)` plus congruence/unit corrections. Test: predict `c_p` at secp
> from **p-side data only**, and check against the directly computed `c_p = 6`.

**This is the arm that matters**, because an exact identity is **scale-free** — unlike (L2)'s density
it does not decay, so it is one of the few statements in this record that reaches `2²⁵⁶` intact.

## 5. Scope, stated before the result

Both sides of the bridge are computable from **public** data (`p`, `n`, `t`). A confirmed bridge is a
**structure map, not a lever**, and must not be reported as leakage or as ECDLP-relevant. What it
would do is replace "`c_p = 6` is an unexplained draw" with an exact law.

**Prior-art caution:** cubic reciprocity, Gauss's `p = a²+27b²` criterion, and the classical link
between sextic characters and point counts on `y²=x³+b` (Ireland–Rosen ch. 18; Rajwade) are
**classical**. Anything confirmed here is to be graded `[VERIFIED — classical]` unless a literature
check says otherwise. Per the ledger's ★ item, **no originality is to be claimed for any of it.**
