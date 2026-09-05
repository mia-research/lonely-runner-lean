# Findings v14 — the leakage question is COMPUTATIONAL, not information-theoretic

**Date:** 2026-07-16 · Script `phase_structure_T_v1.py`. Object: the DLP-relevant twisted sum
`T(a,b) = Σ_d e_p(b·x([d]G))·e_n(a·d)` (field frequency × SCALAR frequency), and
`Corr(a) = (1/n)Σ_d F(x_d)e_n(-ad) = (1/n)Σ_b F̂(b)T(a,b)`.

Standard: **proof = analytical rigor.** Numerics here CHECK the algebra; they are not the proof.

---

## 1. [PROVED] L² methods cannot close the leakage question

- **Parseval (unconditional):** `Σ_a |Corr(a)|² = (1/n)Σ_d|F(x_d)|² ≤ ‖F‖_∞²`.
  ⇒ leakage is **sparse in frequency**: at most `1/ε²` frequencies have `|Corr|≥ε`.
  **But it is SATURATED by a perfect leak** (`c_d = e_n(a₀d)` gives `Corr(a₀)=1`, energy 1).
  So Parseval **cannot** prove absence of leakage. [numerics: exact match 0.994975]
- **Exact identity [derived + verified]:** for `a≠0`,
  > `Σ_b |T(a,b)|² = p(n−2)`
  (from `Σ_b e_p(b·δ) = p·[δ=0]` and `x_d=x_{d'} ⟺ d'=±d`; the `d'=−d` pairs contribute
  `Σ_{d≠0}e_n(2ad) = −1`, **not** 0). *A first draft said `p(n−1)`; the numerics caught the
  slip — ratio 1.000000 at a=1,2,7 after correction.*
- **⇒ Cauchy–Schwarz is vacuous:** `|Corr(a)| ≤ (Σ_b|F̂|²)^½(Σ_b|T|²)^½/n ≤ √(p(n−2))/n ≈ 1`.

**Net:** a whole proof strategy (second-moment / L²) is ruled out. Only an L^∞ (Weil-type)
bound on `T(a,b)` **plus** a small Wiener norm `‖F‖_A` closes anything — leaving the
high-norm gap untouched.

---

## 2. [PROVED + VERIFIED] μ₃ symmetry in the frequency plane

`d ↦ λd` (λ³=1 mod n) is a bijection sending `x_d ↦ βx_d`, hence
> **`T(a,b) = T(aλ, bβ)`** — exact.

[verified: max |diff| = 1.5e-14 = roundoff; λ=92, β=196 on `y²=x³+7 / F_211`, n=199 prime]
This is the **one computable phase pattern** we know in `T`.

---

## 3. ★ [PROVED + VERIFIED] The leak EXISTS — the barrier is computability, not information

Construct the **aligned readout**: `F̂(b) := conj(T(a₀,b))/|T(a₀,b)|` (unit modulus, `F̂(0)=0`).
Then by construction there is **no cancellation**:
> `Corr(a₀) = (1/n)Σ_b F̂(b)T(a₀,b) = (1/n)Σ_b |T(a₀,b)|`

**Measured (p=211, n=199):**

| readout | \|Corr(a₀)\|/‖F‖_∞ |
|---|---|
| **aligned** | **0.3668** |
| random-phase (generic) | 0.0129 |
| **ratio** | **28.4×** |

**Consequences (this is the headline):**
1. **The information about `d` is fully present and recoverable by a bounded readout.** There
   is **no information-theoretic barrier** whatsoever. Only **computability** protects the
   curve: building `F̂` requires `T(a,b)`, i.e. the whole sequence `x_d` — i.e. the DLP.
2. **It reframes every null in this programme.** All our probes used *misaligned* readouts,
   and Weil *guarantees* a misaligned readout sees exactly `√p` noise. So "we measured √p,
   therefore generic" was never evidence about the curve — it is evidence about the
   instrument, provably.
3. **"No leakage" is not provable information-theoretically** — only computational hardness
   can protect. Any future null must be stated as: *this readout class, at this scale.*

**Scaling caveat [ESTIMATE, unverified]:** `Corr ≈ c√p` while `‖F‖_∞ ≈ √(p log p)`, so the
aligned ratio should decay only like `1/√log p` (~c/13 at secp) — astronomically above the
`2^-128` noise floor, and only *logarithmically* decaying. **Not verified across p.**

---

## 4. [EMPIRICAL, thin — closes nothing] The phase hunt

Is `arg T(a,b)` predictable beyond the μ₃ symmetry?

| test | value | uniform null |
|---|---|---|
| circular mean \|R\| | 0.00498 | 0.00490 |
| phase vs `a·b mod p` | 0.00336 | 0.00490 |
| phase vs `a+b` | 0.00630 | 0.00490 |
| phase vs `a·b²` | 0.00217 | 0.00490 |

All at the null ⇒ no simple computable pattern found. **Scope: 3 candidate functions, ONE
prime (p=211).** The space of computable functions is vast; this is a thin search and it
**does not close** the phase-pattern question. It is where the leak must live.

---

## 5. Where this leaves the programme

**The leakage question is now stated exactly:** the leaking readout provably exists; it is
the phase-aligned one; leakage ⟺ *a computable* `F̂` whose phases match `T(a,b)`'s. The
known computable pattern is the μ₃ symmetry (§2), which is not enough. **Open, un-closed:**
any other computable phase structure in `T(a,b)`.

This is the honest form of "leakage exists but is hard to sift": **it is not hidden in noise —
it IS the noise, viewed without the aligning key.**

Next rigorous targets:
- verify the `1/√log p` scaling of the aligned leak across p (cheap; makes §3 quantitative);
- widen the phase hunt (larger p, richer candidate families, and the CM/Frobenius-derived
  candidates rather than ad-hoc `a·b`-type guesses);
- the `‖F‖_A ≳ √p` gap in the closure theorem — the only analytic door left open.
