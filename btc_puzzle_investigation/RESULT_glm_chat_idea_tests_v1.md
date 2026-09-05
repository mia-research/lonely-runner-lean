# Testing the ideas in the GLM-5.2 chat (not the method) — v1

Date: 2026-07-18. Script: `scratchpad/test_glm_ideas.py` (exact integer / point-count /
formal-series tests; no dataset needed). Each claim gets a decisive number and a grade.
Grades: PROVED (exact arithmetic) · VERIFIED-INSTANCE (checked on a finite sample) ·
ASSERTED (not established) · FALSE.

## Summary
The GLM chat is a mixed bag of the exact kind it warned about: several correct
computations, one **confident "correction" that is itself wrong**, one **flatly false
closing statement**, and a genuine p-adic structure that is real but has **no F_p
readout** — so it does not touch the DLP. GLM's own mid-chat retraction ("DLP wall
built on 7") was correct, and an independent homomorphism test confirms it.

## Per-idea verdicts

| # | Idea (from the chat) | Decisive test | Verdict |
|---|---|---|---|
| 0 | "E(F_p) has order **n = p**" (stated ~4× near the end) | n − p = −(t−1), t≈2^128.35 | **FALSE.** Curve is ordinary, NOT anomalous. If n=p Smart's attack would break it. |
| 2 | Semaev S₃ `+2·7` term is a **typo** (GLM), agent's form wrong | S₃ with `+2·7` vanishes **200/200** on real P₁+P₂+P₃=O; GLM's "corrected" form **1/200** (chance) | **GLM WRONG.** The `+2·7` is the standard `+2b` term. The agent's formula was correct; GLM broke it. |
| 3 | Sextant angle law: cosθ=t/2√p, p₀=(¾)|cos2θ|/(2cos2θ+1) | cosθ=0.63538, θ=50.551°, p₀=0.23490, free₂=0.14010, Σ=1.0 | **VERIFIED.** GLM's arithmetic matches to all printed digits. |
| 5 | xy is odd-in-d, x even-in-d (equal-mass shadow) | (n−d)G=−dG ⇒ x_{n−d}=x_d, y_{n−d}=−y_d ⇒ (xy)_{n−d}=−(xy)_d | **PROVED, but trivial** — group-law involution on any odd-order Weierstrass curve. |
| 9 | a₇ = 0 (curve cusps mod 7); B=7 forces it | #E(F₇)=8 ⇒ a₇=0. disc=−2⁴·3³·**7²**·(−1) ⇒ 7 is a bad prime (additive/cusp) | **PROVED.** True — but because b=7 puts 7² in the discriminant (27·7²). Also a₅=a₁₁=a₁₇=a₂₃=a₂₉=0 = the standard j=0 supersingular-at-inert-primes CM fact. |
| 7 | Formal log L(T)=T+3T⁷+(735/13)T¹³+… ; closed form B^k C(3k,k)/(6k+1) | direct series = T+3T⁷+(735/13)T¹³+(28812/19)T¹⁹−… ; closed form matches k=0..3 | **VERIFIED-INSTANCE (k≤3).** Correct. B=7 does cancel the 7 in the k=1 denominator ⇒ integer 3. |
| 8 | ASD/Honda supercongruence 7^k C(3k,k) ≡ a_ℓ (mod ℓ), ℓ=6k+1 | holds for ℓ=13,19,31,37,43 (and degenerately at ℓ=7) | **VERIFIED-INSTANCE.** Genuine (known Atkin–Swinnerton-Dyer-type congruence for CM curves). |
| 10 | "L₁(T)=−x/y linearizes the group over F_p ⇒ the 0.93 leak" | f(P+Q)=f(P)+f(Q) mod p held **0/300** random F_p pairs | **CONFLATION.** The formal log linearizes only the KERNEL OF REDUCTION (p-adic pts ≈ O), not generic F_p points. `−x/y` is no homomorphism on F_p. No F_p readout. |
| — | ε (flap) = 0 ⟺ least residue of x² mod p < 3p/16 | not tested (needs repo's eis() lift) | **ASSERTED.** The step "N(eis(x)) ≡ x² mod p, read as the least positive residue" is asserted, not shown; N(a+π w)≠N(a)+… in general. Needs the actual lift to test. |
| — | (1−π)⁻¹ = −π in Z[ω] | ⇒ π²−π−1=0, contradicts π²−tπ+p=0 | GLM correct that the **exact** equality is false; the true object is the dual isogeny (1−π̄)/n, N(1−π)=n. Prose-interpretation issue. |

## The two things that matter
1. **The Semaev "typo" was not a typo.** GLM asserted (3× across turns, with a worked
   weight argument) that the agent's S₃ had an erroneous `+2·7`. Real curve points say
   the agent was right and GLM was wrong: the `+2b` term is standard Semaev. This is a
   clean instance of the failure GLM was diagnosing — confident wrongness in the
   particulars — landing on GLM itself. **Refuting a mechanism ≠ refuting a claim**
   (feedback_verify_external_critiques): the agent's isobaric-weight-4 story is intact.

2. **The formal-log / B=7 / ASD structure is REAL but sealed at the p-adic boundary.**
   All of it verifies. None of it produces an F_p function of the coordinates that is
   even approximately additive (0/300). The "0.93 leak explained by first-order formal
   log" narrative rests on conflating the p-adic logarithm (converges only on points
   ≡ O mod p) with a naive rational function on F_p points. Consistent with the closure
   note in the master: a cheap F_p readout aligning with e_n(a₀d) *is* the DLP; the
   formal log gives no such readout for free.

## Where this leaves the frontier (positive framing, per feedback_curve_positive_framing)
- The **CM backbone is confirmed structure**: j=0 ⇒ inert primes supersingular (a_ℓ=0),
  a genuine ASD supercongruence tying 7^k C(3k,k) to a_ℓ. This is real arithmetic to keep mapping.
- The **untested lever** is the flap↔quadratic-residue-size claim (ε ⟺ x² small). It is
  the one idea in the chat that (a) is not yet decided and (b) would, if the arithmetic
  identity held against the repo's eis(), give an F_p-computable label with arithmetic
  content. Next probe: compute N(eis(x)) mod p directly from the repo lift and test
  ε against (least residue of x² mod p < 3p/16) out-of-sample. Report as a
  characterization (POWER + SCOPE), not a verdict.
