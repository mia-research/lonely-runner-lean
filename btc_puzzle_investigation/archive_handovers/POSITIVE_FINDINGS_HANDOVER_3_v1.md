# Positive-Findings Handover 3 — the v5–v17 arc (secp256k1 / ECDLP)

**Date drafted:** 2026-07-16. Supersedes nothing (Handover 1 = `POSITIVE_FINDINGS_HANDOVER_v*`,
Handover 2 = `POSITIVE_FINDINGS_HANDOVER_2_v*`); this is the *next* layer.

## Stance (read first)
- ECDLP is **assumed** hard, **not proven**. Investigate for leakage; it may be subtle,
  sub-noise, hard to sift. A **fence** stays a fence until a rigorous analytical proof makes
  it a wall.
- **An empirical null does NOT close an avenue.** Only a rigorous analytical proof closes one.
- **Every claim below carries a grade.** If it is not a rigorous analytical proof it is marked
  `[VERIFIED-scope]`, `[EMPIRICAL]`, `[HEURISTIC]`, or `[CITED]`. Nothing drifts up a grade.

---

## ★ THE CENTRAL RESULT OF THIS ARC — the leakage question is COMPUTATIONAL, not information-theoretic

This reframes everything, including all prior handover "nulls".

Write `T(a,b)=Σ_d e_p(b·x([d]G))·e_n(a·d)` and, for a readout `F`,
`Corr(a)=(1/n)Σ_d F(x_d)e_n(-ad)=(1/n)Σ_b F̂(b)T(a,b)` (exact Fourier expansion).

1. **[PROVED, by construction] The leaking readout EXISTS.** The *aligned* readout
   `F̂(b):=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation: `Corr(a₀)=(1/n)Σ_b|T(a₀,b)|`.
   **[VERIFIED]** measured `|Corr|/‖F‖_∞ = 0.37` (x-only) rising to **0.93 for the joint (x,y)
   readout** — vs `~0.01` for a generic readout (**28×+** above the noise floor), stable in p.
2. **⇒ There is NO information-theoretic barrier.** The information about `d` is fully present
   and recoverable by a *bounded* readout of the public key. **Only computability protects the
   curve:** building the aligned `F̂` requires `T(a,b)`, i.e. the whole sequence `x_d` — i.e. the DLP.
3. **⇒ Every "null" in this whole investigation used a MISALIGNED readout.** And **[CITED: Weil /
   Kohel–Shparlinski]** guarantees a misaligned readout sees *exactly* `√p` noise. So "we measured
   `√p`, therefore generic" was evidence about **the instrument, not the curve** — provably.
4. **⇒ "No leakage" is not provable information-theoretically.** Only computational hardness can
   protect. Any future null must be stated as *this readout class, at this scale*.
5. **[PROVED] Phase alignment is the SOLE axis** (Wiener norm was a red herring): `χ₂` saturates
   the `‖F‖_A ≤ √p·‖F‖_∞` ceiling (100%, via Gauss sums) and provably does **not** leak; the
   aligned readout sits at **36%** of the ceiling and does. High Wiener norm is neither necessary
   nor sufficient — only phase-match to `T` determines leakage.
6. **[PROVED] L² methods cannot close the question.** Parseval `Σ_a|Corr|²≤‖F‖_∞²` is *saturated*
   by a perfect leak; exact identity `Σ_b|T(a,b)|²=p(n−2)` (a≠0) makes Cauchy–Schwarz vacuous.

> **Bottom line of the arc:** the secp curve does not hide `d` by destroying information — it
> hides `d` behind the cost of finding the aligning key. The needle is not *in* the noise; it
> *is* the noise, viewed without the aligning key. (Files: `phase_structure_T_v1.py`,
> `aligned_scaling_and_gap_v1.py`, `masked_structure_findings_v14/v15.md`.)

---

## PROVED (rigorous analytical)

- **Cap Law** `[PROVED — Theorem A, cap_law_proofs_v1.md]`: `ε(x)≠0 ⟺ |u−v|>½` (long-diagonal
  caps). *Proof:* `ω` is an order-3 automorphism of the ideal `L=(π_p)` with basis-independent
  `tr=−1, det=1` (⇒ `M²+M+I=0`); `L` is hexagonal so a reduced basis is two shortest vectors at
  120°, forcing `M=[[0,−1],[1,−1]]`; then `ε=0 ⟺ ω²z∈P ⟺ |u−v|≤½`. (No longer relies on the
  empirical "fixed matrix" observation — it is forced by the hexagonal geometry.)
  **Consequence [PROVED]:** ε, norm-band, and the frame operator are
  functions of the lift coefficients `(u,v)` only ⇒ they **reduce to the single map `x↦(u,v)`**
  and carry *no arithmetic of their own*. The shape constants (½, ¾, 33, 3/16, 1/4, 1/6) are
  θ-independent lattice geometry with **zero secp arithmetic content**.
  (`btc_puzzle_cap_law_2026_07_16.md`, `_findings_v1–v4.md`.)
- **GLV μ₃ zero** `[PROVED + VERIFIED]`: `Σ_d ψ(d)·χ₃(x_d)·s_y(d)=0` exactly — `β` fixes `y` and
  shifts `χ₃(x)` by `ζ₃`, `d↦λd` is a bijection ⇒ `S=ψ(λ)ζ₃S ⇒ S=0`. Any (cubic-χ-of-x)×(fn-of-y)
  readout is annihilated by GLV.
- **σ ⊥ s_y exactly** `[PROVED]`: `Σ_d σ(x_d)s_y(d)=0` (σ even in d, `s_y` odd ⇒ product odd,
  `d↔n−d` cancel). The cancellation is **fixed-point-free** — impossible at `2d=n` since `n` is
  odd/prime — so it is exact *because prime order forbids the 2-torsion endpoint*.
- **Complete symmetry group of `U(a,b,c)=Σ_d e_p(bx_d+cy_d)e_n(ad)`** `[PROVED + VERIFIED exact]`:
  `U(−a,b,c)=U(a,b,−c)` (x even, y odd) and `U(a,b,c)=U(aλ,bβ,c)` (GLV). `T=U(·,·,0)` is even in
  a ⇒ **sees only the even half of the d-spectrum; the odd half requires the y-coordinate.**
- **`Σ_b|T(a,b)|²=p(n−2)` (a≠0), Parseval, and `‖F‖_A≤√p·‖F‖_∞`** — all `[PROVED]` (see central result).
- **Amicable correspondence** `[PROVED + VERIFIED on (907,967)]`: `E(F_p)≅ℤ[ω]/(π_p−1)≅F_n`
  (partner's field **is** the CM coordinate ring); `π_n=1−π_p`. The coordinate map `φ:E(F_p)→F_n`
  **is** the DLP (`φ([d]G)=d`), so the exact correspondence transfers **no** computational advantage.
- **Semaev `S_3` geometry** `[PROVED, general p]`: `S_3` irreducible/ℚ; `β`-weight 1 for `a=0`
  (monomial degrees ≡1 mod 3); discriminant `Δ(t)=c(t³+7)⁴` ⇒ `C_t:S_3(x_1,x_2,t)=0` is singular
  ⟺ `t` is a 2-torsion x-coord ⇒ **prime order ⇒ no 2-torsion ⇒ `C_t` smooth genus-1 for every
  target.** *(The step "genus-1 ⇒ no index-calculus lever" is `[HEURISTIC]`, not proven — see below.)*

## VERIFIED-scope (exact, but at tested primes / not a general-p proof)

- **The joint (x,y) shadow is REAL** `[VERIFIED, stable p=163,433]`: aligned `|Corr|/‖F‖_∞` =
  **0.93 joint vs 0.34 x-only (~2.8×)**. Mechanism: an x-readout is even in d ⇒ can only align
  with the *even* projection of `e_n(a₀d)` (ceiling ~0.34); the y-coordinate supplies the **odd
  half**, ~tripling the extractable correlation. **This is the "shadow information" — present in
  the (x,y) interaction, invisible to either coordinate's marginal — made quantitative.** Still an
  *aligned* readout ⇒ same computational barrier. (`_findings_v16.md`, `xy_interference_U_v1.py`.)
- **σ (flap ±) is μ₃-invariant** `[PROVED — Theorem B, cap_law_proofs_v1.md; Lemma C now PROVED
  ⇒ UNCONDITIONAL]`: `R=(z↦ωz mod L)` has order 3 and fixes `flap = P∖(P∩ωP∩ω²P)` setwise; the flap has
  exactly 2 caps; an order-3 permutation of 2 objects is trivial ⇒ R fixes each cap ⇒ `σ(βx)=σ(x)`.
  With `σ(−x)=−σ(x)`, σ is exactly the μ₂-isotypic (sign) part of the μ₆=Aut(E) action.
- **Reduction = automorphism factor only** `[VERIFIED]`: `Inv(F)={k:F(x_{kd})=F(x_d)∀d}⊆μ₆` for
  every geometric readout (ε→μ₆, sextant/norm→μ₂, y-parity→μ₃); **none larger than μ₆** ⇒ the only
  cheaply-usable **reduction of "what D could be" is `|Aut|≤6`** (the √6 Pollard-ρ speedup).
  (`_findings_v17.md`, `reduction_invariance_spectrum_v1.py`.)
- **`avg_a|U(a,b,c)|²=n` for all (b,c)** `[VERIFIED + derivable]`: the odd half cancels at √n on
  average, same as the even half.
- **Small amicable pairs exist**: (67,79), (907,967), (1249,1303), (2089,2143) — structurally
  identical to secp `[VERIFIED]`.

## EMPIRICAL nulls (matched-null + scaling — SCOPED, do NOT close anything)

**Critical caveat (from the central result): every one of these used a *misaligned* readout, so
each is a scoped fact about that readout at that scale, provably consistent with a hidden aligned
leak.** Hybrid sum `χ_k`×additive ≈2√p; scalar-mult `ψ(d)`; cubic-moment / S3 tensor; bilinear
difference-set (powered to 1.4%); joint (x,y) *magnitude* distribution (CM=non-CM); 3-point group
law / collinearity; index-calculus relation yield (β-invariant lever 1.5×, bounded) and S₄/S₅
decomposition (β-lever → 1.0); easy-target predictability (no lever); phase hunt of `arg T` (9
CM/Frobenius candidates, all null — the only *known* computable phase structure is the μ₆ symmetry group).

## HEURISTIC (plausible, NOT proven)

- "**genus-1 ⇒ no index-calculus lever**" — the standard prime-field heuristic; not a theorem.
- The aligned-leak scaling `~1/√log p` (⇒ ~c/13 at secp, only *logarithmic* decay) — `[PARTIAL]`,
  the data drift downward (0.85→0.73) over too small a p-range; consistent but **unconfirmed**.
- **T_y / odd-half max-boundedness** — only the *average* `|U|²=n` is shown; that `max_a|U(a,b,c)|`
  is `O(√p·polylog)` **uniformly over all (b,c)** is not verified. If some exceptional `(b,c)` fails
  to cancel, that is structure the average hides. **This is a live un-bounded corner.**
- The canonical-**lift** obstruction (xedni) protecting the amicable transfer — heuristic, not proven.

## CITED (from literature — VERIFY before relying)

- Kohel–Shparlinski `|T(a,b)|=O(√p·polylog)` (the bound underwriting "misaligned ⇒ √p noise").
- Xedni-calculus lift obstruction (Silverman 1998; Jacobson–Koblitz–Silverman–Stein–Teske 2000).
- Boneh–Shparlinski (LSB of d is an ECDLP hardcore predicate).

## RETRACTED this arc (grade-discipline in action — recorded so they are not re-claimed)

- χ₂ "doubling transport law" → the **textbook duplication formula** (x(2P) is a rational function
  of x alone for any short-Weierstrass curve). CITED, not a finding.
- Test-A cubic-moment "null" → **zero statistical power** (N=82 needs f=1.0 to detect anything).
- G "tested the blind corner" → tested a **proxy** (`d mod k`, an already-known-null hardcore bit).
- v11 amicable "wall" → **strawman**; only the group-*homomorphism* case was ruled out (coprime
  orders), which is not even the mechanism any transfer uses.
- v14 "the ‖F‖_A gap is the only analytic door" → **wrong**; Wiener norm is a red herring (v15).
- v17 "6–7σ soft shadow" → a **null-mismatch artifact** (a shuffle null that destroyed the
  μ₆-invariance the readout has by definition). Against the correct μ₆-invariant null, z≈0.

## OPEN frontiers (where to look — un-shut)

1. **A *cheap partial* version of the joint (x,y) shadow.** The full aligned readout needs `T` (=DLP),
   but the y-sign bit is free and the joint shadow is real (0.93). Can a cheap readout capture a
   *fraction* of that alignment? This is the one object found this arc where "compute a bit of the
   shadow cheaply" is not immediately circular. **Highest-value lead.**
2. **The odd-half / T_y max-bound** (see HEURISTIC) — an exceptional non-cancelling `(b,c)` would be
   real structure. No literature bound is known to cover the y-twisted sum.
3. **Non-homomorphic amicable map** — only the homomorphic case is ruled out; the CM relation
   `π_n=π_p−1` as a *non-group-hom* correspondence is unanalyzed.
4. **`S₄⁺` elimination / first-fall-degree** (real index-calculus bottleneck) — heavier than anything
   this arc; `S₃`/`S₄`/`S₅` yield-counting is generic, but the Gröbner structure is untouched.
5. Everything at **secp's actual p** — all scaling here is small-to-moderate p; a structure that
   only switches on near `2²⁵⁶` would not show.

## METHOD lessons earned (expensively) this arc

- **Phase alignment, not magnitude/Wiener-norm, is the leakage axis.** Re-orient hunts to it.
- **A null needs a matched null that carries the object's symmetry.** A shuffle that breaks an
  intrinsic invariance manufactures 6–7σ phantoms (v17); zero-power nulls prove nothing (Test-A);
  the control-row/null must match the structure of the object.
- **Grade every positive; a heuristic conclusion attached to a proved fact taints the fact.**
- **Naming the right test ≠ running it** (the proxy trap, G).
- **An empirical null is scoped, never a closure.** Especially now: all our nulls are misaligned-readout facts.

## File map
Findings: `masked_structure_findings_v1–v17.md`. Scripts: `phase_structure_T_v1.py`,
`aligned_scaling_and_gap_v1.py`, `xy_interference_U_v1.py`, `reduction_invariance_spectrum_v1.py`,
`cm_amicable_correspondence_v1.py`, `summation_poly_structure_v1.py`, `hybrid_char_sum_v1.py`,
`flap_sign_parity_v1.py`. Nested memory index: `memory/btc_puzzle_INDEX.md`.
