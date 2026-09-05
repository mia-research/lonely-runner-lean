# Closure theorem for single-coordinate lift readouts (v1, 2026-07-14)

**Goal.** Convert the four converging *empirical* nulls ("single-coordinate lift
readouts of `x([d]G)` do not leak the scalar `d`") into a **proved fence-panel**:
a rigorous bound showing every bounded-complexity readout decorrelates from `d` at
rate `O(p^{-1/2+o(1)})`. This is the "prove the panel solid — equally valid"
direction. Status tags per project convention (PROVED / VERIFIED / CITED / GAP).

Numerical anchors in `glv_closure_verification_v1.py` (small `y²=x³+7` curves of
prime order, p=13..97): `max|T|/√p ≲ 0.5 log p` and sextant/norm-band Wiener norm
`≈ 0.65 log p` — both inputs confirmed.

---

## 1. Setup and definitions

`E/𝔽_p : y²=x³+7`, `#E(𝔽_p)=n`, `G` a generator, `x(·)` the x-coordinate on
`E∖{O}`. `d ↦ [d]G` is a bijection `ℤ/nℤ → E(𝔽_p)`; `x([d]G)=x([n−d]G)`.
For `F:𝔽_p→ℂ` and `g:ℤ/nℤ→ℂ` define the **Wiener norms**
   `‖F‖_A = Σ_b |F̂(b)|`,  `F̂(b)=(1/p)Σ_x F(x) e_p(-bx)`;   likewise `‖g‖_A`.
A **readout** of the point is `F(x([d]G))`; a **target** is `g(d)`. "Bounded
complexity" ≡ `‖F‖_A = p^{o(1)}` (holds for all readouts we ever tested — §5).

The **twisted sum**  `T(a,b) = Σ_{d=0}^{n-1} e_p(b·x([d]G)) · e_n(a d)`.

## 2. Key input  **[CITED — Kohel–Shparlinski]**

> **Theorem (KS).** For `(a,b) ≠ (0,0)` with the curve/coordinate sum nondegenerate,
> `|T(a,b)| ≤ C · p^{1/2+o(1)}`, with `C` absolute.

Kohel & Shparlinski, *On exponential sums and group generators for elliptic curves
over finite fields*, ANTS-IV, LNCS 1838 (2000) 395–404; see also Shparlinski,
*Cryptographic Applications of Analytic Number Theory* (2003), Ch. 6 — the mixed
sum of an additive character of the coordinate against an additive character of the
group index has square-root cancellation over the full group. **[VERIFIED]** here:
`max_{(a,b)≠0}|T|/√p` stays `O(log p)` over p=13..97 (0.97→2.66), never `√p`-scale.
(The pure cases are covered: `T(a,0)=0` for `a≠0` by orthogonality; `T(0,b)` is the
x-coordinate character sum, also `O(√p)`.)

## 3. Reduction  **[PROVED]**

> **Lemma R.** For any `F,g`,
> `|Cov_d(F(x([d]G)), g(d))| ≤ (max_{(a,b)≠(0,0)}|T(a,b)| / n) · ‖F‖_A · ‖g‖_A.`

*Proof.* Expand `F=Σ_b F̂(b)e_p(bx)`, `g=Σ_a ĝ(a)e_n(ad)`. Then
`(1/n)Σ_d F(x([d]G))g(d) = Σ_{a,b} F̂(b)ĝ(a)·T(a,b)/n`. The `(a,b)=(0,0)` term is
`E[F]·E[g]`, so the covariance is the sum over `(a,b)≠(0,0)`. Terms with `b=0,a≠0`
vanish (`T(a,0)=0`). Bound the rest by `|F̂(b)||ĝ(a)|·max|T|/n` and sum: the double
sum of `|F̂(b)||ĝ(a)|` is `‖F‖_A‖g‖_A`. ∎

**Corollary (Main bound).** `|Cov_d(F(x([d]G)),g(d))| = O(p^{-1/2+o(1)})·‖F‖_A‖g‖_A`,
since `n = p+1−t = p(1+o(1))` and `max|T|=O(p^{1/2+o(1)})` by [KS]. So **no
bounded-Wiener readout correlates with any bounded-Wiener target of `d` beyond
`O(p^{-1/2+o(1)})`.** For secp `p≈2^{256}` this is `≤ 2^{-128+o(1)}` — a hard,
not-empirical, decorrelation.

**MI corollary.** For finite-valued `F,g`, `MI(F(x([d]G));g(d)) ≤ C'·‖F‖_A²‖g‖_A²·
p^{-1+o(1)}` via `MI ≤ (2\ln2)^{-1}χ²` and `χ² = Σ_{modes}|correlation|²` with each
mode `O(p^{-1/2+o(1)})` (Lemma R applied per character pair). Negligible.

## 4. Readout classes

**Class C1 (character-class) — [PROVED, given KS].** Any multiplicative character
`χ_k`, any additive character `e_p(bx)`, or an `O(1)`-term combination: `‖F‖_A=O(1)`.
⇒ `Cov = O(p^{-1/2+o(1)})`. This **subsumes** the `χ₆`-uniformity law, the GLV
character shifts, and every multiplicative single-`x` null — now theorem-backed.

**Class C2 (geometric lift readouts) — [given KS + Lemma W].** sextant, the μ₃-orbit
label ε, norm-band bucket, `k×k` fundamental-domain cell: each is `F(x)=Φ(eis(x))`
for a bounded-resolution `Φ` on the rhombus `P`. Need `‖F‖_A = p^{o(1)}`:

> **Lemma W.** `‖1_{sector}∘eis‖_A = O(log p)` (and same for norm-band / bounded cells).
>
> *Proof sketch.* Via the `eis` bijection `𝔽_p ≅ ℤ[ω]∩P`,
> `F̂_s(b)=(1/p)Σ_{(u,v)∈S_s∩P} e_p(-(bu+b'v))`, `b'=bω_p mod p`
> (`ω_p` the image of ω). The sector `S_s∩P` is a lattice **triangle** with edges
> along ℤ[ω]-directions (the reduced basis = unit associates of `π_p`). Iterating
> the 2-D sum along one lattice edge gives, per row, a geometric sum
> `= O(1/‖c/p‖)`; summing the rows gives a second geometric factor; corners
> contribute `O(1)`. Then `Σ_b|F̂_s(b)| = O(p^{-1}·Σ_{c}1/‖c/p‖) = O(log p)` by the
> divisor/`Σ 1/‖c/p‖ ~ p\log p` estimate. ∎ (sketch)
>
> **Status: [VERIFIED empirically] O(log p)** (sextant `≈0.65 log p`, norm-band
> `≈0.65 log p`, p=13..97, monotone, never `√p`). **[GAP]** the full edge/corner
> accounting (standard lattice-polytope harmonic analysis; Brion–Barvinok /
> classical Hardy–Littlewood) is not written out to full rigor here.

Given Lemma W, `Cov = O(p^{-1/2+o(1)})` for all Class-C2 readouts.

## 5. What this closes, and what it deliberately does not

**Closed (proved panel, modulo [KS] cited + Lemma W verified).** The four empirical
nulls this week are single-key coordinate-vs-scalar or bounded-Wiener readouts:
- **two-domain residue** (`sextant/eps of eis_p(x([d]G))` vs labels of `d`) — a
  Class-C2-vs-C2 instance, now bounded by the Main Corollary. Its N=90k null is
  theorem-backed, not just measured.
- **multiplicative single-x** nulls — Class C1, subsumed.

**Not covered (the sharpening — where the gate can still be).**
- **Joint/multi-key readouts.** Lemma R bounds a *single* sum over one `d`. A readout
  of the *set* `{x([d_i]G)}_i` across many independent keys is a bilinear/multilinear
  sum, outside [KS] as stated. The stance-memory principle ("only a joint property of
  the SET can survive the scramble") is exactly the complement of this closure.
- **The addition-law panel** (independent `P,Q`; §1–§3 of the addition findings) is
  the *two-point* analogue: it needs a bound on `Σ_{d_P,d_Q} F(x([d_P]G),x([d_Q]G),x_S)`
  where the group law couples the three via `S₃=0`. That bilinear sum is **[GAP —
  named]**: analogous to Main, but requires a two-variable KS-type bound, not proved
  here. (Its empirical null stands; only the *proof* is pending.)
- **Generation side** (the RNG that selected the puzzle keys) — entirely outside; this
  theorem is about the curve map `d↦x([d]G)`, not key selection.

## 6. One-line status

**PROVED** (Lemma R, Class-C1 corollary) **+ CITED** (Kohel–Shparlinski `√p` bound)
**+ VERIFIED** (both anchors, and Lemma W's `log p` growth) **⇒** every
bounded-Wiener single-coordinate lift readout decorrelates from `d` at
`O(p^{-1/2+o(1)})` (`≤2^{-128}` at secp scale). Remaining rigor: full write-up of
Lemma W; the two-point (addition) and multi-key (joint-set) extensions are named
open bilinear problems — which is precisely where the search should now concentrate.
