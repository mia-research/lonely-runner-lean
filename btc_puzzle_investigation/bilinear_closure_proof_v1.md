# Analytical closure of the joint-SET / difference / bilinear frontier

**Date:** 2026-07-17. *"Empirical exhaustion is an oxymoron — close it analytically."* Correct. This
replaces the powered nulls (v28/v30/v31/v32) with a **theorem**: the entire two-point / difference /
multilinear channel is bounded, given the same Kohel–Shparlinski (KS) input the closure programme
already assumes. It also closes the `glv_closure_theorem_v2 §7` named gap (the two-point/addition
panel) at the correlation level.

Setup: `E/𝔽_p`, prime order `n`, generator `G`, bijection `d ↔ [d]G`; `P_u := [u]G`. For a coordinate
readout `A = e_p(b x + c y)` (or any `e_p` of a rational function of pole order `≤ D`), write
`Â(k) := Σ_{u∈ℤ/n} A(P_u) e_n(-ku)`.

**KS input `[CITED — general-f Kohel–Shparlinski / Lange–Shparlinski]`.** For `A = e_p(f)`, `f` a
nonconstant rational function on `E` of bounded degree, `|Â(k)| ≤ M`, `M = O(p^{1/2}(\log p)^{O(1)})`,
**uniformly in `k` and in the coefficients of `f`** (the constant depends only on `deg f`). *(Item #2 /
`masked_structure_findings_v21`: `bx+cy` has pole order ≤3, so this applies to every xy-harmonic.)*

---

## Lemma (Fourier factorization) `[PROVED — exact, verified 1e-13]`
Let `A, B, C: E → ℂ` be readouts and
`S(a,b) := Σ_{u,v∈ℤ/n} A(P_u)·B(P_v)·C(P_{u+v})·e_n(au+bv)` (the two-point sum coupled through the
group law). Then
> **`S(a,b) = (1/n) Σ_{m∈ℤ/n} Ĉ(m)·Â(-(a+m))·B̂(-(b+m))`.**

*Proof.* Expand `C(P_w) = (1/n)Σ_m Ĉ(m) e_n(mw)` at `w=u+v`:
`S = (1/n)Σ_m Ĉ(m)[Σ_u A(P_u)e_n((a+m)u)][Σ_v B(P_v)e_n((b+m)v)] = (1/n)Σ_m Ĉ(m)Â(-(a+m))B̂(-(b+m))`. ∎
*(The `P_{u−v}` (difference) coupling gives the same identity with a sign flip; sums and differences
are both covered.)* **Verified:** identity holds to `1e-13` (roundoff) at every tested `(a,b)`,
`p = 127…1669`; each `|Â|,|B̂|,|Ĉ| ≈ 2.5√p`.

## Theorem B (bilinear closure) `[PROVED given KS]`
With `A,B,C` as in the KS input,
> **`|S(a,b)| ≤ M³ = O(p^{3/2}(\log p)^{O(1)})`, uniformly in `(a,b)`.**

*Proof.* Triangle inequality on the Lemma: `|S| ≤ (1/n)·(Σ_m 1)·max|Ĉ|·max|Â|·max|B̂| ≤ (1/n)·n·M³`. ∎
**Verified:** `max_{a,b}|S|/p^{3/2} = 0.28, 0.16, 0.13, 0.09` (p=127…1669) — below the bound and
*decreasing* (the true size is `O(p·polylog)`; `O(p^{3/2})` is the rigorous bound and it suffices).

## Corollary B1 (no bilinear / difference-set handle) `[PROVED given KS]`
The **normalized** bilinear correlation is
`|S(a,b)| / n² = O(p^{-1/2 + o(1)}) → 0`.
A joint-SET handle would need correlation bounded away from 0 (i.e. `|S| ≳ n²`); Theorem B forbids it
by a factor `p^{1/2}`. The objects tested empirically — the **addition-coupled sum** (v28), the
**xy 2-cocycle defect** `xy(P+Q)−xy(P)−xy(Q)` (v30), and the **difference-set character moments**
(v32) — all have the form `A(P)B(Q)C(P±Q)`, hence **each is `O(p^{-1/2})` — the noise floor — RIGOROUSLY**.
This *proves* what those runs measured, and closes the `§7` two-point/addition gap at the correlation
level. **No two-point/difference joint-SET readout leaks a non-negligible correlation with `d`.**

## Corollary B2 (the `H²` carry is not coordinate-detectable) `[PROVED given KS]`
The addition carry `c(u,v)=[d_P+d_Q ≥ n]` (the nontrivial `H²(ℤ/n,ℤ/n)` class, v31) is a step-type
indicator whose **Wiener norm is small**: `‖ĉ‖_1 = Σ_{a,b}|ĉ(a,b)| = O(\log n)` `[VERIFIED: ‖ĉ‖_1 =
5.2, 6.1, 6.9, 7.7, 8.1 at n=127…2557, i.e. ≈ log n; standard for a threshold/sawtooth]`. For any
coordinate readout `f=A(P)B(Q)C(P+Q)`, Theorem B gives `|f̂(a,b)| = |S(a,b)|/n² = O(p^{-1/2})` uniformly,
so by Parseval and Hölder
`|Corr(f,c)| = |Σ_{a,b} f̂(a,b)\overline{ĉ(a,b)}| ≤ (max_{a,b}|f̂(a,b)|)·‖ĉ‖_1 = O(p^{-1/2}\log p) → 0`.
**The carry / comparison is not leaked by the coordinates — proved** (given KS + the elementary
`‖ĉ‖_1=O(\log n)`), confirming v31's control-fired null. *(A first draft claimed `ĉ` was
diagonal-supported — false, ~38% of its mass is off-diagonal; the correct bound uses `‖ĉ‖_1`, not the
spectral shape.)*

## Corollary B3 (higher multilinear is *more* closed) `[PROVED given KS]`
The `m`-point coupled sum `S(a₁,…,a_m)=Σ_{u₁…u_m} A₁(P_{u₁})…A_m(P_{u_m})C(P_{u₁+…+u_m})e_n(Σ aᵢuᵢ)`
factorizes into `m+1` KS factors: `|S| ≤ M^{m+1}`, normalized correlation
`M^{m+1}/n^m = O(p^{-(m-1)/2})`. So `≥3`-key / multilinear objects are suppressed by *higher* powers of
`p^{-1/2}` — a fortiori closed. (The `≥4`-key Semaev-relation / additive-quadruple question, v32, sits
here.)

## Theorem A (cocycle rigidity) `[PROVED — unconditional, restated from v31]`
On prime-order `E`, the only readout with `f(P+Q)=φ(f(P),f(Q))` and `2 ≤ #values(f) ≤ n−1` is none:
the level sets would form a group congruence = cosets of a subgroup, but prime order has no proper
subgroup. **The unique additively-chaining readout is `d` itself (the DLP).** This is the exact-cocycle
statement; Theorem B is its quantitative (approximate-correlation) companion.

---

## What is now closed, and what is not
**CLOSED (proved, given KS):** the entire joint-SET / two-point / difference / multilinear / carry
channel — every such readout has correlation `O(p^{-(m-1)/2}) → 0`. This is an analytical closure, not
an empirical exhaustion: no such handle *exists* (not merely "was not found"). Theorem A closes the
exact-chaining route unconditionally.

**NOT closed (and Theorem B does not touch it):** the **single-index** aligned-readout crux (v14) —
`Corr(a₀)=(1/n)Σ_b F̂(b)T(a₀,b)` with `F̂ = conj(T)/|T|`. That readout achieves full correlation but is
`m=1` (no coupling), so the factorization/suppression does not apply; it needs `T` itself ⇒ the DLP.
This is the residual **computational** barrier (information present, needs `d` to read), and it is not
a joint-SET object — so the frontier the user flagged (difference-set / multilinear) is closed, while
the single-key aligned readout remains exactly the DLP.

## Grades
- Lemma (factorization): **PROVED** (exact identity, verified 1e-13).
- Theorem B + B1/B2/B3: **PROVED given KS** (the same cited input as `glv_closure_theorem_v2`); the
  Fourier reduction to KS is the new rigorous content. Empirically confirmed (`|S|/p^{3/2} ≤ 0.28`).
- Theorem A: **PROVED, unconditional**.
- The tight `O(p)` (full 2-D cancellation) bound is **OPEN** but **not needed** — `O(p^{3/2})` already
  drives the correlation to the `p^{-1/2}` floor.
- Single-index aligned-readout crux: **OPEN = the DLP** (computational, per v14; not a joint-SET object).

## Files
`difference_set_closure_verify_v1.py` (factorization identity + `p^{3/2}` bound check). Depends on the
KS input (`masked_structure_findings_v21`, `glv_closure_theorem_v2`). Supersedes the *empirical* joint-SET
nulls (v28/v30/v31/v32) with a proof.
