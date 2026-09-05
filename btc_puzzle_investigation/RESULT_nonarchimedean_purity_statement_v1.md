# RESULT: the non-archimedean (p-adic) purity residual — careful statement and clean close

**Date:** 2026-08-01
**Grade:** `[CLOSED — automatic given the (cited, D2) sheaf-purity; no non-trivial finite-place computation remains]`.
**Register:** purist. Item 2 of the 2026-08-01 handoff (`untested_threads`).

---

## 0. What was open, and the ⚠ in the handoff

`RESULT_powersum_ladder_routeA_control_v1.md` §4 scoped the genuine residual of ledger item 2 ("purity at every embedding") precisely:

> *"The genuinely open part is purity at non-archimedean ($p$-adic) places — a Weil-number condition at the finite primes, which the archimedean minpoly does not capture and which is a distinct, harder computation."*

The 2026-08-01 handoff carries this forward as thread #2 with a well-placed ⚠:

> *"First state carefully what is being tested — for eigenvalues of Frobenius on a smooth proper variety this may be automatic (Deligne); the test is meaningful only if there's a non-automatic finite-place constraint to check."*

This document does exactly that: states what the eigenvalues *are*, applies the cited theorem, and determines whether a non-automatic finite-place constraint exists. **It does not.** The residual dissolves into the already-open citation `(D2)`.

## 1. What the eigenvalues are

The four eigenvalues $\alpha_1,\ldots,\alpha_4$ at frequency $a$ are the Frobenius eigenvalues on the ℓ-adic cohomology with compact supports

$$H^1_c\!\bigl(E_{\bar{\mathbb{F}}_p},\; L_{\chi_2(y)}\otimes L_{\chi_a}\bigr),$$

where $E:y^2=x^3+7$ over $\mathbb{F}_p$, $L_{\chi_2(y)}$ is the Kummer sheaf for the quadratic character of the $y$-coordinate, and $L_{\chi_a}$ is the Kummer (Artin–Schreier–Witt) sheaf for the order-$n$ character $\chi_a$ of $(\mathbb{Z}/n)^\times$ (`PREREG_n1_120deg_exact_ideal_v4.md` A1, A2′; `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §1 line 27). The record asserts (A3, A8):

- $L_{\chi_a}$ is **totally unramified**, so $\dim H^1_c=4$ (the weight-1 model).
- The sheaf $L_{\chi_2(y)}\otimes L_{\chi_a}$ is **pure of weight 1** — graded `[PROVED — CITED]` via Deligne, *La conjecture de Weil II* (1980), théorème 3.2.3(2), and Katz–Sarnak, *Random Matrices*, Prop. 2.

## 2. What Weil II gives

**Deligne, Weil II (1980), théorème 3.2.3.** Let $\mathcal{F}_0$ be a pure ℓ-adic sheaf of weight $w$ on a variety $X_0/\mathbb{F}_q$. For every closed point $x\in|X_0|$ and every embedding $\iota:\bar{\mathbb{Q}}_\ell\hookrightarrow\mathbb{C}$, every eigenvalue $\alpha$ of the geometric Frobenius $\mathrm{Frob}_x$ acting on $\mathcal{F}_{\bar{x}}$ satisfies

$$|\iota(\alpha)| \;=\; q_x^{\,w/2}, \qquad q_x = q^{\deg(x)}.$$

This is the **all-embeddings purity** statement — it is the literal content of the Riemann-hypothesis part of the Weil conjectures, generalized to pure sheaves.

**Application here.** $w=1$, $q=p$. The four eigenvalues $\alpha_i$ of geometric Frob on $H^1_c(E, L_{\chi_2(y)}\otimes L_{\chi_a})$ therefore satisfy $|\iota(\alpha_i)|=\sqrt{p}$ for **every** embedding $\iota$ — archimedean *and* non-archimedean. Concretely:

- **Archimedean places** ($\iota:\bar{\mathbb{Q}}_\ell\hookrightarrow\mathbb{C}$): $|\alpha_i|=\sqrt{p}$ — the purity the moduli column checks numerically (`PREREG` A3).
- **Non-archimedean / $p$-adic places**: the same $|\alpha_i|_\nu=p^{1/2}$ at every finite place $\nu$. This is the *definition* of $\alpha_i$ being a **$p$-Weil number of weight 1**: an algebraic integer with $|\alpha_i|_\nu=p^{1/2}$ at all places $\nu$. Equivalently, the Newton polygon of the char-poly $L_a(T)$ at the prime $p$ has all slopes $=1/2$ (the slopes of a pure-weight-1 Frobenius), and at every $\ell\ne p$ the $\alpha_i$ are $\ell$-adic units.

## 3. Is there a non-automatic finite-place constraint to check? No.

The handoff's ⚠ is resolved: **for Frobenius eigenvalues of a pure sheaf, finite-place Weil-number purity is automatic.** It is not a separate, harder computation — it is a direct corollary of the purity theorem once the sheaf is pure. The investigation posits no *stronger* finite-place property (no specific Newton-polygon shape beyond all-slopes-$1/2$, no prescribed $p$-adic valuation pattern beyond what purity forces — verified by audit: every "Newton/slope" mention in the corpus concerns other objects, the cap-scaling exponent and the supersingularity of $A_{new}$, not a finite-place condition on the $\alpha_i$).

**The residual is therefore not a computation — it is a citation.** The all-places purity rests on the Weil II / Katz–Sarnak citation chain labelled `(D2)`, which the citation-verifier has failed to discharge (4×). The honest status:

- **If the `(D2)` citation is correct** (Weil II 3.2.3 applies, the sheaf is pure of weight 1): finite-place Weil-number purity holds, *at every place, for free*, and item 2 is **closed**.
- **The open work is verifying `(D2)` by hand** — reading Ireland–Rosen Ch. 14 and Berndt–Evans–Williams Ch. 11 directly (`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §8 item G) — **not** running a new finite-place computation. This is the same `(D2)` that blocks cap-chain grade promotion; it is the single load-bearing unverified citation, tracked elsewhere.

## 4. Scope held honestly

- **No fabricated lemma.** The closure rests on the *standard, citable* Weil II purity theorem; it does not invent a finite-place test. The application to *this* sheaf requires the sheaf be pure of weight 1, which is exactly what `(D2)` asserts and what A3/A8 cite.
- **Not a proof the citation is correct.** This document does not discharge `(D2)`; it states that *conditional on `(D2)`* the finite-place residual is automatic. If `(D2)` were to fail (the sheaf were mixed, not pure), the finite-place question would re-open — but the entire archimedean rigidity story would also re-open, so `(D2)` is load-bearing in a much larger sense than item 2.
- **No stronger finite-place property was ever posited** that would require a separate computation; verified by audit of the corpus.

## 5. Verdict

**Item 2 is closed.** The "non-archimedean Weil-number condition" is automatic for Frobenius eigenvalues of a pure weight-1 sheaf (Deligne Weil II). No non-trivial finite-place computation remains; the only open work is the `(D2)` citation discharge (tracked as a prerequisite, not a measurement thread).

## 6. References

- P. Deligne, *La conjecture de Weil : II*, Publ. Math. IHÉS **52** (1980), 137–252, théorème 3.2.3.
- N. M. Katz, *Review of ℓ-adic cohomology*; N. M. Katz and P. Sarnak, *Random Matrices*, Frobenius–Weil purity (Prop. 2 in the record's citation).
- Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14; Berndt–Evans–Williams, *Gauss and Jacobi Sums*, Ch. 11 — the `(D2)` hand-verification sources.
