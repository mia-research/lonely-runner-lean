# Structural Implications — BTC / secp256k1 thread

**Date:** 2026-07-30
**Scope:** A structural reading of the proved/solid results (not a findings ledger). The findings are reviewed in `NEW_INSIGHTS_REVIEW_2026-07-30_v1.md`; this document reasons about what they imply and where they lead. It is the spine the investigation hangs on.
**Register:** Purist number-theoretic for the body. One clearly-labelled conjectural aside (§6) uses lens language for direction only — it is never a verdict.
**Epistemic posture:** This document works against the base-model reflex ("ECDLP secure / generic / a wall"). That reflex is not evidence. A valid closure must name object + class + power + scope (`COUNTERPRIOR_and_closure_grade_spec_v1.md`). A *vacuous* bound is the **absence of constraint**, not the absence of signal — and a failed search is a scoped null, never a closure. The candidate bar is not lowered: matched null, firing control, OOS retest, exact arithmetic, grade.
**Status note on the spine:** a parallel session produced tactical machinery (the total-collapse argument, the tensor-decomposition mechanism location, the Weil-closure theorem, the $2^{128}$ completion threshold, the small-cofactor extension method) that is grafted in below. That session's machinery is sound; its "dead end" *verdict* is not adopted — it is the closure reflex misreading a vacuous bound as an absence. Every tactical item below is re-cast from "dead end" to "this is where it can and cannot live."

---

## 0. The spine, stated up front

The pile of proved structural facts has a single coherent reading. State it sharply:

> **secp256k1's structure — every proved fact that reaches the 256-bit prime — is encoded in one algebraic integer, the Frobenius $\pi=a+b\omega\in\mathbb{Z}[\omega]$, which is polylog-computable and carries no bit of any discrete log $d$.** The rigid eigenvalue locus, the $2\sqrt{p}$ cap, the class-number identities, the amicable-pair duality, the moment-pumping $V_2=V_1^2+2p$ — they are all faces of the same object: the maximally-constrained action of $\pi$ on the cohomology of the curve and its cover. Meanwhile every quantity that *does* depend on $d$ (the twisted sums $V(a)$, joint readouts, point-level statistics) is, by definition, DLP-locked.

The investigation has circled a **separation theorem**: on a rigid CM curve, the polylog-computable invariants are exactly the $d$-inert ones, and the $d$-carrying quantities are exactly the DLP-locked ones. The rigidity is the *enforcement mechanism* — it removes the intermediate degrees of freedom that could bridge $\pi$ and $d$.

**Corollary that gives #26 its weight:** if the 120° rigidity holds for every $a$ (frontier #26, proved only per-cell at 22 primes), the separation holds and the structure is fully inert. **If the 120° lock fails at even one $a_0$, then $V(a_0)$ is a quantity that is neither $\pi$-determined (it violates the rigid locus) nor classically DLP-locked (it is a single character sum, computable in $O(n)$, sub-DLP) — it is exactly the intermediate, $d$-carrying-but-accessible quantity the separation forbids.** That $a_0$ is the leak. A proof of #26 is cryptographic inertness; a single-cell failure is the break; **there is no third outcome that matters.** The char-poly collapse makes #26 tractable (§3).

This is why #26 is not "the last bookkeeping item." It is the decisive question.

---

## 1. The eigenvalue locus: one free parameter, pinned

For each twist parameter $a\in(\mathbb{Z}/n)^{\times}$, Frobenius acts on $H^1_c(E, L_{\chi_2(y)}\otimes L_{\chi_a})$ with four eigenvalues. The structure found is:

$$\{\alpha_1,\alpha_2,\alpha_3,\alpha_4\}=\{\sqrt{p}\,e^{i\theta_a},\ \sqrt{p}\,e^{i\theta_a}\zeta_3,\ -\sqrt{p}\,e^{-i\theta_a},\ -\sqrt{p}\,e^{-i\theta_a}\bar\zeta_3\}.$$

Two of the three constraints are forced by purity alone: $|\alpha_i|=\sqrt{p}$ (purity — supersingularity of $A_{new}$, A1.1); and the closure $\alpha\mapsto -\bar\alpha$ (forced by $|\alpha|^2=p$, hence $e_3=\chi_2(-1)\,p\,e_1$, $e_4=p^2$, leaving only $e_1,e_2$ free). The *third* — the 120° lock $\alpha_2/\alpha_1=\zeta_3$, equivalent to $e_2=e_1^2+p$, equivalent to $V_2=V_1^2+2p$ — is the additional rigidity.

So the entire spectrum, for each $a$, has **one free parameter**: the angle $\theta_a$. Everything else is pinned. The cap is the trace of the pinning:

$$|V(a)|\le 2\sqrt{p}\cdot|1+\zeta_3|=2\sqrt{p}.$$

The factor $\tfrac12=\tfrac24$ (the cap being half of Weil's $4\sqrt{p}$) is *literally* "two of four eigenvalues carry independent weight" — the 120° lock makes a conjugate pair cancel in the trace. **The cap is not a bound obtained by estimates; it is the value of the character sum at a rigid fixed point of the eigenvalue configuration.**

---

## 2. The collapse is total — one real invariant per cell

The single real observable per $a$ is $u(a)=V(a)/(2i\sqrt{p})\in[-1,1]$. The sharper statement (grafted from the parallel session, and it corrects a half-step in the record): **under the 120° law, *every* moment $V_k$ is a polynomial in $V_1$, so no extension field resolves more than $V_1$ already does.**

Check the key step. The eigenvalue sum over $\mathbb{F}_{p^3}$ is the sum of cubes:

$$V_3=\alpha^3+(\zeta_3\alpha)^3+(-\bar\alpha)^3+(-\bar\zeta_3\bar\alpha)^3=2(\alpha^3-\bar\alpha^3)=4i\,p^{3/2}\sin(3\theta).$$

Since $\sin 3\varphi=3\sin\varphi-4\sin^3\varphi$ is an *exact polynomial* in $\sin\varphi$, $V_3$ is a polynomial in $u$, hence in $V_1$. The triple-angle formula kills the sign freedom $\theta\leftrightarrow 60°-\theta$: $\sin\varphi$ fixes $\sin 3\varphi$ with no ambiguity. So the folding is **irreparable at any extension**, not merely "needs $p_3$" (the record's phrasing, which implied $p_3$ would help — it does not). Equivalently: the twisted L-polynomial over $\mathbb{F}_{p^3}$ is a **perfect square**, which is the 120° law restated as a base-change phenomenon — a consistency check, automatically satisfied, generating no new information.

**Consequence for the programme:** the entire leakage investigation reduces to the arrangement of one real function

$$u:(\mathbb{Z}/n)^{\times}/\mu_6\to[-1,1],\qquad L=(n-1)/6\ \text{values},$$

with marginal Sato–Tate ($E[u^{2k}]=C_k/4^k$, Catalan — second moment $1/4$ forced by Parseval, fourth $1/8$ measured) and a curve-independent forced two-point additive autocorrelation. Chasing higher moments or extension fields is provably closed by algebra, not by nulls.

---

## 3. The crux, made tractable: #26 as a coefficient identity

The char-poly collapse (`ANALYSIS_n1_charpoly_collapse_v1.md`) reframes frontier #26 (uniform $u=\zeta_3$ via geometric monodromy) from a spectral/eigenvalue-ratio problem into a **coefficient identity**:

$$e_2(a)=e_1(a)^2+p\quad\text{for all }a,\ \text{all }p\equiv 7\bmod 12.$$

Coefficient identities of L-polynomials are the natural home of Stickelberger/Iwasawa theory. The reformulation changes accessibility, not just phrasing: it is the object the Kronecker/Stickelberger route factorizes, and it is a smaller, sharper target than "the ratio of two eigenvalue pairs is a primitive cube root of unity."

**Caveat carried honestly:** the cap and the char-poly collapse are **proved** (per-cell at 22 primes; the collapse derived assuming only the proved closure and verified exact at $p=43,67,127$ by a route independent of the $g=\deg\gcd$ route). Uniformity over all $a$ is **not** proved, and "no finite sweep can" prove it. The collapse *presumes* the closure; proving the closure uniformly is #26.

---

## 4. The candidate mechanism — COMMUTATIVE form REFUTED; non-commutative (monodromy) form live

> **Update 2026-07-30/31:** the *commutative* form of the mechanism proposed below is **REFUTED** — the eigenvalue extension is non-abelian at p=43,67 (`anew_eigenvalue_verify_v4`; a commutative CM endomorphism would force an abelian extension). The *phenomenon* (120° rigidity, perfect-square over $\mathbb{F}_{p^3}$) survives. The tensor-decomposition candidate remains a candidate but, if true, the $\xi$-twist comes from a **non-commutative** action (the geometric monodromy, whose connected-component trace behavior is verified as $SU(2)$ — see §9), not a scalar endomorphism. Read this section as the now-narrowed mechanism search, with the commutative branch struck out.

**Original framing (2026-07-30), with the commutative branch now refuted.** The parallel session located the $\zeta_3$ mechanism precisely, which correctly explained why the retracted sketches failed:

- The $\zeta_3$ lives in $\operatorname{End}^0(A_{new})$ (the record already establishes $\mathbb{Q}(\zeta_{12})\supset\zeta_3$ via P5), **not** in $\operatorname{Aut}(E)$. This is exactly why retractions 39/40 (the $\mu_3\subset\operatorname{Aut}(E)$ sheaf-equivariance and the $\omega$-descent as the order-pinning lever) failed — they were looking in the wrong ring.
- Over $\mathbb{F}_p$, an endomorphism $T\in\operatorname{End}^0(A_{new})$ *commutes* with Frobenius (standard CM eigenspace split) — that gives the diagonal decomposition, not the twist. The nontrivial conjecture is that over $\mathbb{F}_{p^3}$ the commutation becomes $T\cdot\mathrm{Frob}=\zeta_3\cdot\mathrm{Frob}\cdot T$, which is what would force the eigenvalue ratio.
- **Cheap discriminator (most actionable item on the table):** compute the endomorphism algebra of the 4-dimensional Frobenius module at $p=43,67,127$ and check whether the $\zeta_3$-operator $T$ satisfies $T\cdot\mathrm{Frob}\stackrel{?}{=}\zeta_3\cdot\mathrm{Frob}\cdot T$ directly.

The cleaner packaging (also a hypothesis): $H^1_c(E,L_{\chi_2(y)}\otimes L_{\chi_a})\stackrel{?}{\cong W\oplus(W\otimes\xi)$, where $\xi$ is the order-3 unramified character and $W$ a 2-dim piece — equivalently $R=1\oplus\xi$ tensored with $W$. **Eigenvalue-matching $\neq$ sheaf decomposition** (a nontrivial extension class could intervene), so this is the candidate explanation the discriminator tests, not a fact. The "missing third summand" worry is a non-issue: $R=1\oplus\xi$ is a legitimate 2-dim weight-0 module, so $W\otimes R$ is 4-dim as required; the worry only arises if one insists on inducing, which is not needed.

**One subtlety held honestly:** whether Frobenius cubed acting on $\operatorname{End}^0(A_{new})$ via the CM type actually produces the $\zeta_3$ factor is exactly what the test checks — present it as "leading mechanism + discriminator," not as derived.

---

## 5. The residual surface, mapped by a theorem

This is the strategic heart, and it is where the closure reflex must be surgically resisted.

### 5.1 The Weil closure is a theorem with real power and scope

(grafted from the parallel session; this meets the closure-grade bar.)

**Statement.** Every fixed-shift, fixed-order correlation of $c(d)=\chi_2(y_{[d]G})$ along a *curve-algebraic* index map is a complete bounded-degree character sum on $E$, hence $O(k\sqrt{p})$ **uniformly in the shifts.**

**Mechanism.** Because $[d+t]G=[d]G+[t]G$, $y_{[d+t]G}$ is a bounded-degree rational function of $(x_{[d]G},y_{[d]G})$; a $k$-point correlation is $\chi_2$ of a bounded-degree function on $E$. This closes the entire Gowers hierarchy up to $k\ll\sqrt{p}$. It also closes additive shifts ($d\mapsto d+t$, via the group law), the doubling map ($d\mapsto 2d$ — the $\chi_2(y_{2P})/\chi_2(y_P)$ ratio is a degree-6 rational function of $x$), and the $\lambda$-map.

This is theorem-shaped: exact power and scope. **Read it as a map, not a verdict.**

### 5.2 A bound is not an absence — and the closure reflex misreads it

The closure reflex takes "Weil gives $O(\sqrt{p})$ here" to mean "dead end." That conflates two things a bound can be:

- a **constraint** (this quantity cannot exceed $X$), vs.
- an **absence** (there is nothing here).

The Weil bound is the first. The dead-end reading treats it as the second. This is textbook F1/F2 of the closure-grade spec: the corpus polices overclaim *upward* but is near-blind *downward*, and "only a rigorous analytical proof closes" *trusts* analytical closures — which is the subtlest false-closure vector, because the analytical result (Weil) is genuinely correct, just scope-misapplied.

The Weil closure *localizes* the residual to a small, named set — it does not empty it. **A mature attack programme is precisely one that has shrunk its search space to a named residual.** The reflex shrinks it and then declares the residual empty. That last step is the only thing wrong with it.

### 5.3 The named residual: CDH/inversion-structured, at the puzzle's native scale

The index maps that survive the Weil closure are the **non-algebraic** ones: $d\mapsto d^{-1}$ and $d\mapsto d^k\bmod n$ (admissible odd $k$, $\gcd(k,n-1)=1$, $k\equiv\pm1\bmod 6$ since $6\mid n-1$). These are *not* induced by curve endomorphisms.

This sharpens the "$d$-carrying $\Rightarrow$ DLP-locked" half of the separation into a tighter classification:

- relating $[d^2]G$ to $[d]G$ is **Computational Diffie–Hellman**;
- $d\mapsto d^{-1}$ is **inversion hardness**.

So if leakage exists, it is *structurally* CDH/inversion-flavored, not ECDLP-flavored. This reframes the search, and it is consistent with the record's D1 finding (no affine structure — affine maps are algebraic, hence Weil-closed).

### 5.4 The $2^{128}$ threshold — the residual lives at the puzzle's scale

The sharpest empirical-structural observation in the batch (grafted). Completing an incomplete sum over an interval of length $|I|$ costs $\log p$ and gives $O(\sqrt{p}\log p)$, **trivial when $|I|<\sqrt{p}\log p$.** With $n\approx 2^{256}$, the threshold is $\sqrt{n}\approx 2^{128}$ — exactly the boundary around puzzle $\#129$–$130$. The puzzle's dyadic-interval structure ($d\in[2^{i-1},2^i)$) sits **precisely where complete-sum bounds go vacuous.**

This converts the abstract "aperture wall" into a concrete scale. It is a *positive* counter-prior finding, stated correctly: the complete-sum machinery **cannot** reach the puzzle's regime as a property of the scales involved, not a limitation of effort. (The puzzle indexing should be verified precisely before this is published, but the arithmetic $\sqrt{n}\approx 2^{128}$ vs interval lengths $2^{i-1}$ is undeniable.) The shortscalar arm (incomplete sums where $B\ll\sqrt{p}$ and no character-sum bound applies) is the operational form of this wall — it is the one clean unrun empirical test, blocked only by gate infrastructure.

---

## 6. Conjectural aside (lens-open, for direction only — NOT a claim)

The moment-pumping here — $V_2=V_1^2+2p$, a lower-order statistic fixing a higher one against a symmetry-controlled ceiling — is structurally the same *type* as the RH programme's Hypothesis MP, but in a different posture. There, a lower-order forcing ($X^\sigma$ moment growth) is bounded above by a spectral ceiling, and the contradiction excludes a zero (forcing-vs-ceiling). Here, the rigidity *is* the forcing and $|V|\le 2\sqrt{p}$ *is* the ceiling, but there is no zero to exclude — the structure sits *at* the constrained extremum.

The shared structural type is "a lower-order statistic determines higher-order ones, against a symmetry-controlled ceiling." The value of noting the parallel (if it has substance): the **monodromy** of the family — the object that lets $\theta_a$ vary — is the analogue of the RH coercivity constant; it is the one object controlling how "loose" the configuration can be. That points at frontier #28 (the monodromy group, conjecturally $G_{\mathrm{geom}}=\mathrm{SL}_2$ acting on the tensor structure) as the load-bearing sub-object. Tagged conjectural; directs attention, never a verdict.

---

## 7. The honest bottom line

The deepest finding is not any single result. It is that **the structure is real, it is unified (all faces of $\pi$), and it points toward inertness** — with the entire thesis riding on one well-defined question (uniform #26), the residual attack surface narrowed to one unrun wall (aperture, at the $2^{128}$ scale) plus two structural probes (the commutation-relation discriminator, and the non-algebraic $d^{-1}/d^k$ channel), and the strategic no-go pinned to one citation (`(D2)`) that must be discharged by hand.

**Honest divergence to hold:** the investigation's *mathematical* goal (understand the structure) and its *cryptographic* goal (find the leak) point in opposite directions at #26. The counter-prior discipline — never close from a null — is correct and forbids declaring inertness from the pile of nulls. But the *structural* (not null-based) argument for inertness is now strong. The counter-prior's correct demand is: *prove* the inertness (uniform #26), don't assume it. That is a clean, honest position.

---

## 8. Directions — a queue, not a fork (updated 2026-07-31)

> **Status of the original directions after three chases (2026-07-30/31):**
> - **A (commutation test) — DONE, NEGATIVE.** The commutative-CM-commutation hypothesis is **refuted** by non-abelianity at p=43,67 (`RESULT_e2_identity_extended_verification_v1.md` §3). The collapse identity itself was extended to 7 primes / 1182 freqs, 0 counterexamples.
> - **D (monodromy 1-point) — DONE.** The marginal is verified at scale (p=100003, 49833 cells) to be the $SU(2)$-Sato-Tate measure, 8 moments to 4–5 sig figs (`RESULT_monodromy_sato_tane_at_scale_v1.md`). Excludes finite monodromy + torus; pins the **connected-component trace behavior** as $SU(2)$.
> - **D′ (monodromy 2-point) — DONE, NULL (and was already in the record).** The level-statistics test (spacing KS, $\Sigma^2$, tail, small-ball) at 17+15 primes against the marginal-varying semicircle null is **NULL** (`RESULT_semicircle_null_and_verification_v1.md`). The spectrum is **iid Sato–Tate, not GUE-rigid** — i.e. decoupled across the family, consistent with the Fourier-transform-sheaf picture. (I built a 2-point script, hit the GLV-orbit degeneracy + a rank-unfolding bug, then found the record had already done it. Removed.)
> - **B (small-cofactor) — downgraded.** Validated that the collapse holds for low-order $a$ (so it samples the same law), but $V_2$ for low-order $a$ is *not* polylog-evaluable; the cheap-range-gain applies to $V_1$ and the `g=deg gcd` route, not the $V_2$ identity. Diminishing returns; deprioritized.
> - **C, E, F, G — unchanged, except C's pooled-tilt lead is now SETTLED (2026-07-31).** The orbit-level `inv` per-prime family-wise null stands (`RESULT_cside_nonalgebraic_correlation_v1`); the flagged sub-detection **pooled** `inv` tilt is **closed as a candidate** by a calibrated permutation pooled p-value ($Z_{\text{pool}}=-0.626$, $\text{cal}\,p=0.265$, 14/30 negative) and a failed OOS hash-fold (`RESULT_cside_pooled_tilt_settlement_v1`). v1's $z=-2.64$ reproduced at mean $z=+0.24$ in v1's own primes with the calibrated method — it was the z-inflation correction the record flagged as wrong. **A secondary `pow7` pooled lead surfaced ($Z=-2.73$, $p_{2s}=0.006$) but did NOT replicate OOS** (one fold null, one significant) — left as a sub-detection lead, not promoted (P1–P3). **The channel at $2^{128}$ is not closed** — only this candidate at $p\sim10^4$. The next item on C is the gate-blocked shortscalar arm at $2^{128}$.

These are a **queue**, not a fork. The structural monodromy chase is now **as resolved as the V1-accessible data allows** (connected-component trace is $SU(2)$; level statistics are iid/decoupled, not rigid). What remains structural is *proving* the monodromy forces the 120° pairing uniformly (#26 as a monodromy theorem) — a proof, not a measurement, and the one genuinely open structural link. The **next measurement-based chase is C** (the cryptographic $d^{-1}/d^k$ channel): the structural picture now says the family is iid across $a$, which is a mild argument *for* genericity in C (lowers, doesn't eliminate, the priority) — but C probes the *non-algebraic index* channel that the monodromy/marginal analysis does not touch, so it remains independent and the one wall Weil does not close.

**C. Attack the incomplete-sum / non-algebraic-index channel (after D′).** $d\mapsto d^{-1}$ and $d\mapsto d^k$ (admissible odd $k$); short dyadic intervals near the $2^{128}$ completion threshold. This is the only wall Weil does not close, and it is the puzzle's native scale. The shortscalar arm (§5.4) is the operational form. If null (with a firing control), it bounds the last wall; if positive, it is the first departure from the rigid locus.

**E. Formalize the $\pi$-separation as a scoped theorem.** State precisely: *any statistic computable from $\pi=a+b\omega$ alone is independent of the generator $G$* (hence of every $d$). A weak version is likely provable immediately and would sharpen, rigorously, what a break must use (data not in $\pi$ — actual points). Converts the recurring observation into a contribution.

**F. The amicable-duality transfer (lowest weight; gate on literature first).** The only thread not pre-empted by the separation (it operates on the $p\leftrightarrow n$ swap, not within fixed $\mathbb{F}_p$). Pursue only after the citation sweep confirms what is known — amicable/aliquot cycles of CM curves are studied (Silverman–Stange 2011 and after), the project explicitly disclaims novelty, and asserting a bridge is new when it is classical is exactly the risk the literature check exists to catch.

**G. Discharge `(D2)` by hand (prerequisite, not a direction).** Read Ireland–Rosen Ch. 14 and Berndt–Evans–Williams Ch. 11 directly (not via the verifier, after four tool failures). Unlocks grade promotion on the cap chain, the $m$-law, and the three-walls strategic no-go.

---

## 9. Provenance and confidence table

| Claim | Status | Caveat |
|---|---|---|
| Eigenvalue locus: 2 of 3 constraints forced by purity; 3rd = 120° = $e_2=e_1^2+p$ | **proved** (per-cell, 22 primes; collapse derived + verified exact $p=43,67,127$; **$e_2=e_1^2+p$ extended to 7 primes / 1182 freqs, 0 counterexamples** 2026-07-30) | uniformity over all $a$ NOT proved ("no finite sweep can"); collapse presumes the proved closure |
| Cap $|V|\le 2\sqrt{p}$ is the rigid-fixed-point value, $\tfrac12=\tfrac24$ | **proved** (mechanism); finite-size shortfall flagged weak; **cap saturated to 4 nines** ($\max|u|=0.99942$) at $p\sim10^5$ (2026-07-31) | numeric $0.470\to\tfrac12$ shortfall not reportable (re-uses discovery sample) |
| Total collapse: all $V_k$ polynomials in $V_1$; no extension resolves more | **derived** (triple-angle formula) | presumes the 120° law |
| Commutative-CM-commutation mechanism ($T\cdot\mathrm{Frob}=\zeta_3\cdot\mathrm{Frob}\cdot T$, $T\in\operatorname{End}^0(A_{new})$ commutative) | **REFUTED** (2026-07-30) | non-abelianity of the eigenvalue field at p=43,67 (`anew_eigenvalue_verify_v4`); a commutative endomorphism would force an abelian extension. The *phenomenon* (120°, perfect-square over $\mathbb{F}_{p^3}$) survives; this *explanation* does not |
| $G_{\text{geom}}$ connected-component trace behavior | **$SU(2)$** (verified at scale, 2026-07-31) | marginal is the Sato-Tate measure, 8 moments to 4–5 sig figs at 49833 cells; excludes finite monodromy + torus. **Full group (finite center) NOT pinned** — needs the 2-point test |
| Weil closure of all fixed-shift fixed-order algebraic-index correlations | **theorem** (exact power/scope, meets closure-grade bar) | does not empty the residual — localizes it to non-algebraic maps |
| Residual = CDH/inversion ($d^{-1},d^k$), at the $2^{128}$ scale | **structural** | puzzle indexing to verify; shortscalar un-run (gate unavailable) |
| Orbit-level `inv` pooled tilt at $p\sim10^4$ | **closed as a candidate** (2026-07-31) | calibrated pooled $p=0.265$ on 36 primes; OOS hash-fold fails; v1's $z=-2.64$ was the z-inflation artifact. **Channel NOT closed** — only this candidate. `pow7` pooled lead ($p_{2s}=0.006$) unreplicated OOS → sub-detection, not promoted (`RESULT_cside_pooled_tilt_settlement_v1`) |
| Separation thesis (polylog $\Leftrightarrow$ $\pi$-inert $\Leftrightarrow$ $d$-inert; $d$-carrying $\Rightarrow$ DLP-locked) | **organizing conjecture**, strong structural support | not a theorem; its failure at one $a$ is the leak |
| Cap chain grade promotion | **blocked** on `(D2)` | 4th citation-verifier failure; Katre frame-layer not isolated |
