# Theorem 2 (Rosenfeld) — citation verified

2026-09-07. Verdict: **SUPPORTS, with a convention caveat that we must not
inherit.** Grade for downstream use: **`[CITED — peer-reviewed]`**.

## 1. The source, verified

Rosenfeld cites "[13] Malikiosis, Santos, Schymura, *Linearly-exponential
checking is enough for the Lonely Runner Conjecture and some of its variants*,
arXiv, 2024." That is now **published and peer-reviewed**:

> *Forum of Mathematics, Sigma* **13** (2025) e164, 1–32,
> doi:10.1017/fms.2025.10107.

arXiv:2411.06903 — v1 11 Nov 2024, v2 21 Jun 2025 (referee edits). **Theorem A
is identical in v1, v2 and the published version.** Cite the journal version,
not "arXiv, 2024".

On disk (SHA-256 in `source_integrity.md`):
`sources_malikiosis_santos_schymura_2025_fms_e164.pdf`,
`sources_mss_arxiv_2411.06903v2.pdf`,
`sources_giri_kravitz_arxiv_2304.01462v4.pdf`.

## 2. Theorem A, verbatim from the published version (p. 3)

> for each subset `S ⊆ [n] := {1,…,n}` let us denote `v_S := gcd(vᵢ : i ∈ S)`.
>
> **Theorem A.** *Suppose that LRC is true for `n` runners. Then, LRC is true
> for `n + 1` runners with integral positive velocities `0, v₁, …, v_n`
> satisfying `gcd(v₁,…,v_n) = 1` and*
> `∑_{S ⊆ [n]} v_S > binom(n+1, 2)^{n−1}.`

Read directly from the PDF, page 3, not from a summary.

Everything Rosenfeld transcribes is exact: tuple length, the sum over **all**
`2ⁿ` subsets (with `v_∅ = 0`, their Lemma 2.2), the `gcd = 1` condition, the
threshold `binom(k+1,2)^{k−1}`. Arithmetic cross-check: `binom(8,2)^6 =
481 890 304` and `(481890304/7)^7 = 7.327 × 10⁵⁴`, matching his printed
`< 7,4 × 10⁵⁴`.

## 3. The one delta — an off-by-one in the *label*, not the theorem

MSS state the hypothesis in the **runners** convention: "LRC is true for `n`
runners" means LRC for `n − 1` nonzero velocities, and the conclusion object is
`0, v₁,…,v_n` — `n+1` runners, `n` speeds.

Rosenfeld transcribed that sentence verbatim into a paper whose own convention is
`k` = **speeds**. Read literally in his convention, his Theorem 2 asserts a
hypothesis *strictly stronger* than MSS need, and its phrase "then it holds for
`k+1`" does not match its own conclusion object (a `k`-tuple).

**This does not affect his proof.** His application (proof of Theorem 1) says
"we rely on the fact that the lonely runner conjecture was already proven for 7
runners" — 6 speeds, Barajas–Serra — which is the correct, weaker hypothesis. His
Lemmas 5, 6, 7 all assume "LRC holds for `k − 1`" in the speeds convention, the
same fact. No circularity, no gap.

**It would affect us** if we transcribe his Theorem 2 verbatim. This project has
already been bitten twice by convention slips (the §6.6(b) ratio-2 partner; the
`v33` introduction's `1/(n+1)`). State it in one convention and say which:

> **[CITED — MSS 2025, Thm A]** Let `k ≥ 2`. If LRC holds for all `(k−1)`-tuples
> of speeds, then every `k`-tuple of positive integers `v₁,…,v_k` with
> `gcd(v₁,…,v_k) = 1` and `∑_{S ⊆ [k]} gcd(vᵢ : i ∈ S) > binom(k+1,2)^{k−1}`
> (empty-set term `= 0`) has the LR property.

## 4. What this means for us

The hypothesis for `k = 7` (our `intLRC 8` target) is **LRC for 6 speeds — that
is `intLRC 7`, which this project has machine-verified and axiom-clean**. The
input Rosenfeld's argument needs is a theorem we own.

Should the programme ever reach `k = 8` (nine runners), the required input is
LRC for 7 speeds — Rosenfeld's Theorem 1 itself — and the threshold becomes
`binom(9,2)^7 = 78 364 164 096`.

## 5. The alternative route needs a version pin

Rosenfeld remarks that the weaker bound of "[12] Giri and Kravitz, *The
structure of Lonely Runner spectra*, arXiv, 2023" would probably also suffice.
**Version history matters here:** arXiv:2304.01462 v1 (Apr 2023), v2 (Oct 2023),
**v3 (10 Dec 2023) WITHDRAWN**, v4 (30 Mar 2025) "Fixed error from previous
version"; now carrying DOI 10.1017/S0305004125101497 (*Math. Proc. Camb. Phil.
Soc.*). Verified on the arXiv listing page.

Rosenfeld's citation "arXiv, 2023" predates the fix. If we ever use this as a
second, independent route, **pin v4 or the MPCPS version**.

Their result is the same shape (assume the previous case, bound a counterexample)
but controls a different quantity — the Euclidean norm `√(∑vᵢ²)` rather than the
subset-gcd sum — with a weaker threshold `n^{(5/2)n}` versus MSS's `≈ n^{2n}`.
Their §7 also uses the *speeds* convention, so its labels differ from MSS's: the
same trap again.

## 6. Residual

Theorem A's own proof has not been read; it is accepted on peer review. That is
the appropriate grade for a published result we are not attacking. If a
downstream claim ever needs Theorem A to be `[PROVED]` rather than `[CITED]`,
that proof must be read and, for the Lean route, formalized — and it is
substantial (zonotopal, via their Conjecture A' and the Lonely Vector Property).
