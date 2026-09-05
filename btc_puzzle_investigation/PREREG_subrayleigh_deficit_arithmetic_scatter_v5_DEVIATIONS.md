# DEVIATIONS — analysis realization for PREREG_subrayleigh_deficit_arithmetic_scatter_v5

Recorded 2026-08-06 BEFORE any sweep δ entered a statistic (the δ-sweep was running; only training
data — disjoint from the sweep, frozen — was inspected to lock directions). Each item is a realization
decision the frozen §3/§8 wording under-specifies or over-specifies; none changes a hypothesis, a
threshold, or the §9 outcome logic.

## D-A1 — surface-fit LS is float on analytic δ, not "exact Fraction" (§8 wording over-strict)
§8 says the surface-fit weighted LS is "in exact Fraction". This is INFEASIBLE: the regressors carry
`u = −a_p/√p` and `g₀,g₁` are degree ≤2 in `ln p` — both irrational. The fit is therefore ordinary
float weighted-LS on the **analytic δ values** (which are already floats from the sanctioned FFT-magnitude
carve-out, §8). This is compliant with the carve-out: the fit and the residual `r(p)` are analytic floats
that feed **exact permutation tests** (integer-count p-values); **no float threshold decides a verdict**.
The invariants (`a_p`, `M`, sextic-class, `a_p mod ℓ`) remain exact integers; the permutation counts
remain exact integers.

## D-A2 — H1a / H1a′ residue tests are TWO-SIDED (residue classes are unordered)
§2/§3 call H1a/H1a′ tests with a training-fixed direction. But `a_p mod 3 ∈ {1,2}`, `a_p mod 4 ∈ {1,3}`,
and sextic-class ∈ Z/6 are **unordered categories** — "one-sided" is undefined without a pre-specified
high class, and training cannot supply one (training has base-curve δ only, no surface residuals `r`, so
a residual-vs-class direction cannot be locked). Therefore: **two-sided** exact-permutation Mann–Whitney
(binary splits) and exact-permutation Kruskal–Wallis (Z/6 sextic). This is the correct test for a
categorical predictor; it is *more* conservative than one-sided (≈2× the p-value), never anti-conservative.
Power (§7) is read at the two-sided level.

## D-A3 — H2 direction LOCKED positive; H1b(M) two-sided (training M-direction ≈ 0)
LOCKED from training only (Spearman on the 30 base-curve δ):
- **H2** δ-vs-`a_p`: Spearman(D, a_p) = **+0.489** ⇒ committed one-sided direction **POSITIVE** (δ increases
  with `a_p`), as §2 states. Used for the within-p slope sign and the between-p H2.
- **H1b(M)**: Spearman(D, M) = **+0.009** (essentially zero) ⇒ training supplies NO direction for `M`;
  H1b(M) is therefore **two-sided**. The lag-1 autocorrelation channel is inherently two-sided.

## D-A4 — across-prime permutation p-values by fixed-seed Monte-Carlo (integer-count)
Within-prime H2 π_p are EXACT (enumerate all `m_p! ≤ 720` orderings). Across-prime tests (H1a/H1a′/H1b/SM
over ~30 trajectory primes; the Fisher combined null over ~50 surface primes) use fixed-seed Monte-Carlo
permutation with ≥2·10⁵ shuffles — an **integer-count** p-value (count ≥ observed over total), rule-
compliant (no float threshold decides). Seeds recorded in the analysis script; ≥2·10⁵ resolves p to
≤~2e−3 stderr, adequate at the Holm-0.05 level (a borderline result is re-run at 10⁶).
