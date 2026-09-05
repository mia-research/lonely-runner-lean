# Quorum Prompt Addendum: CLAIM-LRC-000056-EXT-001

Adjudicate the three isolation laws stated in `formal_claim.md` for arithmetic rows in the
000056 corpus. These laws are independent of — and extend beyond — the phi_match exclusivity
claim in CLAIM-LRC-000056. Each law has a distinct character and falsification criterion.

## Required Adjudication Points

### 1. Law 1 — First Isolation Exactness
- Max relative error 5.12e-13 across 55,000 rows qualifies as machine floating-point precision.
  Is this sufficient to classify `fi = 1/(n·delta)` as an exact formula (rather than an
  approximation with very small residual)?
- Does the formula `fi = 1/(n·delta)` have a known closed-form derivation from LRC axioms,
  or is it a purely empirical observation requiring theoretical explanation?
- The formula is independent of `base`, `alpha`, and `seed`. Assess whether this parameter
  independence strengthens the claim or raises questions about the universality of the result.

### 2. Law 2 — Isolation Count Lower Bound
- Zero violations of `iso ≥ phi_n` across 55,000 rows is a strong empirical result.
  Is this sufficient to assert a dataset-level lower bound claim?
- Is the bound tight? Rows where `iso = phi_n` exactly (the minimum achievable) indicate
  tightness and are relevant for claim precision. Recommend requesting tightness data before
  final publication gate.
- Does a lower bound of phi_n follow from any known property of Euler's totient in the
  LRC context, or is theoretical justification absent?

### 3. Law 3 — Isolation Count Mode
- The modal pattern `mode(iso | n) = 3·phi_n` holds for 8/11 tested n values.
  Is 8/11 coverage sufficient for publication, or should the claim be restricted to
  the 8 conforming values {5, 6, 7, 8, 9, 10, 12, 15}?
- All three exceptions (n=11, 13, 14) have observed mode > 3·phi_n, not below.
  n=11 and n=13 are prime; n=14 = 2×7. Assess whether this asymmetry suggests a
  systematic primality or compositeness effect warranting further investigation.
- The factor of 3 in `3·phi_n` has no stated derivation. Flag if a multiplicative
  structure involving phi_n at factor 3 appears in any known LRC or number-theoretic result.

### 4. Bundle vs. Split Decision
Laws 1, 2, and 3 are logically independent (timing, count bound, modal pattern). They are
bundled for adjudication convenience. Recommend one of:
- **Approve bundle as multi-part claim** (if all three are approve-worthy independently)
- **Approve Laws 1+2, hold Law 3** (if modal pattern needs more n values)
- **Split into three separate claims** (if the heterogeneity of claim types warrants it)

### 5. Scope Limitation Check
All three laws are empirical over n ∈ {5..15}, arithmetic family only, 000056 dataset.
Flag if any law appears likely to extend to n>15 based on mathematical reasoning, and
note whether testing beyond n=15 should be required before publication gate.

## Output Format
Return:
- Per-law recommendation: `approve`, `approve_with_caveats`, `hold`, or `escalate`
- Bundle recommendation: same options
- Critical risks (if any) blocking approval
- Caveats required for conditional approval
