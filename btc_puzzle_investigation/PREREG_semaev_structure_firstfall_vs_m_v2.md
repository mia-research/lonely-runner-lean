# PREREG v2 — Route A crux: the first-fall-degree NULL LADDER (semi-regular → S_m-symmetric → Semaev) vs m

**Supersedes** `PREREG_semaev_structure_solvingdegree_vs_m_v1.md`, which was run, found DESIGN-FLAWED
pre-result by its own harness (generic control could not variety-match: 0/24 kept at every m; d_solv
censored above Dmax for m≥3), and audited by `experiment-designer` (5 decidable defects; #1 = the loose
null confounds "these coefficients help" with "any symmetric+graded structure helps", biasing toward a
false LEVER). v2 fixes all five. **Status:** FROZEN before any v2 gap number is read. Model scale.
**Date:** 2026-08-31. **Harness:** `semaev_elimination_v1.py` (exact GF(p) Macaulay ranks; float-free).
**Runner:** `semaev_structure_firstfall_vs_m_v2.py`.

## 0. What changed from v1 (deviation log)
- **D1 — primary statistic → first-fall degree d_ff (was d_solv).** v1's run showed d_solv is censored
  above any session-tractable Dmax for m≥3 (uncomputable at model scale), while d_ff is reached
  (m=2→4, m=3→12). d_ff is ALSO the literal object of the Petit–Quisquater "first-fall assumption" and
  is a property of the leading forms — **variety-independent**, so it needs no decomposable target and
  **dissolves v1's variety-match confound entirely** (experiment-designer #1 §7, #2). d_solv kept as a
  secondary read only where it is reached without censoring.
- **D2 — null LADDER (was single loose null).** Three systems ranked (experiment-designer #1):
  (i) **semi-regular** — per-monomial random coeffs on the Semaev support (breaks S_m symmetry);
  (ii) **symmetric** — random, ONE coeff per S_m-orbit of the support (preserves the x-permutation
  symmetry Semaev has — this is the FGHR-symmetrization structure); (iii) **Semaev** — true coeffs.
  Same-support already preserves the isobaric weighted-degree (support ⊆ one weighted-degree class), so
  only symmetry needs the orbit-constant construction. Two gaps are reported: Δ₁ = d_ff(semi-reg) −
  d_ff(symmetric) [value of the SYMMETRY], Δ₂ = d_ff(symmetric) − d_ff(Semaev) [value of the SPECIFIC
  group-law coefficients beyond symmetry].
- **D3 — all knobs frozen (experiment-designer #5):** see §5.
- **D4 — calibrations pre-stated & hand-computed (experiment-designer #2):** see §4.
- **D5 — decision rule made robust to one noisy point + aggregate frozen (experiment-designer #3,#4):**
  see §6; "asymptotic" dropped from every conclusion slot.

## 1. Object
For the m-summand prime-field relation-search system {P(x₁..x_m; t) = 0} ∪ {∏_{v∈V}(xᵢ−v)=0}, measure
the first-fall degree d_ff of the leading forms as P ranges over {semi-regular random, S_m-symmetric
random, Semaev}, as a function of m. Does the S_m symmetry lower d_ff below semi-regular (Δ₁), do the
specific Semaev coefficients lower it further (Δ₂), and does either gap grow with m?

## 2. Statistic (frozen)
Integer d_ff = smallest D with `macaulay_stats(...)[D]['fall'] > 0` (first degree drop among leading
forms), exact GF(p) ranks. Reported per m for each rung. Δ₁(m)=d_ff(semi-reg,median)−d_ff(symmetric),
Δ₂(m)=d_ff(symmetric)−d_ff(Semaev). Semaev and symmetric-null d_ff are single deterministic values per
(m, seed of the symmetric draw); the symmetric and semi-regular rungs are distributions over K_null
draws — report min/median/max and the RANK of Semaev within the semi-regular spread.

## 3. Systems (frozen construction)
- **Support** = monomials of Sx := S_{m+1}(x₁..x_m, t=τ) with τ frozen (§5). This is the shared support
  of all three P.
- **Semi-regular P**: each support monomial gets an independent uniform-nonzero GF(p) coefficient.
- **Symmetric P**: partition the support into S_m-orbits (permutations of x₁..x_m); every monomial in an
  orbit gets the SAME uniform-nonzero coefficient. (Preserves symmetry; same support ⇒ same isobaric
  weighted degree automatically.)
- **Semaev P** = Sx itself.
- **Field eqs**: ∏_{v∈V}(xᵢ−v) for i=1..m, |V| frozen (§5), identical across all three P.
- No planted solution / no consistency requirement — d_ff reads the leading forms only.

## 4. Calibrations (pre-stated integers — the read-out MUST return these, else VOID)
- **CAL-A (regular sequence ⇒ NO early fall):** field-eqs-only {∏(xᵢ−v)} is a complete intersection of m
  forms of degree |V|; it must report **d_ff = null** (no `fall>0`) up to Dmax. [v1 run confirmed null
  at m=2,3,4.] If a fall appears, the `fall` read-out is spurious → VOID.
- **CAL-B (redundancy ⇒ a fall appears, strictly below Semaev):** {x₁−c} ∪ field-eqs makes xᵢ's degree-
  |V| field equation redundant, forcing a fall at degree ≤ |V|. Pre-stated: d_ff(CAL-B) is finite and
  **≤ |V| < d_ff(Semaev)** for m≥3 (Semaev d_ff=12 at m=3 ≫ |V|=3). If CAL-B is null or ≥ d_ff(Semaev),
  the read-out cannot detect a lowered fall → VOID.

## 5. Frozen knobs
- p = 307 (=1 mod 3, j=0 ordinary; M9 scope) AND a cross-check at p = 2069 (larger, to rule out
  small-field coefficient degeneracy per experiment-designer #5); curve A=0, B=7 (secp form).
- τ (the t-slot value) = F(x(G)) where G = `E.gens()[0]` — a fixed, real target x-coord; frozen. (d_ff
  is a leading-form property, so τ affects only lower-degree terms; frozen for reproducibility.)
- |V| = m; V = the m field elements {F(1), F(2), …, F(m)} (fixed, distinct, nonzero) — identical across
  rungs and draws.
- K_null = 12 for m∈{2,3}; K_null = 6 for m=4 (cost). Frozen.
- Dmax per m: 12 (m=2), 22 (m=3), 30 (m=4). If d_ff is not reached ≤ Dmax for a rung, that rung is
  reported **CENSORED (> Dmax)** at that m — NOT a value, NOT a null. m=4 is expected to censor for the
  higher (semi-regular) rung; that censoring IS the §XI.4 wall, reported as such.
- m ∈ {2, 3, 4}. m=5 is NOT attempted (S₆ degree-16/var Macaulay at the needed Dmax is out of session
  reach; v1 timings: m=4 already 68s). The 3-point trend's power ceiling is stated in §6.

## 6. Decision rule (frozen, robust, no "asymptotic" claim)
Aggregate for the distributional rungs = **median** over K_null draws (frozen; not min/max).
- **SYMMETRY LEVER, model-scale (report + escalate):** Δ₁(m) > 0 at m=2 AND m=3, AND Δ₁(3) ≥ Δ₁(2)
  (gap holds or widens with the one usable increment), with m=4 as confirmatory-if-uncensored. ⇒ the
  S_m symmetry measurably lowers the first-fall degree at model scale, gap non-shrinking — consistent
  with a growth law; prereg a compute-heavy m=4/5 confirmation. This is the known symmetrized-Semaev
  direction; surfacing it is expected, not a surprise, and it is NOT called "asymptotic".
- **COEFFICIENT LEVER (report + escalate — the counter-prior's target):** Δ₂(m) > 0 (Semaev strictly
  below the symmetric-random median) at m=2 AND m=3, with min(symmetric) ≥ d_ff(Semaev) [Semaev below
  the whole symmetric spread, not one draw]. ⇒ the SPECIFIC secp group-law coefficients lower the
  first-fall degree beyond generic symmetry — a genuine curve-specific lever. Escalate, do not close.
- **NO COEFFICIENT LEVER (scoped component null):** Δ₂(m) ≤ 0 or Semaev inside the symmetric spread. ⇒
  the group-law coefficients give no first-fall advantage beyond the generic S_m symmetry at this scope.
  Scoped COMPONENT null on ONE factor of index-calculus cost (relation yield and factor-base size are
  out of frame) — explicitly NOT an avenue closure. Record magnitude + scope + the located m≥5 wall.
- **VOID:** any calibration (§4) fails, or the compared rungs are censored at the m in question.

**Power ceiling (frozen, binding):** m∈{2,3,(4)} is 2–3 integer points; a monotone read is 1–2
increments of small integers. This can SUGGEST a growth law and rank Semaev vs a K_null=12 spread (a
gap smaller than the spread's granularity, or a rank not at an extreme, is NOT detectable) — it CANNOT
prove the asymptotic. No grade above `[EMPIRICAL, model scale]` regardless of outcome. A positive-but-
non-robust pattern is reported as "LEVER-consistent, pending compute-heavy m≥4/5", never as a decided
lever or a decided null.

## 7. Exactness / fence
All arithmetic exact GF(p) (integer Macaulay ranks); `check_no_float` must pass. PRNG/generation
boundary untouched — pure summation-polynomial (curve-arithmetic) structure.
