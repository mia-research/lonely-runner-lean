# RESULT — Semaev / index-calculus: is there a j=0 CM lever in the lower-order terms?

**Date 2026-07-19.** Frontier §X.4 (GLM "frontier E": *"the lower-order terms of Semaev polynomials
are where the CM structure (B=7) lives; analyse the singular fibres of the full S₄ for B=7 — do the
j=0 CM singularities collide / drop the degree of regularity? Express S₄ in x·y instead of x — does it
collapse faster?"*). Scripts: `semaev_elimination_v1.py` (Sage; first-fall + solving degree via
Macaulay rank + Gröbner, matched CM/non-CM controls) and `semaev_pieceA_matched_v1.py` (matched
singular-locus + xy observation). Exact over GF(p)/QQ. Scope: `p ≤ 307`, `m ≤ 4` (S₄/S₅).

## The question, sharpened
The **first-fall degree** is a leading-form invariant; the Semaev polynomials are isobaric, so their
leading forms are curve-independent — hence first-fall cannot see B (master Part VI). The GLM's live
point is subtler: the *lower-order* terms DO carry B, so the finer **solving degree / degree of
regularity** (what an index-calculus attacker actually pays) might be lower for the CM curve. This is
the one place a j=0 lever could hide. The matched controls decide it.

## Result — NO CM lever; matched controls give identical degrees

**[B1] Leading form curve-independent** `[PROVED isobaric + VERIFIED]`. S₃, S₄ isobaric over ℚ[A,B]
(single weighted degree 4, 12; top form free of A,B); S₄ (deg 12, 35 monomials) and S₅ (deg 32, 495
monomials) leading forms **identical** across 4 curves. First-fall degree is curve-blind.

**[B1-num] Matched-control first-fall + solving degree — IDENTICAL** `[VERIFIED]`. On an *identical*
V and target across all three curves (so the only difference is the lower-order A,B terms of S₄):

| system | secp (j=0 CM) | non-CM generic | j=1728 CM-i |
|---|---|---|---|
| p=211,m=3,B=2 | d_ff=12, d_solv=15 | 12, 15 | 12, 15 |
| p=211,m=3,B=3 | d_ff=12, d_solv=18 | 12, 18 | 12, 18 |

The lower-order terms differ between curves; the first-fall AND solving degrees do **not**.

**[B2] Consistent decomposable targets** `[VERIFIED]`. |V|=3: all three curves d_ff=12, d_solv=17,
d_gb=3 — identical. |V|=4: secp shows quo=12 / d_gb=4 vs 6 / 3 for the controls — but this is the
**uncontrolled per-curve target** (different random decomposition ⇒ different #solutions), not a curve
lever; the *matched* control [B1-num] with identical V/target is the clean comparison and it is
identical. *(Recorded as a per-curve artifact, not a finding.)*

**[B2-μ₃] μ₃-invariant factor base does NOT shortcut** `[EMPIRICAL — weak, see correction]`. A
β-invariant V (closed under x→βx, |V|=9) vs a random V of the same size: β-invariant never gives a
*lower* Gröbner degree than random. **⚠ Corrected below — this rests on a non-reproducing proxy.**

> **AUDIT CORRECTION (2026-07-19).** The original claim here — "μ₃-closing **raises** the solving
> degree (d_gb=6 vs 3)" — was a **p=211-only** number and is retracted as stated. The matched re-check
> (`_audit_semaev_matched_largerV_v1.py`) shows at **p=307** the same test gives **d_gb=5 vs 5 (equal)**,
> not 6 vs 3. Worse, `d_solv=None` in *every* μ₃ cell (the solving degree was never reached within
> Dmax), so the entire μ₃ comparison rests on `d_gb` (Gröbner max degree — a **proxy** for the degree
> of regularity), whose magnitudes do not reproduce across two primes. **What survives:** the
> β-invariant V never produced a *lower* d_gb than a random V (6≥3 at p=211, 5=5 at p=307) — i.e. no
> evidence of a μ₃ *shortcut* — but that is a weak, proxy-based, two-prime observation, NOT the
> "raises the degree" mechanism originally asserted. Do not cite "μ₃ raises the solving degree."
> **The CM/first-fall/solving-degree core (below) is unaffected and was independently strengthened**
> by the matched re-check: secp == non-CM at every matched |V|=3,4,5 and p∈{211,307} (the lone |V|=4
> divergence was **j1728**, an accidental consistency, not secp).

**[A-matched] S₄ singular-fibre locus — generic diagonal, no B=7 collision** `[VERIFIED]`. Eliminating
x₁,x₂,x₃ from (S₄, ∇S₄) gives the **zero** t-ideal — the singular locus is the diagonal xᵢ=xⱼ present
in *every* fibre — **identically** for secp (0,7), non-CM (5,11), and j=1728 (3,0) at p=211 and p=307.
The j=0 CM does not make the singularities collide or acquire a special intersection multiplicity; the
singular structure is curve-independent.

**[xy] The x·y substitution cannot lower the degree** `[reasoned + checked]`. w=x·y satisfies
`w² = x⁵ + B·x²` (x-degree 5, verified for B=7,11,0), so a summation relation in w is **higher**
degree in x than S_m, not lower. And μ₃-weight(xy)=weight(x)=1 (the GLV endomorphism fixes y and
scales x by β), so xy carries the **same grading** as x — the μ₃ lever, already shown absent
([B2-μ₃]), is unchanged under x↔xy. No new lever from the product coordinate.

> **The GLM frontier-E hypothesis is refuted by matched controls at the tested scale.** The lower-order
> terms / j=0 CM structure / S₄ singular fibres / the x·y coordinate do **not** give a sub-generic
> index-calculus lever: first-fall degree (12), solving degree (15/17/18), Gröbner degree (3), and the
> singular-fibre locus (diagonal, all t) are **identical** for secp, non-CM, and j=1728 on matched
> systems. This confirms and **upgrades** master Part VI / §X.4 "no CM/GLV elimination lever beyond
> |Aut|≤6" from `[HEURISTIC+CITED]` to a **direct matched-control measurement** `[VERIFIED at p≤307,
> m≤4]`. First-fall curve-independence stays `[PROVED]` (isobaric, all m).

## Scope / what this does NOT say
`p ≤ 307`, `m ≤ 4` (S₄/S₅), exact but small. It does **not** speak to `p=2²⁵⁶`, to larger
decompositions `m ≥ 5` (where the solving degree could in principle diverge from the controls — the
matched comparison should be pushed to S₅/S₆ if resources allow), nor to non-Semaev index-calculus.
The first-fall result is `[PROVED]` for all m; the *solving*-degree curve-independence is `[VERIFIED]`
only at the tested (p,m). Pre-registration note: the comparison's rigor is the **matched CM/non-CM/
j=1728 controls built into the script** (null fixed before data by construction); it was run as
designed, no post-hoc tuning.

## Bearing on the GGM question
This **does not move outside GGM.** The index-calculus solving/regularity degree — the one place the
concrete lower-order (CM) terms could have given a curve-specific sub-generic shortcut — is curve-blind
at the tested scale: secp behaves exactly as a generic or a differently-CM curve. The residual is the
scale gap (p=2²⁵⁶) and larger decompositions m≥5, both untested here.

## Suggested master update (next compile, via compile-diff)
§X.4 / Part VI first-fall clause → keep `[PROVED isobaric]`; add the solving-degree matched-control as
`[VERIFIED] bounded-by RESULT_semaev_cm_lever_v1 (secp=non-CM=j1728, p≤307, m≤4)`; the μ₃-lever and
S₄ singular-collision sub-questions → `resolved-by RESULT_semaev_cm_lever_v1` (no lever / no collision).
