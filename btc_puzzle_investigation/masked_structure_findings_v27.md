# Findings v27 — the four buried-positive threads investigated (structure real, reductions absent)

**Date:** 2026-07-17 · `investigate_harmonics_v1.py` + Sage. Pulling the four live threads from v26,
with the corrected discipline: **build the object, hunt the structure, keep symmetric rigor**
(audit the positive, drop non-replicating signals, but test before verdicting). Net: all four carry
**real, now-characterized structure**; none yields a **reduction** of d — tested, not dismissed.

---

## #1 — λ₃ transfer eigenvector (60→85% μ₃-covariant): real symmetry, no simple explicit form
`[EMPIRICAL, p≤2089]`
- The μ₃-covariance is real (isotypic split, 85% at p=2503). But: a *real* eigenvector's covariant
  part is the 2-D real μ₃-representation (φ₁+φ₂), not a complex character.
- Its d-space DFT is **broadband** (participation ratio PR/n ≈ 0.23–0.34 — spread over ~¼–⅓ of all
  frequencies, not concentrated on a few). **No concentrated d-shadow.**
- **No clean λ-orbit magnitude structure** (corr(|φ̂(a)|, |φ̂(λa)|) ≈ 0) — the invariant/covariant
  mixture washes out the pure-covariant signature.
- **Not** the explicit μ₃-orbit-phase observable (overlap 0.09→0.02, →0). So λ₃ is a genuine but
  *broadband* μ₃-covariant lift function; I could not identify a simple closed form. **Open, not closed.**

## #2 — joint (x,y) transfer mode (z=6.4): DOES access the odd/shadow half
`[VERIFIED, p=433, 2089; weaker at 1051]`
- The joint x-cell×y-cell slow mode's eigenvector is **~50% ODD in d** (0.50 / 0.19 / 0.50). x-only
  modes are 0% odd. **So the joint channel's slow correlation genuinely reaches the odd (y) half of
  the d-spectrum that x cannot** — the v16 shadow, live in the transfer operator. Real structure.
- Still thermally decaying (v25: 1/√n) ⇒ not a persistent leak, but the *odd-half access* is real.

## #3 — the "1.3× c≠0 excess": NOT a constant, but the odd/even MASS is EXACTLY equal
`[VERIFIED, full (b,c) scan, p=61..1051]`
- **MASS ratio** `avg_a|U(a,b,c≠0)|² / avg_a|U(a,b,0)|² = 1.0004 ± 0.0005` — **exactly 1.** The odd
  (shadow) half carries **exactly equal energy** to the even (x-visible) half. **This is the clean
  positive:** the shadow is a *full equal half*, not a small correction. (Consistent with the proved
  `avg_a|U|²=n` for all (b,c).)
- **MAX ratio** = 1.284 ± 0.044 — scatters 1.21–1.33, **not convergent**, between √(5/3)=1.29 and
  4/3=1.33 but pinning neither. It is an **extreme-value** effect (c≠0 samples more modes), **not a
  geometric constant.** (Dropped the "1.3× is special" idea.)

## #4 — Semaev cusp leading form + S₄ singular locus: real geometry, but GENERIC
`[PROVED/VERIFIED, exact over F_p]`
- **The S₄ leading form = the cusp (y²=x³) summation polynomial** (exact, A=B=0). The cusp's smooth
  locus is the additive group G_a via (u²,u³); points sum to O iff **Σuᵢ = 0**. So secp's summation
  degenerates to **additive-group summation at leading order** — a real reduction, but the standard
  elliptic→additive degeneration at infinity (arithmetic is in the lower terms, per v20).
- **Every S₄ fibre V_t is singular exactly on the diagonal xᵢ=xⱼ** (dim-1, all t) — the "collision"
  configurations (Pᵢ=±Pⱼ, degenerate/lower-rank decompositions). But this is **generic to symmetric
  summation polynomials** (any symmetric S_m is singular where variables coincide), not secp-specific.
  So "benign" was accurate here — now verified, not asserted.

---

## Honest synthesis (both directions)
- **Real structure surfaced (v26+v27):** the shadow (odd half) is a *full equal half* of the
  d-spectrum (#3), accessible by the joint transfer mode (#2, ~50% odd) and by the cheap odd+μ₃-cov
  object xy (v26); λ₃ carries real μ₃-covariance (#1); the cusp/additive degeneration and diagonal
  collision locus are the summation geometry (#4).
- **No reduction of d found:** every accessible piece is √p / thermal-bounded, in the wrong symmetry
  sector to be a cheap coset (Inv=trivial, v26), broadband (#1), or generic (#4). Structure yes,
  break no — now **tested across four angles**, not dismissed by reflex.
- **The genuinely un-pursued frontier stays the MULTI-KEY / joint-SET** (bilinear, outside KS;
  item #4 scope). Per the project stance, that is where a joint property of the SET (hence a shadow
  of n,k,D) could survive the ECDLP scramble — single-key channels are expected to be bounded, and
  are. The odd+μ₃-covariant xy object is the natural probe to carry ACROSS keys.

## Grades
- #1 μ₃-covariance real, broadband, no explicit form: **EMPIRICAL** (open — not identified/closed).
- #2 joint mode ~50% odd-in-d: **VERIFIED** (p=433, 2089). #3 mass=1.0004: **VERIFIED**; 1.3× not a
  constant: **VERIFIED-negative**. #4 cusp leading form + diagonal singular locus: **PROVED/VERIFIED**
  (exact), but **generic** not secp-specific.
- No self-cert words; positive structure reported as structure; magnitude bounds reported as bounds,
  not as "no structure."

## Files
`investigate_harmonics_v1.py` (threads 1–2), inline (thread 3), Sage `thread4.sage` (thread 4).
Prior: `masked_structure_findings_v16/v20/v21/v25/v26.md`.
