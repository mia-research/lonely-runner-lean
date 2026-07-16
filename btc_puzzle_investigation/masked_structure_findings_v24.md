# Findings v24 — the substrate cross-domain bet: two substrates, bridged (not one)

**Date:** 2026-07-17 · `substrate_crossdomain_v1.py`. Item #5 (exploratory) — does secp's
thermal/critical/single-well (random-matrix / GUE) lens transfer to the φ-residue RH objects and the
Lonely Runner Conjecture (LRC)? Tests "one programme" rather than asserting it. **Framing bet,
graded EMPIRICAL/CITED — not a theorem** (v18's own caveat: the lens is scaffolding).

## Source-first: the user's own bridge (LRC → φ(n) → Berry–Keating → ζ)

The user's *"Self-Adjoint Realization of the Berry–Keating Operator with φ(n)-Residue Structure"*
derives the φ(n)-residue structure **directly from the Lonely Runner setup** (§1): arithmetic-
progression runners `v_i = v₀+(i−1)δ`; uniform separation `min_{i<j} d(θ_i,θ_j) ≥ 1/n`; **Theorem
1.1: uniform separation occurs at exactly `φ(n)` times** (the coprime residues `gcd(r,n)=1`). That
φ(n)-coprimality sets the operator's boundary conditions ⇒ spectrum `{πk²}` ⇒ Jacobi theta ⇒
Riemann `ξ(s)` functional equation. So "Lonely Runners → Riemann Zeta Spectrum" is the user's own
programme, and item #5 is the right place to test whether it is *one substrate* or a *bridge*.

## Test: nearest-neighbor level-spacing statistics (normalized, mean 1)

Discriminator — **level repulsion / minimum gap** separates the universality classes:
soft (GUE, chaotic) vs hard-gap (arithmetic) vs picket-fence (integrable) vs Poisson.

| object (programme role) | min-gap | P(s<0.3) | cv | class |
|---|---|---|---|---|
| **Riemann ζ zeros** (RH, chaotic end) | 0.29 | 0.007 | 0.37 | **GUE** (soft repulsion) |
| GUE matrix (calibration) | 0.09 | 0.030 | 0.45 | GUE |
| **secp `\|T(a,b)\|²`** (chaotic end) | — | — | — | **Porter–Thomas** `[CITED v18]` (GUE class) |
| **Berry–Keating `{πk²}`** (RH operator, rigid end) | 1.00 | 0.000 | 0.00 | **picket-fence** (integrable) |
| **totatives `{r/n:gcd=1}`** (LRC φ(n) residues, rigid end) | 0.36–0.42 | **0.000** | 0.55 | **arithmetic hard-gap** |

(totatives at n = 2310, 30030, 510510 = primorials; min-gap `≈ 2φ(n)/n`, a **hard** floor —
all totatives of an even n are odd ⇒ gaps ≥ 2.)

**The clean discriminator:** ζ zeros have *soft* repulsion (`P(s<0.3)=0.007 > 0`, small gaps rare but
present, cv≈0.37 — GUE, matching the GUE-matrix calibration); the totatives have a *hard* gap
(`P(s<0.3)=0.000` exactly, min-gap ≈0.4) — a different, arithmetic class, **not GUE.**
(Self-correction: a first pass mislabeled the totatives "GUE-like" from `P(s<0.1)=0` alone, which
conflates GUE's soft quadratic repulsion with a hard arithmetic gap. Min-gap + `P(s<0.3)` separates them.)

## Verdict (framing bet)

**The programme spans TWO opposite substrates, joined by a bridge — it is NOT one shared substrate:**
- **Chaotic / thermal / GUE:** secp Frobenius (Weil criticality + Porter–Thomas, v18) and the Riemann
  ζ **zeros** (Montgomery–Odlyzko GUE `[CITED]`). *secp's thermal lens matches this side.* This
  correspondence is the Katz–Sarnak philosophy (zeta functions of families ↔ random-matrix statistics)
  — real and deep, but **known**, not novel to this project.
- **Rigid / arithmetic / integrable:** the LRC uniform-separation φ(n) residues (arithmetic hard-gap)
  and the Berry–Keating `{πk²}` operator spectrum (picket-fence). **secp's thermal lens does NOT
  describe this generating side.**

The user's "Lonely Runners → Riemann Zeta Spectrum" is precisely a **bridge from a rigid arithmetic
generating structure to a chaotic zero distribution** (via theta / Mellin / Hecke). The programme's
content *is* that bridge — the emergence of GUE zeros from an integrable `{πk²}` operator — which is
the essence of the Hilbert–Pólya / Berry–Keating idea. "One programme" is true as a *bridge between
two substrates*, false as *one shared substrate*.

## Grades (locked)
- ζ-zero GUE / Montgomery–Odlyzko: **CITED** (verified numerically, 300 zeros, soft repulsion).
- secp Porter–Thomas: **CITED** (v18).
- `{πk²}` picket-fence, totative hard-gap: **VERIFIED** (analytic + computed, primorials to 510510).
- Two-substrate-bridge verdict: **EMPIRICAL framing bet, NOT a theorem.** It does not prove or
  disprove RH or LRC; it classifies where each object sits on the integrability↔chaos axis.
- **Scope:** 300 ζ zeros (finite-height, slightly more rigid than asymptotic GUE — known); the lens
  is a heuristic. No claim about the *correctness* of the user's RH framework — only where its
  objects sit on the RMT axis.

## Files
Engine: `substrate_crossdomain_v1.py` (mpmath ζ zeros, totative/operator spacings; analytic-size, no
signal path). Source: `~/Downloads/A Self-Adjoint Realization of the Berry–Keating Operator with
φ(n)-Residue Structure_.md` (the LRC→φ(n)→BK→ζ chain). secp anchor: `masked_structure_findings_v18.md`.
