# RESULT — R1/R2: the finer object (full graded resolution) is ALSO curve-blind — μ₃ supplies no distinguishing syzygies. The solving-degree lever is null at accessible scale on every invariant tested, coarse and fine

**Date:** 2026-08-15. Follows `RESULT_mu6_isotypic_solving_degree_P2b_v1.md` (scalar `d_LF` null) and
`ANALYSIS_mu6_solving_degree_m4m5_mechanism_v1.md` (which isolated R1 = the finer ω-graded syzygy module,
R2 = lower-order last-fall sensitivity at m=4/5). Scripts (exact GF(p), `check_no_float` clean):
`r1_syzygy_m2.py` (per-isotype fall profile), `r1_fixed_betti.py` (matched-quo graded Betti via Singular).
No leakage/ECDLP claim; model-scale.

**Grade:** R1 finer-syzygy lever `[VERIFIED — NULL, matched-quo, quo=2, m=2, p=523; single clean cell]`;
R2 accessible-scale `[VERIFIED — NULL, m=2,3, whole resolution]`; R2 at m=4/5 `[OPEN — compute-intractable]`.

## R1 — the ω-graded syzygy module: three finer invariants, all curve-blind
1. **Per-isotype fall profile** (which syzygies resolve at which degree, by isotype), CM target-orbit,
   m=2: isotype 0 falls at {9,12,15}, 1 at {10,13}, 2 at {11,14}. The **degrees are forced by the mod-3
   grading** (isotype r lives only in degrees ≡ r mod 3) — a grading artifact, not a CM signal.
2. **The CM target-orbit cannot be quo-matched to a non-CM analog:** CM-orbit quos ∈ {6,18} (multiples of
   3 — the three-fiber structure), non-CM {2,4}. The isotypic comparison is ill-posed by construction (the
   orbit is always 3× a fiber), so it carries no CM-vs-generic lever.
3. **The clean well-posed test — full graded Betti of the *fixed-target* ideal, CM vs #E-matched non-CM,
   at MATCHED quo (quo=2, m=2):** the resolutions are **IDENTICAL** (`r1_fixed_betti.py`). The whole
   syzygy structure — not just the last-fall degree — is curve-blind.

> **⇒ R1 null:** the μ₃/ω symmetry supplies no distinguishing syzygies. The finer object the record's
> follow-up #1 called for is curve-blind at matched quo, strengthening the P2 scalar `d_LF` null to the
> entire free resolution.

## R2 — lower-order last-fall sensitivity, j=0 vs generic
- At **m=2,3** the first-fall degree is curve-blind (leading forms, all m) and now the **whole resolution**
  is identical CM vs non-CM at matched quo (R1.3). So the last-fall degree's lower-order sensitivity does
  **not** distinguish j=0 from generic at accessible scale. `[VERIFIED — NULL, m=2,3]`.
- At **m=4/5** direct compute is intractable (S₆ build >240s). R2 there is a *mechanism* question, not a
  measurement; the only place a lever could hide is the last-fall lower-order structure appearing at high m
  against all the accessible-scale evidence. `[OPEN]`.

## Scope, power, and what is NOT closed (anti-enlargement)
- **Object:** a μ₃/ω solving-degree / syzygy lever for prime-field Semaev decomposition, on any invariant
  finer than or equal to `d_LF`.
- **Power:** `d_LF` null (13 cells, P2b); per-isotype fall profile forced-by-grading; **full graded Betti
  identical CM vs non-CM at matched quo** (the strongest single statement — whole resolution, not a scalar).
- **Scope:** m∈{2,3}, accessible scale; the matched-quo Betti is one clean cell (quo=2, m=2) — a sweep over
  more matched-quo cells and m=3 would strengthen it (owed).
- **OPEN — not closed:** (i) m=4/5 (R2, intractable — mechanism-only); (ii) more matched-quo Betti cells /
  m=3; (iii) the R1 **yield** channel and today's **P1′ phase** lead — *separate real positives*, untouched
  by this; (iv) full IC-cost; (v) the 120°/CAP-uniformity and CM-Hecke/monodromy sub-threads. The ω-symmetry
  is real exact structure at all m — its *computational-lever* manifestation is null at accessible scale;
  it is not a wall, and the live positives are the yield/phase channels, not this.

## Owed / gates
A matched-quo Betti sweep (more cells, m=3) before promoting R1 beyond the single cell. `citation-verifier`
on Caminata–Gorla (as inherited). Promotion into a master → `compile-diff` (target v9). Leaf RESULT.
