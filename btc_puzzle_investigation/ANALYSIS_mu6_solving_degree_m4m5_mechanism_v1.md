# ANALYSIS — the m=4/5 mechanism: does the ω-symmetry lower the S₅/S₆ solving degree? The isotypic-block channel is argued-null at ALL m; the residual open piece is isolated

**Date:** 2026-08-15. A *mechanism* run (compute is intractable at m=4/5, so this is an argument, not a
sweep), grounded by two exact m=4 checks (`m4_mechanism_check.py`, exact GF(p)). Follows
`RESULT_mu6_isotypic_solving_degree_P2b_v1.md` (the m=2,3 δ_r null). No leakage/ECDLP claim.

**Grades:** first-fall curve-blindness `[VERIFIED — leading forms, m≤4; PROVED-isobaric all m, record B1]`;
isotypic-block degree-lever null `[ARGUED — structural, all m; VERIFIED m=2,3]`; the residual last-fall
question `[OPEN]`.

## 0. Two exact m=4 facts (grounding)
- **S₅ (m=4) is σ-covariant for j=0:** `S₅(βx₁,…,βx₅)=β²·S₅` `[VERIFIED]` (κ: m=2→1, m=3→0, m=4→2). The
  ω-symmetry is a real exact feature of the Semaev system **at every tested m**, not an m=3 accident.
- **The leading form of S₅ is curve-independent** (free of A,B) `[VERIFIED]` (degree 32, 495-term top form).
  So the **first-fall degree is curve-blind at m=4** too — no first-fall lever at any m (record B1 isobaric,
  re-confirmed at m=4).

## 1. The isotypic-block lever is null at ALL m — a structural argument, not a computation
The m=2,3 result measured δ_r ≤ 0 (blocks never resolve below the plain solve). The reason is structural
and **m-independent**:

1. **The target-orbit ideal = the three fixed-target fibers at {t, βt, β²t}** (`xT³−t³` has roots
   `{t,βt,β²t}`), for any m. `[PROVED — variety decomposition]`
2. **The three fibers are [ω]-isomorphic:** `[ω]:(x,y)↦(ζ₃x,y)` is a group automorphism of E, so it bijects
   decompositions summing to (the preimage of) `t` with those summing to `βt`, acting on x-coordinates as
   `xᵢ↦βxᵢ`. Hence fiber(βt) = β·fiber(t) coordinatewise, and all three have the **same last-fall degree =
   the plain fixed-target solve**. `[PROVED — automorphism, any m]`
3. **The ω-isotypic blocks are twisted combinations of three isomorphic fibers** (the regular μ₃-rep on the
   fibers ⊗ the 12-dim fiber). No block can resolve **below** the common fiber degree, because each block's
   last fall is bounded below by the shared (curve-blind) leading-form floor and the fibers sit at the plain
   solve. Measured directly at m=2,3: block degrees = fiber degree + {0,+1,+2} mod-3 offset, `δ_r ≤ 0`.
   `[VERIFIED m=2,3; ARGUED all m]`

> **⇒ The P2-follow-up-#1 isotypic-block solving-degree lever does not exist at any m** (steps 1–2 rigorous
> at all m; step 3's "no block below the fiber degree" verified m=2,3 and structurally motivated at all m —
> the one soft link, flagged, not papered over). This *extends* the m=2,3 null to m=4/5 **by mechanism**,
> which is exactly what compute cannot reach — and it does so without enlarging: it is the same object
> (3 permuted fibers) at every m.

## 2. What this does NOT settle — the genuinely open residual at m=4/5
The argument above closes **one** channel (the target-orbit isotypic blocks). The ω-symmetry could still
lower the **solving/last-fall degree** at m=4/5 through a *different* mechanism, and this is untested:

- **(R1) The finer ω-graded syzygy module.** A scalar per-block `d_LF` cannot see whether the ω-equivariance
  reshapes *which* syzygies resolve when. At higher m the syzygy module is richer, so "symmetry supplies
  syzygies" has more room than at m=2,3. The isotypic-block null does not touch the graded Betti / Castelnuovo–
  Mumford-regularity refinement. **OPEN.** (This is `RESULT_mu6_solving_degree_v1` follow-up #1's deeper half.)
- **(R2) Lower-order last-fall sensitivity, j=0 vs generic, at m=4/5.** The last-fall degree "can see lower-
  order terms" (record B2), where the ω-covariance of the *whole* S_{m+1} (a j=0-specific feature — generic
  curves are ω-symmetric only in the leading form) lives. Whether that lowers the last-fall degree at m=4/5,
  through a route other than the target-orbit blocks, is not computable here (S₆ build >240s) and not argued.
  **OPEN.**

## 3. Net (anti-enlargement, per `feedback_negative_bias_enlarge_nulls`)
- **Closed (scoped):** the isotypic-block degree lever (P2 follow-up #1's scalar form) — argued-null at all m
  via the 3-fiber structure, not just measured at m=2,3.
- **NOT closed:** (R1) the ω-graded syzygy-module refinement; (R2) the lower-order last-fall sensitivity at
  m=4/5 by non-block mechanisms; and everything the parent RESULT lists (yield/phase channels, uniformity,
  full IC-cost). The ω-covariance is a real exact structure at all m — a potential lever via (R1)/(R2), not a
  wall.
- **What would move it:** (R1) an ω-isotypic **graded-Betti** computation at m=3 (tractable) to see if the
  syzygy *degrees* — not the scalar `d_LF` — differ by isotype; if they do, that is the finer lever object
  and it can then be argued toward m=4/5. This is the concrete next probe, and it does not need the
  intractable m=4/5 compute.

## 4. Owed / gates
`citation-verifier` on Caminata–Gorla (solving degree ≥ last-fall degree) before any grade rests on the
last-fall→cost link. Promotion into a master → `compile-diff` (target v9). This is a leaf analysis.
