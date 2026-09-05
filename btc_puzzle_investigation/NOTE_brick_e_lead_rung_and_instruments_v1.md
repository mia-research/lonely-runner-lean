# NOTE — Brick E opened: instruments located, I1 covariance verified exactly, p=43 LEAD rung reads GENERIC (D=4); the powered ladder run is the defined next session

**Date 2026-08-22.** Status: the frozen prereg `PREREG_brick_e_cd_degree_v2.md` (SHA freeze VERIFIED
against its `.sha256` this session) is runnable; this note records the session's lead-rung
exploratory read and the instrument map, so the full run starts from a known state.

## Instrument map (the prereg's citation is path-incomplete, not missing)

- `lbe_dlog.sage` (the S-projection + dlog instrument, p=43) lives at
  **`scratchpad/session_2026-08-11/lbe_dlog.sage`** (+ compiled `.sage.py`), alongside
  `lbe_full_test2.sage`. To be generalized to the ladder {67, 79, 163, 211, 547} per prereg §6.
- Engine `brick_e_degree_fitter_v1.py` exists at repo root (211 lines, prereg: exact, unit-tested).
- The p=43 REAL-ARM DATA already exists — the I1 table (`OPEN_lbe_isotypic_projection_v1.md`):
  $e(d) = \mathrm{dlog}_{S(G)} S([d]G) \in \mathbb{Z}/1893$ for all 15 QR-half $d$.

## What this session verified exactly (no float, from the I1 table)

1. **μ₃-covariance is EXACT on all five orbits:** $e(\lambda d) = \kappa^2 e(d)$ (κ = 1849, κ³ ≡ 1 mod
   1893) on every orbit {d, λd, λ²d} of the QR half. This (a) answers `OPEN_lbe_isotypic_projection`'s
   open question 2 (yes — constant on orbits up to the eigenvalue), (b) validates the I1 table's
   internal consistency, and (c) confirms the real data satisfies exactly the propagation law the
   prereg's μ₃-null assumes. Free content = (n−1)/6 = 5 values, as the prereg's power accounting says.
2. **LEAD rung (p=43) exploratory degree read:** the 5 free values (orbit reps d = 3, 4, 6, 12, 17;
   e mod 631 = 1, 206, 453, 189, 272 — all distinct) have minimal polynomial degree **D = 4 mod 631 —
   the generic value** (a D ≤ 3 fit imposes 1 linear condition: null P ≈ 1/631 ≈ 0.16%, so D_obs = 4
   sits at the ~99.8th null percentile — the "no reduction" arm). The mod-3 factor is ill-posed for
   degree (three reps collide mod 3) — as the prereg says, a consistency flag only. **Exploratory,
   LEAD-only** (5 reps = no power, per prereg §6); no grade moves.

## The defined next session (the powered run, per the frozen spec)

1. Generalize `lbe_dlog.sage` to the ladder rungs 67/79/163/211/547 (each verified admissible).
2. Run the four controls — (i) engine [exists], (ii) μ₃-covariant plant through the FULL null+π
   pipeline, (iii) calibration (π uniform on null draws), (iv) the ρ-identity structural control in
   F_{p²} (needs the explicit ζ₄ endomorphism on the instrument). ALL must fire before the real arm.
3. Real arm at rungs ≥ 163 (reps ≥ 23): D per large CRT factor; the powered claim is
   **degree-stability across the ladder**; falsifiers independent of the null: D_obs ≥ null-max, or
   instability ⇒ `[VERIFIED-scope — degree ≥ D₀ bound]` (the cover-scramble bound — Brick E's
   either-way deliverable).
4. Echo the prereg SHA before reading any real arm (freeze verified this session: `e3fe35d0…`).
