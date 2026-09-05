# Cheap μ6-isotype-pure readouts — d-character-orbit concentration test

Date: 2026-07-18. Script `joint_shadow_cheap_isotype_v1.py`. Pre-registered by the isolated
`experiment-designer` agent (spec reproduced in the script docstring) BEFORE data. Tests the
"outside the symmetry" complement that `RESULT_joint_shadow_mu3_v1` set up: the aligned/U readout
is forced μ6-symmetric (equivariant), so it cannot separate d; do the **cheap, non-U** isotype-pure
readouts — which are NOT forced symmetric — concentrate their d-spectrum on a single DL-character?

## Readouts (6, each cheap = DLP-free function of the public point)
`(1,+) χ3(x)`, `(2,+) χ3(x)²`, `(0,+) Legendre(x)`, `(0,−) sign(y)`, `(1,−) χ3(x)·sign(y)`,
`(2,−) χ3(x)²·sign(y)`. χ3 = cubic-residue log. Scoped to **β non-cube** primes (p≢1 mod 9), where
χ3(x) is genuinely weight-1 (at p≡1 mod 9, β is a cube, χ3 collapses to weight-0 — those primes are
excluded). Each readout's isotype was **measured**, not assumed.

## Statistic + null (pre-registered)
- `R_orb = max_Ω Σ_{a∈Ω}|F̂(a)|² / Σ_{a≠0}|F̂(a)|²`, Ω over the K=(n−1)/6 μ6-orbits of characters
  (isotype purity forces |F̂| constant on each orbit ⇒ per-character max is wrong). Secondary
  `N_eff` (orbit participation) as the diffuse-concentration guard. Concentration = high R_orb / low N_eff.
- Null: **orbit-value permutation** — permute the K fundamental-domain values, re-inflate by the
  isotype phase θ_{w,s}. Preserves purity + value multiset + DC; destroys value↔orbit alignment.
  B=10000. (Dilation d→cd leaves R_orb invariant and is explicitly avoided — verified in prereg.)

## Controls (fired, all curves)
- Identities `x_λd=βx_d, y_λd=y_d, x_−d=x_d, y_−d=−y_d` = 0 (β paired to λ from data).
- Isotype measured = intended; **purity ≤ 1e-15** for all 6 readouts × 5 curves.
- Positive control: planted φ=1 (isotype-projected DL character) → `R_orb = 1.000` (Legendre
  0.97–0.99, its DC/binary skew). Graded-plant power floor φ_min ≈ 0.2–0.5 (weaker at small n).

## Result — all 30 cells NULL (both R_orb and N_eff)
5 curves (p,n,K) = (211,199,33), (349,313,52), (547,547,91), (733,691,115), (823,829,138).
Every cell: pR > α′ and pN > α′ (α′=0.05/6=0.0083). No readout departs on any curve.

Extreme cells (closest to, but not crossing, threshold):
- `(0,−) sign(y)` at p=823: pR=0.0156 (> α′), **single curve**; sign(y) at the other four: pR =
  0.41 / 0.21 / 0.78 / 0.93. Isolated fluctuation, not replicated ⇒ null.
- `(1,−)/(2,−) χ3·sign` at p=823: pN=0.064 (> α′), single curve. Not replicated ⇒ null.

**Pre-registered conclusion (verbatim scope):** no per-point DL-character-orbit concentration in
any μ6-isotype-pure cheap readout, **scoped to** {these 5 curves, n ≤ 829, concentration fraction
φ ≳ 0.2–0.5 (the power floor)}. This is **not** "cheap readouts cannot leak": structure below
φ_min, at larger n, in the diffuse N_eff channel at larger n, or in a **non-μ6-covariant** cheap
readout (a raw coordinate bit, x mod 2, high bits of x — outside this isotype decomposition) is
not excluded.

## Flagged, not banked (direction-consistent sub-threshold)
`(1,+)/(2,+) χ3` (weight-1/2, the new "outside" channels the earlier anti-invariant probe could not
reach) sits **above** its null mean on 4 of 5 curves — pR = 0.10 / 0.13 / 0.48 / 0.20 / 0.19,
Fisher-combined ≈ 0.08. Below α′ and below the power floor; direction-consistent. Pre-registered
follow-up: retest at larger n (higher power) before this is called either a null or a signal.

## Map position
- `RESULT_joint_shadow_decompose_v2`: joint-shadow magnitudes are generic (char = random); the
  d-specific content is the exact even/odd constraint.
- `RESULT_joint_shadow_mu3_v1`: the aligned/U readout is forced μ6-symmetric (flat across CM
  weights) — the part that cannot separate d.
- **This file**: the cheap non-U isotype-pure readouts — the complement where the principle says
  d-structure could sit — show no orbit-concentration above the power floor, across 5 curves. The
  `(0,−)` odd-y row extends `RESULT_anti_invariant_probe_v1`; the `(1,±)/(2,±)` χ3 rows are new.
- Untested and named: sub-φ_min regime, larger n, N_eff at larger n, and non-isotype (non-covariant)
  cheap readouts.

## Scope / exactness
Signal path exact integer (curve mod p; χ3=pow(x,(p−1)/3,p); Legendre=pow; sign exactly odd).
Float only in DFT/|·|² (analytic size, no key material). secp (2²⁵⁶) not enumerable; no secp claim.
No exploitability assessed.
