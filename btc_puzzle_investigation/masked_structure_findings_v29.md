# Findings v29 — looking at D and derr (the Dₖₙ/D_err lens) on the real keys

**Date:** 2026-07-17. Prompted by: *"make sure you look at D and d'err"* — the Dₖₙ/D_err object that
found the Eisenstein lift, rhombus, sextic, and 3/4:1/8:1/8 (cap/flap) geometry. I had found `xy→D`
(the `(X·Y)mod64 → D_terms` shadow) but treated it as inert single-key; I had **not** looked at
`derr = |n(d−A) − kA|` at all, nor applied the lift lens to the (D, derr) residual. This records that
look on the real 82 solved keys (exact ints; `solved_keys_augmented_v1.csv`).

## What I looked at
- **Per-key correlations** `(X·Y)mod64` vs `D_terms / derr / d / n / k`: all `|corr| ≤ 0.09` on 82
  keys — null, but **low power** (n=82 needs `|corr|>0.22` for p<0.05). Not informative either way.
- **μ₃ residues** of `derr, n, k, D_terms, d, xy`: generic `{~1/3,1/3,1/3}` except `D_terms[0] mod 3
  = {0:0,1:80,2:2}` — a **tautology** (the greedy unit-fraction expansion starts at `1`, so
  `D_terms[0]≈1`), not structure.
- **★ A real lead: derr ↔ cap.** All **11 derr=0 keys are in the μ₃-core** (flap fraction **0.00**),
  while derr>0 keys sit at **0.24** (≈ the cap-law ¼). A key-side-residual ↔ curve-lift-geometry link
  — exactly the Dₖₙ/D_err → cap shape. **But confounded:** all 11 derr=0 keys are tiny-bit (≤13).

## The lead disentangled (powered) — it is a bit-length confound
Constructed derr=0 keys at **fixed** bit-length (`d = A + k·A/n`, `n` a power of 2 ⇒ exact (n,k)
approximation ⇒ derr=0 at any bits) vs random-in-band (derr>0) controls, 200 each, and measured the
cap flap fraction:

| bits | derr=0 flap frac | derr>0 flap frac | P(derr=0 ≤ obs \| ¼) |
|---|---|---|---|
| 40 | 0.260 | 0.265 | 0.66 |
| 64 | 0.250 | 0.325 | 0.54 |
| 96 | 0.235 | 0.240 | 0.35 |
| 128 | 0.285 | 0.270 | 0.89 |

**At fixed non-tiny bits, derr=0 keys have exactly the generic cap-law ¼ flap fraction, indistinguishable
from the derr>0 control.** So the real-key "derr=0 → core" is the **small-d / bit-length confound**,
not a real derr↔cap geometric connection. `[VERIFIED, disentangled, bits 40–128, 200/cell]`

## Honest state
- No key-side-residual (D, derr) → curve-side-lift-geometry (cap/μ₃) connection survives, beyond the
  (tautological) fact that both live on the ℤ[ω] lattice. `xy→D` remains a **modular tautology** (both
  encode d), not a lift-geometry leak.
- **The lift geometry itself is real and PROVED** (cap law `ε≠0⟺|u−v|>½`, densities ¾:⅛:⅛; rhombus;
  sextic — `cap_law_proofs_v1.md`, `btc_puzzle_lift_sextant_law`). It is the **curve/lattice** geometry,
  present independent of keys. The question here was whether the KEY residual connects to it; on these
  keys + constructed controls, it does not beyond confounds.
- **Caveat (open):** my reconstruction of "Dₖₙ/D_err" may not be the exact object that found the lift
  geometry. I looked at correlations, μ₃ residues, and the derr↔cap link. If the intended object is a
  specific ratio/derivative (D/derr) or a distributional lattice statistic, that aspect is untested —
  the exact object should be pinned before concluding.

## Grades
- derr↔cap connection: **VERIFIED-negative** (disentangled confound, bits 40–128). Per-key xy↔(D,derr):
  **null, low-power** (82 keys). D_terms[0] mod 3: **tautology**. Lift geometry (cap/rhombus/sextic):
  **PROVED** (curve, not key). Method: found the lead, extended with a powered disentangled test, did
  not inflate a confound into a finding.

## Files
Inline probes on `solved_keys_augmented_v1.csv` + constructed derr=0/derr>0 controls via
`ecc_secp256k1.scalar_mul` and `int1_frame_operator_v1.build`. Prior: `cap_law_proofs_v1.md`,
`solved_keys_and_construction_v1.md`, `KNOWN_FACTS_secp256k1_and_keys_v5.1.md`.
