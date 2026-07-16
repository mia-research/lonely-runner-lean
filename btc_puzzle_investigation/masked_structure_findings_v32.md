# Findings v32 — the three difference-set / multilinear objects, powered with firing controls

**Date:** 2026-07-17 · `difference_set_xy_geometry_v1.py` + inline. Digging into the three
joint-SET objects flagged as untouched. **Cocycle rigidity governs exact chaining, not distributional
structure — so these test something genuinely new.** All three: generic, with validated (firing) controls.

## (1) Finer-m difference scan `[VERIFIED, powered null, control fires]`
Single-key `xy mod {8,16,64}` vs D/d/n/k on 20k constructed keys: **all z ≈ 0**. Difference
`xy(P_i−P_j) mod {8,16,64}` vs scalar-difference: z = +2.0 / −1.2 / −0.1. The scalar-vs-scalar
**control fires** (z = 1050 / 831 / 365, MI = max). ⇒ no scalar shadow in the difference set at any m
(as rigidity + KS require — it is the single-key null applied to the difference).
*Note:* the known `(X·Y)mod64→D` single-key signal did NOT reproduce here because the 36k `D` column
is the **curve-identity D** (huge/signed), not the `D_terms` d-signature that signal used.

## (2)+(3) Difference-set distribution geometry with the xy odd+μ₃ harmonic `[VERIFIED, AP fires]`
Extended the harness cubic moment `Σ eis(x(P_i−P_j))³` with the μ₃ resonance `Σ χ₃(x_diff)` and the
xy-harmonic `Σ χ₃(xy_diff)`. `|M|/√(pairs)`: ~1 random, ≫1 structured.

| set | eis-cube (÷random) | M3 (μ₃-x) | M3xy (μ₃-xy) |
|---|---|---|---|
| random-curve (null) | 1.0× | 0.74 | 0.37 |
| constructed-36k | 1.5× | 0.26 | 0.48 |
| real-82 | 2.4× | 0.38 | 0.40 |
| **AP control (fires)** | **16×** | **9.76** | **13.29** |
| GLV-triple control | 1.4× | 0.17 | 0.16 |

- The **AP control fires hard** (M3 13×, M3xy 36×, eis-cube 16×) — the moment battery genuinely
  detects additive structure in a difference set. Detector validated.
- **Real-82 and constructed-36k difference sets are generic** (M3/M3xy at the random level).
  **The xy odd+μ₃ harmonic adds nothing over the eis(x) baseline** — both generic.
- (The GLV-triple control correctly does NOT fire: GLV triples make x-coords β-multiples but their
  *differences* `[d(λ−1)]G` are generic — only additive structure moves these moments, and the AP
  has it.) This also covers the **≥4-key/additive-quadruple** question: the cubic moment ≈ 3-term
  additive energy; real/constructed have no excess (AP does).

## Synthesis — the joint-SET / multilinear frontier, complete
Tested with theorems or firing-control powered nulls:
| angle | result |
|---|---|
| single-key (v29/v30, finer-m v32) | powered null (8000–20000 keys, mod≤64) |
| bilinear additive (v28) | powered null (planted rank-1 fires) |
| H¹ cocycle / chaining (v31) | **theorem: only `d`** (prime-order rigidity) |
| H² carry / comparison (v31) | powered null (control z=849) |
| difference-set μ₃ / cubic / xy geometry (v32) | powered null (AP control fires 13–36×) |
| multiplicative / pairing | absent by MOV (~254-bit) |

**No joint-SET handle from `xy` or the difference set survives** any of these objects, at these
scales, with validated detectors. Positive reading: the difference-set moment battery is a working
additive-structure detector, and it **confirms the keys carry no joint additive/μ₃ structure** —
consistent with MT19937-random generation and KNOWN_FACTS.

## The one crux none of it touches (unchanged)
Cheap **spectral concentration** without `d` (v14/v31) — a cheap operator concentrating the flat
character spectrum onto one `e_n(a₀d)`. Rigidity proves it cannot be additive/chaining; the
difference-set nulls show it is not in the pairwise-difference geometry. It is essentially the DLP,
and it is the sole remaining door. The scaled CM/Frobenius-guided phase-hunt (v31 idea #3) is the
only continuation that could be a break.

## Scope / open
`m≤64`; 160-point sets (12k pairs); MT19937-constructed + real 82. Untouched: explicit ≥5-key
relations; secp full-p spectral hunt; other harmonics beyond μ₃/eis/xy. An empirical null is scoped.

## Grades
Finer-m null: **VERIFIED** (control fires). Difference-set geometry generic: **VERIFIED** (AP fires
13–36×). Joint-SET frontier complete from 6 angles: theorem (H¹) + CITED (MOV) + VERIFIED powered
nulls (rest). Spectral-concentration crux: **OPEN** (= DLP). No self-cert words; nulls scoped;
xy structure real but non-reducing.

## Files
`difference_set_xy_geometry_v1.py`, inline finer-m scan, `bilinear_jointset_harness_v1.py` (the
baseline object). Prior: `masked_structure_findings_v28/v30/v31.md`.
