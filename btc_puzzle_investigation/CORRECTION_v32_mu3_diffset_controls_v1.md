# CORRECTION — the μ₃ difference-set cell had NO working control (v32 → masters)

**Date:** 2026-07-30 · **Grade of this document:** `[PROVED]` for the forcing and the
multiplicity account; `[NO VALIDATED POWER]` for what it retracts. It states **no new bound** —
the replacement bound is pending `PREREG_mu3_diffset_control_repair_v1.md` gate 5.

**Basis (independently re-derived, 26/26 checks):**
`mu3_diffset_forced_zero_reproduce_v1.py` (§10 R1–R4 of the prereg). Nothing here is asserted
from the prereg text; every clause was computed.

---

## 1. What is corrected

Three sentences, in three files. Quoted exactly, with locations.

| # | file:line | sentence | status |
|---|---|---|---|
| C1 | `masked_structure_findings_v32.md:31-32` | "The GLV-triple control **correctly** does NOT fire: GLV triples make x-coords β-multiples but their *differences* `[d(λ−1)]G` are generic" | **WRONG** — retracted |
| C2 | `masked_structure_findings_v32.md:28` | "The **AP control fires hard** … Detector validated." | **misattributed** — the AP validates a different channel |
| C3 | `POSITIVE_FINDINGS_MASTER_v1.md:232` and `POSITIVE_FINDINGS_MASTER_v2.md:530` (identical clause) | "difference-set μ₃/cubic/xy geometry generic (AP control fires 13–36×)" | **re-tagged** `[NO VALIDATED POWER]` |

Also affected by C3's framing: `POSITIVE_FINDINGS_MASTER_v2.md:528` introduces that whole list as
bounding a magnitude "*with a control that fired*". For the μ₃ difference-set item, no control fired
for the reason claimed.

---

## 2. C1 — the GLV-triple control is forced to exactly zero

`difference_set_xy_geometry_v1.py:12-14, 94-101` declares a "GLV-triple set (keys closed under
d→λ·d → mu3 resonance)" among "CONTROLS (must fire)". It cannot fire, for an algebraic reason:

- `λ̂(x,y) = (β_GLV·x, y)` is a group **endomorphism**, so `λ̂(P−Q) = λ̂P − λ̂Q`: if `S` is λ̂-closed
  then the difference set `D` is λ̂-closed too.
- `x(−R) = x(R)`, so the multiset `V_x = {x(R) : R ∈ D}` is closed under `x ↦ β_GLV·x`.
  Verified as an **exact `Counter` equality** `β·V_x == V_x` (support 1770, total 1770), not a spot check.
- `(p−1) mod 9 = 6`, so `χ₃(β)` is a **primitive** cube root of unity and
  `1 + χ₃(β) + χ₃(β)² = (0,0)` in `Z[ω]` — computed, not asserted.
- Therefore `M3x = M3xy = (0,0)` **exactly**, for every λ̂-closed set.

Measured, all `C(m,2)` pairs, fresh seeds:

| m | n_pairs | class counts (x) | class counts (xy) | M3x | M3xy | E3x |
|---|---|---|---|---|---|---|
| 60 | 1,770 | `[590, 590, 590]` | `[590, 590, 590]` | `(0,0)` | `(0,0)` | 0 |
| 162 | 13,041 | `[4347, 4347, 4347]` | `[4347, 4347, 4347]` | `(0,0)` | `(0,0)` | 0 |

The class counts are **exactly equal thirds** — stronger than `M3 = 0`.

**Why v32's explanation is wrong.** It reasons about *one* difference's scalar (`[d(λ−1)]G` is
indeed a generic scalar) and concludes about the *whole multiset's character sum*. The relevant
object is `V_x`, and `V_x` is β-closed. This is the "trace the object, not the tag" failure named in
`btc_puzzle_investigation/CLAUDE.md`.

**The disconfirming evidence was already in v32's own table.** The GLV row reads **0.17 / 0.16**
against a random-curve null row of **0.74 / 0.37**. A control whose differences were "generic" lands
*at* the null. Landing *below* it is the forcing signature. The residual is entirely the pair
subsampling (`maxpairs=12000` of `C(160,2)=12720`): at 94% retention the reproduction gives
`E3x = 1047`, retired-float-scale **0.292**, against **0.000** at 100% retention. Subsampling breaks
orbit completeness, which is why a forced-zero cell read 0.17 instead of 0.

**The forcing theorem was already on disk, four days earlier.**
`glv_orbit_structure_proof_v1.py:24` (2026-07-13) proves `chi3(beta x) = chi3(x) + 1 (mod 3)`, hence
"on a GLV triple {x,βx,β²x}: chi3 realizes ALL THREE classes {0,1,2} exactly once".
`difference_set_xy_geometry_v1.py` is dated 2026-07-17 08:48.

---

## 3. C2 — the AP control validates multiplicity, not μ₃

An AP of 160 points realizes only **159 distinct** differences, with weights `w_j = 160−j`. A
random-phase χ₃ over that weight multiset has scale `√(Σw²/Σw) = √(1352560/12720) = 10.3118`
(verified: `Σw = 12720 = C(160,2)`, `Σw² = 1,352,560`), against v32's reported **9.76** at 94.3%
retention. So the AP's firing needs no cubic-class structure at all.

Confirmed by the surrogate that keeps the multiplicity spectrum and randomizes the χ₃ labels:

```
AP observed  E3x = 628,761
surrogate 95% region = [33,204 , 4,898,469]      rank = 0.364   -> INSIDE
```

**The AP is reclassified as a multiplicity control.** It genuinely certifies sensitivity to
degenerate-multiplicity structure — a real capability, retained — but carries no information about
sensitivity to a cubic-class imbalance among multiplicity-1 differences, which is the studied sets'
regime. The words "Detector validated" do not transfer to the μ₃ channel.

**Consequence:** the μ₃ difference-set cell of v32 had **zero** working controls — one forced to 0,
one firing for an unrelated reason.

---

## 4. C3 — a further defect: the two cells were never independent tests

On `E: y² = x³+7`, `χ₃(y) = χ₃(y²)² = χ₃(x³+7)²`, so

```
chi3(x*y) = chi3(x) * chi3(x^3+7)^2        verified 144/144
```

— a function of `x` **alone**. And it is y-sign blind (`χ₃(x·y) == χ₃(x·(−y))`, **155/155**), because
`χ₃(−1) = 1`.

So v32's "**xy odd**+μ₃ harmonic" is **not odd** and **not a second harmonic**: it is a second
weight-1 character on the *same* multiset `V_x`. Part of "the xy harmonic adds nothing over the
eis(x) baseline" is therefore an **algebraic identity**, not an empirical finding, and the two table
cells are not independent tests. Their null correlation must be measured, not assumed.

---

## 5. What is NOT corrected

Stated explicitly so this correction is not over-read:

- **No signal claim.** Nothing here shows structure in the real keys. The real-82 and
  constructed-36k sets are **not** λ̂-closed, so their own `M3`/`M3xy` values were never forced —
  those are legitimate measurements. Against a properly measured 50-set null they sit at
  −1.09σ / −1.06σ (real-82) and −1.34σ / −0.85σ (constructed-36k): unremarkable.
- **The additive column is untouched.** `eis_cube` is an additive/geometric readout. An additive
  character sum over a β-closed set is *never* forced to zero — the twist permutes the dual variable
  (`F̂(b) = F̂(ωb)`, measured 1008/1008, with **0/1008** exact vanishings) instead of rotating the
  value. Different channel, different behaviour, no defect.
- **The rest of the codebase is clean.** A full sweep found only this one instance.
  `lbe_harness_v1.py:214-235` and `isotypic_selection_rule_v1.py` handle orbit structure correctly;
  `summation_relation_yield_v1.py` and `dlevel_same_n_relations_v1.py:74` are safe because their
  statistics are **counts**, which cannot self-annihilate (this is also why the β-invariant
  index-calculus lever of 1.5× is a real measurement). The μ₂/negation analogue is already handled in
  `bitleak_tests_134_v1.py:17`, `n1_flap_bridge_v2.py:15`, and `_sy_skew_test_v1.py`.
- **No closure either way.** Per the prereg §7.2, a cell with no validated power "is not a null
  result, and it does not close anything." The μ₃ difference-set channel is **un-probed**, not null.

---

## 6. Replacement status

`PREREG_mu3_diffset_control_repair_v1.md` is frozen and its gates 1–2 have passed
(`mu3_diffset_forced_zero_reproduce_v1.py`, 26/26). Gates 3–5 are running
(`mu3_diffset_run_gates345_v1.py`). Until gate 5 completes:

> The μ₃ weight-1 channel of the group-law difference multiset carries
> **`[NO VALIDATED POWER]`** — no bound, in either direction, may be stated for it.

Two incidental disclosures found while auditing, both recorded:

- `difference_set_xy_geometry_v1.py:82` slices the 36k pool to its **first 4000 rows** before
  sampling — an undisclosed filter. The repaired run uses the whole pool for both the draw and its null.
- `difference_set_xy_geometry_v1.py:95-97` has a dead `λ` fallback
  (`[l for l in range(2,10000) if pow(l,3,N_ORDER)==1 and l!=1][0]`) that would raise `IndexError`
  if ever reached; no such small `l` exists. The primary `pow(2,(n−1)//3,n)` is correct
  (`λ³ ≡ 1`, `λ²+λ+1 ≡ 0 mod n`, both verified). New scripts assert rather than fall back.
