# Lean inventory, for the manuscript update

2026-09-17. Prepared for unfreezing `MANUSCRIPT_v9_1.md`. **Facts only — no update plan, and no
recommendation about what to write.** That is for the discussion.

---

## 1. What the manuscript already records, and whether it holds up  `[VERIFIED]`

| check | result |
|---|---|
| declaration names cited in §7's machine-checked table | 114 cited; **110 resolve in the tree**, the other 4 are artefacts of name-matching (`Flanks.flankOpening`, `ManyDifferences.stops_when_twice_card_lt`, `VersionB.two_diffs` exist unqualified; `n` is a variable) |
| numbered results (Theorem / Proposition / Corollary) in the manuscript | **26, and all 26 appear in §7's table** |

> **Nothing among the manuscript's own numbered results is unformalised.** §7 is accurate for what it
> claims. What is stale is the counts and the module list, not the correspondence.

## 2. The tree now

**18 modules, 4,669 theorems, axiom-clean, zero `sorry`, no `native_decide`** (gate, 11m33s).

| module | thms | | module | thms |
|---|---|---|---|---|
| PinnedBatch1–3 | 1200 each | | Irrational | 18 |
| PinnedBatch4 | 813 | | ManyDifferences | 17 |
| CensusBatch | 62 | | Reading | 11 |
| Iteration | 41 | | Certificate | 9 |
| SmallOrders | 30 | | EighthFamily | 8 |
| FourDifferences | 29 | | VersionB | 6 |
| Flanks | 20 | | NearAP | 4 |
| | | | CensusFamilies | 1 |

Plus `LRC/Spec/Target.lean` — **4 theorems, deliberately outside the artefact** so the gate's check [4]
keeps its meaning.

The manuscript's §7 records the cascade artefact at **9 modules / 161 theorems**; `RESEARCH.md` had it at
170. Both predate today.

## 3. Formalised since the freeze, not recorded in the manuscript

**The `U`/`K` calculus** (`Flanks`) — the batch machine's mechanism, as theorems:

| declaration | content |
|---|---|
| `clear_of_residue_band` | **Proposition 2.1 as integer arithmetic**: `m` clear at opening `k` of flank `e` ⟺ `m(nk+1) mod ne ∈ [e, (n−1)e]` |
| `lonely_of_band_list` | the same over a list of differences — a concrete arrangement closes by `decide` |
| `circDist_ge_of_band` | `y ∈ [1/n, 1−1/n]` plus an integer is clear |
| `class_killer_int`, `clear_in_class_of_not_int` | shadowing a whole residue class of openings forces `P·(d/e) ∈ ℤ` — why the killer set is finite |
| `circDist_periodic_of_lattice` | on the lattice, the verdict depends only on `k` mod `P` — why `U_e` is a residue set |
| `lonely_opening_of_free_off_lattice` | an off-lattice free parameter cannot shadow an uncovered class |
| `lonely_of_flank_unkillable` + `stops_` | the machine's `K_e = ∅` verdict, for **every real** value of the free parameter |
| `lonely_of_some_flank_unkillable` + `stops_` | the empty-killer-intersection route |

**The census, formalised** — 4,475 families:

| | families | route |
|---|---|---|
| `PinnedBatch1–4` | 4,413 | `s = 6` covers (no free parameter); one `decide` each |
| `CensusBatch` | 62 | `s = 5` covers, `K = ∅` on both counts, `e/P = 1` |
| `CensusFamilies` | 1 | the first cold family, done by hand before the emitter existed |
| `EighthFamily.eighth_family_via_calculus` | — | the eighth family re-derived from the general calculus |

6,759 + 197 = **6,956 of 6,964 census covers** are covered by these (many covers share a difference set).

**The target and the reduction** (`LRC/Spec/Target.lean`, outside the artefact):

| declaration | content |
|---|---|
| `ExistenceAt8`, `_cascade`, `_flank` | the target in three wordings |
| `target_forms_agree`, `target_flank_agrees` | the wordings are equivalent — no wording can be substituted for another |
| `CascadeCapped` | a uniform cap on the cascade's instants |
| `existence_of_capped`, `capped_of_existence` | **`CascadeCapped ↔ ExistenceAt8`**, both directions |

## 4. Claims in the manuscript carrying a grade below `[PROVED]`

17 lines. These are the candidates for "formalise what we haven't", and the list is short because §1
found the numbered results already covered.

| grade | count | examples (line) |
|---|---|---|
| `[OPEN]` | 4 | fitting between AP locations (158); the gap-frame obligation (319); **Existence, §6.7 (492)**; flanks (§6.9) |
| `[VERIFIED]` | 8 | perturbations read by `d_min` (324); the §6.7 computations (511); the `(9,25)` case (555) |
| `[DERIVED]` | 2 | the mirror of Theorem 4.8 (600) |
| `[EMPIRICAL]` | 2 | unrelated grids (534); the largest `R` found (533) |

## 5. Owed in Lean, named

From `REQUIREMENTS_v1` §3, unchanged by today:

| | owed | shape |
|---|---|---|
| A | the 8 intersection families | `lonely_of_some_flank_unkillable` exists; hypotheses not discharged for them |
| B | census families with `e/P > 1` | the emitter's `hkill` assumes the free parameter ranges over the integers |
| C | no-mixing | validated at `c ≤ 14` and `c ≤ 15`; named as the structural target in `RESEARCH.md` |
| D | the census beyond `M ≤ 60` | the per-`M` census is finite |
| E | `ExistenceAt8` itself | equivalently `CascadeCapped`; A–D give the census, not the theorem |

## 6. Artefact state

- gate: `scripts/cascade/gate.sh`, corrected today (module list from disk, coverage assertion against an
  independent broader count, step [4] documented as a name tripwire). Previous kept as
  `gate_v1_prev.sh.bak`.
- reproducibility: `census_families_v1.json` is now committed, so the 4,475 census theorems regenerate
  from this repository alone.
- commits today: 10, across both repositories.
