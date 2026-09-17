# Update plan: v9.1 → v9.2

2026-09-17. **For discussion. No edits made.** All four rulings are in; this is what they imply, section
by section, with the check for each.

**Target file `MANUSCRIPT_v9_2.md`.** `MANUSCRIPT_v9_1.md` stays frozen and untouched (versioning rule;
v8.2 and v9.1 both frozen).

**The author's rulings, recorded with the date.**

| | ruling | 2026-09-17 |
|---|---|---|
| 1 | the `U`/`K` vocabulary enters under **framework names** | translation table, `UPDATE_RESOLUTIONS_v1` §1 |
| 2 | census placement — **it matters**, so the split decides | 30.4% → §4.5, 69.6% → §6.9 |
| 3 | order-5 grade → **whatever is post-correct**, ambiguity named | `[PROVED — ratio ≤ 26]`, four ambiguities |
| 4 | `n > 2k` — **keep as a row with the coincidence stated** | §8.2 |

---

## The changes, by section

### §7 Formal verification — **counts stale**
- cascade artefact: recorded as 9 modules / 161 theorems; the tree is **18 modules / 4,669**.
- add the new declarations to the machine-checked table: `clear_of_residue_band` (Prop 2.1 as integer
  arithmetic), `lonely_of_band_list`, `circDist_ge_of_band`, `class_killer_int`,
  `circDist_periodic_of_lattice`, `lonely_opening_of_free_off_lattice`, `lonely_of_flank_unkillable`,
  `lonely_of_some_flank_unkillable` and the two `stops_` corollaries.
- **the gates paragraph.** It already records *"a fixed file list once left a new module unchecked"* and
  says the axiom check reads the directory — accurate for step [3]. Step [1] was still a fixed list and
  is now derived from disk; a coverage assertion was added against an independent broader count. Record
  both, and that the gate now runs 11m33s.
- **ripples: §5 and §10 cite §7.**

### §6.7 Existence — highest ripple, cited by 7
- the `[OPEN]` **stays**, and the gate's check [4] must keep matching it.
- add the reduction: `CascadeCapped ↔ ExistenceAt8`, both directions, axiom-clean — the obligation is a
  uniform cap on the cascade's instants, and "capped" is already §8.2's word.
- add the calculus in framework names: the flank's **clear openings**, the **shadowing values**, and that
  shadowing a whole class of openings forces the ratio's denominator to divide `P`.
- the harness `framework_cases_v1` reproduces four of §6.8's named cases exactly; two of them read
  `R = 10.26` and `R = 10.31`.

### §6.9 Flanks — **3,072 census families** decided at a later opening
- the vocabulary throughout in framework names (ruling 1).
- its two open items stay.

### §4.5 Families in which Existence holds at once — **1,341 census families** clear at the bound
- state the population difference against the "about 31% of runners" figure so the near-agreement is not
  read as evidence.

### §8.2 Existence with few differences
- **order 5:** `[EMPIRICAL] ≈ 31/9` → `[PROVED — exhaustive word certificate, exact rational LPs, ratio
  d_max/d_min ≤ 26]`, `sup R = 31/9`, word and margin given. Drop "found". The `[OPEN]` on order-5
  Existence **stays** — the upgrade is about `R`, not about Existence.
- **`n > 2k`:** keep the row; state the coincidence — `n > 2k ⟺ k·(2/n) < 1`, the `k` arcs of width
  `2/n` cannot cover the circle; at `n = 8, k = 7` they cover 1.75 times over. Keep the existing
  sentence that its proof uses no zone width, and that nothing else is built on it. The author's ruling
  replaces *"nativeness pending"*.
- the `[OPEN]` on five differences at `n = 6…10` stays.

### §10 Data and code availability — cited by six sections
- new artefacts: the emitters (`gen_census_batch_v1`, `gen_pinned_batch_v1`), the verifiers
  (`census_batch_verify_v1`, `pinned_batch_verify_v1`), the calibration harness (`framework_cases_v1`),
  the census export and its JSON, and `manuscript_map_v1`.
- **the cross-repository point:** `census_families_v1.json` is now committed here, so the census
  theorems regenerate from this repository alone; the underlying dump lives in the parallel repository.

### §5 No external dependency — **verify, probably no text change**
- its claim (*"no equidistribution, no result at another order, no proof sketch"*) must still hold after
  the additions. `class_killer_int` replaced a density argument with `exists_clear_step`, which takes no
  density input — so the claim survives, but this is the check, not an assumption.

### §6.8 Hard cases — the harness, and the two `R` readings

### Appendix B — a new **B.3 From v9.1 to v9.2**, in the existing form

---

## What does not change

The 26 numbered results and their declarations (all resolve, all machine-checked). §1.3's no-window
statement. §6A. The five open items — **all five survive**, four untouched and §6.7's gaining an
equivalent form.

## Checks, in order

1. **map diff** — `manuscript_map_v1.py` on v9.2 against `manuscript_map_v9_1.json`. Catches: an open
   item that left the register, a citation that stopped resolving, a dangling reference. Mechanical.
2. **compile-diff** — mandatory before promotion (project rule §2). Tracks every open item, caveat,
   retraction and grade from v9.1 into v9.2 by object, not by count.
3. **gate** — unchanged, 4,669 theorems; §7's numbers must match what it reports on the day.
4. **nativeness pass** — the translation table applied, and §5 re-checked. Not mechanical; the material
   most likely to carry an import is mine.

## Order of work

§7 first (it is the factual base the others cite), then §8.2 (both rulings are self-contained), then
§4.5 and §6.9 (the census split), then §6.7 (highest ripple, and it depends on the vocabulary being
settled first), then §10 and Appendix B.3 (both record what the others did), then §5's verification last
because it is a check on everything above.
