# Research Log

Chronological record of computational work, discoveries, and decisions.  
Format: `## YYYY-MM-DD — {what was done / found / decided}`  
Add an entry whenever: a dataset is computed, a finding is confirmed or refuted, a file is promoted to canonical, a paper draft changes status.

---

## 2026-04-20 — Source-line inventory; d=10 double-boundary; kaprekar_d101-150.csv repair

### Done
- Forked `scripts/kaprekar_structural_inventory.py` into `scripts/kaprekar_source_line_inventory.py`. Adds two exact source-line families to the bucket list:
  - `E_k` (period `+6`): freq = `[1,k,k,0,k,k,0,k,k,1]`, `d = 6k+2`, growth `{1,2,4,5,7,8}`.
  - `O_t` (period `+14`): freq = `[0,1,3t+1,t+1,2t+1,2t+1,t+1,3t+1,1,2t+1]`, `d = 14t+9`, growth `{2,2,2,3,4,4,5,5,6,7,7,7,9,9}`.
  - Bucket closed under `+9` insertion (one copy of each of `1..9` per step, keep if multiset is still `K`-fixed).
- Extended `low_d_boundary` from one point to two at `d=10` (`9975084201` and `9753086421`). These are the two paired-lattice-shape points sitting at the lowest dimension where the `c09 + c36 + 3k = d/2` lattice first applies.
- Swept `d <= 100` and `d <= 150` after repair. Outputs in `analysis/base10/source_line_inventory/`.
- Wrote `scripts/kaprekar_fix_d101-150.py` to repair 50 corrupted rows surfaced by the sweep in `data/base10/canonical/kaprekar_d101-150.csv`; pre-fix file archived to `archive/superseded/kaprekar_d101-150_superseded_2026-04-20.csv`.
- Wrote `analysis/base10/source_line_inventory/source_line_inventory_2026-04-20.md` (full writeup of the sweep, the two new source-line families, the `d=10` double-boundary clause, and the repair).

### Found
- **Zero canonical residue at `d <= 100`** against the bucket list `{495, 6174, 864, paired_lattice, unpaired_bulk, boundary_line, source_line_family, low_d_boundary}`.
- **Zero canonical residue at `d <= 150`** (post-fix) against the same bucket list. Every row in both canonical files is captured by one of the listed generators.
- **The `d=37` orphan `8777765544433221999997776655544322222` is exactly `O_2`** on the `+14` source line — no longer an anonymous exception.
- **`d=10` needs two boundary points, not one.** `9753086421` is not in any prior family generator at `d=10` and has to be enumerated alongside `9975084201`.
- **`kaprekar_d101-150.csv` had 50 corrupt rows (0.89%).**
  - 25 odd-`d` rows (`d=101,103,...,149`): `864`-shape with `333.../666...` blocks swapped to `666.../999...`, producing non-`K`-fixed strings.
  - 25 even-`d` rows (`d=102,104,...,150`): `6174`-shape with middle block written as `777...` instead of `666...`, producing strings whose multiset contains no `5`, `8`, or `9` — structurally impossible for a `K`-fixed point.
  - Post-fix audit: `5609 / 5609` rows `K`-fixed at declared `d`; post-fix source-line sweep residue = 0 at `d = 101..150`.
- **`kaprekar_d101-150.csv` is complete on correctness but not on enumeration.** Exact-family generators produce 103,609 fixed points at `d <= 150` while the CSV holds 5,609. At `d=150` coverage is `133 / 2927 ≈ 4.5%`. This is a completeness gap, not a correctness gap, and is flagged in `archive/superseded/DATA_DECISIONS.md`.

### Decided
- The `provisional_base10_d_all_theorem_2026-04-19.md` low-`d` boundary clause is updated to enumerate both `d=10` points; the single-point version is retired.
- The source-line family is added to the canonical bucket list for the `d=all` theorem draft; the explicit orphan-seed bag is replaced by "descendants of `E_k` and `O_t` under `+9` closure."
- The 50-row repair is written in place; pre-fix file archived, `DATA_DECISIONS.md` updated.
- Regenerating the canonical `kaprekar_d101-150.csv` to include the missing ~77k family members is a separate governance decision and is not done in this pass.

### Open
- Global completeness: prove that `+6` and `+14` are the _only_ missing native source periods beyond `+9`, or produce a higher-level generator for any further ones.
- Promotion from the finite window `d <= 150` to all dimensions.
- Family-complete enumeration of canonical at `d = 101..150`.

### Files
- Runner: `scripts/kaprekar_source_line_inventory.py`
- Repair runner: `scripts/kaprekar_fix_d101-150.py`
- Writeup: `analysis/base10/source_line_inventory/source_line_inventory_2026-04-20.md`
- Sweep outputs: `analysis/base10/source_line_inventory/source_line_inventory_2026-04-20.{summary.json,rows.csv}` (`d <= 100`), `source_line_inventory_d150_2026-04-20.{summary.json,rows.csv}` (`d <= 150`)
- Archive: `archive/superseded/kaprekar_d101-150_superseded_2026-04-20.csv`; entry prepended to `archive/superseded/DATA_DECISIONS.md`
- Canonical: `data/base10/canonical/kaprekar_d101-150.csv` (repaired in place, 5,609 rows, all `K`-fixed)

---

## 2026-04-17 — Thermo-view Experiment 6: K as a relaxation process

### Done
- Wrote `/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_k_dynamics_sweep.py`. Stage A (exhaustive) for d ≤ 6; Stage B (50k samples) for d ∈ {7,8,10,12,15,20,25,30}. Pre-image ensemble BFS depth 1..3 for d ≤ 6.
- Calibration gate passed: d=3 basin of 495 = 99.0%, d=4 basin of 6174 = 99.90% (classical Kaprekar 1949 values).

### Found
- **Mean relaxation time under K is bounded and essentially d-independent** (2.65 ≤ τ_K ≤ 7.05 across d=3..30). K is a rapid-contraction map.
- **At all d ≥ 5, the largest-basin attractor is a cycle, not a fixed point.** d=3 (495) and d=4 (6174) are the outliers. The classical "Kaprekar constant" picture describes a special d ∈ {3,4} regime.
- **d=7 (50k sample) has a single attractor** covering 100.0% of sampled starts (7509843, cycle:8). Phase-transition-like.
- **Pre-image ensemble grows ~0.4–1.3 bits/depth** at d ∈ {3,4,5,6} — bounded thermal-expansion rate under K⁻¹.

### Decided
- K's relaxation dynamics are non-trivial and measurable — the thermo programme continues.
- None of these beat Lehmer; they characterise the K substrate honestly.
- d=7-single-attractor and τ_K d-independence are worth future follow-up.

### Files
- Writeup: `analysis/encoding/thermo_view/k_relaxation_observables_2026-04-17.md`
- Output: `/tmp/k_dynamics_full.json`

---

## 2026-04-17 — Thermo-view Experiment 3: Boltzmann reread of v27 cycle gap distribution

### Done
- Extended `/Users/trentpalelei/Desktop/Math Ex/ride_v27_cycle_characteriser.py` in place with per-cycle `gap_histogram`, `p_geom` (shifted-geom MLE), `p_geom_residual`, and `beta_gap = -log(1-p)`. Existing outputs unchanged; calibration gate on `eleven_lonely_runners.pdf` cycle 0 reproduces finding 4's gap=1 frequency 0.3780.
- Wrote `/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_thermo_eos_sweep.py` (cross-file sweep harness, 80 rows over 8 files including synthetic random and constant controls).

### Found
- **`p_geom ≡ cycle_length / n_digits` across all 80 (file, cycle) rows** (max residual 5e-5, traceable to 4-decimal rounding). Pearson r = 1.0000. The "geometric gap" parameter is not an independent thermodynamic observable — it is an algebraic identity.
- Fit residual (RMS empirical vs geometric PMF) is tiny everywhere (2e-4 to 5e-3): cycles are statistically indistinguishable from a uniform random subset at their density. The geometric *shape* is universal; its *parameter* is redundant with cycle length.
- Finding 4 of `analysis/encoding/ride_state_2026-04-13.md` (p ≈ 0.377 as a Shannon wall on LRC PDF) stands, but is re-framed: the wall is cycle-membership entropy at cycle density, not a temperature.

### Decided
- The gap-distribution parameter is not a universal thermodynamic fixed point nor an equation of state. The direction is not abandoned, but the *next* informative observable is one level up: cycle count and cycle-length distribution, which Experiment 6 will reach through K-dynamics.

### Files
- Writeup: `analysis/encoding/thermo_view/boltzmann_eos_2026-04-17.md`
- Output: `/tmp/thermo_eos_sweep.jsonl` (80 rows)
- Plan: `/Users/trentpalelei/.claude/plans/fluttering-booping-gizmo.md`

---

## 2026-04-15 — MIAI v36/v37/v38 step-count implementations are broken; reported Calgary paper4 success is false

### Done
- Wrote benchmark harness `/Users/trentpalelei/Desktop/Math Ex/ride_v41_miai_v37_benchmark.py`. Imports MIAI v37 directly. Ran on rungs 0-1: 256B synthetic, 1KB synthetic, 784B text. 3 runs per target.
- Result: 0/3 targets, 0/9 runs matched hash.
- Diagnostic on 171B toy input: v37's `build_traversal` is a single-pass sort that doesn't revisit re-displaced positions. Final state (412 digits) has 380 still wrong.
- Followed user's suspicion ("I am very suspect of coincidence") and ran v37's and v38's own `__main__` blocks on the real Calgary corpus files (paper4, paper5, paper1, bib).

### Found
- **v37 fails on all real Calgary files:** `RuntimeError("Hash not found in TSP traversal")` on paper4 (13.3KB), paper5 (11.9KB), paper1 (53KB), bib (111KB).
- **v38 also fails:** `RuntimeError("Hash not found in dynamic TSP traversal (1 steps)")` on all Calgary files.
- **Implication:** The claimed "bit-perfect round-trip on Calgary paper4 with N ≈ 32,000 steps" in finding 13 is false. The code does not work end-to-end on paper4 or any other real file tested.

### Decided
- Finding 13 is deleted and replaced with: "No working step-count implementation exists in MIAI. v37/v38 docstrings claim bit-perfect round-trip on Calgary paper4 but fail when tested."
- Q8, Q10, Q11 are all closed as moot (there is no working v37 to build on).
- Amended `analysis/encoding/ride_state_2026-04-13.md` Addendum 2026-04-15 (iii) with full findings.

### Outputs
- Script: `/Users/trentpalelei/Desktop/Math Ex/ride_v41_miai_v37_benchmark.py`
- JSONL: `experiments/outputs/ride_v41_v37_benchmark_20260415T123046.jsonl`
- Findings: `experiments/outputs/ride_v41_v37_findings_2026-04-15.md`

---

## 2026-04-15 — RIDE consolidated working doc landed; Part 2 designed-seed experiment scoped

### Landed
- New working document: `analysis/encoding/ride_consolidated_working_doc.md`. Proposes layered architecture (manifold material → broad-order stage → mismatch-guided move-DSL cleanup) and introduces a 5-op move DSL (`rot`/`rev`/`swap`/`blockswap`/`localrot`). Reports toy-scale bit-perfect reconstruction. Explicitly distanced from prior "confirmations" that did not meet forensic standard.
- Status: working position, not a finding. Toy-only evidence.

### Reconciliation with source of truth
- `analysis/encoding/ride_state_2026-04-13.md` received an addendum block, three new Open Questions (Q5, Q6, Q7), and one File Map row.
- "What Is Settled" §11 (v28–v30 87% real-file wall) is UNCHANGED. Toy success does not overturn real-file falsification.
- Tension between the new doc and §11 is flagged, not resolved. Deciding experiment is a real-file run of mismatch-guided annealing on the v28–v30 target set (LRC PDF, `palelei_reconstructed.jpeg`, `cantrbry.zip`).

### Scoped (not yet executed)
- Part 2: "designed seed" exploration. TSP SA kernel (`lambda_function 41.py` + `ride_v24_order_family_harness.py` outer schedule + `ride_v32_tsp_seed_annealer.py`) is retargeted to search over seed-construction **parameters** whose output permutations are engineered to match v18 cycle geometry (13–16 huge cycles, geometric gap p≈0.377). This sits between v30 (random seeds, falsified) and the consolidated doc's move-DSL direction (toy-only).
- Planned script: `ride_v40_designed_seed_param_search.py` in `/Users/trentpalelei/Desktop/Math Ex/`. Success/falsification criteria calibrated against v30's 87% wall; see `/Users/trentpalelei/.claude/plans/serialized-hugging-fairy.md` §5c.

### Novel vs. consistent-with-known
- **NOVEL:** move DSL formulation, mismatch-guided annealing at toy scale, "designed seed parameter search" framing.
- **CONSISTENT WITH KNOWN:** v18 cycle geometry as the structural target, TSP SA as the encoder-side search brain, K-source + delta as the material layer, §11 real-file wall.

### Follow-up docs deferred
- Move DSL Spec, Chef Search Architecture, Material Richness Test Plan are stubbed inside the consolidated doc but NOT split into separate files yet. Promotion triggers recorded in the consolidated doc's "Planned Follow-Up Docs" section.

---

## 2026-04-13 — Base-16 full analysis and base-256 initial results

### Base-16 (d=3–100, 5,783 constants)

Completed full universal law verification with corrected methodology (using actual n digits, not multiset extremes):
- All 5 laws hold with zero violations across 5,783 constants
- Central pair distribution: (0,14) sum=14 at 98.4%, (15,15) sum=30 at 1.6%
- Even/odd ratio: **31.49x** (5,605 even-d vs 178 odd-d) — confirms super-linear growth of base-parity/dimension-parity law
- Even-d counts grow linearly (+6 per step from d=26); odd-d stabilizes at 4
- Dead zones at d=4,5,8 (exhaustive, proven)
- Cross-validation discrepancies at d=21–24 confirm orphan seeds exist in base-16

Updated: `analysis/alternate_bases/base16_d3-100_findings.md`, `universal_kaprekar_constraints_cross_base.md` (§2b and §12 tables)

### Base-256 — v1 (extension-only): seed starvation failure

Initial run found only 33 constants — all U6 family. Extension failed completely due to seed starvation: only 1 d=3 seed, and U6 members don't extend to non-U6 dimensions.

### Base-256 — v2 (smart exhaustive d=3..11 + extension): 88 constants, 2 families

Smart search exploits inner frequency symmetry to reduce search space (e.g. d=10: 333M candidates vs 10^19 naive). Results:

**Proven FPF (smart exhaustive):** d = 4, 5, 8, 10
**Constants found:**
- d=3: 1 (closed-form formula)
- d=6: 1 (U6)
- d=7: 1 (orphan seed: {63, 64, 127, 128, 191, 192, 255} — evenly-spaced quartiles)
- d=9: 10 (1 U6 + 9 parametric family with first digit 42..50, 4 complementary pairs + middle 255)
- d=11: 1 (85-family chain member)

**Two families identified:**
1. **U6:** {127^k, 128^k, 255^k} at d=3k, growth pair (127,128)
2. **85-family:** Seed {42,43,85,127,128,170,212,213,255} at d=9, growth pair (85,170), one constant at every odd d≥9. Only 1 of 10 d=9 constants extends — the other 9 are orphan seeds.

**Extension chain:** d=9→11→13→...→99 via (85,170) insertion. Perfectly regular.

**Family construction:** 171 constants constructed directly (no search) for d=3..200 in 0.0s. All verified K(n)=n.

**Even/odd ratio: 0.24x** — odd-d dominates, contradicting smaller even bases (all >1x). This is because the 85-family is exclusively odd-d and no non-U6 even-d family has been found. **Caveat:** Even d>10 not exhaustively searched; undiscovered even-d families could exist.

All 5 universal laws hold on 171 constants with zero violations.

Updated: `analysis/alternate_bases/base256_d3-100_findings_v2.md`, `base256_family_analysis.md`

---

## 2026-04-12 — RIDE reframed as algorithmic coordinates (not compression)

### Decision: retire the compression framing

Two files in `analysis/encoding/` had fundamentally incorrect framing:
- `kaprekar_compression_framework_proven.md` — claimed 5–35× compression via frequency encoding
- `kaprekar_coordinate_encoding_findings.md` — GPS/triangulation framing with storage analysis

Both archived to `archive/superseded/` with `_superseded_2026-04-12` suffix.

### Correct framing: Kolmogorov, not Shannon

RIDE (Replication via Instruction, Delta, and Extension) is an **algorithmic coordinate system**
for Kaprekar constants — it identifies a constant by its position in the extension tree
(seed + extension sequence), not by how many bytes it saves.

This is Kolmogorov complexity thinking: the RIDE address is the **shortest program** that
generates the constant. The program executes the extension sequence from the seed.

**What is genuinely proven:**
- A d-dimensional Kaprekar constant's RIDE address requires ~d/2 · log₂(b/2) bits  
- vs d · log₂ b bits for direct storage — a genuine ~2× reduction in description length
- For parametric families, complexity is O(log d) — essentially constant with d

**What cannot be claimed:**
- RIDE as a compression scheme for arbitrary data
- The permutation step (which arrangement of the multiset?) carries all the information  
  that makes an arbitrary number unique — O(d log d) bits — and cannot be avoided

---

## 2026-05-03 — Odd rotor weighted shell fan; period-2 boundary knot

### Done
- Wrote `kaprekar_h_weighted_shell_fan.py` and `h_weighted_shell_fan_2026-05-03.md`.
- Promoted the odd period-3 rotor side from “axial `H` + degree-1 shell fan + `J` residual” to a weighted shell grammar:
  - `A=+36`, `B=+09`, `C=+(45,18,27)`, `D=+(27,45,18)` all weight `1`
  - `E=+(18+27+45)` uniform, weight `3`
- Verified exact low-weight closure counts against the known reduced-state period-3 census:
  - `d=21`: `4`
  - `d=23`: `10`
  - `d=25`: `21`
- Stress-tested the weighted closure by random reduced-state attractor sampling at:
  - `d=27`
  - `d=29`
  - `d=31`
  - `d=33`

### Found
- The odd period-3 side is best read as a **weighted rotor fan** over `H`, not an ad hoc list of extra families.
- The closure-size formula is
  `N_3(r) = sum_{e=0}^{floor(r/3)} C(r-3e+3, 3)` for `d=19+2r`.
- High-dimensional sampling matched the weighted closure exactly on the sampled attractor set:
  - `d=27`: sampled period-3 count `39`, misses `0`
  - `d=29`: sampled period-3 count `66`, misses `0`
  - `d=31`: sampled period-3 count `105`, misses `0`
  - `d=33`: sampled period-3 count `159`, misses `0`
- In those same samples, the only observed odd period-2 attractor was the old `B` line:
  - `d=27`: `[0,1,1,9,2,2,10,0,0,2]`
  - `d=29`: `[0,1,1,10,2,2,11,0,0,2]`
  - `d=31`: `[0,1,1,11,2,2,12,0,0,2]`
  - `d=33`: `[0,1,1,12,2,2,13,0,0,2]`
- So the extra period-2 attractor seen at `d=25` currently reads as an isolated low-dimensional boundary knot, not as evidence of a second continuing period-2 branch.

### Decided
- The odd rotor side should now be presented as:
  - primitive kernel `H`
  - weighted shell generators `A,B,C,D,E`
  - weighted closure counts `N_3(r)`
  - period-2 `B` line plus one known `d=25` boundary knot
- This is a stronger theorem path than the earlier `H`-fan / `J`-residual wording.

### Files
- Runner: `kaprekar_h_weighted_shell_fan.py`
- Note: `h_weighted_shell_fan_2026-05-03.md`
- Artifact: `kaprekar_h_weighted_shell_fan_2026-05-03.json`

---

## 2026-05-03 — Odd period-3 affine rotor law; `d=25` boundary-knot isolation

### Done
- Wrote `kaprekar_odd_period3_affine_rotor.py` and `odd_period3_affine_rotor_2026-05-03.md`.
- Wrote `kaprekar_period2_boundary_knot.py` and `period2_boundary_knot_2026-05-03.md`.
- Recast the odd period-3 weighted fan as one exact affine rotor family with phase laws `R0,R1,R2`.
- Isolated the extra `d=25` period-2 attractor inside the natural symmetric boundary ansatz `Q(w,x,y)`.

### Found
- The odd period-3 side has an exact affine normal form:
  - `R0(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+1]`
  - `R1(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+1]`
  - `R2(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+1]`
- For `u>=1, x>=1, v>=2, w>=v, y>=v+1`, the Kaprekar map cycles `R0 -> R1 -> R2 -> R0`.
- The five shell directions are exactly the affine cone coordinates:
  - `B = u-1`
  - `E = v-2`
  - `D = w-v`
  - `A = x-1`
  - `C = y-v-1`
- All exact odd period-3 census representatives at `d=25,27,29` fit this affine rotor law with zero residue.
- The extra `d=25` period-2 attractor is unique in its natural symmetric class `Q(w,x,y)`:
  - two parameter presentations `Q(3,3,3)` and `Q(4,2,3)`
  - one unique 2-cycle
- That knot has no one-shell period-2 continuation to `d=27`.

### Decided
- The period-3 generator question is now best phrased as an affine-symmetry completeness problem, not just a weighted-fan counting problem.
- The extra `d=25` period-2 attractor is best treated as a finite boundary-knot exception unless a more remote continuation is later found outside direct shell grammar.

### Files
- Runner: `kaprekar_odd_period3_affine_rotor.py`
- Note: `odd_period3_affine_rotor_2026-05-03.md`
- Artifact: `kaprekar_odd_period3_affine_rotor_2026-05-03.json`
- Runner: `kaprekar_period2_boundary_knot.py`
- Note: `period2_boundary_knot_2026-05-03.md`
- Artifact: `kaprekar_period2_boundary_knot_2026-05-03.json`

---

## 2026-05-12 — Boundary thread `K_p`; reduced odd rotor scope correction

### Done
- Wrote `kaprekar_boundary_thread_k_family.py` and `boundary_thread_k_family_2026-05-12.md`.
- Rechecked the old `d=25` boundary-knot claim against a broader symmetric thread and corrected the interpretation.
- Narrowed the scope wording in `odd_period3_affine_rotor_2026-05-03.md`: the affine rotor is now stated as the reduced high-minus-low=`1` odd period-3 theorem path, not the whole odd period-3 story globally.

### Found
- The old `d=23` / `d=25` period-2 knots lie on the explicit boundary thread
  `K_p = [0,p,3,3,3,3,3,3,p,3]`, `d=21+2p`.
- Verified thread phase diagram through `p<=20`:
  - `p=1,2`: period `2`
  - `p=3`: fixed
  - `p=4..7`: period `5` after finite preperiod
  - `p=8`: fixed
  - `p>=9`: period `3` after preperiod `12`
- The period-3 tail is itself exact:
  - `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
  - `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
  - `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`
  with `r=p-4`, verified for `r=5..24` with zero failures.

### Decided
- The old `period2_boundary_knot_2026-05-03.md` remains locally true in its narrow ansatz, but is no longer the right global interpretation.
- The global odd cycle picture now splits into:
  - reduced high-minus-low=`1` rotor cone (weighted fan / affine rotor)
  - explicit boundary thread `K_p` on a different high-minus-low level

### Files
- Runner: `kaprekar_boundary_thread_k_family.py`
- Note: `boundary_thread_k_family_2026-05-12.md`
- Artifact: `kaprekar_boundary_thread_k_family_2026-05-12.json`

**New document:** `analysis/encoding/ride_algorithmic_coordinates.md`

---

## 2026-04-12 — Extension to d=1000 completed; multiset dataset generated

### New file: kaprekar_d101-1000_multiset.csv

Extended the canonical d=3-100 dataset to d=1000 using `scripts/kaprekar_extend_large_d.py`.

**Algorithm:** Pure multiset-space extension. Seeds loaded from `kaprekar_d3-100_verified.csv`
(21,055 constants, d=3-100). For each dimension d, all 5 symmetric pairs (x,y) with x+y=9 are
tried as insertions into every known multiset. Each candidate verified using the O(10) closed-form
K formula with precomputed pow10/cumsum_geom tables (Python big-integer arithmetic).

**Output format:** CSV with columns d, c0, c1, ..., c9 (multiset representation). Actual constant
value recoverable via n = desc(ms) − asc(ms). Multiset format used because d=1000 constants
have 1000-digit decimal representations — storing full integers would produce a multi-GB file.

**Key counts:**
- d=100: 918 constants/dimension (even d) | d=101: 720 (odd d)  
- Growth: linear ~255 per 10d (even d), ~240 per 10d (odd d)
- d=1000: ~23,800 constants (even), ~19,000 (odd) — estimated from linear growth

**Timing:** ~30-40 min total (O(d²) cost per step due to big-integer arithmetic at large d)

**Completeness:** Zero false positives by construction. Orphan seeds first appearing above d=32
may be missed (empirical rate: ~0.7% at d≤100, expected to decrease at larger d as extension
chains densify). No orphan verification was performed above d=32.

**File location:** `data/base10/canonical/kaprekar_d101-1000_multiset.csv`

---

## 2026-04-12 — Complete algorithm established; dataset finalised at 21,055 verified constants

### Algorithm

Two-component algorithm now documented in `analysis/base10/kaprekar_complete_algorithm.md`
and implemented in `scripts/kaprekar_find_constants.py`:

1. **Exhaustive enumeration** (d ≤ 32): iterates all digit multisets (c₀,...,c₉) with Σcᵢ=d.
   Uses closed-form O(10) formula for asc/desc via geometric series G(k)=(10^k−1)/9.
   Pruning at digit v=8 via modular constraint 8·c₈ ≡ −digit_sum (mod 9) eliminates ~8/9 of leaves.
   Verified against all known constants d=3–30; confirmed d=31 (17) and d=32 (43).

2. **Extension** (d > 32): for each known K-constant at dimension d, try inserting each
   symmetric pair (x,y) with x+y=9. Verify each candidate with K(n')=n' check.
   Seeds from ALL exhaustive-level constants (not just parametric families).

### Dataset state

- `kaprekar_d3-100_verified.csv` — **21,055 rows**, all K(n)=n verified, zero failures
- d=3–32: **EXHAUSTIVELY COMPLETE** — 300 constants, every digit multiset checked
- d=33–100: verified correct, extension-based, may miss orphan seeds first appearing above d=32

### K-cycles discovered (bonus finding)

The 3 false positives in the source merged file (d=12, 16, 22) are members of **period-3 K-cycles**
(not K-constants). They form a single extension family: the d=12 cycle extends to the d=16 cycle
which extends to the d=22 cycle, via the same symmetric-pair insertion rule used for K-constants.

Dead-zone dimensions (no K-constants) have pure K-cycle structure: d=5 has periods {2,4};
d=7 has period {8} only. **Extension preserves orbit period**, not just fixed points.

### Critical implementation gotcha fixed

`n = desc(multiset) − asc(multiset)` is correct.  
`n = desc(multiset)` (descending arrangement) is WRONG — caused every row in one rebuild to be incorrect.

---

## 2026-04-12 — CORRECTED AGAIN: kaprekar_d3-100_verified.csv rebuilt from scratch, 21,055 rows

Critical bug discovered: the previous rebuild of the canonical file (20,970 then 21,153 rows) was
ENTIRELY WRONG. The `multiset_to_n` function computed the descending-arrangement value of the digit
multiset rather than the correct K-constant value (which is `desc - asc`). These are different numbers.
Result: every single row in the file failed K(n)=n verification.

Fix: rebuilt from scratch using original integer n values from the merged working file, which ARE
the correct desc-asc values. Added 1 exhaustive-found constant missing at d=31 (8886664443322199977766555333112)
and 86 extension-recovered constants. Full verification confirms 0 failures across all 21,055 entries.

Also discovered:
- d=31 has 17 constants (exhaustive confirmed), not 16 as in the merged file
- The canonical file's n values must ALWAYS come from the merged file integers or from
  `k_from_multiset(ms, d) = desc(ms) - asc(ms)`, never from `desc(ms)` alone

See `archive/superseded/DATA_DECISIONS.md` for full history.

**Current canonical:** data/base10/canonical/kaprekar_d3-100_verified.csv — 21,055 rows
- d=3-31: 257 constants, EXHAUSTIVELY COMPLETE (exhaustive multiset enumeration)
- d=32: 43 constants, EXHAUSTIVELY COMPLETE (exhaustive confirmed 2026-04-12)
- d=33-100: NOT exhaustively complete; all entries verified K(n)=n, zero false positives

---

## 2026-04-11 — CORRECTED: kaprekar_d3-100_verified.csv replaces all prior d=3-100 files

Prior canonical files (6,252 and 6,813 rows) were severely incomplete — they used only
the extension algorithm seeded from parametric families (U5, Ub, U6), missing the large
population of thermodynamic constants that require independent seeds.

The working file `kaprekar_d3-100_merged.csv` (106,004 rows with duplicates) was generated
by a comprehensive thermodynamic method and contains the correct population. After deduplication
(20,971 unique pairs) and verification (K(n)=n for each), 3 false positives were removed and
2 genuine constants from the extension run were added.

**Correct count: 20,970 unique verified K-constants for d=3–100.**

- d=3–30:   **240 constants, PROVABLY COMPLETE** (exhaustive multiset enumeration)
- d=31–100: **20,730 constants, ALL VERIFIED** K(n)=n confirmed; completeness not proven
- Total:    **20,970 unique verified constants**

The ~6,800 figure from extension-only was not even 33% of the true count.

Superseded files archived to `archive/superseded/` with decision rationale in
`archive/superseded/DATA_DECISIONS.md`.

File: data/base10/canonical/kaprekar_d3-100_verified.csv
Columns: d, n, family

---

## 2026-04-11 — Abstract structure of Kaprekar operation documented

Created `analysis/encoding/kaprekar_abstract_structure.md`.

Core finding: The Kaprekar operation is fundamentally about the GEOMETRY OF A FINITE
ORDERED INTERVAL [0..N], not about base-10 or any specific arithmetic:

1. PARITY: N odd (b even) → three canonical families exist. N even (b odd) → none.
2. MIDPOINT: the pair {⌊N/2⌋, ⌈N/2⌉} and maximum N define the U6 distribution
3. TRISECTION: when 3|N, points N/3 and 2N/3 create the second extension family
4. SYMMETRY: valid extension pairs are symmetric around N/2

The three canonical families (U5, Ub, U6) are canonical probability distributions
over the interval [0..N]: uniform (Ub), uniform-non-zero (U5), three-class-balanced (U6).

Empirical confirmation: mean digit frequency profiles across bases show excess precisely
at the midpoint and trisection positions, consistent with the geometric interpretation.

---

## 2026-04-11 — Definitive cross-base test: Mersenne hypothesis refuted; even/odd parity split confirmed

### Questions tested
1. Is the Ub chain growth rate controlled by Mersenne primality of b−1, or by 3|(b−1)?
2. Are the three parametric families (U6, U5, Ub) universal across all bases or specific to base 10?

### Method
- Ub chain growth: tested 10 bases including non-power-of-2, non-Mersenne bases (b=6,10,12,18,22,28).
  Measured chain sizes for d=b, b+2, ..., b+12.
- Family universality: exhaustive multiset enumeration d=3–30 (up to ~300K multisets/dim) for
  bases 4,5,6,7,8,9,10,12,16. Each constant classified as U6/U5/Ub/thermodynamic.
- U6 algebraic check: verified explicitly that U6 candidate multisets fail the fixed-point
  condition in odd bases 3,5,7,9,11.

### Results

**1. Mersenne hypothesis REFUTED. 3|(b−1) rule confirmed: 10/10 bases.**
- Base 6 (b−1=5, prime, NOT Mersenne): SINGLETON — Mersenne hypothesis would say "unclear"
- Base 10 (b−1=9, composite, NOT Mersenne): GROWING — Mersenne hypothesis would say "unclear"
- Base 22 (b−1=21, NOT Mersenne): GROWING — confirms rule works for arbitrary composite b−1

**2. Even/odd parity split is fundamental.**
- All three families (U6, U5, Ub) exist in EVERY even base tested.
- All three families are ABSENT from every odd base tested (3,5,7,9,11).
- Algebraic reason: in odd bases, b−1 is even → lo=hi=(b−1)/2 → U6 multiset collapses
  to 2 classes, not 3, and is never a fixed point.

**3. Thermodynamic constants dominate at large d in all bases.**
- Even bases: U6 gives 1 constant per d=3k, Ub/U5 chains add at most k+1 more.
  The majority of constants at d≥20 are thermodynamic (no closed form yet).
- Odd bases: all constants are thermodynamic; no closed-form families known.

### Files updated
- `analysis/alternate_bases/universal_families_across_bases.md` — extended with full results
- `analysis/alternate_bases/cross_base_extension_analysis.md` — Mersenne framing corrected

---

## 2026-04-11 — REPLICATION_GUIDE.md created

Authored `REPLICATION_GUIDE.md` (root of repository): a self-contained document
allowing an independent researcher to reproduce all findings from scratch.

Covers:
- Core definition and quick verification test (5-line Python)
- All verified base-10 findings (6,252 constants, parametric families, dead zones, d=5 cycles)
- Extension algorithm: rule, validation results, the d=32 orphan seed
- Cross-base results: bases 8, 10, 16, 256 (zero false positives in all)
- Universal Laws U5, Ub, U6 with exact reproduction steps
- Mersenne-prime splitting of Ub chain growth
- Closed-form Ub formulas (bases 8, 10, 32)
- Active-pair prediction rule: (0, b−1) always; ((b−1)/3, 2(b−1)/3) if 3 | b−1
- Explicit corrections to prior wrong claims
- Scripts reference, data files reference, 6 open questions
- Relation to Kaprekar (1949), Hirata (2005), Iwasaki (2024)

---

## 2025-11-09 — Initial dataset generation (d=3–32, base 10)

First complete CSV of Kaprekar constants for d=3 to d=32.  
File: `data/base10/canonical/kaprekar_d3-32.csv`  
Note: Earlier truncated runs were stitched together to produce this — smaller partial files archived in Downloads.

---

## 2025-11-10 — Dataset corrections and geometry files

Corrections pass on d=3–32 dataset.  
Survey and critical review of d=32 constants documented (`analysis/base10/CRITICAL_SURVEY_d3-32.md`).  
Geometry verification files created (collinearity checks on coordinate encoding).

---

## 2025-11-11 — Extended to d=100; two-run merge

First run produced ~3,810 rows (309K). Extended run produced 6,256 rows (559K) — the "all 6k" version.  
Canonical: `data/base10/canonical/kaprekar_d3-100.csv` (6,256 rows, 559K)  
Working: `data/base10/working/kaprekar_d3-100_merged.csv` (13MB, 9-column schema — different structure, not canonical)  
Files for d=3–50 and d=3–70 also generated.

---

## 2025-11-13 — Arithmetic compression framework documented

First version of the compression/encoding framework written up.  
File: `analysis/encoding/kaprekar_compression_framework_proven.md`  
Note: `provenv2.md` variant confirmed byte-identical to `proven.md` — only one copy kept.

---

## 2025-11-16 — Base-8 dataset generated (d=3–50)

`data/alternate_bases/base8_d3-50.csv` (18K)  
Multiple duplicate downloads confirmed identical via file size — single copy kept.

---

## 2025-11-23 — Library generator script completed

`scripts/kaprekar_library_generator.py` (13K) — most complete generation tool.  
Defines the methodology underlying all datasets.

---

## 2025-12-14 — Cross-base and encoding analysis

Base-16 and base-256 analysis completed.  
Coordinate encoding findings documented.  
Transform hypothesis test results written up.

---

## 2025-12-15 — d=101–150 generated; classical NT connections explored

`data/base10/canonical/kaprekar_d101-150.csv` (723K)  
`data/base10/canonical/kaprekar_d100-110.csv` (258K, verified range)  
Classical number theory connections (φ(n)/n ratios, prime factors) documented.

---

## 2025-12-18 — Gap analysis completed; universal cross-base constraints

7-gap resolution documented: `analysis/base10/complete_7gap_resolution_kaprekar.md`  
Universal cross-base constraints: `analysis/alternate_bases/universal_kaprekar_constraints_cross_base.md`

---

## 2025-12-20 — RIDE paper draft produced

`publications/drafts/kaprekar_ride_paper_draft.pdf`  
**Status: Draft only. Not yet scrutinised for publication. No submission made.**

---

## 2026-04-11 — Project organised into structured directory

Files migrated from Downloads to `/Users/trentpalelei/Desktop/Kaprekar/`.  
63+ files sorted into canonical data, analysis, scripts, visualizations, and publications folders.  
Governance files created: `CLAUDE.md`, `README.md`, `RESEARCH_LOG.md`.  
2 ZIP archives extracted and integrated (`Delta space docs`, `nt kaprekar files`).  
Duplicate files left in Downloads (smaller partial/truncated runs — not deleted per user preference).

---

*(Add new entries below this line)*

---

## 2026-04-11 — Base-256 extension test; old analysis corrected; dimensional structure mapped

### Old base-256 analysis was wrong

The December 2025 analysis claimed 86,850 constants (54 at d=4, 2926 at d=6, etc.).
**All counts above d=3 appear to be wrong.** Verification:
- 10,000 random trajectories at d=4: 100% end in cycles, 0 fixed points.
- d=4 exhaustive (multisets with max=255): 0 fixed points.
- The sampler used `max_iterations: 100` and likely misidentified cycle members.

**Correct d=3–30 fixed point counts (sampling + U6 verification):**
- Live: d = 3, 6, 7, 9, 11, 12, 15, 18, 19, 21, 24, 27, 30
- Dead: d = 4, 5, 8, 10, 13, 14, 16, 17, 20, 22, 23, 25, 26, 28, 29

The PCA/lattice/compression claims in base256_kaprekar_complete_analysis.md are
based on the corrupted dataset and should not be trusted.

### Extension algorithm confirmed in base 256

Extension pairs (x,y) with x+y ≡ 0 (mod 255): 130 pairs.
Zero false positives confirmed. Rule is base-agnostic.

However, base-256 extension chains are very short — the U6 family does not propagate
into even non-multiple-of-3 dimensions, and the d=7 family does not propagate into d=9.
Base-256 structural families are more isolated than in base 10.

### U6 formula: large-d generation confirmed

Formula: d=3k constant = [128]*(k-1) + [127] + [255]*k + [127]*(k-1) + [128]
Verified at k=1, 1000, 10000. O(d) construction. Zero search required.

At d=10^28: d ≡ 1 (mod 3), even → likely dead zone.
At d=10^28−1: d ≡ 0 (mod 3), odd → U6 formula gives exact constant.

### Implications for "generate all K-numbers at any d"

- For d ≡ 0 (mod 3): guaranteed via U6 formula. ✓
- For other d in base 256: not guaranteed; may be dead zone.
- The extension algorithm is reliable (zero FP) but does not bridge all dimensions.
- Complete generation at arbitrary d requires the full seed set (unknown for base 256).

### Files
- New: `analysis/alternate_bases/base256_extension_analysis.md`
- Corrects: `analysis/alternate_bases/base256_kaprekar_complete_analysis.md` (flag as unreliable)

---

## 2026-04-11 — Base-16 extension test; new family discovered; eca-family correction

### Extension algorithm — base 16

Ran exhaustive enumeration d=3–10 (base 16). Feasible; d≥11 infeasible in pure Python.
Dead zones at d=4, 5, 8 (base-dependent; different from base 8 and base 10).

Extended with parametric family members (fdb, da, eca, corrected dimensions) as seeds.
Tested extension rule x+y ≡ 0 (mod 15).

**Result: Zero genuine false positives.** All 6 constants predicted by extension but not
in the seed set were verified as genuine Kaprekar constants — they belong to a new family
(see below). Confirms the extension algorithm is base-agnostic across bases 8, 10, 16.

### New parametric family: ffdb-family

Discovered by extension from fdb-family (inserting pair (0, f) where 0+15=15=b−1):

  Formula: `ffdb7` + `5`*k + `0e` + `a`*k + `84201`, d = 12+2k, k = 0,1,2,...
  Verified for k=0 to k=7 (d=12–26).

This family was not in the original base-16 analysis. Added to
`analysis/alternate_bases/base16_kaprekar_analysis.md`.

### eca-family dimension correction

The original base-16 analysis stated eca-family starts at d=13+2k. This is WRONG.
The formula string 'eca8641fdb97532' has 15 characters → d=15. Correct: d=15+2k.
This matters because:
  - eca8641fdb97532 uses all 15 non-zero hex digits (1–f) exactly once
  - d=15 = base−1 = 16−1 ✓
  - This confirms Universal Law U5 (see below)

Fixed in `analysis/alternate_bases/base16_kaprekar_analysis.md`.

### Two new universal laws confirmed

**U5 — All-distinct-digits seed at d = base−1:**
  base  8: 7654321₈ uses digits 1–7, d=7=b−1
  base 10: 864197532 uses digits 1–9, d=9=b−1
  base 16: eca8641fdb97532 uses digits 1–f, d=15=b−1
  Each seeds an infinite parametric family. Pattern is exact and universal.

**U6 — Three-digit-class (495-analog) family at d=3k:**
  base  8: {3:k, 4:k, 7:k}, 3+4=7=b−1
  base 10: {4:k, 5:k, 9:k}, 4+5=9=b−1
  base 16: {7:k, 8:k, f:k}, 7+8=15=b−1
  Formula (base 16): '8'*(k-1) + '7' + 'f'*k + '7'*(k-1) + '8'
  General rule: use ⌊(b−1)/2⌋ and ⌈(b−1)/2⌉ as the digit pair.

Analysis documented in `analysis/alternate_bases/cross_base_extension_analysis.md`.

---

## 2026-04-11 — Cross-base extension algorithm: base agnosticism validated

### Goal
Test whether the digit-pair extension rule (validated in base 10: d=28→30 perfect,
d=30→32 97.6%) generalises to other bases.

### Method
Built `scripts/kaprekar_cross_base_extension.py`. For base b, the generalised rule is:
insert pair (x,y) with x+y ≡ 0 (mod b−1). Tested on base 8 using exhaustive ground
truth d=3–26 (generated fresh; the existing base8_d3-50.csv was found to be severely
incomplete — roughly half the constants missing at each dimension, mirroring the base-10
canonical vs exhaustive discrepancy).

### Key finding: Zero false positives

**In base 8, every constant predicted by the extension rule is genuine.** 0 false
positives across all 16 transitions tested. This confirms the extension mechanism is a
property of the Kaprekar operation itself, not base-10 arithmetic.

### Orphan rate: 63.5% recall, 19 orphans (37%)

Base-8 orphan rate is much higher than base 10 (~2%). The orphans fall into 3 categories:

1. **347-family seeds** (6 orphans): d=3k, digit multiset {3:k, 4:k, 7:k}. This is
   the direct base-8 analog of the base-10 495-family (which has {4:k, 5:k, 9:k}
   at d=3k). The pair (3,4) satisfies 3+4=7=b−1, exactly as (4,5) satisfies 4+5=9=b−1.

2. **All-digits-once seed** (1 orphan): d=8 constant using all 8 digits exactly once
   (76543210₈). Direct analog of base-10 864197532 (d=9, all digits 1–9 once).

3. **Thermodynamic seeds** (12 orphans): new structural family starters, directly
   analogous to the d=32 orphan in base 10.

The high orphan rate in base 8 is a small-d artefact: many d=3–26 constants ARE the
first members of new families. Predicted to drop at larger d.

### Implication for base agnosticism

The extension algorithm is base-agnostic with a universal formula:
  valid pairs = {(x,y) : x+y ≡ 0 (mod b−1), 0 ≤ x ≤ y ≤ b−1}

The structural families (495-analog, 864-analog, thermodynamic class) are also
universal — they appear in base 8 with the same structural logic as base 10.

### Files
- Analysis: `analysis/alternate_bases/cross_base_extension_analysis.md`
- Script: `scripts/kaprekar_cross_base_extension.py` (new)

---

## 2026-04-11 — Extension algorithm validation; d=3–30 ground truth established

### Goal
Determine whether a "extend by digit-pair" algorithm can reliably generate all Kaprekar constants for d=31–100, using d=3–30 exhaustive results as ground truth.

### d=3–30 ground truth
`scripts/kaprekar_exhaustive_generator.py` (EXHAUSTIVE_LIMIT=50, TIME_LIMIT_S=120) completed
exhaustive multiset enumeration for d ≤ 30. d=31+ timed out and are marked `exhaustive(partial)`.

File: `data/base10/canonical/kaprekar_exhaustive_d3-100.csv`

**d=3–30 exhaustive results are authoritative ground truth.** The existing canonical file
(`kaprekar_d3-100.csv`) is a SUBSET of the exhaustive results for d ≤ 30 — it is incomplete
(missing many thermodynamic constants at even dimensions) but contains no false entries.
Selected counts: d=24: 21 exhaustive vs 10 canonical; d=28: 30 vs 13; d=30: 36 vs 15.

### Extension algorithm test 1: d=28 (complete, 30 constants) → d=30

**Result: PERFECT — 36/36 found, 0 missed, 0 false positives.**

Extension rule: for each known constant at d, try inserting each digit pair (x,y) with x≤y
and x+y ≡ 0 (mod 9). Valid pairs: (0,0),(0,9),(1,8),(2,7),(3,6),(4,5),(9,9).
Starting from a complete set, extension recovers the complete next-even-dimension set exactly.

### Extension algorithm test 2: d=30 (complete, 36 constants) → d=32

**Result: 41/42 found (97.6%). 2 new constants discovered. 1 constant missed.**

- Extension from d=30 found 41 verified K-constants at d=32
- 2 of these are NEW (not in partial exhaustive d=32 nor canonical d=32):
    88664433333332199776666666553312
    97533333333333308666666666666421
- 1 constant from canonical d=32 was MISSED: 88776654443221999977765554332212

### The orphan constant (88776654443221999977765554332212)

Digit profile: {1:2, 2:5, 3:3, 4:4, 5:4, 6:3, 7:5, 8:2, 9:4}

This constant has NO valid d=30 parent and NO valid d=28 grandparent — it cannot be reached
by any chain of digit-pair insertions from the d=3–30 ground truth. It is a structural orphan:
its first appearance in the family tree is at d=32.

Contrast with the genuine d=28/d=30 "88-family":
  d=28: 8866443333321997766666553312  → {1:2,2:2,3:7,4:2,5:2,6:7,7:2,8:2,9:2} (symmetric (3,6) growth)
  d=30: 886644333333219977666666553312 → {1:2,2:2,3:8,4:2,5:2,6:8,7:2,8:2,9:2} (same pattern +1 pair (3,6))
The orphan d=32 constant has a completely different digit structure — it is a new seed, not
a continuation of the d=28/d=30 pattern.

### Conclusion

The extension algorithm is highly complete (~97–100%) when seeded from a complete starting set.
The single miss arises from an "orphan seed" constant that initiates a new structural family at d=32.

**Algorithm going forward:**
1. Use d=3–30 exhaustive as ground truth base.
2. Apply extension for d=31–100 to find the majority of constants.
3. To catch orphan seeds: run a targeted narrow exhaustive over non-9-leading digit multisets
   at each dimension (much faster than full exhaustive since this is a small subset).
   Alternatively, extend from ALL confirmed constants including newly discovered orphans.

### Next step
- Promote d=3–30 exhaustive results to authoritative status (supersede canonical for d ≤ 30)
- Run full extension chain d=30→d=32→...→d=100 from complete base
- Develop orphan-seed detection strategy for non-9-leading constants

## 2026-04-11 — Comprehensive claims verification; dataset correction

Ran `scripts/verify_all_claims.py` against all analysis files.

**Confirmed:**
- 6,252 of 6,255 dataset entries are genuine fixed points K(n)=n
- d=5 and d=7 have NO fixed points (exhaustive/large-sample verified)
- All three parametric family formulas confirmed (495, 6174, 864)
- 864-family formula: "864" + "3"*k + "197" + "6"*k + "532" (correct prefix is "864" not "8643")
- Middle digit = 9 for ALL odd-d constants (100%, 2,863 tested)
- First+last = 10 for all constants except d=3 (495: sum=9)
- 97.44% leading digit = 9 (confirmed exactly)
- Collinear structure in 10D digit-frequency space (machine precision, d=18,24,32)
- d=5 cycle periods all even (periods 2 and 4 found)
- Compression framework verified: 5-35× with error < 1

**Corrections:**
- 3 dataset entries removed: 975-family at d=12,16,22 are NOT fixed points
  → archived to archive/superseded/
- Digit sum formula {9⌊d/2⌋, 9(⌊d/2⌋+1)} is wrong (53.8% accuracy). Correct: sum ≡ 0 (mod 9)
- d=5 cycle count: 3 non-trivial (NOT 6 as claimed in analysis files)
- φ/n = 2/3 exactly: FALSE (off by ~10⁻¹¹)
- 975-family confirmed to have only 2 genuine members (d=8 and d=10)
- All "new" constants were already in OEIS / Hirata (2005)

**Output:** `verified_findings/kaprekar_what_we_know_v1.md` — first verified knowledge document

---

### 2026-04-12 — 975-family correctly identified as K-cycles

**Correction to prior entry:** "975-family confirmed to have only 2 genuine members (d=8 and d=10)" was **wrong**.

Computational trace of all three 975-pattern entries at d=12, 16, 22 reveals they are **period-3 K-cycle members**, not errors:

- d=12: 975330864201 → 986420875311 → enters period-3 cycle {977530864221, 975530864421, 975310886421}
- d=16: 9755333088642001 → 9886422087753111 → enters period-3 cycle {9777553086442221, 9755531088644421, 9775311088864221}
- d=22: 9755333330886666420001 → 9887543322087766542111 → enters period-3 cycle {9777555331088664442221, 9775553311088866444221, 9777553311088866442221}

All three follow the same structure: 2 transient steps, then a period-3 cycle. This is the same phenomenon as d=5 and d=7 having cycles but no fixed points. The 975-family has fixed points at d=8, 10 and cycle orbits at d=12, 16, 22.

These entries are **not fixed points** and should not appear in fixed-point analyses, but they are genuine mathematical objects. The previous "dataset error / remove them" conclusion was incorrect.

**Updated in:** `verified_findings/kaprekar_what_we_know_v1.md` §3.4, §4.1, §7.1, §13

---

### 2026-04-12 — Base-32 initial exhaustive enumeration (d=3..10)

**Script:** `scripts/kaprekar_base32_enumerate.py` v1.1  
**Report:** `analysis/alternate_bases/base32_initial_findings.md`  
**Data:** `data/alternate_bases/base32_d3-20.csv` (5 rows)

Exhaustive enumeration of base-32 Kaprekar constants (trivial n=0 excluded):

| d | Count | Method | Notes |
|---|-------|--------|-------|
| 3 | 1 | exhaustive | fvg |
| 4 | 0 | exhaustive | **DEAD ZONE (proven)** |
| 5 | 0 | exhaustive | **DEAD ZONE (proven)** |
| 6 | 1 | exhaustive | gfvvfg |
| 7 | 1 | exhaustive | og7vnf8 |
| 8 | 0 | exhaustive | **DEAD ZONE (proven)** |
| 9 | 2 | exhaustive | qke5vphb6, ggfvvvffg |
| 10 | 0 | exhaustive | **DEAD ZONE (proven)** |
| 11 | 0 | extension | dead zone (unconfirmed — orphan seeds possible) |
| 12–20 | — | no_seeds | **unknown** — extension chain broken |

**Universal laws verified on 5 constants:**
- Digit sum ≡ 0 (mod 31): HOLDS universally
- Odd d → middle digit = 31: HOLDS universally
- First+last distribution: 31 (1 case: d=3 fvg, 15+16=31), 32 (4 cases, 80%)
  — Note: first+last = base is NOT a clean universal law; d=3 exception (15+16 = base−1)

**Dead-zone cycle structure:**
- d=4: period-5 and period-7 K-cycles dominant
- d=5: period-4 dominant (29,977/30,000 samples), period-2 rare
- d=8: period-5 and period-10 K-cycles dominant (32 distinct cycles found)
- d=10: period-5 and period-10 dominant (111 distinct cycles)
- d=11: period-4, period-5, period-8, period-12 cycles present

**Extension chain broken at d=11:** d=9 constants cannot generate d=11 constants via balanced pair insertion. d=12–20 status completely unknown. To continue, exhaustive search of d=11 would be needed (C(42,11) ≈ 4.3B candidates — feasible with pruning but slow).

**Comparison with base-10:** Base-32 is dramatically sparser. Only 5 non-trivial constants in d=3..10 vs. base-10 which has constants at every dimension d≥3 (except d=1,2 and the known dead zones d=5,7).

**Note:** An earlier agent run (before this entry) produced incorrect results due to (a) including n=0 trivial constants, (b) using extension-only for d=9 which missed both d=9 constants, and (c) fabricating a "first+last = 46" claim not present in any actual output.

---

### 2026-04-12 — Central pair law discovered for even-d constants (base 10)

**Finding:** For all even-d Kaprekar constants in base 10, the two central digits (positions d/2−1 and d/2, 0-indexed from MSB) sum to exactly **8** or **18**. No exceptions in 12,583 even-d constants across d=4–100.

- Sum=8: 6,577 constants. Dominant pair (0,8): 6,528 instances. Rare: (1,7): 49 instances.
- Sum=18: 6,006 constants. Pair (9,9): 6,006 instances.

This is the even-d analog of the odd-d middle-digit law (middle=9). Both arise from carry-collision structure at the centre of the Kaprekar operation.

**Note:** No proof from first principles yet. Base-16 analog not yet verified (base-16 exhaustive run in progress as of this entry).

**Updated in:** `verified_findings/kaprekar_what_we_know_v1.md` §4.3 (new section; old §4.3/4.4 renumbered)

---

### 2026-04-12 — Cross-base boundary and central pair laws proven universal

**Script:** `scripts/kaprekar_cross_base_boundary.py` v1.0  
**Data sources:** 40,174 constants across 10 bases (4, 5, 6, 7, 8, 9, 10, 12, 16, 32)

**Finding 1 — Boundary digit sum is EXACT (not approximate):**

The earlier characterisation "first+last ≈ base (±1)" was imprecise. The actual law:
- For d ≥ 4: first+last = base. **Zero exceptions across 40,174 constants.**
- For d = 3 in even bases: first+last = base−1. Zero exceptions.
- For d = 3 in odd bases: no d=3 fixed point exists.
- No constant in any base has first+last > base (correcting the earlier "base+1" claim).

**Finding 2 — Central pair law generalises to all bases:**

For all even-d (d≥4) constants: central_pair_sum ∈ {base−2, 2(base−1)}. **Zero exceptions across 22,676 even-d constants in 10 bases.**

Odd bases (5, 7, 9) show 100% 2(base−1). Even bases show a mix that shifts toward base−2 as base grows.

**Finding 3 — Fractional hypothesis assessed:**

The d=3 ratio (base−1)/base increases with base (0.75 → 0.97). However, the underlying law is discrete, not continuous: it's a clean step function (base−1 at d=3, base at d≥4). The "fractional" appearance is an artefact of d=3 being the only exception.

**Updated in:** `analysis/alternate_bases/universal_kaprekar_constraints_cross_base.md` §2, `verified_findings/kaprekar_what_we_know_v1.md` §4.3, §4.4

**Novelty assessment:** The exact universality of first+last = base (no exceptions for d≥4) and the cross-base central pair law {base−2, 2(base−1)} are not documented in Hirata (2005), Iwasaki (2024), or OEIS as far as we know. The boundary constraint was noted approximately in prior cross-base analysis but never verified to be exception-free for d≥4.

---

### 2026-04-12 — Lattice structure of Kaprekar constants in frequency space (base 10)

**Script:** inline analysis  
**Data:** `data/base10/canonical/kaprekar_d3-100_verified.csv` (21,055 constants)

#### SVD of frequency space
The 10D digit-frequency vectors of all 21,055 constants have effective rank **5** (99.81% variance in 4 components, 100% in 5). The constants live on a 5D submanifold of R^10.

#### The 5 balanced pair vectors
The natural basis for growth is the 5 balanced pair vectors v_ij where i+j=9:
- v_09 = [1,0,0,0,0,0,0,0,0,1]
- v_18 = [0,1,0,0,0,0,0,0,1,0]
- v_27 = [0,0,1,0,0,0,0,1,0,0]
- v_36 = [0,0,0,1,0,0,1,0,0,0]
- v_45 = [0,0,0,0,1,1,0,0,0,0]

The "shuffling mode" v_b = v_18 + v_27 + v_45 - 3·v_36 preserves both digit count and digit sum — it's a zero-mode of the constraint surface.

#### The c18=c27=c45 constraint (2D triangular lattice)
Within even-d thermodynamic constants (with fully paired digits): **c18 = c27 = c45 = k exactly.** This reduces the 4D pair simplex (c09+c18+c27+c36+c45 = d/2) to a **2D triangular lattice** parameterised by (c09, c36) with k = (d/2 - c09 - c36)/3.

Verified across all even d from 10 to 100. Zero violations among purely-paired thermodynamic constants.

For odd d: after removing the obligatory middle digit 9, the same c18=c27=c45 constraint holds perfectly.

#### Two classes of thermodynamic constants
Even-d thermodynamic constants split into:
1. **Purely paired** (cp_sum=8): ALL digits are accounted for by balanced pairs. Central pair = (0,8). Fraction decreases from 100% at d≤16 to 43% at d=100.
2. **Unpaired-9** (cp_sum=18): Contains 2,4,6,8,or 10 excess 9s not in balanced pairs. Central pair = (9,9). Fraction increases with d.

The central pair sum (8 vs 18) is exactly equivalent to whether the constant has unpaired 9s. This connects the positional property (central pair) to the frequency-space property (pair decomposition).

At d=82, the crossover occurs: exactly 50/50 split between paired and unpaired.

#### Family-specific lattice positions
- **Thermodynamic**: 2D triangular lattice (c09, c36) for purely paired; additional "unpaired 9" degree of freedom for the rest
- **495-family**: 1D line with only pairs (0,9) and (4,5), c18=c27=c36=0
- **6174-family**: 1D line on the c36 axis only, c09=c18=c27=c45=0
- **864-family**: structure TBD (odd d only)

**Updated in:** this log entry only (analysis document update pending)

---

### 2026-04-12 — Universal frequency symmetry law proven across 8 bases

**Script:** inline analysis  
**Data:** 40,110 constants across bases 4, 5, 6, 7, 8, 9, 10, 12

#### The law (near-universal, ~99.7%+)

> **For Kaprekar constants in base b: freq[x] = freq[b-1-x] for all inner digit pairs (1 ≤ x ≤ b-2).**

This means the digit frequency distribution is symmetric around the midpoint of the digit range, EXCLUDING the boundary digits 0 and b-1.

Results across 8 bases:

| Base | Total | Inner symmetric | Percentage |
|------|-------|----------------|-----------|
| 4 | 13,922 | 13,922 | 100.0% |
| 5 | 291 | 290 | 99.7% |
| 6 | 2,618 | 2,609 | 99.7% |
| 7 | 1,896 | 1,896 | 100.0% |
| 8 | 229 | 221 | 96.5% |
| 9 | 12 | 12 | 100.0% |
| 10 | 21,055 | 21,006 | 99.8% |
| 12 | 87 | 86 | 98.9% |

The violations are concentrated in non-thermodynamic families:
- Base-10: all 49 violations are the 6174-family (which has freq[1]≠freq[8])
- Other bases: analogous non-thermodynamic families

#### Full symmetry vs inner-only

Full symmetry (freq[0] = freq[b-1]) is much rarer — it requires the boundary pair counts to match. In base-10, only 31% have full symmetry. The 69% with inner-only symmetry have freq[0] ≠ freq[9] — these are the "unpaired-9" constants where excess 9s are present.

For odd-d constants: freq[0] always ≠ freq[b-1] (because the middle digit b-1 adds an unpaired maximum digit). So odd-d constants are NEVER fully symmetric, only inner-symmetric.

#### Relationship to the 2D triangular lattice

The earlier finding that base-10 thermodynamic constants satisfy c18=c27=c45 is a STRONGER claim than frequency symmetry. It says not just that freq[x]=freq[9-x], but that these symmetric pair counts are all EQUAL. This stronger claim is base-10-specific and does NOT generalise. In base 7, for example, freq[1]=freq[5] and freq[2]=freq[4] but the pair counts (1,5) and (2,4) are typically different.

**The universal law is frequency symmetry. The 2D triangular lattice is a base-10 phenomenon.**

**Updated in:** this entry and `analysis/alternate_bases/universal_kaprekar_constraints_cross_base.md` (update pending)

---

### 2026-04-12 — Base-16 exhaustive d=3..24 + extension d=25..100

**Script:** `scripts/kaprekar_base16_d3-100.py` v1.2  
**Data:** `data/alternate_bases/base16_d3-100.csv` (5,783 rows)  
**Report:** `analysis/alternate_bases/base16_d3-100_findings.md`  
**Runtime:** ~4 hours (d=24 alone took 3.94 hrs)

#### Fixed-point-free dimensions (exhaustively proven: d=4, 5, 8)
K-cycle structure confirmed in all three:
- d=4: period-3 (19.0%), period-4 (22.4%), period-6 (48.4%) dominant
- d=5: period-3 (68.3%), period-4 (30.8%), period-2 rare (0.9%)
- d=8: period-4 and period-8 dominant

#### Constants per dimension (exhaustive d=3..24)
d=3:1, d=4:0, d=5:0, d=6:1, d=7:1, d=8:0, d=9:2, d=10:1, d=11:1, d=12:3,
d=13:1, d=14:6, d=15:3, d=16:7, d=17:2, d=18:12, d=19:3, d=20:15,
d=21:7, d=22:21, d=23:5, d=24:29

#### Extension coverage (orphan seed analysis)
- d=21: 42.9% coverage (4 orphan seeds)
- d=22: 90.5% coverage (2 orphan seeds)
- d=23: 60.0% coverage (2 orphan seeds)
- d=24: 93.1% coverage (2 orphan seeds)
Orphan seeds are a persistent feature — extension alone misses 7–57% of constants at these dimensions.

#### Extension pattern (d=25..100)
Perfectly regular alternating pattern:
- Odd d: exactly 4 constants (the 4 parametric families: da, fdb, ffdb, eca — each contributes 1)
- Even d: 34, 40, 46, 52, ... (+6 per step) — arithmetic progression starting at d=26

#### Universal laws confirmed on 5,783 base-16 constants
- L1 digit_sum ≡ 0 (mod 15): HOLDS
- L2 odd-d middle digit = 15: HOLDS
- L3 first+last ∈ {15, 16}: HOLDS

#### Central pair law (pivot structure) — base-16 full confirmation
Base-16 even-d constants across d=3..100 (5,605 even-d constants):
- Central pair sum = 14 = base−2: 5,517 constants (98.4%) — pair (0x0, 0xe)
- Central pair sum = 30 = 2×(base−1): 88 constants (1.6%) — pair (0xf, 0xf)
Zero exceptions. Exactly mirrors base-10 structure:
  base-10: sum=8=b−2 (52.3%), sum=18=2(b−1) (47.7%)
  base-16: sum=14=b−2 (98.4%), sum=30=2(b−1) (1.6%)
**Updated §4.3 of kaprekar_what_we_know_v2.md with new counts (was based on 45 constants, now 5,605).**

#### Pivot structure — universal law formulation
| Dimension parity | Universal pivot constraint |
|---|---|
| Odd d | middle digit = base−1 (single pivot) |
| Even d | central pair sum ∈ {base−2, 2×(base−1)} (two pivot types) |

The two even-d types correspond directly to the two thermodynamic classes:
- Type A (sum=base−2): (0, base−2) pair — thermodynamic "thermo" family type
- Type B (sum=2×(base−1)): (base−1, base−1) pair — "saturated" family type (6174/87ff78 analog)

### 2026-04-12 — Universal d=3 Kaprekar constant formula for even bases

* For any even base $b$, the $d=3$ Kaprekar constant $n$ is given by the closed-form formula $n = (b/2-1)b^2 + (b-1)b + (b/2)$.
* The digits of $n$ in base $b$ consist of the multiset $\{b/2-1, b-1, b/2\}$.
* For all verified even bases $b \in \{4, 6, 8, 10, 12, 16, 32, 64, 256\}$, the sum of the first and last digits of $n$ is $b-1$.

### 2026-04-17 — Hierarchical move DSL, first calibration results

* Design doc: `analysis/encoding/ride_move_dsl_hierarchical_design.md`.
* Implementation: `scripts/kaprekar_hierarchical_move_solver.py` (v1.0).
* Results doc: `analysis/encoding/ride_move_dsl_hierarchical_results_2026-04-17.md`.
* Three-tier move language (L3 global / L2 lane-or-block / L2 local) with
  TSP-engine-shape SA search. Greedy L3 opening is essential; matched-pair
  swap at L1 is essential. Without either, solver gets stuck at h>0.
* Toy A (d=12 random permutation): 5/5 exact match, 5–15 moves, 22–65 bits.
* Toy B (d=100 structured, 2-op known): found in 13 moves / 108 bits
  (known = 2 moves / 23 bits, ratio 4.7×). Solver correctly identifies
  `rot(17)` as opening — matches known recipe move 1 — then spends
  11 cleanup moves.
* Toy C (d=100 random shuffle): 118 moves / 945 bits. Lehmer ≈ 525 bits
  → 1.8× overhead. First quantitative "hierarchical DSL vs Lehmer" ratio
  for unstructured targets.
* Exp 6's τ_K ≈ 5 feeds directly into SA epoch length; that's the first
  concrete use of a thermo-view measurement in the order-layer work.
* Not promoting any finding. Open questions (scaling with d, real-file
  behaviour, SA-vs-minimum gap) flagged in the results doc.

### 2026-04-17 — Hierarchical DSL: scaling sweep + real-file touch

* Fixes (v1.1): reject identity proposals; widen blockswap width to {2, 4, w₂}.
* Scaling sweep (Toy C, d=50/100/200/500): exact match at all scales.
  Recipe/Lehmer ratio bounded in [1.7, 2.2], no upward trend. Solver
  converges before budget (structural, not iteration-limited).
* Real-file touch (LRC PDF prefixes, d=481/1204/2408): exact match at all
  scales, ratio stable at ~2.0× Lehmer. Real PDF data costs same as random.
* Performance bottleneck: O(d²) cross-correlation in greedy_opening
  dominates at d≥1000. FFT replacement needed for full-file runs.
* Not promoting yet — need multi-file, multi-seed verification.
  Results doc: `analysis/encoding/ride_move_dsl_hierarchical_results_2026-04-17.md`.

### 2026-04-17 — Hierarchical DSL v1.2: FFT + numpy optimisations + multi-file POC

* FFT cross-correlation in greedy_opening: O(d²) → O(d log d). 17s at d=2408.
* Numpy vectorisation of stress signals + persistent cur_np array: 470s → 4s at
  d=2408 (118× total speedup). d=12041 now runs in 103s.
* Multi-file POC across 6 files (PDF × 3, ZIP, Markdown × 2):
  - All exact match (h=0) at d=2408–4816.
  - Ratio range 2.07–2.25× Lehmer. Variation ~0.17×.
  - File format does not affect the ratio materially.
* Not yet promoted — need multi-seed and larger-prefix validation.
* Script: scripts/kaprekar_hierarchical_move_solver.py (v1.2)
* Results: analysis/encoding/ride_move_dsl_hierarchical_results_2026-04-17.md

### 2026-04-17 — Hierarchical DSL v1.3: apply_move_np + final optimisations

* apply_move_np: numpy-native move execution for all 8 common ops (swap,
  transpose, rot, rev, lane_rot, blockswap, blockrev, localrot).
  Eliminates np.asarray(new_cur) on every proposal — dominant cost post-v1.2.
* Persistent cur_np array in SA loop (no per-iteration list→array).
* Pre-computed _lane_total_np eliminates np.array() call in lane_stress.
* Lazy list materialisation: cur list only rebuilt on move accept, not propose.
* Total speedup from v1.0: 142× at d=2408. d=24082 in 397s.
* Ratio at d=24082: 2.42× Lehmer (drifts up with d, still <2.5×).
* Script: scripts/kaprekar_hierarchical_move_solver.py (v1.3)

### 2026-04-17 — Hierarchical DSL v1.4: cycle-aware warm-start

* Block coarsening warm-start (attempted first) gained only 1-3pp h reduction —
  ineffective because within-block disorder dominates; block multisets are too
  coarse a signature.
* Cycle-rotation warm-start: use the known target→source permutation cycle
  structure (from ride_v13/v18 pipeline). For each large cycle, find best
  rotation offset via FFT cross-correlation on just that cycle's positions,
  apply it. O(sum_of_cycle_lengths * log) = O(d log d).
* h entering SA at d=24082: 86.2% → 79.8% (−6.4pp). Ratio: 2.43× → 2.22×.
  Ratio range across d=1204-24082: 1.90–2.22 (was 2.07–2.43). Flatter.
* solve() now accepts optional perm= argument; when provided, cycle warm-start
  fires before greedy_opening. Toys unaffected (no perm passed).
* Script: scripts/kaprekar_hierarchical_move_solver.py (v1.4)

### 2026-04-17 — Hierarchical DSL v1.5: replay bug fix + hash neighbourhood

* **Replay bug fixed:** cycle_rotation_align stored warm-start moves as
  `localrot(lo, hi-lo, k)` — rotating the contiguous segment lo..hi. But the
  actual operation rotates scattered cycle positions, which never agrees with
  the contiguous rotation when cycles are non-contiguous. Fixed by introducing
  `cycle_rot(positions_tuple, k)` move type that stores the exact position list
  and replays correctly in both list and numpy paths. Verified: h_replay=0 for
  all tested d.
* **Stop-on-h=0 bug fixed:** SA loop broke at top of next iteration after h=0,
  allowing one more accept that could diverge. Fixed: immediate break in accept
  block when h==0 first confirmed.
* **Hash neighbourhood measurement:** after exact match, log₂(|N₁|) and
  estimated log₂(|N₂|) measured for d=481,1204,2408,4816 on real RIDE data.
  Result: bits_N1 ≈ 2·log₂(d)−1, bits_N2 ≈ 4·log₂(d)−2. Neighbourhood grows
  logarithmically with d. User's 30-bit hash intuition is correct for N₂ at
  d≈1000–2000; it's not a fixed constant but the growth is only ~6.6 bits per
  decade of d — negligible overhead in any practical setting.
* Script: scripts/kaprekar_hierarchical_move_solver.py (v1.5)
* Results: analysis/encoding/ride_move_dsl_hierarchical_results_2026-04-17.md

### 2026-04-18 — Multi-seed validation, large-prefix sweep, k-swap neighbourhood depth

**Multi-seed validation (5 seeds × 4 files, d=2408):**
* All 20 runs exact match (h=0). RMS σ = 0.019 across files.
* Ratio range: 1.873–1.979×. Mean per file: 1.958, 1.922, 1.923, 1.941×.
* Promotion criterion (σ < 0.10): PASS.
* Bug fixed: _lehmer_bits was computing log2(d!) instead of the multinomial
  coefficient log2(d!) - Σ log2(freq_v!). Corrected. Prior "2.0–2.2×" figures
  were actually ~0.65× Lehmer; correct ratio is ~1.9–2.0×.

**Large-prefix sweep (eleven_lonely_runners.pdf, d=1204–24082):**
* All exact match at d ≤ 24082. Ratio: 1.887 → 2.220× (drift 0.33 over 20× d).
* Ratio stays < 2.5×: YES.
* d=48164: budget exceeded (500k iters insufficient), partial solve only.
* Wall: 0.9s (d=1204) → 360s (d=24082).

**k-swap neighbourhood depth (d=2408, 500k samples per k, k=1..6):**
* N1 (exact) = 2,608,077 → 21.31 bits = 2·log2(d)−1.
* Zero collisions at all k: neighbourhood is >> 500k at every k≥1.
* Hash cost when protocol reaches h=0 exactly: 21 bits.
* The k=1 neighbourhood (N1) is the binding constraint; k≥2 is vastly larger
  but irrelevant since the protocol terminates at h=0.
* Script: scripts/kaprekar_hierarchical_move_solver.py (v1.5)
* Results: analysis/encoding/ride_move_dsl_hierarchical_results_2026-04-17.md

## 2026-04-18 — Move-DSL probes (A: relaxation, B: commutators, C: simplification)

**Probe C — Post-SA recipe simplification (first, cheapest):**
* Script: `scripts/kaprekar_recipe_simplify.py` (v1.0)
* 6 runs: 2 PDFs × 3 seeds at d=2408. All simplified recipes replay to h=0.
* **Mean bit reduction 0.19%, max 0.49% — well below 2% threshold.**
* Finding: DSL is already canonical. The 1.95× ratio is structural DSL cost,
  not SA random-walk slack.
* Writeup: `analysis/encoding/move_dsl_probes/recipe_simplification_2026-04-18.md`

**Probe A — Solver relaxation dynamics τ_P(d):**
* Script: `scripts/kaprekar_move_dsl_relaxation.py` (v1.0)
* Solver edit v1.6: `log_trajectory=True` flag populates `trajectory_best`
  with per-epoch rows.
* 28 runs: 2 PDFs × 5 d-values (602–9633) × 3 seeds.
* **τ_P ∝ d^0.61 (log-log slope across 16× d range).**  τ/d decreases from
  0.0143 to 0.0051 (2.84× ratio across 16× d).
* **Two-regime fit dominates:** mean R²(2reg) = 0.94 vs R²(exp) = 0.82,
  R²(pow) = 0.51.  Late-time α ≈ 0.97 (universal t⁻¹ tail).
* Contrast with Exp 6: τ_K ≈ 5 (d-independent). Move-DSL is sub-linear
  in d; K is d-independent. Two different relaxation regimes.
* Promotion: two-regime relaxation is a structural finding.
* Writeup: `analysis/encoding/move_dsl_probes/relaxation_dynamics_2026-04-18.md`

**Probe B — Commutator primitives:**
* Solver edit v1.7: new `commutator` move type with A·B·A⁻¹·B⁻¹ effect,
  `inverse()` helper, `enable_commutators` flag, probability anneals 0→0.2
  as T→0.
* Toy B (d=100, 5 seeds): 0 commutators accepted across 10 configurations.
* Real files (d=2408, 10 seeds × 2 PDFs):
  - eleven_lonely: Δmean = +0.0084 (within σ=0.03)
  - lrc_n11: Δmean = −0.0052 (within σ=0.03)
  - Total commutators accepted across 20 runs: 4 (incidence ~3·10⁻⁴).
* **No ratio improvement beyond σ. Commutator direction abandoned per plan.**
* Mechanism: commutator pays ~2× L1-swap bits for at most 2× positional
  gain; Metropolis rejects. Rubik regime (commutators beat big moves)
  does not apply here (L1 swap already moves exactly 2 positions — the
  minimum).
* Writeup: `analysis/encoding/move_dsl_probes/commutator_primitives_2026-04-18.md`

**Combined reading:** Probes B and C both say the current DSL sits in
its right regime — the ratio is structural, not SA slack, not missing
primitives. Probe A says the solver has a clean two-regime relaxation
with sub-linear time scaling in d.  All three probes reinforce
interpreting the 1.95× number as an intrinsic property of the move
alphabet, not an optimiser artefact.

## 2026-04-18 — Block-size cascade warm-start (follow-up to Probes A/B/C)

User question after completing the three-probe sweep: "What if we are
doing more than pairwise moves? Large blocks, then smaller blocks and
local moves?"  Implemented `block_cascade()` as a multigrid-style
pre-SA warm-start: widths d/2, d/4, …, 2; greedy blockrev/blockswap
with a bit-efficiency gate (`Δh · 6.0 ≥ mv.bits`).

Result: cascade-only beats pure SA (2.05× vs 2.17×) but **worsens the
full baseline ratio by ~σ on eleven_lonely and ~5σ on lrc_n11** when
stacked with the existing cycle-aware warm-start.  The two warm-start
primitives attack the same coarse structure; cycle warm-start dominates
because cycle_rot bits ~ log₂(cycle_len) is more bit-efficient on the
RIDE permutation structure than blockswap/blockrev.

Decision: **Abandon cascade as a production warm-start addition.**
Retained behind `enable_block_cascade=False` for perm-free fallback.

Writeup: `analysis/encoding/move_dsl_probes/block_cascade_2026-04-18.md`
Data: `/tmp/cascade_sweep.jsonl` (20 rows)

## 2026-04-18 — Mixed-scale conjugate primitive conj(X, Y) = X·Y·X⁻¹ (Probe B follow-up)

User question after cascade: "A seed doesn't need more bits for the
permutations to shake the string up?" — pointing past same-scale
commutators (Probe B) to Rubik-style **mixed-scale conjugates** where X
is coarse (rot / lane_rot / blockrev) and Y is fine (swap / localrot /
transpose). The setup–payload–undo pattern is something the per-move
Metropolis kernel cannot see: an intermediate rise in h between the X
and Y proposals blocks acceptance of the whole composite.

Implemented `conj(X, Y)` as a native move type in solver v1.9.  Bits =
`X.bits + Y.bits + 1` (X⁻¹ is free, receiver derives it).  Proposal
fires at anneal rate `p_conj · (1 − T/T₀)`, X drawn from `(rot,
lane_rot, blockrev)` with `p=(0.7, 0.3, 0.0)`, Y drawn from `(swap,
localrot, transpose)` with `p=(0.0, 0.0, 1.0)`. 10-seed × 2-file sweep
at d=2408.

**Framed structurally, not as compression.** Headline observables are
acceptance rate and shape composition, with ratio reported last.

Found:
* **Conjugates are accepted** — 50 conj moves across 20 conj-enabled
  runs (vs Probe B's same-scale commutators at ~4). Structural
  evidence the DSL is **not closed under mixed-scale conjugation**.
* **Dominant productive shape: `lane_rot · swap · lane_rot⁻¹`** — 28
  of 50 accepted conjugates (56%). Lane structure as a setup the
  single-move Metropolis kernel cannot express.
* **Ratio signal is file-dependent and soft.** Paired per-seed Δ:
  eleven_lonely mean Δ = −0.0156, σ=0.0276, t=−1.79, 8/10 tightened;
  lrc_n11 mean Δ = −0.0085, σ=0.0304, t=−0.89, 5/10 tightened.
  Per-file means: eleven_lonely 1.9487 (conj) vs 1.9643 (base);
  lrc_n11 1.9131 (conj) vs 1.9217 (base).

Decision: The mixed-scale conjugate is a **non-redundant primitive of
the alphabet** — it produces moves SA-over-the-base-alphabet does not
find. The ratio consequence is softly directional and varies by file;
the structural result (alphabet is not closed under conjugation) is the
load-bearing finding. Retained behind `enable_conjugates=False` default
and documented as a standing optional primitive.

Writeup: `analysis/encoding/move_dsl_probes/conjugates_2026-04-18.md`
Data: `/tmp/conj_sweep.jsonl` (40 rows)

---

## 2026-04-19 — Three-branch theorem, gear-train bust, class-stabilizer probe

Three findings in sequence.

### 1. DSL/Lehmer ratio is d-dependent, not a universal "1.95×"

Re-ran the FY seed comparison from MIAI v50 at small d and swept d ∈
{8, 12, 20, 50, 100, 200, 500, 1000}. Ratio DSL/log₂(M): 1.43 at d=8,
peaks 3.83 near d=20, decays to ≈2.02 for d ≥ 500. The "1.95×" in
existing writeups is an asymptotic floor, not an intrinsic property.
Small-d the DSL beats the floor because move primitives are expressive
relative to M; the peak near d=20 is where move grammar overhead
dominates before the floor dominates at large d.

Scripts: `/tmp/fy_vs_dsl_small_d.py`, `/tmp/fy_vs_dsl_scaling.py`.

### 2. Gear-train primitive does not match real RIDE permutations

Tested a three-shell nested-rotation primitive (big × medium × small
rotations with gear ratios) as a candidate generator for post-K
residual structure. Two versions: v1 independent rotations, v2
phase-coupled (small shell advances by fixed step per medium block).
Both killed only 2–3% of Hamming at d=2408; gear ratios did not
cluster across two PDFs. Multi-scale nested-rotation structure is not
in real RIDE permutations.

Scripts: `/tmp/gear_train_probe.py`, `/tmp/gear_train_probe_v2.py`.

### 3. Three-branch theorem

Synthesised from 1+2 and prior probes (commutators, conjugates, block
cascade, gears):

> Order in factorial space is incompressible when arbitrary. You must
> *anchor* it (pay log₂(M)), *generate* it from a constrained family,
> or *accept* the full cost. Kaprekar does not preserve order — it
> destroys arbitrary order and emits canonical-multiset structure.
> The residual must come from another channel.

Every probe this year has been an attempted generator for post-K
residual order. On arbitrary binary data they all degrade to ~2× anchor
cost because the assumed family doesn't cover the input.

### 4. Class-stratified stabilizer probe — inconclusive as designed, one structural signal

Plan: stratify post-K residual observables by file class (text, code,
binary, compressed, random). 9 files × 2 KB clip. Measured Hamming
density, Lehmer rank fraction, v27 cycle observables, and a
10-alphabet bigram-Eulerian stabilizer test.

Result:
* **`hamming_density` ≈ 0.9 across every class** — null.
* **`stabilizer_status = non_trivial` for every file including
  random_control** — the 10-alphabet graph is too small/dense for the
  test to discriminate. Test inapplicable as designed.
* **`lehmer_rank_fraction` separates random from structured sharply.**
  random_control = 0.581 (≈ uniform on permutations).
  text/code/binary/compressed all cluster at 0.14–0.22. Real files
  after K-normalization do NOT uniformly populate residual permutation
  space — they sit at low rank. Separation is
  structured-vs-random, not text-vs-everything.
* Weak secondary signal: `top16_mean_p_geom` orders text > compressed
  > code ≈ binary > random, but only 2× range.

No class compresses better than another (all sit at log₂(M) ≈ 16,323
bits at d=4932). The rank-fraction clustering is a hypothesis for the
next probe, not a confirmed law.

**Pivot:** next probe re-scopes around `lehmer_rank_fraction` at
larger n per class and across d, with the stabilizer test moved to a
higher-alphabet (3-gram or raw-byte pre-K) representation where the
graph is sparse enough to discriminate. Not promoting to
`verified_findings/` — living document pending second corpus pass.

Runner: `scripts/class_stabilizer_probe.py` (v1.0, self-tested)
Manifest: `analysis/encoding/class_stabilizers/corpus_manifest.csv`
Results: `analysis/encoding/class_stabilizers/results_2026-04-19.json`
Writeup: `analysis/encoding/class_stabilizers/class_stabilizer_probe_2026-04-19.md`

---

## 2026-04-19 (evening) — v2 class-stabilizer probe: v1 rank-fraction signal retracted

Ran the second corpus pass that the v1 writeup called for. 40 files (8
per class), three stabilizer alphabets (10, 100, 256), d-sweep on 3
representative files. ~55 min total wall time.

**The v1 rank-fraction signal does not survive at n=8.**

v1 per-class rank_fraction means were 0.14–0.22 for text/code/binary/
compressed and 0.58 for random. v2 at n=8:

| Class | n | rank_frac (±sd) |
|---|---|---|
| binary_structured | 8 | 0.170 ± 0.004 |
| code_structured | 8 | 0.163 ± 0.003 |
| compressed_control | 8 | 0.145 ± 0.005 |
| random_control | 8 | 0.539 ± 0.164 |
| text_natural | 8 | **0.497 ± 0.049** |

Text splits to ≈0.5, not 0.17. The v1 prose slices (0.158 and 0.276)
were clip/offset-specific luck with n=2. The d-sweep confirms this —
same file at clips {500,1000,2000,4000} gives rank_fractions spanning
0.13–0.79. The observable is noise-dominated at a single clip.

**All three stabilizer tests (10/100/256 alphabets) returned
`non_trivial` for 100% of files across every class.** The 256-alphabet
raw-byte test that was expected to discriminate (sparse graph with only
~2000 edges over 65536 possible edge types) does not — any bigram
graph dense enough to be Eulerian-reconstructable admits many valid
paths, and real files never sit on the unique-path knife edge.

Verdict: **Negative outcome** per the plan's stopping criteria. No class
separates from random_control on any observable beyond 1σ; no class
yields class-specific stabilizer structure. The weak "structured
sub-cluster" at rank_frac ≈ 0.15 for code/binary/compressed at
clip=2048 is clip-specific and doesn't include text — not a generator
signal.

**Pivot:** drop the generator hunt. Next direction is characterising
the K-normalizer's coset structure in S_d directly — the
group-theoretic question of what permutations commute with K on a
fixed multiset. Finite, verifiable, and doesn't depend on finding a
small parametric family that covers arbitrary input.

Retracted: v1 writeup's "weakly positive on rank_fraction" conclusion.
v1 file stays on disk as a timestamped record (never promoted to
`verified_findings/`, so no retraction ladder).

Runner: `scripts/class_stabilizer_probe_v2.py` (v2.0)
Manifest: `analysis/encoding/class_stabilizers/corpus_manifest_v2.csv`
Results: `analysis/encoding/class_stabilizers/results_2026-04-19_v2.json`
Summary: `analysis/encoding/class_stabilizers/results_2026-04-19_v2.summary.json`
d-sweep: `analysis/encoding/class_stabilizers/results_2026-04-19_v2_dsweep.json`
Writeup: `analysis/encoding/class_stabilizers/class_stabilizer_probe_v2_2026-04-19.md`

---

## 2026-04-19 (late) — thermodynamic triangular lattice is generative for the purely paired class

Ran the thermodynamic generator probe against the canonical base-10
dataset (`data/base10/canonical/kaprekar_d3-100_verified.csv`).

Tested the stronger claim:

> For even d, does every valid lattice point
> `c09 + c36 + 3k = d/2` with `c09 >= 1`, `c36 >= 0`, `k >= 1`
> generate a purely-paired thermodynamic fixed point, and does that
> generated set match the canonical `family=thermodynamic`, central-pair
> `08` subset exactly?

Construction used:

- digit frequencies `freq = [c09, k, k, c36, k, k, c36, k, k, c09]`
- materialise candidate by one Kaprekar step `n = desc(ms) - asc(ms)`

**Main result:** for every even dimension **d = 12, 14, ..., 100**,
the answer is **yes exactly**.

- every valid lattice point generates a fixed point
- every generated point is canonical
- every canonical purely-paired thermodynamic constant is reached
- counts match identically in four ways:
  lattice-point count = closed-form count = generated count = canonical count

Selected checkpoints:

| d | count |
|---|---:|
| 12 | 3 |
| 20 | 12 |
| 50 | 92 |
| 82 | 260 |
| 100 | 392 |

Closed-form count:

Let `d = 2m`, `m - 4 = 3q + r`, `r in {0,1,2}`. Then the purely-paired
thermodynamic count is

`N(d) = ((q + 1) * (3q + 2r + 2)) / 2`.

Checks:

- `N(20) = 12`
- `N(50) = 92`
- `N(100) = 392`

These exactly match the canonical data.

**Boundary exception at d=10:** the same lattice has two valid points.
One is the thermodynamic constant `9975084201`; the other is
`9753086421` (family `975`). So the triangular lattice alone does not
isolate the thermodynamic family at the smallest even boundary. Clean
statement:

> The 2D triangular lattice is an exact generator for the purely-paired
> thermodynamic family for every even `d >= 12`, with a single boundary
> collision at `d = 10`.

This upgrades the earlier frequency-space statement from
descriptive/post-hoc to **constructive** for the purely-paired half of
the thermodynamic family. The remaining thermodynamic gap is now sharply
reduced:

- **Solved constructively:** purely-paired class (central pair `08`)
- **Still open:** unpaired-9 class (central pair `99`)

Also corrected a documentation bug in
`analysis/base10/frequency_space_structure.md`: the table under the
triangular-lattice section had been using total thermodynamic counts
(`13/132/912`) instead of purely-paired counts (`12/92/392`).

Runner: `scripts/kaprekar_thermo_lattice_probe.py`
Writeup: `analysis/base10/thermodynamic_lattice_generator_2026-04-19.md`
JSON note: `analysis/base10/thermodynamic_lattice_probe_2026-04-19.json.note.md`

---

## 2026-04-19 (late night) — unpaired-9 class is a shifted-lattice bulk plus tiny residue

Ran the next thermodynamic probe: does one extra coordinate `e` extend the
paired lattice to generate the even-d thermodynamic constants with central
pair `99`?

Tested frequency model:

`freq = [c09, k, k, c36, k, k, c36, k, k, c09 + e]`

with `e` even and positive.

Two results:

### 1. One-`e` frequency fit is almost exact

Out of **5928** canonical unpaired-9 thermodynamic constants:

- **5927** fit the one-`e`, one-`k` model exactly
- **1** does not:
  - `d=32`: `88776654443221999977765554332212`
  - frequency vector `[0,2,5,3,4,4,3,5,2,4]`

So a single excess-9 coordinate is the right structural variable at the
frequency level for **99.98%** of the class.

### 2. The bulk is constructive and exact on its domain

Adding the bulk inequalities

- `c09 >= 1`
- `c36 >= e`
- `k >= e + 1`
- `c09 + c36 + 3k + e/2 = d/2`

gives a genuine generator:

- **5910** canonical unpaired-9 constants generated exactly
- **0** spurious fixed points
- coverage = **5910 / 5928 = 99.70%**

This is not just a fit. Every bulk lattice point materialises to a true
Kaprekar fixed point, and every bulk constant is reached.

Key structural identity:

> For fixed excess `e`, the bulk slice count satisfies  
> `N_unpaired_bulk(d, e) = N_paired(d - 9e)`.

So the main unpaired-9 class is a **stack of shifted paired lattices** indexed
by `e`.

Examples:

- `d=50`: `e=2 -> 35`, `e=4 -> 5` = paired counts at `d=32` and `d=14`
- `d=100`: `e=2 -> 260`, `e=4 -> 155`, `e=6 -> 77`, `e=8 -> 26`
  = paired counts at `d=82,64,46,28`

### Residue

The full unpaired-9 class is not yet a single perfect 4-parameter lattice.
The residue is only **18** constants total:

- **17** boundary points with `c09 = 0` that still fit the one-`e` model
  but sit outside the bulk inequalities
- **1** orphan-like non-fit point at `d=32`

Boundary residue dimensions:

- `e=2`: `d=18,20,22,24,26,34`
- `e=4`: `d=36,38,40,46,52`
- `e=6`: `d=54,56`
- `e=8`: `d=72,74`
- `e=10`: `d=90,92`

Dimensions where the shifted-lattice bulk matches the full canonical `99`
class exactly:

`28, 30, 42, 44, 48, 50, 58, 60, 62, 64, 66, 68, 70, 76, 78, 80, 82, 84, 86, 88, 94, 96, 98, 100`

Interpretation:

- **Solved:** purely-paired thermodynamic class
- **Solved for 99.7% of cases:** unpaired-9 bulk via shifted lattices
- **Still open:** tiny `c09=0` boundary residue + the lone `d=32` outlier

This materially shrinks the remaining “thermodynamic generator” gap.

Runner: `scripts/kaprekar_thermo_unpaired_probe.py`
Writeup: `analysis/base10/thermodynamic_unpaired_probe_2026-04-19.md`
JSON: `/tmp/thermo_unpaired_probe_2026-04-19.json`

---

## 2026-04-19 (boundary follow-up) — c09=0 residue is an exact boundary-line family

Followed up the tiny unpaired-9 residue:

- `17` sparse `c09=0` boundary points inside the thermodynamic `99` class
- `1` orphan-like point at `d=32`

**Main structural result:** the `c09=0` points are not isolated leftovers. They sit on an exact fixed-point family

`L_e(c): freq = [0, e, e, c, e, e, c, e, e, e]`

with

`d = 7e + 2c`, `c >= e`.

For every tested `e <= 10` and every admissible `d <= 100`, these line
points are genuine fixed points.

This unifies several previously separate-looking phenomena:

- `e = 1`: the full `864` line
- `e = 2`: the low-d even thermodynamic boundary residue, then its continuation
  through `extension_recovered`
- `e = 4,6,8,10`: the higher even boundary branches visible inside the
  thermodynamic `99` class

So the correct reading is:

> the `c09=0` thermodynamic residue is only the low-dimensional slice of a
> much larger exact boundary-line family.

### Dataset / label consequence

Canonical labels are not structural here. Members of `L_e` appear variously as:

- `864`
- `thermodynamic`
- `extension_recovered`
- `exhaustive`
- or are currently **missing** from `kaprekar_d3-100_verified.csv`

Examples of valid fixed points on `L_e` that are missing from the canonical file:

- `d=42, e=4`: `888866664444333222199997777666555533331112`
- `d=44, e=4`: `88886666444433332221999977776666555533331112`
- `d=58, e=6`: `8888886666664444443322222199999977777766555555333333111112`
- `d=76, e=8`: `8888888866666666444444443322222221999999997777777766555555553333333311111112`
- `d=94, e=10`: `8888888888666666666644444444443322222222219999999999777777777766666555555555533333333331111111112`

All verified directly by both multiset and integer checks `K(n)=n`.

### Relation to the d=32 orphan-like point

The orphan-like point

`88776654443221999977765554332212`

does **not** fit `L_e`: it breaks the equal-inner-count law.

So:

- `c09=0` residue = exact boundary-line family `L_e`
- `d=32` orphan-like point = separate phenomenon (consistent with the earlier
  +9/orphan-chain story)

### Implication for the later d=all confirmation

Before any full `d=all` confirmation pass, the structural inventory now has to
include:

1. paired thermodynamic lattice
2. shifted unpaired-9 bulk lattice
3. exact `c09=0` boundary lines `L_e`

Only then does it make sense to ask what residue genuinely remains.

Runner: `scripts/kaprekar_boundary_line_probe.py`
Writeup: `analysis/base10/boundary_line_classification_2026-04-19.md`
JSON: `/tmp/kaprekar_boundary_line_probe_2026-04-19.json`

---

## 2026-04-19 (dead-zone proof) — direct algebraic proof that d=5 and d=7 have no fixed points

Closed the old dead-zone gap with a direct parameter-state proof, independent
of the insertion grammar.

### d=5

Let sorted digits be `a >= b >= c >= d >= e` and define

- `A = a - e`
- `B = b - d`

Then

`K(n) = 9999A + 990B = A*10^4 + B*10^3 - 10B - A`

so the decimal digits of `K(n)` depend only on `(A,B)`:

- if `B=0`: `[A-1, 9, 9, 9, 10-A]`
- if `B>0`: `[A, B-1, 9, 9-B, 10-A]`

This induces a deterministic map `F5(A,B)` on the finite state space

- `1 <= A <= 9`
- `0 <= B <= A`

which has **54** states total.

Exhaustive decomposition of `F5`:

- fixed states: **0**
- cycles: lengths **[4, 4, 2]**

The three known d=5 Kaprekar cycles are exactly those parameter cycles:

- `53955 <-> 59994`
- `74943 -> 62964 -> 71973 -> 83952 -> back`
- `63954 -> 61974 -> 82962 -> 75933 -> back`

So `d=5` has cycles but no fixed points.

### d=7

Let sorted digits be `a >= b >= c >= d >= e >= f >= g` and define

- `A = a - g`
- `B = b - f`
- `C = c - e`

Then

`K(n) = 999999A + 99990B + 9900C`

and its digits depend only on `(A,B,C)`:

- if `C>0`: `[A, B, C-1, 9, 9-C, 9-B, 10-A]`
- if `C=0, B>0`: `[A, B-1, 9, 9, 9, 9-B, 10-A]`
- if `B=C=0`: `[A-1, 9, 9, 9, 9, 9, 10-A]`

This induces a deterministic map `F7(A,B,C)` on the finite state space

- `1 <= A <= 9`
- `0 <= B <= A`
- `0 <= C <= B`

which has **219** states total.

Exhaustive decomposition of `F7`:

- fixed states: **0**
- cycles: one cycle of length **8**

Actual 7-digit cycle:

`8429652 -> 7619733 -> 8439552 -> 7509843 -> 9529641 -> 8719722 -> 8649432 -> 7519743 -> back`

So `d=7` also has cycles but no fixed points.

### Why this is a proof

Every fixed point would have to be a fixed state of the induced parameter map.
Since the finite maps `F5` and `F7` have no fixed states, `K(n)=n` has no
solutions in dimensions 5 or 7.

This gives a direct algebraic dead-zone proof:

- no reliance on extension chains
- no whole-space brute-force over all 5-digit or 7-digit numbers
- bounded stopping condition achieved

This closes gap 5 more cleanly:

- grammar story explains why `d=5,7` are unreachable
- parameter proof shows directly that `d=5,7` admit no fixed points at all

Runner: `scripts/kaprekar_dead_zone_parameter_proof.py`
Writeup: `analysis/base10/dead_zone_parameter_proof_2026-04-19.md`
JSON: `/tmp/kaprekar_dead_zone_parameter_proof_2026-04-19.json`

---

## 2026-04-19 (structural inventory) — d<=100 collapses to one boundary residue

Built the first single structural inventory runner for base-10 nontrivial fixed
points over the trusted finite window `d <= 100`.

Runner:

- reads the canonical file
- augments it with the exact/proved family generators from this session
- assigns each point to the first matching bucket in fixed priority order
- reports the remaining residue by dimension

Buckets:

- `495`
- `6174`
- `864`
- paired thermodynamic lattice
- shifted unpaired-9 bulk
- boundary lines `L_e`
- orphan / `+9` chain
- residue

### First inventory pass

Before updating the orphan seed list, the runner left exactly two canonical
residue points:

- `9975084201` at `d=10`
- `8777765544433221999997776655544322222` at `d=37`

The `d=10` point matched the earlier paired-lattice boundary-collision story.
The `d=37` point was the interesting one.

### New result: thermodynamic orphan seed at d=37

Direct testing showed the `d=37` point is not isolated. It seeds an exact `+9`
chain:

- `d=37`: `8777765544433221999997776655544322222`
- `d=46`: `8877776655444433222199999977776655554433222212`
- `d=55`: `8887777666554444433222219999999777776655555443332222112`
- `d=64`: `8888777766665544444433222221999999997777776655555544333322221112`
- ...
- `d=100`: still fixed

So the inventory runner was updated to include this new seed in the orphan
`+9` family.

This matters because older notes already warned that orphan verification had not
been performed above `d=32`; the new `d=37` seed confirms that warning was
substantive.

### Final inventory result

After adding the new `d=37` orphan seed and promoting `9975084201` to an
explicit low-`d` boundary clause:

- assigned family counts:
  - `495`: `33`
  - `6174`: `49`
  - `864`: `46`
  - paired lattice: `11250`
  - shifted unpaired bulk: `9555`
  - boundary line: `215`
  - orphan / `+9` chain: `19`
  - low-`d` boundary: `1`
- canonical residue by dimension:
  - none

So over `d <= 100`, the structural inventory now covers **every canonical
fixed point**.

### Interpretation of the low-d boundary clause

The only point needing an explicit boundary clause is:

- `9975084201` at `d=10`

This is not a diffuse unresolved family. It is the already-known small-`d`
boundary collision:

- current verified CSV labels it `thermodynamic`
- older canonical files labeled it `975`
- its frequency vector lies on the paired-lattice coordinate constraint
- the exact paired-lattice theorem itself begins only at even `d >= 12`

So the residue is now empty; the theorem just needs one explicit low-`d`
boundary clause.

### Canonical omissions surfaced by the inventory

The inventory also identified exact-family points missing from the current
canonical CSV:

- boundary lines `L_e`: `99` generated-only points
- orphan / `+9` chains: `14` generated-only points

The orphan-chain omissions include both:

- the already-known chain descendants at `d=41,50,59,68,77,86,95`
- the new `d=37` thermodynamic chain descendants at `d=46,55,64,73,82,91,100`

### Why this changes the d-all program

This is the first near-complete partition over a large trusted window.

The finite-window theorem shape is now:

> every nontrivial base-10 fixed point with `d <= 100` belongs to the explicit
> structural inventory, with `9975084201` handled by an explicit `d=10`
> boundary clause.

That turns the next stage from a family hunt into a theorem-writing problem:

- formalize `9975084201` as a permanent explicit low-`d` boundary clause
- formalize the new `d=37` orphan seed as part of the orphan inventory
- then return to the base-10 `d=all` confirmation with a nearly closed finite
  model

Runner: `scripts/kaprekar_structural_inventory.py`
Writeup: `analysis/base10/structural_inventory/structural_inventory_2026-04-19.md`
JSON: `/tmp/kaprekar_structural_inventory_2026-04-19.summary.json`
CSV: `/tmp/kaprekar_structural_inventory_2026-04-19.rows.csv`

### Provisional theorem note

Based on the inventory result, wrote a theorem-shaped synthesis note:

- `analysis/base10/provisional_base10_d_all_theorem_2026-04-19.md`

Current base-10 picture:

- exact classical families
- exact paired thermodynamic lattice
- exact shifted unpaired bulk on its domain
- exact boundary lines `L_e`
- explicit orphan / `+9` seed chains
- explicit low-`d` boundary clause `9975084201`

What remains open is no longer "what large family are we missing?" but:

- is the orphan seed inventory complete for `d=all`,
- or is there a higher-level generator for orphan seeds?

---

## 2026-04-20 (orphan source lines) — d=37 explained by a new +14 source line

Tried to answer the next theorem-facing question directly:

> why do the orphan seeds exist at all?

The answer is no longer "unknown seed list." A cleaner mechanism emerged.

### New source lines

Two exact fixed-point source lines were identified:

1. **975-source line** (native period `+6`)

   Frequency vector

   `E_k = [1,k,k,0,k,k,0,k,k,1]`, `d = 6k + 2`, `k >= 1`

   First members:

   - `d=8`: `97508421`
   - `d=14`: `97755108844221`
   - `d=20`: `97775551108884442221`
   - `d=26`: `97777555511108888444422221`

   Consecutive members differ by the size-6 growth multiset

   `G6 = {1,2,4,5,7,8}`.

2. **864-source line** (native period `+14`)

   Frequency vector

   `O_t = [0,1,3t+1,t+1,2t+1,2t+1,t+1,3t+1,1,2t+1]`, `d = 14t + 9`, `t >= 0`

   First members:

   - `d=9`: `864197532`
   - `d=23`: `87765443219997765543222`
   - `d=37`: `8777765544433221999997776655544322222`
   - `d=51`: `877777765554444333222199999997777666555544432222222`

   Consecutive members differ by the size-14 growth multiset

   `G14 = {2,2,2,3,4,4,5,5,6,7,7,7,9,9}`.

### Why this explains the d=37 orphan

The `d=37` thermodynamic orphan is exactly `O_2`, the third member of the
864-source line.

So the reason it looked like an orphan is simple:

- the older reverse-parent grammar only checked `+2`, `+3`, and `+9`
- the natural growth period of this line is `14`

So `d=37` was not a random anomaly; it was the first point where the missing
`+14` structure became visible beyond the old search window.

### Relation to earlier "orphans"

- `97508421` is `E_1`, the base of the `+6` source line
- `864197532` is `O_0`, the base of the `+14` source line
- the old `d=32` orphan-like point
  `88776654443221999977765554332212` is not a source at all; it is a `+9`
  descendant of `O_1` at `d=23`
- the new `d=37` point is the next source on the same `O_t` line

So the orphan picture is now:

1. true source lines with periods `6` and `14`
2. plus descendants under the already-known `+9` move

### Verification strength

Runner: `scripts/kaprekar_orphan_source_lines.py`
Writeup: `analysis/base10/orphan_source_lines_2026-04-20.md`
JSON: `/tmp/kaprekar_orphan_source_lines_2026-04-20.json`

Verified:

- `E_k` fixed and parentless under `+2/+3/+9` for `k=1..150`
  (`d=8..902`)
- `O_t` fixed and parentless under `+2/+3/+9` for `t=0..80`
  (`d=9..1129`)

### Consequence

This does not yet prove the full orphan inventory is complete for `d=all`, but
it gives the first real explanation of *why* orphan seeds appear:

- the working grammar was missing native growth moves
- at least two such moves now exist explicitly: `+6` and `+14`

So the next proof-facing question is sharper again:

> Are `G6` and `G14` the missing generators that complete the base-10 grammar,
> or are there still more source-line periods waiting above them?

### Borrow-chain / restricted-pivot note

Wrote a short structural note to restore the subtraction mechanism that had
started to disappear from the writeups:

- `analysis/base10/borrow_chain_pivot_note_2026-04-20.md`

Core viewpoint:

- fixed points are self-reproducing inward borrow chains in `desc(n) - asc(n)`
- the centre is a restricted pivot where the borrow chain must close in one of a
  very small number of ways
- the current family evidence suggests the admissible pivot closures are
  basically `9` (odd), `08` (even paired), and `99` (even unpaired)

This gives a cleaner explanation of:

- why the source lines are real families rather than arbitrary vectors,
- why `9975084201` behaves like a low-dimensional boundary collision,
- and why cycles / dead zones should be understood as failed pivot closure.

---

## 2026-04-20 (borrow automaton theorem note) — closed form for all canonical fixed points

Promoted the borrow/pivot picture from intuition to an exact normal form.

### Closed-form statement

Let the descending sorted digits of `n` be

`a_1 >= ... >= a_d`

and define the gap profile

`g_i = a_i - a_{d+1-i}`, `1 <= i <= floor(d/2)`.

Let `r` be the number of trailing zeros in the gap profile and `m = h-r`.

Then the decimal digits of

`K(n) = desc(n) - asc(n)`

are determined purely by `(g,r)`:

- even `d=2h`:
  `g_1 ... g_{m-1} (g_m-1) 9^{2r} (9-g_m) ... (10-g_1)`
- odd `d=2h+1`:
  `g_1 ... g_{m-1} (g_m-1) 9^{2r+1} (9-g_m) ... (10-g_1)`

This is the borrow automaton in closed form.

### Verification

Runner: `scripts/kaprekar_borrow_automaton_probe.py`
Writeup: `analysis/base10/borrow_automaton_pivot_theorem_2026-04-20.md`
JSON: `/tmp/kaprekar_borrow_automaton_probe_2026-04-20.json`

Checked against all canonical base-10 fixed points in `d <= 100`:

- total checked: `21,055`
- failures: `0`

### Consequences

This explains the restricted pivots uniformly:

- odd pivot: central block `9^{2r+1}` (minimal case: single `9`)
- even paired pivot: `r=0`, especially `g_h=1` giving centre `08`
- even unpaired pivot: `r=1` giving centre `99`

It also makes the source lines much cleaner:

- `+6` source line = gap profile `(9, 7^k, 5^k, 1^k)`
- `+14` source line = gap profile
  `(8, 7^{2t}, 6, 5^t, 4^{t+1}, 3^t, 2^{t+1}, 0^t)`

So the source-line families are not arbitrary frequency constructions; they are
simple gap-profile families under the borrow normal form.

### Why this matters

This is the missing mechanism the proof program needed:

- family descriptions now sit on top of a real subtraction law
- `9`, `08`, and `99` are no longer separate empirical centre rules
- the next proof step can now target shell-extension invariance in gap-profile
  language rather than raw digit counting

---

## 2026-04-20 (shell-extension invariance) — +6 and +14 are exact family-preserving moves

Used the borrow normal form to upgrade the source-line results from "verified
patterns" to exact shell-preservation laws.

### 975-source line

Digit family:

`E_k = [1,k,k,0,k,k,0,k,k,1]`

Gap family:

`(9, 7^k, 5^k, 1^k)`

Exact shell-preserving move:

- digit growth multiset: `{1,2,4,5,7,8}`
- induced gap growth word: `{7,5,1}`

Meaning:

- adding `{1,2,4,5,7,8}` to the digit multiset of `E_k` gives exactly `E_{k+1}`
- equivalently, the gap profile gains one new `7`, one new `5`, and one new `1`

### 864-source line

Digit family:

`O_t = [0,1,3t+1,t+1,2t+1,2t+1,t+1,3t+1,1,2t+1]`

Gap family:

`(8, 7^{2t}, 6, 5^t, 4^{t+1}, 3^t, 2^{t+1}, 0^t)`

Exact shell-preserving move:

- digit growth multiset: `{2,2,2,3,4,4,5,5,6,7,7,7,9,9}`
- induced gap growth word: `{7,7,5,4,3,2,0}`

Meaning:

- adding that size-14 multiset to the digit multiset of `O_t` gives exactly
  `O_{t+1}`
- equivalently, the gap profile gains two new `7`s and one each of
  `5,4,3,2,0`

### Verification

Runner: `scripts/kaprekar_shell_extension_invariance.py`
Writeup: `analysis/base10/shell_extension_invariance_2026-04-20.md`
JSON: `/tmp/kaprekar_shell_extension_invariance_2026-04-20.json`

Checked:

- 975 line for `k=1..150`
- 864 line for `t=0..80`

Failures:

- `0` for the `+6` line
- `0` for the `+14` line

### Consequence

This is the first exact shell-preservation result for the orphan/source families.

So the current situation is:

- borrow normal form explains how a gap profile reconstructs a fixed point
- shell-extension invariance explains how the `+6` and `+14` source families
  reproduce themselves

The next missing theorem step is now very sharp:

> Are there any further admissible shell-preserving growth moves beyond
> `+2,+3,+6,+9,+14` in base 10?

---

## 2026-04-20 (extended grammar source check) — no new move forced by d<=100

Checked the cleanest finite-window version of the question:

> under the extended reverse grammar using exactly
> `+2,+3,+6,+9,+14`, how many sources remain in the canonical fixed-point
> window?

Extended moves used:

- balanced `+2` pairs
- `+3 = {4,5,9}`
- `+6 = {1,2,4,5,7,8}`
- `+9 = {1,2,3,4,5,6,7,8,9}`
- `+14 = {2,2,2,3,4,4,5,5,6,7,7,7,9,9}`

Result on canonical `d <= 100`:

- total fixed points checked: `21,055`
- sources remaining: exactly `4`

The four primitive sources are:

- `495` at `d=3`
- `6174` at `d=4`
- `97508421` at `d=8`
- `864197532` at `d=9`

No other canonical fixed point in the trusted finite window is parentless under
the extended grammar.

### Interpretation

This is the strongest finite-window evidence yet that no further
shell-preserving move is being demanded by the base-10 fixed-point data up to
`d=100`.

This does **not** prove global completeness for `d=all`, but it does show:

- the newly added `+6` and `+14` moves remove the higher-dimensional source
  clutter completely in the trusted window
- the remaining source set is exactly the natural primitive base set one would
  expect

So the project has moved from

- "many unexplained orphan seeds"

to

- "four primitive sources, and no finite-window evidence for any further move"

Runner: `scripts/kaprekar_extended_grammar_source_check.py`
Writeup: `analysis/base10/extended_grammar_source_check_2026-04-20.md`
JSON: `/tmp/kaprekar_extended_grammar_source_check_2026-04-20.json`

## 2026-04-20 (no new native source period beyond +2,+3,+6,+9,+14)

Closed the remaining source-period question as far as the current project can
honestly take it.

1. Extended the reverse-parent check under the grammar
   `+2,+3,+6,+9,+14` from the canonical `d <= 100` window to the local
   `d <= 150` coverage (`kaprekar_d3-100_verified.csv` plus
   `kaprekar_d101-150.csv`). Result: still exactly 4 primitive fixed-point
   sources:
   - `495`
   - `6174`
   - `97508421`
   - `864197532`

2. Matched this constructive source picture to the repository's standing
   literature baseline from Iwasaki (2024): 5 mutually disjoint sets generated
   from 7 seeds `{495, 6174, 36, 123456789, 27, 124578, 09}`.

3. Clarified the role of the extra Iwasaki seeds:
   - `123456789` is the one-step preimage of the primitive fixed-point source
     `864197532`
   - `124578` is the structural generator whose digits are exactly the `+6`
     growth multiset `{1,2,4,5,7,8}`
   - `36`, `27`, and `09` are 2-digit cycle/generator seeds, not additional
     primitive fixed-point sources

4. Wrote the honest theorem-shaped conclusion:
   - unconditional local statement through `d <= 150`: no new native
     fixed-point source period appears beyond `+2,+3,+6,+9,+14`
   - conditional all-`d` statement: assuming Iwasaki's seven-seed / five-set
     classification, no further native fixed-point source period occurs in base
     10 for any `d`

Artifacts:
- note: `analysis/base10/no_new_native_source_period_2026-04-20.md`
- theorem synthesis patched: `analysis/base10/provisional_base10_d_all_theorem_2026-04-19.md`
- ad hoc d<=150 reverse-parent JSON: `/tmp/extended_source_check_d150.json`

## 2026-04-20 (Iwasaki seed compression)

Took the next step toward an internal `d=all` story by compressing the seven
Iwasaki seeds into the current borrow/shell grammar.

Main structural split:

1. **Primitive fixed-point sources**
   - `495`
   - `6174`
   - `97508421`
   - `864197532`

2. **Non-fixed shell generators**
   - `123456789` with `K(123456789) = 864197532`
   - `124578`, whose digit multiset is exactly the `+6` growth shell
     `{1,2,4,5,7,8}`

3. **Low-dimensional cycle representatives**
   - `36`, `27`, `09`, all lying on the same 2-digit Kaprekar cycle

Recorded the gap-profile view:

- `124578` has shell gaps `(7,5,1)` — the core shell word of the `+6` source
  line
- `123456789` has shell gaps `(8,6,4,2)` — the minimal odd-source gap word

So the external seven-seed classification is now much less opaque in the local
grammar: most of the seeds are either fixed-point primitives, shell generators,
or cycle representatives.

Artifact:
- note: `analysis/base10/iwasaki_seed_compression_2026-04-20.md`

## 2026-04-20 (two-digit gap cycle theorem)

Internalized the `09 / 27 / 36` part of the Iwasaki seed list.

For any 2-digit string with sorted gap `g = x-y` (`1 <= g <= 9`):

- `K = 9g = (g-1)(10-g)`
- the induced gap map is exactly `T(g) = |2g - 11|`

This gap map has a unique nonzero cycle:

- `1 -> 9 -> 7 -> 3 -> 5 -> 1`

and every even gap enters this cycle in one step:

- `2 -> 7`, `4 -> 3`, `6 -> 1`, `8 -> 5`

So `09`, `27`, and `36` are not three primitive generator types. They are
three representatives of one exact 2-digit cycle mechanism.

This materially narrows the generator side of the external seven-seed
classification:

- fixed-point primitives,
- shell generators,
- one exact 2-digit cycle.

Artifacts:
- script: `scripts/kaprekar_two_digit_gap_cycle.py`
- note: `analysis/base10/two_digit_gap_cycle_2026-04-20.md`

## 2026-04-20 (primitive gap-word scan)

Pushed the generator-side internalization further by scanning the full positive
no-zero gap-profile space under the borrow normal form.

Scan:

- all nonincreasing gap profiles `g`
- positive entries only (`r = 0`)
- `h <= 9`
- keep only profiles that are
  1. self-consistent fixed points under the borrow normal form, and
  2. primitive sources under the reverse grammar `+2,+3,+6,+9,+14`

Result: exactly four primitive source profiles survive:

- odd `(5)`          -> `495`
- even `(6,2)`       -> `6174`
- even `(9,7,5,1)`   -> `97508421`
- odd `(8,6,4,2)`    -> `864197532`

So after removing the classical pivots, the only nonclassical primitive source
profiles are:

- even paired source `(9,7,5,1)` with shell word `(7,5,1)` -> `124578`
- odd source `(8,6,4,2)` with shell word `(8,6,4,2)` -> `123456789`

This is the strongest internal evidence yet that the non-fixed shell generators
`124578` and `123456789` are forced by the borrow automaton rather than being
opaque imported seeds.

Artifacts:
- script: `scripts/kaprekar_primitive_gap_word_scan.py`
- note: `analysis/base10/primitive_gap_words_2026-04-20.md`

## 2026-04-20 (positive gap-profile reduction)

Converted the primitive-gap scan into a near-symbolic reduction.

Every checked positive no-zero self-consistent gap profile falls into one of
five explicit families:

1. `495` atom: `(5)`
2. `6174` chain: `(6, 3^m, 2)`
3. `864` chain: `(8, 6, 4, 3^m, 2)`
4. even paired family: `(9^a, 7^k, 5^k, 3^d, 1^k)`
5. odd `+9`-lifted paired family: `(9^a, 8, 7^k, 6, 5^k, 4, 3^d, 2, 1^k)`

and for every non-primitive member there is an explicit reverse parent rule:

- `6174` chain: `-+2_36`
- `864` chain: `-+2_36`
- even paired family:
  - `-+2_09` if `a > 1`
  - else `-+2_36` if `d > 0`
  - else `-+6_124578` if `k > 1`
- odd lifted family: always `-+9_123456789`

So the primitive positive no-zero profiles reduce to exactly four:

- `(5)`          -> `495`
- `(6,2)`        -> `6174`
- `(9,7,5,1)`    -> `97508421`
- `(8,6,4,2)`    -> `864197532`

This sharply isolates the remaining theorem gap: prove symbolically that every
positive no-zero self-consistent gap profile lies in one of those five
families.

Artifacts:
- script: `scripts/kaprekar_positive_gap_profile_classifier.py`
- note: `analysis/base10/positive_gap_profile_reduction_2026-04-20.md`

Follow-up stress test:

- extended the family classifier from `h <= 12` to `h <= 15`
- still `0` unmatched (`231/231` classified)

Support-level collapse through `h <= 15`:

- only 9 support sets appear:
  - `(5,)`
  - `(6,2)`, `(6,3,2)`
  - `(8,6,4,2)`, `(8,6,4,3,2)`
  - `(9,7,5,1)`, `(9,7,5,3,1)`
  - `(9,8,7,6,5,4,2,1)`, `(9,8,7,6,5,4,3,2,1)`

So the remaining symbolic task is now visibly finite:

1. prove only those support sets can occur;
2. prove the multiplicities on each support are forced into the 5 family forms.

## 2026-04-20 (extremal gap lemma skeleton)

Turned the positive no-zero classification into a concrete proof skeleton.

Current symbolic split:

1. **Tail-gap lemma**
   - prove `g_h in {1,2,5}` for every positive no-zero self-consistent gap
     profile

2. **Support restriction by tail**
   - `g_h = 5` -> only `{5}`
   - `g_h = 2` -> `{6,3,2}` or `{8,6,4,3,2}`
   - `g_h = 1` -> `{9,7,5,3,1}` or `{9,8,7,6,5,4,3,2,1}`

3. **Multiplicity forcing**
   - recover the five parametric family forms from those supports

This is the first point where the remaining `d=all` generator-side problem can
be stated as three explicit lemmas instead of an open-ended source-completeness
problem.

Artifact:
- note: `analysis/base10/extremal_gap_lemma_2026-04-20.md`

Follow-up stress test on the tail-gap claim:

- extended positive no-zero scan to `h <= 18`
- tails observed: exactly `{1,2,5}`
- counts:
  - tail `1`: `390`
  - tail `2`: `32`
  - tail `5`: `1`
- unmatched profiles: `0`

So the extremal split the proof needs is now strongly stable computationally.

## 2026-04-20 (tail-gap-5 lemma proved)

Closed the first symbolic branch of the extremal-gap program.

For a positive no-zero self-consistent gap profile `g`, if the tail gap

- `g_h = 5`,

then necessarily:

- `h = 1`,
- the parity is odd,
- and the resulting fixed point is `495`.

Proof split:

1. **Even case**
   - if `g_1 = 5`, then all gaps are `5` and the borrow word sorts to `5^h 4^h`,
     giving tail gap `1`, contradiction
   - if `g_1 > 5`, then the even borrow word has only `h-1` digits above `4`,
     so after sorting the middle shell is `4|4`, giving tail gap `0`,
     contradiction

2. **Odd case**
   - if `g_1 = 5`, the borrow word sorts to `9 5^h 4^h`, giving tail gap `1`,
     contradiction
   - if `g_1 > 5`, the top `h` digits must be `9, g_1, ..., g_{h-1}` and the
     next bottom digit is forced to be `4`, so tail gap `5` implies
     `g_1 = ... = g_{h-1} = 9`; but then the borrow word sorts to
     `9^h 4^2 1 0^{h-2}`, whose gap profile is `(9^{h-2},8,5)`, contradiction

Therefore the only admissible profile with tail `5` is the singleton `(5)`,
yielding `495`.

Artifacts:
- note: `analysis/base10/tail_gap_5_lemma_2026-04-20.md`
- extremal-gap skeleton updated: `analysis/base10/extremal_gap_lemma_2026-04-20.md`

## 2026-04-20 (tail-gap-2 even lemma proved)

Closed the even half of the tail-`2` branch symbolically.

Statement:

- if `g` is a positive no-zero self-consistent **even** gap profile and
  `g_h = 2`,
- then necessarily

  `g = (6, 3^{h-2}, 2)`.

Proof mechanism:

1. the even borrow word has average digit `4.5`
2. tail gap `2` therefore forces the middle pair `6|4`
3. that excludes digit `5`, hence excludes gap values `4` and `5`
4. the only remaining source of digit `4` is `10-g_1`, so `g_1 = 6`
5. uniqueness of the outer `7-1` pair forces every remaining shell to be
   `6-3`, hence all middle gaps are `3`

So the even tail-`2` branch is exactly the `6174` chain:

- `(6,2)`
- `(6,3,2)`
- `(6,3,3,2)`
- ...

Stress confirmation:

- through `h <= 18`, every even positive no-zero self-consistent tail-`2`
  profile is exactly one of these chain members
- no deviations observed

Artifacts:
- note: `analysis/base10/tail_gap_2_even_lemma_2026-04-20.md`
- extremal-gap note updated:
  `analysis/base10/extremal_gap_lemma_2026-04-20.md`

This leaves only:

- the odd tail-`2` branch (`864` chain)
- and the tail-`1` branch (paired / lifted paired)

on the generator-side symbolic program.

## 2026-04-20 (odd tail-gap-2 branch reduced to one sublemma)

Pushed the odd `g_h = 2` branch into a much tighter form.

New reduction note:

- `analysis/base10/tail_gap_2_odd_reduction_2026-04-20.md`

What is now proved symbolically for a positive no-zero odd self-consistent
profile with `g_h = 2`:

1. **No leading `9`**
   - any leading `9`-block collapses after sorting to a profile beginning
     `8` or `9^{a-1},8`, never `9^a`

2. **Unique leading `8`**
   - a second `8` forces prefix `(8,7,...)`

3. **No `7`-gap**
   - any `7`-block after the leading `8` forces prefix `(8,6,5,...)`

4. **Forced second gap**
   - therefore `g_2 = 6`

5. **Conditional closure**
   - if the value `2` occurs only at the tail, then the whole profile is
     forced to be

     `(8, 6, 4, 3^m, 2)`

     i.e. the `864` chain

Also recorded the exact obstruction patterns:

- extra `8` -> `(8,7,...)`
- any `7`-gap -> `(8,6,5,...)`
- any interior `2` -> `(8,6,5,...)`
- repeated `4` or explicit `5` -> tail `1`

So the odd tail-`2` branch is no longer a large open branch. The only remaining
symbolic obstacle there is:

- prove that no interior `2` can occur.

That is now the single sublemma standing between the odd tail-`2` branch and a
full symbolic `864`-chain theorem.

## 2026-04-20 (tail-gap-2 odd lemma proved)

Closed the odd half of the tail-`2` branch symbolically.

New theorem note:

- `analysis/base10/tail_gap_2_odd_lemma_2026-04-20.md`

Using the earlier odd reduction (`no leading 9`, `unique leading 8`, `no 7`,
forced `g_2 = 6`), every odd tail-`2` profile has block form

`g = (8, 6^a, 5^u, 4^v, 3^m, 2^t)`.

Then the odd borrow word gives exact digit counts:

- `1^1`
- `2^t`
- `3^{a+m}`
- `4^{u+v}`
- `5^{u+v}`
- `6^{a+m}`
- `7^t`
- `8^1`
- `9^1`

So after sorting, the induced gap profile is:

- if `u+v = 0`:
  - `(8, 6, 5^{t-1}, 4, 3^{a+m-1})`
- if `u+v >= 1`:
  - `(8, 6, 5^{t-1}, 4, 3^{a+m-1}, 2, 1^{u+v-1})`

Self-consistency plus positivity immediately force:

- `u+v = 1`
- `a = 1`
- `t = 1`
- `u = 0`, `v = 1`

hence:

`g = (8, 6, 4, 3^m, 2)`.

So the entire tail-`2` branch is now closed:

- even: `6174` chain
- odd: `864` chain

This leaves the generator-side symbolic program with only the tail-`1` branch
still open.

## 2026-04-20 (tail-gap-1 even lemma proved)

Closed the even half of the tail-`1` branch symbolically.

New theorem note:

- `analysis/base10/tail_gap_1_even_lemma_2026-04-20.md`

Split the proof into two cases.

1. **No leading `9`**

   For a general block form

   `g = (8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)`

   the exact induced gap map is:

   `(8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)
    -> (8, 7^{p+t-2}, 6, 5^{b+s}, 3^{q+d}, 1^{c+r})`

   Comparing the `6`- and `3`-blocks forces both `q=1` and `q=0`, so this case
   is impossible.

2. **Leading `9`**

   For a general block form

   `g = (9^a, 8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)`

   the exact induced gap map is:

   `(9^a, 8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)
    -> (9^a, 7^{p+t}, 5^{b+s}, 3^{q+d}, 1^{c+r})`

   Self-consistency forces:

   - `p=q=r=s=0`
   - `b=c=t`

   hence:

   `g = (9^a, 7^k, 5^k, 3^d, 1^k)`.

So the even tail-`1` branch is exactly the paired family.

## 2026-04-20 (tail-gap-1 odd lemma proved)

Closed the odd half of the tail-`1` branch symbolically.

New theorem note:

- `analysis/base10/tail_gap_1_odd_lemma_2026-04-20.md`

Because the odd borrow word always contains both `9` and `0`, every odd
tail-`1` profile must begin with a `9`.

For a general block form

`g = (9^a, 8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)`

the exact induced gap map is:

`(9^a, 8^p, 7^b, 6^q, 5^c, 4^r, 3^d, 2^s, 1^t)
 -> (9^a, 8, 7^{p+t-1}, 6, 5^{b+s-1}, 4, 3^{q+d-1}, 2, 1^{c+r-1})`

Self-consistency forces:

- `p=q=r=s=1`
- `b=c=t`

hence:

`g = (9^a, 8, 7^k, 6, 5^k, 4, 3^d, 2, 1^k)`.

So the odd tail-`1` branch is exactly the `+9`-lifted paired family.

Net consequence:

- `g_h = 5` branch closed
- `g_h = 2` branch closed
- `g_h = 1` branch closed

So the positive no-zero side of the generator theorem is now branch-complete.

## 2026-04-20 (positive no-zero gap theorem stitched)

Stitched the branch lemmas into one unified classification theorem.

New top-level note:

- `analysis/base10/positive_no_zero_gap_theorem_2026-04-20.md`

The theorem says:

If `g` is a positive nonincreasing gap profile with `r=0` whose borrow normal
form is self-consistent, then `g` belongs to exactly one of:

1. `(5)`
2. `(6, 3^m, 2)`
3. `(8, 6, 4, 3^m, 2)`
4. `(9^a, 7^k, 5^k, 3^d, 1^k)`
5. `(9^a, 8, 7^k, 6, 5^k, 4, 3^d, 2, 1^k)`

and these five families are exactly the:

- `495` atom
- `6174` chain
- `864` chain
- even paired family
- odd `+9`-lifted paired family

The note also packages the immediate primitive-source corollary:

- `(5)`          -> `495`
- `(6,2)`        -> `6174`
- `(8,6,4,2)`    -> `864197532`
- `(9,7,5,1)`    -> `97508421`

So the positive no-zero side of the generator theorem is no longer a collection
of branch notes. It is now one stitched theorem with one stitched corollary.

## 2026-04-20 (positive no-zero theorem bridged to the global fixed-point grammar)

Wrote the bridge note:

- `analysis/base10/positive_no_zero_global_grammar_bridge_2026-04-20.md`

This ties together three strands that had been proved separately:

1. the positive no-zero gap theorem
2. the primitive shell-word identification
3. the extended global fixed-point grammar

The bridge statement is:

- the positive no-zero theorem leaves exactly four primitive fixed-point
  sources:
  `495`, `6174`, `97508421`, `864197532`
- the two nonclassical primitive profiles force exactly two nonclassical shell
  words:
  `(7,5,1)` -> `124578`
  and `(8,6,4,2)` -> `123456789`
- hence the finite-window base-10 source grammar closes under
  `+2,+3,+6,+9,+14` with those four primitive fixed-point sources and no extra
  native source period forced by the checked data

This is the first note where:

- the borrow-profile classification,
- the shell words,
- and the global source grammar

are stated as one mechanism rather than as parallel results.

I also patched `analysis/base10/provisional_base10_d_all_theorem_2026-04-19.md`
to add a short update section pointing to this bridge.

## 2026-04-20 (internal base-10 d=all promotion pass)

Implemented the internal-promotion pass from the positive no-zero theorem stack
to the full borrow/shell grammar.

New runners:

- `scripts/kaprekar_zero_plateau_source_check.py`
- `scripts/kaprekar_internal_grammar_inventory.py`

New notes:

- `analysis/base10/zero_plateau_lifting_2026-04-20.md`
- `analysis/base10/internal_grammar_inventory_2026-04-20.md`
- `analysis/base10/internal_base10_d_all_theorem_2026-04-20.md`

Main results:

1. Zero-plateau check through `d<=150`:
   - checked fixed points: `26,664`
   - source counts by plateau length: `{0: 4}`
   - so every primitive source still has `r=0`
   - terminal zero plateaus create no new primitive sources in the local window

2. Internal grammar inventory through `d<=150`:
   - buckets:
     `495`, `6174`, `864`, `even_paired`, `odd_lifted`, `source_line`
   - residue is empty in every dimension
   - `9975084201` is absorbed directly into `even_paired`

3. Acceptance rechecks:
   - positive gap-profile classifier through `h<=15`: `231/231` classified,
     unmatched `0`
   - primitive shell-word scan through `h<=10`: still exactly four primitive
     source profiles, with nonclassical shell words exactly
     `124578` and `123456789`

Interpretation:

- the positive no-zero theorem now really does feed the full internal grammar
- the old low-`d` boundary clause is no longer needed on the main path
- the theorem story no longer has to pass through Iwasaki’s seven seeds as the
  primary explanation

The remaining gap is now sharply phrased as:

- promote the locally saturated internal grammar from `d<=150` to a genuine
  all-`d` theorem

rather than:

- discover another family or another seed type

## 2026-04-21 (internal grammar multiset sweep through d<=1000)

Pushed the internal grammar beyond the `d<=150` theorem window by streaming the
available multiset dataset through `d<=1000`.

New runner:

- `scripts/kaprekar_internal_grammar_multiset_sweep.py`

New note:

- `analysis/base10/internal_grammar_multiset_sweep_2026-04-21.md`

Main result:

- rows scanned: `9,910,464`
- exact internal buckets used:
  `495`, `6174`, `864`, `even_paired`, `odd_lifted`, `source_line`
- residue: empty in every dimension through `d<=1000`
- source dimensions remain exactly:
  - `d=3`
  - `d=4`
  - `d=8`
  - `d=9`

Assigned counts:

- `495`: `50`
- `6174`: `499`
- `864`: `496`
- `source_line`: `4`
- `even_paired`: `1,791,827`
- `odd_lifted`: `8,117,588`

Interpretation:

- no new family type is forced anywhere in the currently available `d<=1000`
  data
- no new source dimension appears anywhere in that window
- the remaining gap is now genuinely the all-`d` promotion step, not local
  family discovery

## 2026-04-21 (zero-tail gap reduction)

Wrote `analysis/base10/zero_tail_gap_reduction_2026-04-21.md` and added
`scripts/kaprekar_zero_tail_gap_scan.py` to isolate the last symbolic branch
after the positive no-zero theorem and the `d<=1000` multiset sweep.

Main result:

- exhaustive zero-tail gap-profile scan through `h<=14` found only `20`
  self-consistent fixed-point profiles with a terminal zero
- the zero-tail branch is not an open cloud; it is a tiny ladder zoo
- the `495` zero-tail ladder is explicit:
  - even: `(5^{2r},0^r)`
  - odd: `(5^{2r+1},0^r)`
- the exact `+14` source-line core is already on the theorem side
- the residual zero-tail profiles look like a very small set of `+9` lifts of
  that `+14` core inside the odd-lifted family

Interpretation:

- the honest remaining symbolic target is now a zero-tail lift lemma
- the all-`d` promotion problem is no longer broad at all; it has been reduced
  to controlling the `r>0` branch over the already-understood `+14` core

## 2026-04-21 (P / E / O lift-family normal form)

Wrote `analysis/base10/peo_lift_families_2026-04-21.md` and added
`scripts/kaprekar_peo_lift_families.py`.

Main result:

- the internal grammar compresses naturally to three parametric count families:
  - `P` = `495` ladder
  - `E` = paired / odd-lift branch with `c0 >= 1`
  - `O` = `864 / +14` branch with `c0 = 0`
- verified on parameter grids:
  - `P`: `19` points
  - `E`: `980`
  - `O_core`: `49`
  - `O_boundary`: `49`
  - failures: `0`
- mixed `O` interior (`t>=1`, `s>=1`) checked on `252` grid points:
  - fixed-point exceptions: `0`
- all `20` zero-tail scan profiles fit exactly one of `P/E/O`:
  - `P`: `8`
  - `E`: `3`
  - `O`: `9`
  - fit failures: `0`

Interpretation:

- the remaining symbolic gap is now even tighter than the earlier zero-tail
  reduction suggested
- the endgame is best phrased as:
  - prove completeness of `P/E/O`
  - prove the mixed `O` interior is impossible

## 2026-04-21 (corrected `P / C / E / O` completion through d<=1000)

Wrote `analysis/base10/pceo_completion_2026-04-21.md` and added
`scripts/kaprekar_pceo_completion_check.py`.

Main correction:

- the earlier `P/E/O` normal form was structurally close but omitted the
  classical `6174` chain
- the apparent `P/E/O` residue on the full corpus was exactly:
  - the `495` atom boundary, and
  - one `6174`-chain point in every even dimension

Corrected normal form:

- `P` = `495` ladder
- `C` = `6174` chain
- `E` = paired / odd-lift branch
- `O_core` = `864 / +14` core face
- `O_boundary` = `c0=0` boundary face

Completion sweep through the full available corpus `d<=1000`:

- rows scanned: `9,910,464`
- `P`: `50`
- `C`: `499`
- `E`: `9,905,475`
- `O_core`: `13`
- `O_boundary`: `4,427`
- residue: `0`

Mixed `O` interior scan:

- checked all `O(t,q,s)` with `t>=1`, `s>=1`, `d<=1000`
- parameter points checked: `637,796`
- fixed-point exceptions: `0`

Interpretation:

- the remaining all-`d` target is now the corrected one:
  - prove completeness of `P/C/E/O`
  - prove the mixed `O` interior is impossible

## 2026-04-21 (exact mixed-`O` update law and family equivalence)

Wrote:

- `analysis/base10/mixed_o_update_law_2026-04-21.md`
- `analysis/base10/pceo_family_equivalence_2026-04-21.md`

and added:

- `scripts/kaprekar_mixed_o_update_law.py`

Main result:

- for the mixed interior
  `O(t,q,s)` with `t>=1`, `s>=1`,
  the exact observed one-step law is

  `K(O(t,q,s)) = R(t,q,s)`

  with

  `R(t,q,s) = [0,1+q,3t+m+1+q,|t-s|+1+q,2t+m+1+q,2t+m+1+q,|t-s|+1+q,3t+m+1+q,1+q,2t+1+q]`

  where `m=min(t,s)`

- checked on all mixed parameter points with `d<=1000`:
  - checked: `637,796`
  - mismatches: `0`

Immediate corollary:

- mixed `O` interior cannot be fixed, because the digit-`2/7` and `4/5`
  multiplicities jump by `m>0`

Also clarified:

- `P/C/E/O` is not a new grammar
- it is a reparameterization of the existing internal grammar buckets:
  - `P` = `495`
  - `C` = `6174`
  - `E` = `c0>=1` paired / odd-lift branch
  - `O_core` = `864 / +14` core face
  - `O_boundary` = `c0=0` boundary face

Interpretation:

- the remaining endgame is now stated as tightly as it has been all session:
  - prove completeness of `P/C/E/O`
  - prove the mixed-`O` update law symbolically

## 2026-04-21 (symbolic mixed-`O` law and sharpened completeness theorem)

Wrote:

- `analysis/base10/mixed_o_symbolic_update_law_2026-04-21.md`
- `analysis/base10/pceo_completeness_theorem_2026-04-21.md`

and added:

- `scripts/kaprekar_mixed_o_gap_profile.py`

Main symbolic result:

- for
  `O(t,q,s) = [0,1+q,3t+1+q,t+1+q+s,2t+1+q,2t+1+q,t+1+q+s,3t+1+q,1+q,2t+1+q]`
  with `t>=1`, `s>=1`,
  the exact sorted gap profile is

  `g_O(t,q,s) = (8^(q+1),7^(2t),6^(q+1),5^t,4^(t+q+1+m),3^|t-s|,2^(t+q+1+m),0^(t+ceil(q/2)))`

  where `m=min(t,s)`

- applying the borrow normal form to that gap profile yields exactly

  `K(O(t,q,s)) = R(t,q,s)`

  with the previously recorded count formula

This gives a symbolic proof that mixed `O` interior cannot be fixed:

- for `t,s>=1`, `m>0`
- so the `2/7` and `4/5` multiplicities increase
- therefore `R(t,q,s) != O(t,q,s)`

Validation:

- exact mixed-gap formula checked on all `O(t,q,s)` with `d<=1000`
  - parameter points: `669,288`
  - mismatches: `0`
- exact mixed-update law checked on all mixed `O(t,q,s)` with `t>=1`, `s>=1`,
  `d<=1000`
  - parameter points: `637,796`
  - mismatches: `0`

Also recorded the sharpened completeness theorem:

- every base-10 fixed point lies in exactly one of
  - `P`
  - `C`
  - `E`
  - `O_core`
  - `O_boundary`

where:

- `P` = `495` ladder
- `C` = `6174` chain
- `E` = the `c0>=1` paired / odd-lift branch, including `975` descendants
- `O_core` = the `864 / +14` core face
- `O_boundary` = the `c0=0` boundary face

Interpretation:

- the mixed-`O` branch is now symbolic, not just computational
- the internal grammar now has a theorem-facing sharpened normal form
- the honest remaining gap is the final all-`d` promotion, not any missing
  family inside the current grammar

## 2026-04-21 (explicit `P/C/E/O` reduction grammar)

Wrote:

- `analysis/base10/pceo_reduction_grammar_2026-04-21.md`

and added:

- `scripts/kaprekar_pceo_reduction_check.py`

Main result:

- the sharpened family system is now not only a completion partition but an
  explicit parent-reduction grammar

Parent rules:

- `P(m>1) -> P(m-1)` via `+3_459`
- `C(m>0) -> C(m-1)` via `+2_36`
- `E(z,k,q,d)` reduces by:
  - `+9` if `q>0`
  - else `+2_09` if `z>1`
  - else `+2_36` if `d>0`
  - else `+6` if `k>1`
  - else stops at primitive `97508421`
- `O_core(t,q)` reduces by:
  - `+9` if `q>0`
  - else `+14` if `t>0`
  - else stops at primitive `864197532`
- `O_boundary(q,s)` reduces by:
  - `+2_36` while `s>1`
  - then lands on the `864` ridge `O_core(0,q)` when `s=1`

Important theorem-hygiene correction:

- `O_core` and `O_boundary` are not disjoint
- they overlap exactly on the ridge

  `O_core(0,q) = O_boundary(q,0)`

So the right object is a reduction grammar with one explicit seam, not five
strictly disjoint buckets.

Validation through the full available corpus `d<=1000`:

- rows scanned: `9,910,464`
- family counts:
  - `P`: `50`
  - `C`: `499`
  - `E`: `9,905,475`
  - `O_core`: `13`
  - `O_boundary`: `4,427`
- reduction-check failures: `0`
- primitive terminals found: exactly
  - `495`
  - `6174`
  - `97508421`
  - `864197532`

Interpretation:

- every checked non-primitive fixed point now has an explicit one-step parent
  inside the internal grammar
- the honest remaining gap is the final symbolic promotion of this reduction
  grammar to all `d`

## 2026-04-23 (`O`-family symbolic reduction theorem)

Wrote:

- `analysis/base10/o_family_symbolic_reduction_2026-04-23.md`

and added:

- `scripts/kaprekar_o_family_symbolic_check.py`

Main result:

- the `c0=0` branch is now symbolically closed from the borrow automaton,
  not just computationally saturated

The theorem proves:

- `O_core(t,q)` is a fixed point for all `t,q`
- `O_boundary(q,s)` is a fixed point for all `q,s`
- `O_core(t,q)` reduces by:
  - `+9` if `q>0`
  - `+14` if `q=0, t>0`
- `O_boundary(q,s)` reduces by:
  - `+2_36` while `s>0`
  - then lands exactly on the ridge
    `O_boundary(q,0)=O_core(0,q)`

This gives a direct symbolic reduction of every `c0=0` fixed point to
`864197532`, once the mixed interior is excluded by the existing mixed-`O`
update law.

Validation box:

- `O_core(t,q)` with `0<=t<=80`, `0<=q<=40`
  - checked: `3,321`
- `O_boundary(q,s)` with `0<=q<=40`, `0<=s<=80`
  - checked: `3,321`
- total failures: `0`

Interpretation:

- the remaining gap is no longer inside the `O` family
- the honest remaining all-`d` target is now the global promotion statement:
  prove that every base-10 fixed point enters the `P/C/E/O` reduction grammar

## 2026-04-23 (late) — inner asymmetry is an outer-gap / tail-gap invariant

Wrote:

- `analysis/base10/inner_asymmetry_lemma_2026-04-23.md`

and added:

- `scripts/kaprekar_inner_asymmetry_check.py`

Main result:

- the inner asymmetry vector

  `(c1-c8, c2-c7, c3-c6, c4-c5)`

  is determined exactly by just the lead/tail pair `(g_1, g_m)` of the
  borrow-profile, independent of plateau length.

Exact specialization on the current grammar:

- `(5,5)` -> `(0,0,0,0)`  (`P`)
- `(6,2)` -> `(1,-1,-1,1)` (`C`)
- `(8,2)` -> `(0,0,0,0)`  (`O`)
- `(9,1)` -> `(0,0,0,0)`  (`E`)

So the `6174` chain is now isolated as the **unique inner-asymmetry branch**.
Everything else in the internal grammar is exactly inner-symmetric.

Local theorem-window validation through `d<=150`:

- checked fixed points: `26,664`
- observed lead/tail pairs:
  - `(5,5)`: `50`
  - `(6,2)`: `74`
  - `(8,2)`: `190`
  - `(9,1)`: `26,350`
- asymmetry mismatches against the exact formula: `0`

This sharpens the remaining global promotion step:

- it is no longer “prove completeness of `P/C/E/O`” in one undifferentiated
  pass
- it is now:
  1. prove all fixed points have lead/tail pair in
     `{(5,5),(6,2),(8,2),(9,1)}`
  2. prove the `(9,1)` branch is exactly `E`

The other three branches are already symbolically closed.

## 2026-04-23 (late night) — `(9,1)` branch reduced to one shell-inequality sublemma

Wrote:

- `analysis/base10/e_branch_shell_reduction_2026-04-23.md`

and added:

- `scripts/kaprekar_e_branch_shell_reduction.py`

Main reduction:

For a fixed point with lead/tail pair `(9,1)`, the inner-asymmetry lemma gives
the exact inner-symmetric count form

`[z, A, B, C, D, D, C, B, A, z+q]`.

The new shell-reduction note proves:

- if
  - `A >= q`
  - `B >= q`
  - `C >= q`
  - `D > q`
  then outer shell pairing already forces the exact `E`-support gap profile

  `g = (9^z, 8^q, 7^(A-q), 6^q, 5^(B-q), 4^q, 3^(C-q), 2^q, 1^(D-q), 0^u)`

- feeding that profile back through the borrow normal form forces
  `A = B = D`

- so the whole branch is exactly

  `E(z,k,q,d)` with `k=A-q`, `d=C-q`.

So the `(9,1)` branch is no longer a full classification problem. The
remaining sublemma is only:

> prove that every `(9,1)` fixed point satisfies the shell inequalities.

Local validation through `d<=150` on all `(9,1)` rows:

- checked: `26,350`
- shell-inequality failures: `0`
- induced-gap formula failures: `0`
- `E`-fit failures: `0`

This narrows the global promotion step again:

1. prove all fixed points have lead/tail pair in `{(5,5),(6,2),(8,2),(9,1)}`
2. prove the `(9,1)` shell inequalities

Once (2) is done, `(9,1) -> E` follows immediately.

## 2026-04-23 (late night) — full-corpus sweep closes the computational side of the endgame

Wrote:

- `analysis/base10/global_promotion_sweep_2026-04-23.md`

and added:

- `scripts/kaprekar_global_promotion_sweep.py`

Main result:

The two remaining endgame claims were checked on the **full available base-10
fixed-point corpus through `d<=1000`**:

- rows scanned: `9,910,464`

Lead/tail pair counts:

- `(5,5)`: `50`
- `(6,2)`: `499`
- `(8,2)`: `4,440`
- `(9,1)`: `9,905,475`

Everything else:

- bad pair count: `0`

So there is now **zero computational evidence** for any fifth lead/tail branch.

On the full `(9,1)` branch:

- rows checked: `9,905,475`
- shell-inequality failures: `0`
- `E`-fit failures: `0`

So there is also **zero computational evidence** for any non-`E` `(9,1)`
family.

This is the first point in the project where the remaining gap is honestly
purely symbolic:

1. prove the four lead/tail pairs
2. prove the `(9,1)` shell inequalities

The computational side of the endgame is now saturated.

## 2026-04-24 — symbolic closure of the four lead/tail pairs; first resource-count reduction on `(9,1)`

Wrote:

- `analysis/base10/lead_tail_pair_theorem_2026-04-24.md`
- `analysis/base10/resource_count_reduction_2026-04-24.md`

and patched:

- `analysis/base10/internal_base10_d_all_theorem_2026-04-20.md`

Main structural gain:

- the four lead/tail pairs are now proved symbolically, not just observed in
  the `d<=1000` sweep

Proof spine:

1. every fixed point has a positive nucleus
2. the positive no-zero theorem classifies those nuclei into five families
3. those families have lead/tail pairs only in
   `{(5,5),(6,2),(8,2),(9,1)}`
4. terminal zero plateaus insert only a central `9`-block and preserve the
   lead and last positive gap

So no fifth lead/tail branch can appear beyond the positive nucleus stage.

The `(9,1)` branch also moved forward symbolically:

- for inner-symmetric counts
  `[z, A, B, C, D, D, C, B, A, z+q]`,
  the first shell inequality is now proved:
  `A >= q`

Reason:

- if `A<q`, all copies of digit `1` are consumed by the excess `9`s,
- but the branch still has terminal gap `1`,
- so reconstruction forces `c1 >= A+1`, contradiction.

And the remaining shell inequalities are now reduced to explicit wrong-block
contradiction patterns:

- `B<q` under `A>=q, C>=q, D>q` forces reconstructed
  `c3' = B + C - q < C`
- `C<q` under `A>=q, B>=q, D>q` forces reconstructed
  `c3' = 2q - C > C`
- once `A,B,C` are in place, `D<=q` destroys the terminal `1` gap required by
  the `(9,1)` branch

So the global promotion step has now narrowed again:

- the lead/tail side is closed symbolically
- the only remaining symbolic debt is the ordered shell-inequality chain on
  the `(9,1)` branch

## 2026-04-24 (late) — `(9,1)` shell-inequality chain closed; fixed-point `d=all` promotion completed

Wrote:

- `analysis/base10/e_branch_resource_closure_2026-04-24.md`

and patched:

- `analysis/base10/internal_base10_d_all_theorem_2026-04-20.md`

Main result:

The remaining `(9,1)` shell-inequality chain is now closed symbolically.

Setup:

- on the `(9,1)` branch, inner symmetry gives counts
  `[z, A, B, C, D, D, C, B, A, z+q]`
- the earlier reduction had already proved `A >= q`

New symbolic closure:

1. `B >= q`
   - proved by a three-way case split:
     - `C >= q`
     - `C < q` with `B+C >= q`
     - `C < q` with `B+C < q`
   - each case gives an exact shell profile and a direct self-consistency
     contradiction

2. `C >= q`
   - with `A>=q, B>=q`, the branch `C<q` has an exact wrong-block profile
   - reconstruction gives `c3' = 2q - C > C`, contradiction

3. `D > q`
   - once `A,B,C >= q`, the exact shell profile has tail multiplicity
     `p1 = D-q`
   - but the lead/tail pair is `(9,1)`, so `p1 > 0`
   - therefore `D > q`

So all shell inequalities now hold symbolically:

- `A >= q`
- `B >= q`
- `C >= q`
- `D > q`

By the earlier shell-reduction note, that forces the exact `E` support profile
and then forces `A=B=D`. Therefore every `(9,1)` fixed point is exactly
`E(z,k,q,d)`.

This closes the last open entrance branch.

Combined with the already-closed branches:

- `(5,5) -> P`
- `(6,2) -> C`
- `(8,2) -> O`
- `(9,1) -> E`

and the lead/tail theorem, the fixed-point global entrance theorem is now
complete:

> every nontrivial base-10 Kaprekar fixed point enters the `P/C/E/O`
> reduction grammar symbolically for all `d`.

So the fixed-point side of the base-10 `d=all` program is now internally
closed. The remaining open work is on the broader cycle side, not on fixed
point classification.

## 2026-04-24 — dead zones reframed as pure-cycle borrow automata

Wrote:

- `analysis/base10/dead_zone_cycle_automata_2026-04-24.md`

and added:

- `scripts/kaprekar_dead_zone_cycle_automata.py`

with machine artifact:

- `analysis/base10/dead_zone_cycle_automata_2026-04-24.json`

Main result:

The base-10 dead zones `d=5` and `d=7` are better understood as exact
finite-state borrow automata, not just as dimensions with no fixed points.

Using the already-proved shell-difference maps:

- `d=5` reduces to a 54-state automaton on `(A,B)`
- `d=7` reduces to a 219-state automaton on `(A,B,C)`

New dynamical structure:

- `d=5`: three attractors, with cycle lengths `[2,4,4]` and basin sizes
  `[3,21,30]`; max transient depth `5`
- `d=7`: one universal attractor, an 8-cycle with basin size `219`; max
  transient depth `12`

So the dead-zone story is now:

> pivot closure fails at the fixed-point level, but the borrow state still
> closes dynamically as a finite cycle automaton.

This is especially sharp for `d=7`, where the whole admissible state simplex
flows to one period-8 attractor.

This gives a much better starting point for the cycle program:

- 2-digit gap cycle
- 5-digit dead-zone automaton
- 7-digit dead-zone automaton

and suggests the next clean question:

> can the higher-dimensional cycle families also be organized as exact
> borrow-state automata plus shell-extension rules?

## 2026-04-24 (later) — exact 975 period-3 cycle automaton found

Wrote:

- `analysis/base10/975_cycle_automaton_theorem_2026-04-24.md`

and added:

- `scripts/kaprekar_975_cycle_automaton.py`

with machine artifact:

- `analysis/base10/kaprekar_975_cycle_automaton_2026-04-24.json`

Main result:

The higher-dimensional `975` cycle side is not a sparse list of examples. It is
an exact 4-parameter borrow-state automaton.

For `a,b,c >= 1`, `m >= 0`, define three phase states:

- `X0 = [1,a,c,m,b,b,m,c,a,1]`
- `X1 = [1,b,a,m,c,c,m,a,b,1]`
- `X2 = [1,c,b,m,a,a,m,b,c,1]`

Then symbolically:

- `K(X0) = X1`
- `K(X1) = X2`
- `K(X2) = X0`

with exact gap profiles:

- `g0 = (9,7^a,5^c,3^m,1^b)`
- `g1 = (9,7^b,5^a,3^m,1^c)`
- `g2 = (9,7^c,5^b,3^m,1^a)`

So `K` acts by cyclically permuting the exponent triple `(a,b,c)` while
leaving the `3`-block `m` fixed.

Structural split:

- `a=b=c` gives a fixed ridge
- otherwise the orbit has exact period `3`

This unifies:

- `97508421` as `(1,1,1,0)`
- `9753086421` as `(1,1,1,1)`
- the old period-3 examples:
  - `d=12` = `(1,1,2,1)`
  - `d=16` = `(1,2,3,1)`
  - `d=22` = `(2,3,3,2)`

So the old `d=12,16,22` record is now explained as slices of one exact
symbolic automaton, not three isolated cycle sightings.

The family also carries explicit shell-extension rules:

- `m -> m+1` adds `(3,6)` uniformly to all phases
- increasing `a,b,c` adds phase-rotating complementary pairs among
  `(1,8),(2,7),(4,5)`

Grid verification:

- `a,b,c in {1,...,8}`
- `m in {0,...,8}`
- checked: `4608`
- failures: `0`
- fixed-ridge points: `72`
- period-3 points: `4536`

This is the first higher-dimensional cycle-side result with the same flavor as
the fixed-point grammar: exact symbolic automaton + exact shell extensions.

## 2026-04-24 (later) — exact 863 period-7 cycle automaton found

Wrote:

- `analysis/base10/863_cycle_automaton_theorem_2026-04-24.md`

and added:

- `scripts/kaprekar_863_cycle_automaton.py`

with machine artifact:

- `analysis/base10/kaprekar_863_cycle_automaton_2026-04-24.json`

Main result:

The unique period-7 count-space cycle at `d=8` extends by the uniform shell
move `+2_36` to an exact period-7 automaton in every even dimension

`d = 8 + 2m`.

For `m >= 0`, define the seven phase states:

- `Y0(m) = [1,0,1,m+1,1,1,m+1,0,2,0]`
- `Y1(m) = [1,0,1,m+2,0,0,m+2,0,2,0]`
- `Y2(m) = [0,0,2,m+2,0,0,m+3,0,1,0]`
- `Y3(m) = [0,0,1,m+1,2,1,m+3,0,0,0]`
- `Y4(m) = [1,0,1,m+1,1,0,m+2,1,1,0]`
- `Y5(m) = [0,1,1,m+1,1,1,m+1,1,1,0]`
- `Y6(m) = [1,0,0,m+2,1,1,m+1,1,1,0]`

Then exactly:

- `K(Y0)=Y1`, `K(Y1)=Y2`, `K(Y2)=Y3`, `K(Y3)=Y4`,
  `K(Y4)=Y5`, `K(Y5)=Y6`, `K(Y6)=Y0`.

So the orbit has exact period `7` for every `m`.

This recovers the observed small-d slices:

- `d=8`  (`m=0`)
- `d=10` (`m=1`)
- `d=12` (`m=2`)

and gives a second higher-dimensional cycle-side family with the same shape as
the fixed-point grammar:

- finite phase automaton,
- exact shell-gap words,
- one shell-extension rule.

Validation:

- `m = 0..20`
- checked parameter points: `21`
- failures: `0`

So the cycle side is no longer just:

- the 2-digit gap cycle,
- the dead-zone automata,
- and the `975` period-3 chain.

It also contains an exact `863` period-7 extension chain.

## 2026-04-24 (later) — odd `d=11/13` cycles collapse into four exact `+2_36` families

Wrote:

- `analysis/base10/odd_cycle_extension_families_2026-04-24.md`

and added:

- `scripts/kaprekar_odd_cycle_extension_families.py`

with machine artifact:

- `analysis/base10/kaprekar_odd_cycle_extension_families_2026-04-24.json`

Main result:

The odd-side cycle phenomena at `d=11` and `d=13` are not isolated examples.
They organize into four exact automaton families, all propagated by the same
uniform shell lift `+2_36`.

Families:

- `A_m` — period `5`, dimensions `d = 11 + 2m`
- `B_m` — period `2`, dimensions `d = 13 + 2m`
- `C_m` — period `5`, dimensions `d = 13 + 2m`
- `D_m` — period `5`, dimensions `d = 13 + 2m`

Each family is given by explicit phase count vectors and satisfies exact orbit
identities under `K`.

This explains:

- the known `d=11` period-5 cycle as `A_0`
- the known `d=13` period-2 cycle as `B_0`
- the three known `d=13` period-5 cycles as `A_1`, `C_0`, `D_0`

There is also an unstable lifted period-8 branch:

- lifting the `d=11` period-8 cycle by `+2_36` does **not** preserve period 8
- for every `m >= 1`, the lifted orbit enters the period-2 family `B_{m-1}`
  in bounded phase-dependent time
- verified hit times are constant across tested `m`:
  `[4,3,2,1,1,1,6,5]`

Validation:

- `A`: `m = 0..20`, failures `0`
- `B`: `m = 0..20`, failures `0`
- `C`: `m = 0..20`, failures `0`
- `D`: `m = 0..20`, failures `0`
- `T -> B`: `160` lifted phase points checked, failures `0`

So the odd-side cycle program now looks like a genuine grammar:

- several exact automata,
- one shared shell direction,
- and unstable low-dimensional seeds reducing into stable families after lift.

## 2026-04-24 (later) — cycle grammar skeleton: universal `+2_36` shell axis

Added:

- `analysis/base10/cycle_grammar_skeleton_2026-04-24.md`
- `scripts/kaprekar_cycle_grammar_inventory.py`
- `analysis/base10/kaprekar_cycle_grammar_inventory_2026-04-24.json`

The cycle side now has a genuine grammar-level skeleton.

### Universal shell axis

Across all currently known higher-dimensional count-space cycle families, the
same shell move keeps reappearing:

- `L36`: add one `3` and one `6` to every phase state

This raises dimension by `2`.

Families verified to be exactly closed under this shared axis:

- `863` period-7 chain
- odd `A` period-5 chain
- odd `B` period-2 chain
- odd `C` period-5 chain
- odd `D` period-5 chain
- odd `E` period-5 chain
- odd `F` period-5 chain
- the `m`-axis of the `975` family

So `L36` is the first genuine universal cycle-shell operator seen in base 10.

### Branching odd kernels

The odd-side story does not stop at `d=11` and `d=13`.

Exact count-space scan at `d=15` revealed two further stable period-5 kernels,
now recorded as:

- `E_m` — period `5`, `d = 15 + 2m`
- `F_m` — period `5`, `d = 15 + 2m`

Both are exactly preserved by the same `+2_36` shell lift.

So by `d=15` the odd cycle grammar is already branching:

- one shared shell axis,
- multiple primitive odd kernels.

### Unstable-to-stable reduction

The lifted `d=11` period-8 orbit does not remain periodic of length `8`.
Instead, after applying the same shell lift, it reduces into the stable
period-2 family `B`.

This makes the cycle grammar structurally closer to the fixed-point grammar:

- primitive kernels,
- shell operators,
- stable family closures,
- and reduction rules from unstable seeds into stable branches.

Inventory validation:

- `Y` period-7 family (`863`)
- `A,B,C,D,E,F` odd families
- lifted unstable `T -> B` reduction
- all checked through `m <= 20`
- failures: `0`

This does **not** yet close the full cycle classification. But it is the first
coherent higher-level picture:

- universal shell axis `L36`
- one richer transverse shell system on the `975` side
- stable cycle families
- unstable low-dimensional seeds reducing into stable families

## 2026-04-24 (later) — primitive cycle-kernel births continue at `d=17` and `d=19`

Added:

- `analysis/base10/cycle_kernel_birth_inventory_2026-04-24.md`

and updated:

- `analysis/base10/cycle_grammar_skeleton_2026-04-24.md`
- `scripts/kaprekar_cycle_grammar_inventory.py`
- `analysis/base10/kaprekar_cycle_grammar_inventory_2026-04-24.json`

Main result:

The primitive cycle-kernel inventory under the shared shell axis `L36`
continues to grow on the odd side.

Exact count-space scans showed:

- `d=17`: one genuinely new stable period-5 kernel `G_0`
- `d=19`: one genuinely new stable period-3 kernel `H_0`

Both are exactly preserved by the same `+2_36` lift:

- `G_m` — period `5`, `d = 17 + 2m`
- `H_m` — period `3`, `d = 19 + 2m`

and both verified cleanly through:

- `m <= 15`
- failures: `0`

So the odd stable primitive birth counts through `d=19` are now:

- `d=11`: 1 (`A_0`)
- `d=13`: 3 (`B_0,C_0,D_0`)
- `d=15`: 2 (`E_0,F_0`)
- `d=17`: 1 (`G_0`)
- `d=19`: 1 (`H_0`)

The even side still has the cleaner birth rule:

- `Y_0` at `d=8`
- then `975` primitive kernels at every even `d >= 10`
  (all positive nonconstant triples at `m=0`)

So the strongest current statement is:

- birth dimensions are **not** ad hoc,
- parity matters strongly,
- the shell axis `L36` is universal across all currently known stable
  higher-dimensional cycle families,
- but the odd primitive-kernel multiplicity still has no closed formula.

## 2026-04-24 (later) — odd primitive kernels compress to staircase / rotor / boundary

Added:

- `kaprekar_work/odd_kernel_template_hypothesis_2026-04-24.md`
- `kaprekar_work/kaprekar_odd_kernel_template_probe.py`
- `kaprekar_work/kaprekar_odd_kernel_template_probe_2026-04-24.json`

Main result:

The raw odd primitive inventory

- `A,B,C,D,E,F,G,H`

is already much more structured than it looks.

In paired-core / asymmetry coordinates:

- every odd kernel has total asymmetry `+1` on the high side,
- the period-5 branch uses only the three asymmetry microstates
  - `(1,0,0,0,0)`
  - `(2,-2,1,0,0)`
  - `(0,2,-1,0,0)`

and on the gap side:

- `A,C,D,E,F,G` all satisfy the exact cycle-sum staircase law
  - `(r,5,r,5,r,5,r,5,r)`
- the successful birth links
  - `A -> C`
  - `C -> F`
  - `D -> E`
  - `F -> G`
  all use the same 5-piece layer increment multiset after phase rotation.

So the current best reading is:

- one deeper **period-5 staircase channel**
  containing `A,C,D,E,F,G` as observed slices/decorations,
- one deeper **period-3 rotor channel**
  beginning at `H`,
- one low-dimensional **boundary degeneration**
  at `B`.

`H` is especially clean:

- its base support is fixed,
- the extra odd gap rotates through `1,7,5`,
- so it is a genuine period-3 rotor rather than another staircase member.

This does **not** prove the full odd-kernel grammar yet, but it shrinks the
open problem substantially:

- we no longer need to explain `A..H` one-by-one,
- we now need to prove the staircase channel, the rotor channel, and the role
  of the boundary degeneration.

## 2026-04-24 (later) — the next correct odd-cycle move is symbolic staircase derivation

Added:

- `kaprekar_work/odd_cycle_next_move_decision_2026-04-24.md`

Main result:

The branch point between

- pushing the odd birth inventory further, and
- deriving the period-5 staircase channel symbolically

is now decided in favor of the symbolic route.

Reason:

- the stable period-5 side already has an exact cycle-sum staircase law
  `(r,5,r,5,r,5,r,5,r)`,
- the successful birth links already use one common 5-piece phase-layer
  increment multiset,
- and the non-staircase branches (`H` rotor, `B` boundary degeneration) are
  already separated.

So another birth pass would now be mostly confirmatory, whereas a symbolic
staircase derivation is the higher-value theorem move.

## 2026-04-24 (later) — canonical period-5 staircase template extracted

Added:

- `kaprekar_work/period5_staircase_template_2026-04-24.md`
- `kaprekar_work/kaprekar_period5_staircase_template_probe.py`
- `kaprekar_work/kaprekar_period5_staircase_template_2026-04-24.json`

Main result:

The stable odd period-5 branch now has a canonical operator form.

In a normalized phase gauge:

- `S_1 = A`
- `S_2 = C`
- `S_3 = F`
- `S_4 = G`

and there is one fixed 5-piece layer operator

- `M_0 = (0,0,0,0,0,0,1,0,0)`
- `M_1 = (0,0,0,0,1,0,0,0,0)`
- `M_2 = (1,0,0,0,0,0,0,0,0)`
- `M_3 = (0,0,0,0,0,1,0,-1,1)`
- `M_4 = (0,0,1,0,0,-1,0,1,0)`

such that

`S_(r+1)^(i) = S_r^(i) + M_((i+r-1) mod 5)`.

This unrolls to a closed form

`S_r^(i) = S_1^(i) + sum_{t=0}^{r-2} M_((i+t) mod 5)`,

and the probe verified:

- `A,C,F,G` recovered exactly
- failures: `0`

Most importantly, the predicted next level is:

- `S_5^(i) = (1,1,1,1,1,1,1,1,1)` for all phases

So the odd period-5 branch terminates naturally by ridge collapse at level
`5`, instead of continuing to produce fresh primitive period-5 births. This is
why the inventory reaches `G` and then stops.

The observed companion branch `D -> E` is also not a separate mechanism: it is
the same layer operator seen with a phase offset.

## 2026-04-26 — the period-5 staircase closes to a fixed ridge; `H` is its minimal rotor defect

Added:

- `kaprekar_work/period5_h_bridge_2026-04-26.md`
- `kaprekar_work/kaprekar_period5_h_bridge_probe.py`
- `kaprekar_work/kaprekar_period5_h_bridge_2026-04-26.json`

Main result:

The stable odd period-5 branch and the period-3 `H` branch are now connected
cleanly in count space.

The canonical staircase recurrence on

- `A -> C -> F -> G`

extends one more step to the unique ridge state

- `R = (1,2,2,2,2,2,2,2,2,2)`

and this ridge is a genuine fixed point:

- `K(R) = R`
- number: `9876543209876543211`

So the period-5 birth stream ends by **fixed-point ridge closure**, not by
turning into `H`.

The period-3 family `H` is then exactly the nearest rotating defect of this
ridge:

- `H_0 = R + D_45`
- `H_1 = R + D_18`
- `H_2 = R + D_27`

where each defect is formed by removing one `(3,6)` shell and reinserting it
into one of the three complementary odd-pair directions:

- `(4,5)`
- `(1,8)`
- `(2,7)`

and `K` rotates these three defects cyclically.

So the bridge is now:

- staircase branch -> fixed ridge
- ridge + one minimal odd defect -> `H` rotor

That is a much sharper structural relation than “the odd side has two
templates.” It says exactly how the period-3 rotor sits next to the terminating
period-5 staircase.

## 2026-04-26 (later) — staircase count pieces forced; ridge has exactly three primitive one-shell rotor directions

Added:

- `kaprekar_work/staircase_count_piece_forcing_2026-04-26.md`
- `kaprekar_work/kaprekar_staircase_count_piece_forcing.py`
- `kaprekar_work/kaprekar_staircase_count_piece_forcing_2026-04-26.json`
- `kaprekar_work/ridge_defect_direction_minimality_2026-04-26.md`
- `kaprekar_work/kaprekar_ridge_defect_direction_probe.py`
- `kaprekar_work/kaprekar_ridge_defect_direction_2026-04-26.json`

Main results:

1. The raw count-space staircase pieces `N_0,...,N_4` are now forced by the
   odd automaton rather than read off the family differences.

   Starting from:

   - the canonical gap-space staircase pieces `M_0,...,M_4`,
   - the odd asymmetry alphabet `{u,v,w}`,
   - and the minimal two-digit raw-lift condition `Δk in {-1,0,1}`,
     `sum Δk = 2`,

   the probe searched all candidate raw count lifts across the main chain
   `A->C->F->G` and the companion slice `D->E`, for `m=0..8`.

   For every `j=0,...,4`, the valid raw count lift is unique.

   The unique forced lifts are exactly:

   - `N_0 = (0,1,0,0,0,0,0,0,1,0)`
   - `N_1 = (0,0,1,0,0,0,0,1,0,0)`
   - `N_2 = (0,0,0,0,1,1,0,0,0,0)`
   - `N_3 = (1,-1,1,0,0,0,0,0,1,0)`
   - `N_4 = (0,1,-1,1,0,0,1,0,-1,1)`

   So the staircase now has both halves of its operator pinned internally:

   - gap-space pieces `M_0,...,M_4`
   - raw count-space lifts `N_0,...,N_4`

2. The ridge defect directions are now exhausted at the minimal one-shell
   level.

   The probe enumerated all `20` ordered complementary-pair shell transfers
   away from the ridge

   - `R = (1,2,2,2,2,2,2,2,2,2)`

   and classified the resulting orbit under `K`.

   Exact outcome:

   - primitive `H` rotor directions: exactly `3`
     - `36->18`
     - `36->27`
     - `36->45`
   - non-primitive captures into `H`: exactly `3`
     - `18->09`
     - `27->09`
     - `45->09`
   - all remaining `14` directions fall into period `1` or period `5`, not a
     new primitive rotor.

So the odd bridge picture is now much tighter than before:

- staircase operator forced in both gap space and count space,
- staircase closes onto a fixed ridge,
- the ridge admits exactly three primitive one-shell rotor exits,
- those exits are precisely the `H` family.

## 2026-04-26 (later) — the odd period-3 side is an `H` shell fan through `d=23`, with one residual at `d=25`

Added:

- `kaprekar_work/kaprekar_odd_cycle_census.py`
- `kaprekar_work/kaprekar_odd_cycle_census_2026-04-26.json`
- `kaprekar_work/kaprekar_h_shell_fan_probe.py`
- `kaprekar_work/h_shell_fan_2026-04-26.md`
- `kaprekar_work/kaprekar_h_shell_fan_2026-04-26.json`

Main result:

Built a reduced odd count-state census on the exact state space

- `sum(c0..c4)=l`
- `sum(c5..c9)=l+1`
- `d=2l+1`

and used it to classify non-fixed odd attractors.

Validation first came back perfectly on the known window:

- `d=11`: exactly `A` and unstable `T`
- `d=13`: exactly `A,B,C,D`
- `d=15`: exactly `A,B,C,D,E,F`
- `d=17`: exactly `A,B,C,D,E,F,G`
- `d=19`: exactly `A,B,C,D,E,F,G,H`

So the reduced census is matching the existing odd grammar exactly through the
current proven window.

Then the new result:

- `d=21`: `11` odd non-fixed attractors total, with `4` period-3
  attractors; these are exactly the degree-1 shell fan on top of `H`
- `d=23`: the period-3 sector has exactly `10` families, and they are
  **exactly** the degree-2 commutative shell closure of the four directions
  on top of `H`
- `d=25`: the same shell-fan construction gives `20` of the `21`
  period-3 attractors, leaving one honest residual period-3 family

The four shell directions on top of `H` are:

- `A = +36` uniformly
- `B = +09` uniformly
- `C = +(45,18,27)` by phase
- `D = +(27,45,18)` by phase

So the period-3 odd side is not just the old axial chain `H_m`.
It is already a genuine shell fan:

- degree `1` closure exact at `d=21`
- degree `2` closure exact at `d=23`
- degree `3` closure nearly exact at `d=25`

This is strong structural evidence that the odd cycle births after `d=19` are
still living inside the rotor channel rather than forcing a completely new
odd mechanism. The honest remaining gap is the single residual period-3 family
visible at `d=25`, plus the period-2 boundary line `B`.

## 2026-05-03 — the `d=25` period-3 residual is an exact `J` family; `B` absorbs as a boundary repair of `T`

Added:

- `kaprekar_work/kaprekar_j_cycle_family.py`
- `kaprekar_work/j_cycle_family_2026-05-03.md`
- `kaprekar_work/kaprekar_j_cycle_family_2026-05-03.json`
- `kaprekar_work/kaprekar_b_boundary_repair.py`
- `kaprekar_work/b_boundary_repair_2026-05-03.md`
- `kaprekar_work/kaprekar_b_boundary_repair_2026-05-03.json`

Main results:

1. The former `d=25` period-3 residual is not unexplained.

   If

   - `H_m` is the old axial period-3 rotor family, and
   - `E = +18 +27 +45` uniformly across all three phases,

   then

   - `J_m = H_m + E`

   is an exact period-3 family for every tested `m=0..20`, with zero
   failures.

   So the residual representative

   - `(1,3,3,1,4,4,1,3,3,2)`

   is exactly `J_0`, not a stray exception.

   This means the odd period-3 side now has:

   - the old axial chain `H_m`
   - the four-direction shell fan through degree `2`
   - one exact new residual family `J_m` at degree `3`

2. The period-2 line `B` can be absorbed into the shell grammar as a boundary
   repair of the unstable `T` seed.

   Exact identities for every tested `m=0..20`:

   - `B_0(m) = T_0(m) + 45`
   - `B_1(m) = T_5(m) + 36`

   with zero failures.

   So `B` is no longer best read as a wholly separate odd primitive species.
   It is a stabilized two-phase boundary repair of the unstable `T` orbit.

What remains open after this:

- the full odd period-3 shell-fan closure beyond `J`,
- and the broader odd period-2 boundary sector, since the reduced census at
  `d=25` still shows one additional period-2 attractor beyond the old `B`
  line.

## 2026-05-12 — Odd period-3 affine levels and boundary-thread integration

Two cycle-side clarifications landed and both matter for the eventual unified
`d=all` paper path:

1. The reduced odd period-3 rotor cone and the `K_p` boundary-thread tail are
   now integrated into one odd affine-delta normal form.

   Define

   - `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
   - `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
   - `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

   with `delta = c9-c0`.

   Then:

   - every exact reduced-sector odd period-3 attractor in the local census at
     `d=23,25,27,29` fits level `delta=1`, with zero failures
   - the boundary-thread period-3 tail satisfies
     `Z_i(r) = Ri_delta(1,r,4,4,4)` on level `delta=3`, verified for
     `r=5..24` with zero failures

   So the boundary thread is no longer just a side correction to the reduced
   rotor cone. The odd period-3 side now has two exposed affine levels:

   - reduced level `delta=1`
   - boundary level `delta=3`

2. The phase-sum template is now shared between those two levels.

   Any affine-delta period-3 orbit has cycle-sum vector

   - `[3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]`

   where `M = v+w+y`.

   In particular:

   - reduced level `delta=1` gives `[3u,M,M,3x,M,M,3x,M,M,3u+3]`
   - boundary tail `delta=3` gives `[3,r+8,r+8,12,r+8,r+8,12,r+8,r+8,12]`

   This is a cleaner algebraic integration than the earlier wording “reduced
   cone plus boundary correction.”

Artifacts:

- `kaprekar_odd_period3_affine_levels.py`
- `odd_period3_affine_levels_2026-05-12.md`
- `kaprekar_odd_period3_affine_levels_2026-05-12.json`

I deliberately did not overwrite the external Kaprekar `RESEARCH_LOG.md`. The
local mirror remains the safe working log until the divergent logs are merged
deliberately.

## 2026-05-12 — Odd period-3 affine hierarchy emerged

The affine-level bridge immediately strengthened into a larger internal cycle
picture.

Inside the exact odd affine-delta normal form

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

the direct exact scan now gives:

- level `delta=1` counts
  - `d=19: 1`
  - `d=21: 4`
  - `d=23: 10`
  - `d=25: 21`
  - `d=27: 39`
  - `d=29: 66`
  - `d=31: 105`
  - `d=33: 159`
  - `d=35: 231`
- level `delta=3` counts
  - `d=37: 1`
  - `d=39: 4`
  - `d=41: 10`
  - `d=43: 21`
  - `d=45: 39`
  - `d=47: 66`
  - `d=49: 105`
  - `d=51: 159`
  - `d=53: 231`
  - `d=55: 325`
- level `delta=5` already begins with
  - `d=55: 1`
  - `d=57: 4`
  - `d=59: 10`
  - `d=61: 21`
  - `d=63: 39`
  - `d=65: 66`

So the odd period-3 side is not best described anymore as:

- reduced affine cone, plus
- one boundary-thread tail.

The better reading is:

- reduced level `delta=1`
- higher odd affine hierarchy, with the `K_p` tail as one explicit slice of
  level `delta=3`

This is a real shift in the theorem path. The boundary thread did not merely
fix the old `d=25` knot story; it exposed the next affine level.

Artifacts:

- `kaprekar_odd_affine_delta_scan.py`
- `odd_period3_affine_hierarchy_2026-05-12.md`
- `kaprekar_odd_affine_delta_scan_2026-05-12.json`

The external Kaprekar log is still deliberately untouched.

## 2026-05-19 — Odd affine lift and boundary-thread entrance law

Two exact cycle-side closure steps landed on the odd period-3 hierarchy.

1. The odd affine period-3 levels are connected by an exact `delta -> delta+2`
   lift.

   Inside the affine normal form

   - `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
   - `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
   - `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

   the lift

   - `L : (u,v,w,x,y,delta) -> (u,v+2,w+2,x+2,y+2,delta+2)`

   preserves exact period `3` and raises dimension by `18`.

   Verified:

   - all exact affine cycles on `delta=1` through `d<=35` lift to exact
     `delta=3` cycles, zero failures
   - all exact affine cycles on `delta=3` through `d<=55` lift to exact
     `delta=5` cycles, zero failures
   - the inverse lowering `3->1` and `5->3` also holds on the same windows,
     zero failures

   Consequence:

   - every positive odd `delta` occurs in the affine grammar

   via the base seed

   - `(u,v,w,x,y) = (1,delta+1,delta+1,delta,delta+2)`
   - `d = 9*delta + 10`.

2. The non-period-3 boundary thread now has an exact entrance law into affine
   level `delta=3`.

   For the explicit thread

   - `K_p = [0,p,3,3,3,3,3,3,p,3]`

   we now have the exact verified rule

   - `K^12(K_p) = Z0(p-4)` for every `p>=8`

   where

   - `Z0(r) = [1,r,4,4,4,4,4,4,r,4] = R0_3(1,r,4,4,4)`.

   So the boundary thread does not merely “eventually” reach the period-3
   sector. It enters affine level `delta=3` after a constant time of `12`
   steps.

Artifacts:

- `kaprekar_odd_affine_delta_lift.py`
- `odd_affine_delta_lift_2026-05-19.md`
- `kaprekar_odd_affine_delta_lift_2026-05-19.json`
- `kaprekar_boundary_thread_affine_entrance.py`
- `boundary_thread_affine_entrance_2026-05-19.md`
- `kaprekar_boundary_thread_affine_entrance_2026-05-19.json`

The external Kaprekar `RESEARCH_LOG.md` remains deliberately untouched.

## 2026-05-20 — Odd period-3 scope lock and full-state sample audit

I explicitly scope-locked the remaining odd period-3 theorem debt:

> prove that every odd period-3 attractor is affine-`delta`.

That was written down in:

- `odd_period3_scope_lock_2026-05-20.md`

The point of that note is to stop drifting into “more family growth” and keep
the cycle-side endgame attached to one sharp claim.

Then I ran the matching full-state sample audit:

- `5000` random full odd count states at each of
  `d=19,21,23,25,27,29,31,33,39,45,55`
- iterate each sample to its count-space attractor
- if the attractor period is `3`, test whether all three phases are
  affine-`delta`

Result:

- zero sampled non-affine odd period-3 attractors

Observed sampled `delta` levels:

- only `delta=1` up through `d=33`
- `delta=1,3` by `d=39,45`
- `delta=1,3,5` by `d=55`

So the full-state samples support both of the current internal claims:

1. affine-`delta` is the right global odd period-3 candidate normal form
2. the higher odd `delta` levels really do appear in the full odd universe,
   not just in the explicit constructed families

This is still not a theorem. But it means the next honest move is no longer
“check more families.” It is:

- find a symbolic invariant forcing pairwise symmetry on odd period-3
  attractors

Artifacts:

- `kaprekar_global_odd_period3_sample_audit.py`
- `global_odd_period3_sample_audit_2026-05-20.md`
- `kaprekar_global_odd_period3_sample_audit_2026-05-20.json`

External Kaprekar `RESEARCH_LOG.md` remains untouched.

## 2026-05-20 (later) — odd period-3 phase-sum bridge into fixed points

Found the first direct bridge from the odd period-3 affine hierarchy back into
the already closed fixed-point `d=all` theorem.

For an affine odd period-3 cycle

- `R0_delta(u,v,w,x,y)`
- `R1_delta(u,v,w,x,y)`
- `R2_delta(u,v,w,x,y)`

the phase-sum vector

- `S = R0_delta + R1_delta + R2_delta`

is exactly

- `S = [3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]`

with `M=v+w+y`, and satisfies

- `K(S)=S`.

So every currently verified affine odd period-3 family has a canonical
fixed-point shadow.

This was verified on:

- `1000` random exact affine parameter points, zero failures
- the exact reduced odd period-3 census at `d=23,25,27,29`, zero failures
- the boundary-thread tail `Z_r` for `r=5..24`, zero failures

This matters because it sharpens the global theorem path:

- we no longer need to think of the cycle side as wholly separate from the
  fixed-point `d=all` proof
- instead, the right remaining move is:
  1. force odd period-3 attractors into affine-`delta`
  2. inherit fixed-point structure from their phase-sum shadow

Artifacts:

- `kaprekar_odd_period3_phase_sum_bridge.py`
- `odd_period3_phase_sum_bridge_2026-05-20.md`
- `kaprekar_odd_period3_phase_sum_bridge_2026-05-20.json`

External Kaprekar `RESEARCH_LOG.md` still untouched.

## 2026-05-27 — odd period-3 asymmetry profile sharpens to pure outer defect

Ran a stronger audit on the odd period-3 asymmetry side and wrote:

- `kaprekar_odd_period3_asymmetry_profile_audit.py`
- `odd_period3_asymmetry_profile_2026-05-27.md`
- `kaprekar_odd_period3_asymmetry_profile_audit_2026-05-27.json`

This strengthens the earlier “phasewise asymmetry constancy” claim.

Observed across every currently exposed odd period-3 sector:

- exact reduced odd census at `d=23,25,27,29`
- boundary-thread tail `Z_r`, `r=5..24`
- sampled full odd states at
  `d=19,21,23,25,27,29,31,33,39,45,55`

the phasewise asymmetry is not merely constant. It is exactly

- `A(C) = (delta,0,0,0,0)`.

So the higher affine levels introduce no new inner asymmetry behavior. They
only raise the outer odd defect.

This sharpens the live odd period-3 theorem debt again. The current best
reduction is now:

1. prove phase-sum fixedpoint globally
2. prove exact asymmetry-profile collapse
   `A(C)=(delta,0,0,0,0)` globally

Once those hold, pairwise symmetry and the affine-`delta` normal form follow
through the fixed-point theorem path already in place.

External Kaprekar `RESEARCH_LOG.md` remains untouched.

## 2026-05-20 (latest) — odd period-3 pairwise symmetry reduced to two invariants

Wrote the first theorem-facing reduction from the odd period-3 cycle side back
into the already closed fixed-point theorem.

New note:

- `odd_period3_pairwise_symmetry_reduction_2026-05-20.md`

Main statement:

If an odd period-3 attractor satisfies

1. phase-sum fixedpoint: `K(C0+C1+C2)=C0+C1+C2`
2. phasewise asymmetry constancy:
   `A(C0)=A(C1)=A(C2)=(delta,a,b,c,d)`

then pairwise symmetry is forced:

- `c1=c8`
- `c2=c7`
- `c3=c6`
- `c4=c5`

phasewise.

Reason:

- the phase-sum shadow `S` is then a fixed point whose inner asymmetry is
  `(3a,3b,3c,3d)`
- but the fixed-point theorem allows only two inner asymmetry types:
  - zero
  - the classical `6174` type `(1,-1,-1,1)`
- the classical type is not divisible by `3`

So the shadow cannot be classical, hence it is inner-symmetric, hence each
phase is inner-symmetric too.

This materially sharpens the odd period-3 theorem debt. The live target is no
longer “prove affine-`delta` directly.” It is now:

1. prove phase-sum fixedpoint globally
2. prove phasewise asymmetry constancy globally

The new reduction is fully consistent with:

- exact reduced odd census at `d=23,25,27,29`: `136/136`
- boundary tail `Z_r`, `r=5..24`: `20/20`
- sampled global odd states at
  `d=19,21,23,25,27,29,31,33,39,45,55`: zero sampled violations

Artifacts:

- `kaprekar_odd_period3_reduction_audit.py`
- `kaprekar_odd_period3_reduction_audit_2026-05-20.json`
- `odd_period3_pairwise_symmetry_reduction_2026-05-20.md`

External Kaprekar `RESEARCH_LOG.md` still untouched.
