import LonelyRunner.LRC.Cascade.Flanks

/-!
# Fully-pinned census families, part 3 of 4

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Each theorem is one seven-difference arrangement from an `s = 6` census cover — fully pinned,
so there is no free parameter and Existence for the runner is just that some flank has a lonely
opening.  The framework's clearing test (`Flanks.clear_of_residue_band`, Proposition 2.1) makes
that decidable arithmetic, so each family closes by `decide` on the residue band.

Emitted by `experiments/n8/gen_pinned_batch_v1.py`; data recomputed and cross-checked in
`experiments/n8/census_export_v1.py`.
-/

set_option maxHeartbeats 1000000

namespace PinnedBatch3

open MomentIterationN Flanks

/-- Differences `[2, 13, 15, 28, 34, 48, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 28, 34, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 28, 34, 48, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 16, 22, 24, 35, 44]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_2 : ∃ k : ℕ, Lonely 8 (([2, 13, 16, 22, 24, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 16, 22, 24, 35, 44]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 17, 28, 30, 32, 60]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_3 : ∃ k : ℕ, Lonely 8 (([2, 13, 17, 28, 30, 32, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 17, 28, 30, 32, 60]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 22, 24, 30, 35, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_4 : ∃ k : ℕ, Lonely 8 (([2, 13, 22, 24, 30, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 22, 24, 30, 35, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 22, 24, 32, 35, 44]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_5 : ∃ k : ℕ, Lonely 8 (([2, 13, 22, 24, 32, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 22, 24, 32, 35, 44]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 16, 17, 23, 34]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_6 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 16, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 16, 17, 23, 34]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 16, 18, 21, 42]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_7 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 16, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 16, 18, 21, 42]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 16, 19, 23, 28]`, flank `14`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_8 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 16, 19, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 16, 19, 23, 28]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 16, 26, 29, 39]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_9 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 16, 26, 29, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 16, 26, 29, 39]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 17, 21, 25, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_10 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 17, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 17, 21, 25, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 15, 21, 25, 29, 42]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_11 : ∃ k : ℕ, Lonely 8 (([2, 14, 15, 21, 25, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 15, 21, 25, 29, 42]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 16, 18, 23, 30, 35]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_12 : ∃ k : ℕ, Lonely 8 (([2, 14, 16, 18, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 16, 18, 23, 30, 35]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 21, 23, 25, 32, 42]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_13 : ∃ k : ℕ, Lonely 8 (([2, 14, 21, 23, 25, 32, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 21, 23, 25, 32, 42]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 22, 23, 24, 25, 33]`, flank `22`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_14 : ∃ k : ℕ, Lonely 8 (([2, 14, 22, 23, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 22, 23, 24, 25, 33]) (e := 22) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 23, 25, 27, 32, 54]`, flank `14`, opening `8`.  Covers 1 census rows. -/
theorem fam_3_15 : ∃ k : ℕ, Lonely 8 (([2, 14, 23, 25, 27, 32, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 23, 25, 27, 32, 54]) (e := 14) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 14, 23, 25, 30, 32, 33]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_16 : ∃ k : ℕ, Lonely 8 (([2, 14, 23, 25, 30, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 14, 23, 25, 30, 32, 33]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 16, 18, 21, 28, 42]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_17 : ∃ k : ℕ, Lonely 8 (([2, 15, 16, 18, 21, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 16, 18, 21, 28, 42]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 17, 19, 21, 23, 30]`, flank `15`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_18 : ∃ k : ℕ, Lonely 8 (([2, 15, 17, 19, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 17, 19, 21, 23, 30]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 17, 19, 21, 23, 42]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_19 : ∃ k : ℕ, Lonely 8 (([2, 15, 17, 19, 21, 23, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 17, 19, 21, 23, 42]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 17, 21, 25, 33, 34]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_20 : ∃ k : ℕ, Lonely 8 (([2, 15, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 17, 21, 25, 33, 34]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 17, 21, 32, 36, 45]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_21 : ∃ k : ℕ, Lonely 8 (([2, 15, 17, 21, 32, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 17, 21, 32, 36, 45]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 17, 26, 28, 32, 40]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_22 : ∃ k : ℕ, Lonely 8 (([2, 15, 17, 26, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 17, 26, 28, 32, 40]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 19, 21, 23, 27, 38]`, flank `15`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_23 : ∃ k : ℕ, Lonely 8 (([2, 15, 19, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 19, 21, 23, 27, 38]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 19, 21, 23, 34, 46]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_24 : ∃ k : ℕ, Lonely 8 (([2, 15, 19, 21, 23, 34, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 19, 21, 23, 34, 46]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 21, 25, 28, 29, 42]`, flank `15`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_25 : ∃ k : ℕ, Lonely 8 (([2, 15, 21, 25, 28, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 21, 25, 28, 29, 42]) (e := 15) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 21, 33, 35, 37, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_26 : ∃ k : ℕ, Lonely 8 (([2, 15, 21, 33, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 21, 33, 35, 37, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 22, 24, 26, 28, 35]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_27 : ∃ k : ℕ, Lonely 8 (([2, 15, 22, 24, 26, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 22, 24, 26, 28, 35]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 26, 28, 33, 41, 52]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_28 : ∃ k : ℕ, Lonely 8 (([2, 15, 26, 28, 33, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 26, 28, 33, 41, 52]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 26, 28, 41, 43, 52]`, flank `15`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_29 : ∃ k : ℕ, Lonely 8 (([2, 15, 26, 28, 41, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 26, 28, 41, 43, 52]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 15, 28, 32, 43, 46, 56]`, flank `15`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_30 : ∃ k : ℕ, Lonely 8 (([2, 15, 28, 32, 43, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 15, 28, 32, 43, 46, 56]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 17, 18, 19, 35, 47]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_31 : ∃ k : ℕ, Lonely 8 (([2, 16, 17, 18, 19, 35, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 17, 18, 19, 35, 47]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 18, 20, 21, 27, 54]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_32 : ∃ k : ℕ, Lonely 8 (([2, 16, 18, 20, 21, 27, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 18, 20, 21, 27, 54]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 18, 21, 23, 30, 35]`, flank `16`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_33 : ∃ k : ℕ, Lonely 8 (([2, 16, 18, 21, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 18, 21, 23, 30, 35]) (e := 16) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 18, 23, 28, 30, 35]`, flank `16`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_34 : ∃ k : ℕ, Lonely 8 (([2, 16, 18, 23, 28, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 18, 23, 28, 30, 35]) (e := 16) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 19, 21, 23, 25, 33]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_35 : ∃ k : ℕ, Lonely 8 (([2, 16, 19, 21, 23, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 19, 21, 23, 25, 33]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 16, 20, 21, 27, 36, 54]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_36 : ∃ k : ℕ, Lonely 8 (([2, 16, 20, 21, 27, 36, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 16, 20, 21, 27, 36, 54]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 19, 21, 23, 25, 38]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_37 : ∃ k : ℕ, Lonely 8 (([2, 17, 19, 21, 23, 25, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 19, 21, 23, 25, 38]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 19, 21, 23, 25, 50]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_38 : ∃ k : ℕ, Lonely 8 (([2, 17, 19, 21, 23, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 19, 21, 23, 25, 50]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 19, 21, 23, 40, 50]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_39 : ∃ k : ℕ, Lonely 8 (([2, 17, 19, 21, 23, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 19, 21, 23, 40, 50]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 21, 23, 25, 38, 50]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_40 : ∃ k : ℕ, Lonely 8 (([2, 17, 21, 23, 25, 38, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 21, 23, 25, 38, 50]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 21, 23, 25, 40, 50]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_41 : ∃ k : ℕ, Lonely 8 (([2, 17, 21, 23, 25, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 21, 23, 25, 40, 50]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 21, 30, 32, 36, 45]`, flank `17`, opening `13`.  Covers 1 census rows. -/
theorem fam_3_42 : ∃ k : ℕ, Lonely 8 (([2, 17, 21, 30, 32, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨13, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 21, 30, 32, 36, 45]) (e := 17) (k := 13)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 24, 26, 28, 45, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_43 : ∃ k : ℕ, Lonely 8 (([2, 17, 24, 26, 28, 45, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 24, 26, 28, 45, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 24, 26, 28, 55, 56]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_44 : ∃ k : ℕ, Lonely 8 (([2, 17, 24, 26, 28, 55, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 24, 26, 28, 55, 56]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 26, 28, 30, 33, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_45 : ∃ k : ℕ, Lonely 8 (([2, 17, 26, 28, 30, 33, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 26, 28, 30, 33, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 17, 26, 28, 30, 43, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_46 : ∃ k : ℕ, Lonely 8 (([2, 17, 26, 28, 30, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 17, 26, 28, 30, 43, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 18, 21, 23, 24, 25, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_47 : ∃ k : ℕ, Lonely 8 (([2, 18, 21, 23, 24, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 18, 21, 23, 24, 25, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 18, 23, 28, 30, 32, 35]`, flank `18`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_48 : ∃ k : ℕ, Lonely 8 (([2, 18, 23, 28, 30, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 18, 23, 28, 30, 32, 35]) (e := 18) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 20, 21, 23, 27, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_49 : ∃ k : ℕ, Lonely 8 (([2, 19, 20, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 20, 21, 23, 27, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 21, 23, 25, 27, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_50 : ∃ k : ℕ, Lonely 8 (([2, 19, 21, 23, 25, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 21, 23, 25, 27, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 21, 23, 25, 32, 33]`, flank `19`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_51 : ∃ k : ℕ, Lonely 8 (([2, 19, 21, 23, 25, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 21, 23, 25, 32, 33]) (e := 19) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 21, 23, 27, 30, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_52 : ∃ k : ℕ, Lonely 8 (([2, 19, 21, 23, 27, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 21, 23, 27, 30, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 21, 23, 27, 35, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_53 : ∃ k : ℕ, Lonely 8 (([2, 19, 21, 23, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 21, 23, 27, 35, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 19, 30, 32, 34, 49, 60]`, flank `19`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_54 : ∃ k : ℕ, Lonely 8 (([2, 19, 30, 32, 34, 49, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 19, 30, 32, 34, 49, 60]) (e := 19) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 20, 21, 23, 27, 31, 46]`, flank `20`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_55 : ∃ k : ℕ, Lonely 8 (([2, 20, 21, 23, 27, 31, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 20, 21, 23, 27, 31, 46]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 21, 23, 24, 25, 30, 33]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_56 : ∃ k : ℕ, Lonely 8 (([2, 21, 23, 24, 25, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 21, 23, 24, 25, 30, 33]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 21, 23, 25, 27, 48, 54]`, flank `21`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_57 : ∃ k : ℕ, Lonely 8 (([2, 21, 23, 25, 27, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 21, 23, 25, 27, 48, 54]) (e := 21) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 21, 23, 25, 28, 32, 42]`, flank `21`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_58 : ∃ k : ℕ, Lonely 8 (([2, 21, 23, 25, 28, 32, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 21, 23, 25, 28, 32, 42]) (e := 21) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 21, 25, 27, 46, 48, 54]`, flank `21`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_59 : ∃ k : ℕ, Lonely 8 (([2, 21, 25, 27, 46, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 21, 25, 27, 46, 48, 54]) (e := 21) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 21, 26, 38, 40, 47, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_60 : ∃ k : ℕ, Lonely 8 (([2, 21, 26, 38, 40, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 21, 26, 38, 40, 47, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 23, 28, 30, 32, 41, 56]`, flank `23`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_61 : ∃ k : ℕ, Lonely 8 (([2, 23, 28, 30, 32, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((23 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 23, 28, 30, 32, 41, 56]) (e := 23) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 23, 28, 30, 32, 51, 56]`, flank `23`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_62 : ∃ k : ℕ, Lonely 8 (([2, 23, 28, 30, 32, 51, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((23 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 23, 28, 30, 32, 51, 56]) (e := 23) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 26, 30, 33, 35, 37, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_63 : ∃ k : ℕ, Lonely 8 (([2, 26, 30, 33, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 26, 30, 33, 35, 37, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 26, 31, 32, 33, 35, 42]`, flank `26`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_64 : ∃ k : ℕ, Lonely 8 (([2, 26, 31, 32, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 26, 31, 32, 33, 35, 42]) (e := 26) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 26, 31, 33, 35, 37, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_65 : ∃ k : ℕ, Lonely 8 (([2, 26, 31, 33, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 26, 31, 33, 35, 37, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 29, 31, 33, 35, 37, 58]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_66 : ∃ k : ℕ, Lonely 8 (([2, 29, 31, 33, 35, 37, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 29, 31, 33, 35, 37, 58]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 33, 36, 38, 40, 42, 45]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_67 : ∃ k : ℕ, Lonely 8 (([2, 33, 36, 38, 40, 42, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 33, 36, 38, 40, 42, 45]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_68 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 16, 33]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_69 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 16, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 16, 33]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_70 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_71 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_72 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 11, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_73 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 11, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 12, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_74 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 12, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 12, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 13, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_75 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 13, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 16, 22, 33]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_76 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 16, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 16, 22, 33]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 7, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_77 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 7, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 7, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 8, 13, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_78 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 8, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 8, 13, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 9, 13, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_79 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 9, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 9, 13, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 11, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_80 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 11, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 11, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 11, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_81 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 11, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 11, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 13, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_82 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 13, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 13, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 13, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_83 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 13, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 13, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 5, 14, 18, 34, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_84 : ∃ k : ℕ, Lonely 8 (([3, 4, 5, 14, 18, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 5, 14, 18, 34, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 6, 7, 10, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_85 : ∃ k : ℕ, Lonely 8 (([3, 4, 6, 7, 10, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 6, 7, 10, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 6, 7, 15, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_86 : ∃ k : ℕ, Lonely 8 (([3, 4, 6, 7, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 6, 7, 15, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 6, 10, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_87 : ∃ k : ℕ, Lonely 8 (([3, 4, 6, 10, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 6, 10, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 6, 10, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_88 : ∃ k : ℕ, Lonely 8 (([3, 4, 6, 10, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 6, 10, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 8, 12, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_89 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 8, 12, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 8, 12, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 9, 16, 25, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_90 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 9, 16, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 9, 16, 25, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 11, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_91 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 11, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 11, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 11, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_92 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 11, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 11, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_93 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 11, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 12, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_94 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 12, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 12, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 13, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_95 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 13, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 13, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 13, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_96 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 13, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 13, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 15, 18, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_97 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 15, 18, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 15, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_98 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 15, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 16, 24, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_99 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 16, 24, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 16, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_100 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 16, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 16, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 17, 24, 35]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_101 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 17, 24, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 17, 24, 35]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 10, 24, 32, 48]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_102 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 10, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 10, 24, 32, 48]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 15, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_103 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 15, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 15, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 15, 18, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_104 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 15, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 15, 18, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 15, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_105 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 15, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 15, 19, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_106 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 15, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 15, 19, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_107 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 11, 18, 30, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_108 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 11, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 11, 18, 30, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 12, 15, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_109 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 12, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 12, 15, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 13, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_110 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 13, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 13, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 13, 17, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_111 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 13, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 13, 17, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 15, 18, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_112 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 15, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 15, 18, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 15, 18, 22, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_113 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 15, 18, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 15, 18, 22, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 15, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_114 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 15, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 7, 16, 18, 25, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_115 : ∃ k : ℕ, Lonely 8 (([3, 4, 7, 16, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 7, 16, 18, 25, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 11, 14, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_116 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 11, 14, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 11, 14, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 12, 14, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_117 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 12, 14, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 12, 14, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 14, 17, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_118 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 14, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 14, 17, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 14, 20, 23, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_119 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 14, 20, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 14, 20, 23, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 14, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_120 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 14, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 14, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 8, 14, 22, 25, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_121 : ∃ k : ℕ, Lonely 8 (([3, 4, 8, 14, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 8, 14, 22, 25, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 9, 12, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_122 : ∃ k : ℕ, Lonely 8 (([3, 4, 9, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 9, 12, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 9, 14, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_123 : ∃ k : ℕ, Lonely 8 (([3, 4, 9, 14, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 9, 14, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 11, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_124 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 11, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 11, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 11, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_125 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 11, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 11, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 11, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_126 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 11, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 11, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 11, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_127 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 11, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 11, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 13, 14, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_128 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 13, 14, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 13, 14, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 13, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_129 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 13, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 13, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 13, 16, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_130 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 13, 16, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 13, 16, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 13, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_131 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 13, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 13, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 13, 21, 24, 26]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_132 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 13, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 13, 21, 24, 26]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 14, 15, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_133 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 14, 15, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 14, 17, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_134 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 14, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 14, 17, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 14, 17, 24, 35]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_135 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 14, 17, 24, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 14, 17, 24, 35]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 14, 17, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_136 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 14, 17, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 14, 17, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 16, 19, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_137 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 16, 19, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 16, 19, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 16, 21, 24, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_138 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 16, 21, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 16, 21, 24, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 17, 21, 24, 35]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_139 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 17, 21, 24, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 17, 21, 24, 35]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 17, 24, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_140 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 17, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 17, 24, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 18, 24, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_141 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 18, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 18, 24, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 10, 21, 24, 32, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_142 : ∃ k : ℕ, Lonely 8 (([3, 4, 10, 21, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 10, 21, 24, 32, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 12, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_143 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 12, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 14, 15, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_144 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 14, 15, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 14, 16, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_145 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 14, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 14, 16, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 14, 20, 24, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_146 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 14, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 14, 20, 24, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 14, 20, 32, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_147 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 14, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 14, 20, 32, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 15, 17, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_148 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 15, 17, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 15, 17, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 15, 19, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_149 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 15, 19, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 15, 19, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 15, 19, 28, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_150 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 15, 19, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 15, 19, 28, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 11, 15, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_151 : ∃ k : ℕ, Lonely 8 (([3, 4, 11, 15, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 11, 15, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 12, 15, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_152 : ∃ k : ℕ, Lonely 8 (([3, 4, 12, 15, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 12, 15, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 13, 14, 22, 35, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_153 : ∃ k : ℕ, Lonely 8 (([3, 4, 13, 14, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 13, 14, 22, 35, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 13, 15, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_154 : ∃ k : ℕ, Lonely 8 (([3, 4, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 13, 15, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 13, 17, 20, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_155 : ∃ k : ℕ, Lonely 8 (([3, 4, 13, 17, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 13, 17, 20, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 13, 17, 21, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_156 : ∃ k : ℕ, Lonely 8 (([3, 4, 13, 17, 21, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 13, 17, 21, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 13, 19, 21, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_157 : ∃ k : ℕ, Lonely 8 (([3, 4, 13, 19, 21, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 13, 19, 21, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 16, 17, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_158 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 16, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 16, 17, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 16, 20, 23, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_159 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 16, 20, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 16, 20, 23, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 17, 20, 24, 25]`, flank `14`, opening `12`.  Covers 2 census rows. -/
theorem fam_3_160 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 17, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨12, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 17, 20, 24, 25]) (e := 14) (k := 12)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 17, 20, 24, 40]`, flank `14`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_161 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 17, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 17, 20, 24, 40]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 17, 20, 32, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_162 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 17, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 17, 20, 32, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 17, 21, 25, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_163 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 17, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 17, 21, 25, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 18, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_164 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 18, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 18, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 18, 22, 25, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_165 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 18, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 18, 22, 25, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 20, 23, 24, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_166 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 20, 23, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 20, 23, 24, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 20, 23, 32, 40]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_167 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 20, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 20, 23, 32, 40]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 14, 22, 25, 26, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_168 : ∃ k : ℕ, Lonely 8 (([3, 4, 14, 22, 25, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 14, 22, 25, 26, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 15, 19, 21, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_169 : ∃ k : ℕ, Lonely 8 (([3, 4, 15, 19, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 15, 19, 21, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 15, 21, 25, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_170 : ∃ k : ℕ, Lonely 8 (([3, 4, 15, 21, 25, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 15, 21, 25, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 17, 21, 25, 33, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_171 : ∃ k : ℕ, Lonely 8 (([3, 4, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 17, 21, 25, 33, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 20, 24, 28, 33, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_172 : ∃ k : ℕ, Lonely 8 (([3, 4, 20, 24, 28, 33, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 20, 24, 28, 33, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 20, 24, 28, 34, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_173 : ∃ k : ℕ, Lonely 8 (([3, 4, 20, 24, 28, 34, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 20, 24, 28, 34, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 20, 24, 28, 37, 38]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_174 : ∃ k : ℕ, Lonely 8 (([3, 4, 20, 24, 28, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 20, 24, 28, 37, 38]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 4, 28, 31, 34, 40, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_175 : ∃ k : ℕ, Lonely 8 (([3, 4, 28, 31, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 4, 28, 31, 34, 40, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 7, 11, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_176 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 7, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 7, 11, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 7, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_177 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 7, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 7, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 11, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_178 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 11, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 11, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 11, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_179 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 11, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 11, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 11, 16, 21, 33]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_180 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 11, 16, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 11, 16, 21, 33]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 14, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_181 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 14, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 16, 21, 22, 33]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_182 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 16, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 16, 21, 22, 33]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 6, 16, 21, 26, 52]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_183 : ∃ k : ℕ, Lonely 8 (([3, 5, 6, 16, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 6, 16, 21, 26, 52]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 10, 15, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_184 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 10, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 10, 15, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 11, 15, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_185 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 11, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 11, 15, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 11, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_186 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 11, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 11, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 12, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_187 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 12, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 12, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 12, 21, 25]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_188 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 12, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 12, 21, 25]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 12, 23, 25]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_189 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 12, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 12, 23, 25]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 21, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_190 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 21, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 22, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_191 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 22, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_192 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 23, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_193 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 23, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 24, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_194 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 24, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 13, 25, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_195 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 13, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 13, 25, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 15, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_196 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 15, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 15, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 8, 17, 23, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_197 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 8, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 8, 17, 23, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 11, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_198 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 11, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 11, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 12, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_199 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 12, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 12, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 12, 15, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_200 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 12, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 12, 15, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 12, 17, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_201 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 12, 17, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 12, 17, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 12, 19, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_202 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 12, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 12, 19, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 12, 19, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_203 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 12, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 12, 19, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 15, 24, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_204 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 15, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 15, 24, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 17, 24, 36]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_205 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 17, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 17, 24, 36]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 9, 19, 24, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_206 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 9, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 9, 19, 24, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 11, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_207 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 11, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 12, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_208 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 12, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 12, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_209 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 15, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_210 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 15, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 15, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_211 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 10, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_212 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 10, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 10, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 12, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_213 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 12, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 12, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 13, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_214 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 13, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 13, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 14, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_215 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 14, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 14, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_216 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 15, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_217 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 15, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 15, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_218 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_219 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_220 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 17, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_221 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 17, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 17, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 17, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_222 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 17, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 17, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_223 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 11, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_224 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 11, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 11, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 15, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_225 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 15, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 15, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_226 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 15, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 18, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_227 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 18, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 19, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_228 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 19, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 20, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_229 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 20, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 22, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_230 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 22, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_231 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 27, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_232 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 27, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 27, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 27, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_233 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 27, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 30, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_234 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 30, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 31, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_235 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 31, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 31, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 17, 31, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_236 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 17, 31, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 18, 19, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_237 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 18, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 18, 19, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 12, 19, 27, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_238 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 12, 19, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 12, 19, 27, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 15, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_239 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 15, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 15, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_240 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 16, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_241 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 16, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 18, 19, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_242 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 18, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 18, 19, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 19, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_243 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 19, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 19, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 19, 20, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_244 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 19, 20, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 19, 20, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 19, 22, 38]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_245 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 19, 22, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 19, 22, 38]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 13, 19, 24, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_246 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 13, 19, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 13, 19, 24, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 14, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_247 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 14, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 14, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 15, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_248 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 15, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 15, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 15, 21, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_249 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 15, 21, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 15, 21, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 16, 17, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_250 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 16, 17, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 16, 17, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 16, 17, 23, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_251 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 16, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 16, 17, 23, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 16, 21, 26, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_252 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 16, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 16, 21, 26, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 16, 21, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_253 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 16, 21, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 16, 21, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 16, 21, 30, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_254 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 16, 21, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 16, 21, 30, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 18, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_255 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 18, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 18, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 18, 24, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_256 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 18, 24, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 20, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_257 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 20, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 20, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 20, 27, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_258 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 20, 27, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 22, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_259 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 22, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 22, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 23, 24, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_260 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 23, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 23, 24, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 23, 26, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_261 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 23, 26, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 23, 26, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 23, 28, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_262 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 23, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 23, 28, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 23, 30, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_263 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 23, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 23, 30, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 23, 32, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_264 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 23, 32, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 23, 32, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 17, 24, 27, 36]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_265 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 17, 24, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 17, 24, 27, 36]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 18, 19, 24, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_266 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 18, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 18, 19, 24, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 7, 19, 24, 27, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_267 : ∃ k : ℕ, Lonely 8 (([3, 5, 7, 19, 24, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 7, 19, 24, 27, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 11, 12, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_268 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 11, 12, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 11, 12, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 11, 13, 21, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_269 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 11, 13, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 11, 13, 21, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 11, 13, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_270 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 11, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 11, 13, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 11, 14, 19, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_271 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 11, 14, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 11, 14, 19, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 11, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_272 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 11, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 11, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 12, 13, 21, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_273 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 12, 13, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 12, 13, 21, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 12, 21, 31, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_274 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 12, 21, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 12, 21, 31, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 14, 22, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_275 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 14, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 14, 22, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 14, 23, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_276 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 14, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 14, 23, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 15, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_277 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 15, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 18, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_278 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 18, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 18, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 18, 21, 31]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_279 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 18, 21, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 18, 21, 31]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 18, 21, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_280 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 18, 21, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 21, 22, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_281 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 21, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 21, 22, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 21, 23, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_282 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 21, 23, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 13, 21, 29, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_283 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 13, 21, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 13, 21, 29, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 14, 19, 22, 44]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_284 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 14, 19, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 14, 19, 22, 44]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 8, 21, 31, 41, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_285 : ∃ k : ℕ, Lonely 8 (([3, 5, 8, 21, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 8, 21, 31, 41, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 9, 12, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_286 : ∃ k : ℕ, Lonely 8 (([3, 5, 9, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 9, 12, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 9, 12, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_287 : ∃ k : ℕ, Lonely 8 (([3, 5, 9, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 9, 12, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 9, 12, 15, 21, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_288 : ∃ k : ℕ, Lonely 8 (([3, 5, 9, 12, 15, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 9, 12, 15, 21, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 9, 14, 15, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_289 : ∃ k : ℕ, Lonely 8 (([3, 5, 9, 14, 15, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 9, 14, 15, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 9, 14, 17, 24, 28]`, flank `9`, opening `8`.  Covers 2 census rows. -/
theorem fam_3_290 : ∃ k : ℕ, Lonely 8 (([3, 5, 9, 14, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 9, 14, 17, 24, 28]) (e := 9) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 10, 11, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_291 : ∃ k : ℕ, Lonely 8 (([3, 5, 10, 11, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 10, 11, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 10, 12, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_292 : ∃ k : ℕ, Lonely 8 (([3, 5, 10, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 10, 12, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 10, 12, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_293 : ∃ k : ℕ, Lonely 8 (([3, 5, 10, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 10, 12, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 10, 12, 15, 21, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_294 : ∃ k : ℕ, Lonely 8 (([3, 5, 10, 12, 15, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 10, 12, 15, 21, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 12, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_295 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 12, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 12, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 12, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_296 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 12, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 12, 16, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_297 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 12, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 12, 16, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 13, 16, 21, 24]`, flank `11`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_298 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 13, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 13, 16, 21, 24]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 13, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_299 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 13, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 13, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_300 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 16, 19, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_301 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 16, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 16, 19, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 16, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_302 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 16, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 16, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_303 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_304 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_305 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_306 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 14, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_307 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 14, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 15, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_308 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 15, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 15, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 15, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_309 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 15, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 15, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 16, 19, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_310 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 16, 19, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 16, 19, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 11, 16, 19, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_311 : ∃ k : ℕ, Lonely 8 (([3, 5, 11, 16, 19, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 11, 16, 19, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 13, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_312 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 13, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 13, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 13, 16, 21, 24]`, flank `12`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_313 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 13, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 13, 16, 21, 24]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 15, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_314 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 15, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 17, 18, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_315 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 17, 18, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 18, 19, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_316 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 18, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 18, 19, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 19, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_317 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 19, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 19, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_318 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 14, 19, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_319 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 14, 19, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 14, 19, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 12, 15, 19, 21, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_320 : ∃ k : ℕ, Lonely 8 (([3, 5, 12, 15, 19, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 12, 15, 19, 21, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 14, 15, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_321 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 14, 15, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 14, 15, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 14, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_322 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 14, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 14, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 14, 16, 23, 24]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_323 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 14, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 14, 16, 23, 24]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 15, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_324 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 15, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 15, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 18, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_325 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 18, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 18, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 21, 22, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_326 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 21, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 21, 22, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 21, 23, 24]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_327 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 21, 23, 24]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 21, 25, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_328 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 21, 25, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 21, 25, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 21, 29, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_329 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 21, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 21, 29, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 16, 21, 29, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_330 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 16, 21, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 16, 21, 29, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 18, 21, 31, 54]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_331 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 18, 21, 31, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 18, 21, 31, 54]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 18, 23, 28, 36]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_332 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 18, 23, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 18, 23, 28, 36]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 21, 24, 29, 40]`, flank `21`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_333 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 21, 24, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 21, 24, 29, 40]) (e := 21) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 21, 29, 32, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_334 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 21, 29, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 21, 29, 32, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 13, 21, 31, 36, 54]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_335 : ∃ k : ℕ, Lonely 8 (([3, 5, 13, 21, 31, 36, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 13, 21, 31, 36, 54]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 15, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_336 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 15, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 15, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 17, 18, 24, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_337 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 17, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 17, 18, 24, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 17, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_338 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 17, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 17, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 17, 20, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_339 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 17, 20, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 17, 20, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 17, 20, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_340 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 17, 20, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 17, 20, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 18, 19, 24, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_341 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 18, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 18, 19, 24, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 19, 23, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_342 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 19, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 19, 23, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 20, 23, 25, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_343 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 20, 23, 25, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 20, 23, 25, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 14, 22, 25, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_344 : ∃ k : ℕ, Lonely 8 (([3, 5, 14, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 14, 22, 25, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 15, 20, 21, 25, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_345 : ∃ k : ℕ, Lonely 8 (([3, 5, 15, 20, 21, 25, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 15, 20, 21, 25, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 18, 21, 26, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_346 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 18, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 18, 21, 26, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 19, 22, 42, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_347 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 19, 22, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 19, 22, 42, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 21, 23, 26, 52]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_348 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 21, 23, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 21, 23, 26, 52]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 21, 25, 26, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_349 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 21, 25, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 21, 25, 26, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 21, 26, 29, 52]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_350 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 21, 26, 29, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 21, 26, 29, 52]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 16, 21, 26, 35, 52]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_351 : ∃ k : ℕ, Lonely 8 (([3, 5, 16, 21, 26, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 16, 21, 26, 35, 52]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 17, 21, 26, 31, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_352 : ∃ k : ℕ, Lonely 8 (([3, 5, 17, 21, 26, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 17, 21, 26, 31, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 19, 22, 32, 42, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_353 : ∃ k : ℕ, Lonely 8 (([3, 5, 19, 22, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 19, 22, 32, 42, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 20, 23, 25, 28, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_354 : ∃ k : ℕ, Lonely 8 (([3, 5, 20, 23, 25, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 20, 23, 25, 28, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 21, 24, 26, 31, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_355 : ∃ k : ℕ, Lonely 8 (([3, 5, 21, 24, 26, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 21, 24, 26, 31, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 21, 26, 31, 41, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_356 : ∃ k : ℕ, Lonely 8 (([3, 5, 21, 26, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 21, 26, 31, 41, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 21, 30, 35, 40, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_357 : ∃ k : ℕ, Lonely 8 (([3, 5, 21, 30, 35, 40, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 21, 30, 35, 40, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 5, 21, 31, 34, 41, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_358 : ∃ k : ℕ, Lonely 8 (([3, 5, 21, 31, 34, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 5, 21, 31, 34, 41, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 8, 15, 22, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_359 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 8, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 8, 15, 22, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 10, 13, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_360 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 10, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 10, 13, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 10, 15, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_361 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 10, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 10, 15, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 13, 15, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_362 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 13, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 13, 15, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 15, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_363 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 15, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 15, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 7, 15, 22, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_364 : ∃ k : ℕ, Lonely 8 (([3, 6, 7, 15, 22, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 7, 15, 22, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 9, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_365 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 9, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 9, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 10, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_366 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 10, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 10, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 10, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_367 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 10, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 10, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_368 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 14, 15, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_369 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 14, 15, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 14, 15, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_370 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 14, 15, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 14, 15, 22, 24]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_371 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 14, 15, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 14, 15, 22, 24]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 8, 14, 15, 22, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_372 : ∃ k : ℕ, Lonely 8 (([3, 6, 8, 14, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 8, 14, 15, 22, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 9, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_373 : ∃ k : ℕ, Lonely 8 (([3, 6, 9, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 9, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 12, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_374 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 12, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 12, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_375 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 12, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 13, 14, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_376 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 13, 14, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_377 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 13, 14, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_378 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 13, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 13, 14, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 15, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_379 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 15, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_380 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 15, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_381 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 15, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 15, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_382 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 15, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_383 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 10, 14, 19, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_384 : ∃ k : ℕ, Lonely 8 (([3, 6, 10, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 10, 14, 19, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 13, 14, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_385 : ∃ k : ℕ, Lonely 8 (([3, 6, 13, 14, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 13, 14, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 13, 14, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_386 : ∃ k : ℕ, Lonely 8 (([3, 6, 13, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 13, 14, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 13, 14, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_387 : ∃ k : ℕ, Lonely 8 (([3, 6, 13, 14, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 13, 14, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 13, 14, 20, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_388 : ∃ k : ℕ, Lonely 8 (([3, 6, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 13, 14, 20, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 13, 15, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_389 : ∃ k : ℕ, Lonely 8 (([3, 6, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 13, 15, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 14, 15, 16, 22, 24]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_390 : ∃ k : ℕ, Lonely 8 (([3, 6, 14, 15, 16, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 14, 15, 16, 22, 24]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 14, 15, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_391 : ∃ k : ℕ, Lonely 8 (([3, 6, 14, 15, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 14, 15, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 14, 15, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_392 : ∃ k : ℕ, Lonely 8 (([3, 6, 14, 15, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 14, 15, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 14, 19, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_393 : ∃ k : ℕ, Lonely 8 (([3, 6, 14, 19, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 14, 19, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 15, 18, 21, 24, 26]`, flank `15`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_394 : ∃ k : ℕ, Lonely 8 (([3, 6, 15, 18, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 15, 18, 21, 24, 26]) (e := 15) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 15, 22, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_395 : ∃ k : ℕ, Lonely 8 (([3, 6, 15, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 15, 22, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 6, 17, 19, 21, 25, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_396 : ∃ k : ℕ, Lonely 8 (([3, 6, 17, 19, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 6, 17, 19, 21, 25, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 9, 16, 25, 27]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_397 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 9, 16, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 9, 16, 25, 27]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 11, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_398 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 11, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 11, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 12, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_399 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 12, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 12, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 12, 21, 25]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_400 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 12, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 12, 21, 25]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 12, 23, 25]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_401 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 12, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 12, 23, 25]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 13, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_402 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 13, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 13, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 13, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_403 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 13, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 13, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 13, 21, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_404 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 13, 21, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 13, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_405 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 13, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 13, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 14, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_406 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 14, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 14, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 17, 23, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_407 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 17, 23, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 17, 24, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_408 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 17, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 17, 24, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 10, 17, 25, 34]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_409 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 10, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 10, 17, 25, 34]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 11, 13, 25, 26]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_410 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 11, 13, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 11, 13, 25, 26]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 11, 15, 22, 26]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_411 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 11, 15, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 11, 15, 22, 26]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 15, 21, 25]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_412 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 15, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 15, 21, 25]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 15, 23, 25]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_413 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 15, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 15, 23, 25]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 17, 20, 25]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_414 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 17, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 17, 20, 25]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 19, 20, 25]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_415 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 19, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 19, 20, 25]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 20, 21, 25]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_416 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 20, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 20, 21, 25]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 12, 20, 23, 25]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_417 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 12, 20, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 12, 20, 23, 25]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 15, 21, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_418 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 15, 21, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 15, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_419 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 15, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 15, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 16, 25, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_420 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 16, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 16, 25, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_421 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 20, 21, 26]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_422 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 20, 21, 26]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 20, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_423 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 20, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 13, 21, 25, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_424 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 13, 21, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 13, 21, 25, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 15, 19, 22, 44]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_425 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 15, 19, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 15, 19, 22, 44]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 15, 22, 25, 44]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_426 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 15, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 15, 22, 25, 44]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 15, 22, 31, 44]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_427 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 15, 22, 31, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 15, 22, 31, 44]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 15, 22, 42, 43]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_428 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 15, 22, 42, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 15, 22, 42, 43]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 16, 18, 25, 27]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_429 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 16, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 16, 18, 25, 27]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 17, 20, 27, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_430 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 17, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 17, 20, 27, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 8, 17, 25, 33, 34]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_431 : ∃ k : ℕ, Lonely 8 (([3, 7, 8, 17, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 8, 17, 25, 33, 34]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 10, 11, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_432 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 10, 11, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 10, 11, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 10, 11, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_433 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 10, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 10, 11, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 10, 11, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_434 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 10, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 10, 11, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 10, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_435 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 10, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 10, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 10, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_436 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 10, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 10, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 11, 13, 20, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_437 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 11, 13, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 11, 13, 20, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 11, 15, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_438 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 11, 15, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 11, 15, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 11, 16, 25, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_439 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 11, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 11, 16, 25, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 12, 13, 20, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_440 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 12, 13, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 12, 13, 20, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 12, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_441 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 12, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 12, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 12, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_442 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 12, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 13, 20, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_443 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 13, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 13, 20, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 15, 16, 22, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_444 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 15, 16, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 15, 16, 22, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 9, 15, 16, 23, 26]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_445 : ∃ k : ℕ, Lonely 8 (([3, 7, 9, 15, 16, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 9, 15, 16, 23, 26]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_446 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 16, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_447 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 16, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 16, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_448 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_449 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_450 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 19, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_451 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 19, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_452 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 24, 26]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_453 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 24, 26]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 13, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_454 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 13, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 13, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 14, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_455 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 14, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 14, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 17, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_456 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 17, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 17, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 11, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_457 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 11, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 11, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 12, 13, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_458 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 12, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 12, 13, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 12, 15, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_459 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 12, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 12, 15, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 12, 15, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_460 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 12, 15, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 12, 15, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 12, 17, 18, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_461 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 12, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 12, 17, 18, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 12, 18, 19, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_462 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 12, 18, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 12, 18, 19, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 17, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_463 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 17, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 17, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_464 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 17, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 18, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_465 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 18, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_466 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_467 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 15, 29, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_468 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 15, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 15, 29, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_469 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_470 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 23, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_471 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 23, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 23, 28]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_472 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 23, 28]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 23, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_473 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 23, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 16, 23, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_474 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 16, 23, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 16, 23, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 19, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_475 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 19, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 19, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_476 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 19, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_477 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_478 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_479 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 23, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_480 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 23, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 23, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 27, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_481 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 27, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 27, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_482 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 27, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 27, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 17, 31, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_483 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 17, 31, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 23, 33, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_484 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 23, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 23, 33, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 13, 23, 33, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_485 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 13, 23, 33, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 13, 23, 33, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 14, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_486 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 14, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 14, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_487 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 14, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 14, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 14, 17, 24, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_488 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 14, 17, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 14, 17, 24, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 15, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_489 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 15, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 15, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 15, 17, 18, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_490 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 15, 17, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 15, 17, 18, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 15, 17, 19, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_491 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 15, 17, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 15, 17, 19, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 15, 17, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_492 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 15, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 15, 17, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 15, 17, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_493 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 15, 17, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 15, 17, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 16, 17, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_494 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 16, 17, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 16, 17, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 16, 17, 23, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_495 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 16, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 16, 17, 23, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 16, 23, 26, 52]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_496 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 16, 23, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 16, 23, 26, 52]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 18, 24, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_497 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 18, 24, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 19, 28, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_498 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 19, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 19, 28, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 21, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_499 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 21, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 21, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 23, 24, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_500 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 23, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 23, 24, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 23, 29, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_501 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 23, 29, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 23, 29, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 23, 32, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_502 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 23, 32, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 23, 32, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 27, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_503 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 27, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 27, 35]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_504 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 27, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 27, 35]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 27, 48]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_505 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 27, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 27, 48]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 27, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_506 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 27, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 27, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 31, 34]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_507 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 31, 34]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 17, 24, 31, 35]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_508 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 17, 24, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 17, 24, 31, 35]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 18, 19, 24, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_509 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 18, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 18, 19, 24, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 10, 24, 27, 34, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_510 : ∃ k : ℕ, Lonely 8 (([3, 7, 10, 24, 27, 34, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 10, 24, 27, 34, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 15, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_511 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 15, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 15, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 15, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_512 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 15, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 15, 28, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_513 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 15, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 15, 28, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 16, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_514 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 16, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 16, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_515 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 18, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_516 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 18, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 18, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 19, 20, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_517 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 19, 20, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 19, 20, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 13, 19, 30, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_518 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 13, 19, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 13, 19, 30, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 14, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_519 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 14, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 14, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 14, 17, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_520 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 14, 17, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 14, 17, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 14, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_521 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 14, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 14, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 15, 17, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_522 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 15, 17, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 15, 17, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 15, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_523 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 15, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 15, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 17, 18, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_524 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 17, 18, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 17, 18, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 17, 18, 20, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_525 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 17, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 17, 18, 20, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 17, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_526 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 17, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 17, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 18, 19, 20, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_527 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 18, 19, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 18, 19, 20, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 18, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_528 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 18, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 18, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 11, 18, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_529 : ∃ k : ℕ, Lonely 8 (([3, 7, 11, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 11, 18, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 12, 13, 15, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_530 : ∃ k : ℕ, Lonely 8 (([3, 7, 12, 13, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 12, 13, 15, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 12, 15, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_531 : ∃ k : ℕ, Lonely 8 (([3, 7, 12, 15, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 12, 15, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 12, 15, 22, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_532 : ∃ k : ℕ, Lonely 8 (([3, 7, 12, 15, 22, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 12, 15, 22, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 12, 18, 25, 32, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_533 : ∃ k : ℕ, Lonely 8 (([3, 7, 12, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 12, 18, 25, 32, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 16, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_534 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 16, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 17, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_535 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 17, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 18, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_536 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 18, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 18, 33, 34]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_537 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 18, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 18, 33, 34]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 20, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_538 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 20, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 20, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 20, 24, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_539 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 20, 24, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 20, 29, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_540 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 20, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 20, 29, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 15, 22, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_541 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 15, 22, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 15, 22, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 19, 20, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_542 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 19, 20, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 19, 20, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 19, 25, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_543 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 19, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 19, 25, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 20, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_544 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 20, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 20, 23, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_545 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 20, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 20, 23, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 20, 23, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_546 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 20, 23, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 20, 23, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 23, 30, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_547 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 23, 30, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 23, 30, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 23, 40, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_548 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 23, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 23, 40, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 16, 25, 29, 48]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_549 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 16, 25, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 16, 25, 29, 48]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 19, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_550 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 19, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 19, 20, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_551 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 19, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 19, 20, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 21, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_552 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 21, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 21, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 23, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_553 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 23, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_554 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 23, 40]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_555 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 23, 40]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 23, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_556 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 23, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 23, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 25, 40]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_557 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 25, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 25, 40]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 27, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_558 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 27, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 20, 27, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_559 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 20, 27, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 23, 30, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_560 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 23, 30, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 23, 30, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 17, 23, 40, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_561 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 17, 23, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 17, 23, 40, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 19, 20, 27, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_562 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 19, 20, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 19, 20, 27, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 20, 23, 32, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_563 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 20, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 20, 23, 32, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 20, 23, 33, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_564 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 20, 23, 33, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 20, 23, 33, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 23, 30, 33, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_565 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 23, 30, 33, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 23, 30, 33, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 23, 33, 40, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_566 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 23, 33, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 23, 33, 40, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 13, 25, 29, 32, 48]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_567 : ∃ k : ℕ, Lonely 8 (([3, 7, 13, 25, 29, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 13, 25, 29, 32, 48]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 14, 17, 20, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_568 : ∃ k : ℕ, Lonely 8 (([3, 7, 14, 17, 20, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 14, 17, 20, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 14, 17, 20, 21, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_569 : ∃ k : ℕ, Lonely 8 (([3, 7, 14, 17, 20, 21, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 14, 17, 20, 21, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 18, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_570 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 18, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 19, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_571 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 19, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 19, 22, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_572 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 19, 22, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 19, 22, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 20, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_573 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 20, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 20, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_574 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 20, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_575 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 20, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 20, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 21, 24, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_576 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 21, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 21, 24, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 17, 23, 24, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_577 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 17, 23, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 17, 23, 24, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 18, 21, 24, 26]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_578 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 18, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 18, 21, 24, 26]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 18, 22, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_579 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 18, 22, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 18, 22, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 19, 22, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_580 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 19, 22, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 19, 22, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 22, 24, 29, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_581 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 22, 24, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 22, 24, 29, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 15, 22, 25, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_582 : ∃ k : ℕ, Lonely 8 (([3, 7, 15, 22, 25, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 15, 22, 25, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 16, 17, 20, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_583 : ∃ k : ℕ, Lonely 8 (([3, 7, 16, 17, 20, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 16, 17, 20, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 16, 17, 20, 27, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_584 : ∃ k : ℕ, Lonely 8 (([3, 7, 16, 17, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 16, 17, 20, 27, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 16, 17, 23, 30, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_585 : ∃ k : ℕ, Lonely 8 (([3, 7, 16, 17, 23, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 16, 17, 23, 30, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 16, 18, 25, 34, 36]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_586 : ∃ k : ℕ, Lonely 8 (([3, 7, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 16, 18, 25, 34, 36]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 16, 19, 22, 30, 32]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_587 : ∃ k : ℕ, Lonely 8 (([3, 7, 16, 19, 22, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 16, 19, 22, 30, 32]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 19, 20, 28, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_588 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 19, 20, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 19, 20, 28, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 21, 27, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_589 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 21, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 21, 27, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 23, 24, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_590 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 23, 24, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 23, 24, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 23, 29, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_591 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 23, 29, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 23, 29, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 24, 27, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_592 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 24, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 24, 27, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 24, 27, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_593 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 24, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 24, 27, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 27, 29, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_594 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 27, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 27, 29, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 27, 32, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_595 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 27, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 27, 32, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 20, 27, 37, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_596 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 20, 27, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 20, 27, 37, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 23, 24, 25, 34]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_597 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 23, 24, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 23, 24, 25, 34]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 23, 24, 30, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_598 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 23, 24, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 23, 24, 30, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 17, 23, 29, 30, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_599 : ∃ k : ℕ, Lonely 8 (([3, 7, 17, 23, 29, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 17, 23, 29, 30, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 22, 25, 32, 36]`, flank `18`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_600 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 22, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 22, 25, 32, 36]) (e := 18) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 22, 29, 40, 44]`, flank `18`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_601 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 22, 29, 40, 44]) (e := 18) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 23, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_602 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 23, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 23, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 24, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_603 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 24, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 24, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 25, 32, 34, 36]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_604 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 25, 32, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 25, 32, 34, 36]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 18, 25, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_605 : ∃ k : ℕ, Lonely 8 (([3, 7, 18, 25, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 18, 25, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 22, 25, 29, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_606 : ∃ k : ℕ, Lonely 8 (([3, 7, 22, 25, 29, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 22, 25, 29, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 7, 24, 33, 40, 47, 48]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_607 : ∃ k : ℕ, Lonely 8 (([3, 7, 24, 33, 40, 47, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 7, 24, 33, 40, 47, 48]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 9, 11, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_608 : ∃ k : ℕ, Lonely 8 (([3, 8, 9, 11, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 9, 11, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 9, 12, 15, 21, 29]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_609 : ∃ k : ℕ, Lonely 8 (([3, 8, 9, 12, 15, 21, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 9, 12, 15, 21, 29]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 9, 14, 15, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_610 : ∃ k : ℕ, Lonely 8 (([3, 8, 9, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 9, 14, 15, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 11, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_611 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 11, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 11, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 11, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_612 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 11, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 11, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 11, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_613 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 11, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 11, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 11, 14, 19, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_614 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 11, 14, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 11, 14, 19, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 11, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_615 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 11, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 11, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 13, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_616 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 13, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 13, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 13, 14, 23, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_617 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 13, 14, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 13, 14, 23, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 13, 18, 21, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_618 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 13, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 13, 18, 21, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 14, 15, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_619 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 14, 15, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 14, 17, 22, 28]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_620 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 14, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 14, 17, 22, 28]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 14, 17, 26, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_621 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 14, 17, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 14, 17, 26, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 14, 19, 22, 44]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_622 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 14, 19, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 14, 19, 22, 44]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 10, 21, 31, 41, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_623 : ∃ k : ℕ, Lonely 8 (([3, 8, 10, 21, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 10, 21, 31, 41, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 12, 14, 20, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_624 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 12, 14, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 12, 14, 20, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_625 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 13, 19, 35, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_626 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 13, 19, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 13, 19, 35, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 13, 19, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_627 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 13, 19, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 13, 19, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 15, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_628 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 15, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 15, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_629 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 15, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 16, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_630 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 16, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 16, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 17, 20, 22]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_631 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 17, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 17, 20, 22]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_632 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 17, 25, 33]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_633 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 17, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 17, 25, 33]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 17, 25, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_634 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 17, 25, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 18, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_635 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 18, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 18, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_636 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 19, 25, 28]`, flank `8`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_637 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 19, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 19, 25, 28]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 19, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_638 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 19, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 19, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 14, 19, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_639 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 14, 19, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 14, 19, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 15, 19, 21, 33]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_640 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 15, 19, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 15, 19, 21, 33]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 17, 25, 28, 30]`, flank `11`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_641 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 17, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 17, 25, 28, 30]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 19, 21, 30, 33]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_642 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 19, 21, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 19, 21, 30, 33]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 19, 27, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_643 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 19, 27, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 19, 27, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 11, 19, 28, 30, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_644 : ∃ k : ℕ, Lonely 8 (([3, 8, 11, 19, 28, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 11, 19, 28, 30, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 13, 14, 20, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_645 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 13, 14, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 13, 14, 20, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 13, 15, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_646 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 13, 15, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 14, 15, 20, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_647 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 14, 15, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 14, 15, 20, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 14, 15, 22, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_648 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 14, 15, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 14, 15, 22, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 14, 17, 20, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_649 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 14, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 14, 17, 20, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 14, 20, 21, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_650 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 14, 20, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 14, 20, 21, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 12, 20, 21, 28, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_651 : ∃ k : ℕ, Lonely 8 (([3, 8, 12, 20, 21, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 12, 20, 21, 28, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 13, 15, 17, 21, 26]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_652 : ∃ k : ℕ, Lonely 8 (([3, 8, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 13, 15, 17, 21, 26]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 13, 15, 19, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_653 : ∃ k : ℕ, Lonely 8 (([3, 8, 13, 15, 19, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 13, 15, 19, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 13, 15, 21, 24, 26]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_654 : ∃ k : ℕ, Lonely 8 (([3, 8, 13, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 13, 15, 21, 24, 26]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 15, 17, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_655 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 15, 17, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 15, 17, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 15, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_656 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 15, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 15, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 15, 18, 22, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_657 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 15, 18, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 15, 18, 22, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 15, 19, 22, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_658 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 15, 19, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 15, 19, 22, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 15, 22, 25, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_659 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 15, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 15, 22, 25, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 16, 22, 25, 33]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_660 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 16, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 16, 22, 25, 33]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 20, 22, 28]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_661 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 20, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 20, 22, 28]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 20, 24, 28]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_662 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 20, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 20, 24, 28]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 20, 48, 60]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_663 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 20, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 20, 48, 60]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 22, 25, 33]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_664 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 22, 25, 33]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 22, 25, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_665 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 22, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 22, 25, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 22, 25, 44]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_666 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 22, 25, 44]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 17, 40, 48, 60]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_667 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 17, 40, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 17, 40, 48, 60]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 18, 20, 23, 25]`, flank `8`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_668 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 18, 20, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 18, 20, 23, 25]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 18, 22, 25, 33]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_669 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 18, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 18, 22, 25, 33]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 20, 22, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_670 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 20, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 20, 22, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 22, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_671 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 22, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 22, 25, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_672 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 22, 25, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 22, 30, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_673 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 22, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 22, 30, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 22, 35, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_674 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 22, 35, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 19, 22, 40, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_675 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 19, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 19, 22, 40, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 21, 22, 25, 44]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_676 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 21, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 21, 22, 25, 44]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 21, 22, 30, 42]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_677 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 21, 22, 30, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 21, 22, 30, 42]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 22, 23, 25, 44]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_678 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 22, 23, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 22, 23, 25, 44]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 22, 25, 36, 44]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_679 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 22, 25, 36, 44]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 22, 25, 38, 44]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_680 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 22, 25, 38, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 22, 25, 38, 44]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 22, 25, 40, 44]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_681 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 22, 25, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 22, 25, 40, 44]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 14, 22, 25, 42, 44]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_682 : ∃ k : ℕ, Lonely 8 (([3, 8, 14, 22, 25, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 14, 22, 25, 42, 44]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 15, 19, 21, 22, 33]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_683 : ∃ k : ℕ, Lonely 8 (([3, 8, 15, 19, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 15, 19, 21, 22, 33]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 17, 18, 26, 35, 36]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_684 : ∃ k : ℕ, Lonely 8 (([3, 8, 17, 18, 26, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 17, 18, 26, 35, 36]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 17, 22, 25, 28, 30]`, flank `17`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_685 : ∃ k : ℕ, Lonely 8 (([3, 8, 17, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 17, 22, 25, 28, 30]) (e := 17) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 18, 22, 25, 28, 35]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_686 : ∃ k : ℕ, Lonely 8 (([3, 8, 18, 22, 25, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 18, 22, 25, 28, 35]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 19, 21, 22, 30, 33]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_687 : ∃ k : ℕ, Lonely 8 (([3, 8, 19, 21, 22, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 19, 21, 22, 30, 33]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 19, 22, 28, 30, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_688 : ∃ k : ℕ, Lonely 8 (([3, 8, 19, 22, 28, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 19, 22, 28, 30, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 19, 22, 30, 42, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_689 : ∃ k : ℕ, Lonely 8 (([3, 8, 19, 22, 30, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 19, 22, 30, 42, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 8, 21, 22, 28, 30, 42]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_690 : ∃ k : ℕ, Lonely 8 (([3, 8, 21, 22, 28, 30, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 8, 21, 22, 28, 30, 42]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 12, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_691 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 12, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 13, 14, 15, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_692 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 13, 14, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 13, 14, 15, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_693 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 13, 15, 28, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_694 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 13, 15, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 13, 15, 28, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 14, 15, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_695 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 14, 15, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 14, 15, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_696 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 14, 15, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 14, 15, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 11, 15, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_697 : ∃ k : ℕ, Lonely 8 (([3, 9, 11, 15, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 11, 15, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 12, 13, 15, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_698 : ∃ k : ℕ, Lonely 8 (([3, 9, 12, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 12, 13, 15, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 12, 13, 15, 21, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_699 : ∃ k : ℕ, Lonely 8 (([3, 9, 12, 13, 15, 21, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 12, 13, 15, 21, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 12, 14, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_700 : ∃ k : ℕ, Lonely 8 (([3, 9, 12, 14, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 12, 14, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 12, 15, 21, 26, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_701 : ∃ k : ℕ, Lonely 8 (([3, 9, 12, 15, 21, 26, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 12, 15, 21, 26, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 13, 15, 21, 24, 26]`, flank `15`, opening `4`.  Covers 2 census rows. -/
theorem fam_3_702 : ∃ k : ℕ, Lonely 8 (([3, 9, 13, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 13, 15, 21, 24, 26]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 14, 15, 16, 23, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_703 : ∃ k : ℕ, Lonely 8 (([3, 9, 14, 15, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 14, 15, 16, 23, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 9, 15, 19, 28, 37, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_704 : ∃ k : ℕ, Lonely 8 (([3, 9, 15, 19, 28, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 9, 15, 19, 28, 37, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 12, 13, 14, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_705 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 12, 13, 14, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 12, 14, 15, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_706 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 12, 14, 15, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 12, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_707 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 12, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 12, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 12, 14, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_708 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 12, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 12, 14, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 14, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_709 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 14, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 14, 16, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_710 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 14, 16, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 14, 16, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 14, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_711 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 14, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 14, 24, 26]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_712 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 14, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 14, 24, 26]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 14, 24, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_713 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 14, 24, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 16, 21, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_714 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 16, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 16, 21, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_715 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 13, 21, 24, 26]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_716 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 13, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 13, 21, 24, 26]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 15, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_717 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 15, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 15, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_718 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 15, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 15, 24, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_719 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 15, 24, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 16, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_720 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 16, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 16, 19, 24]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_721 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 16, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 16, 19, 24]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 16, 19, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_722 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 16, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 16, 19, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_723 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 16, 25, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_724 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 16, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 16, 25, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_725 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_726 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 14, 19, 24, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_727 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 14, 19, 24, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 11, 16, 19, 21, 33]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_728 : ∃ k : ℕ, Lonely 8 (([3, 10, 11, 16, 19, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 11, 16, 19, 21, 33]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 13, 14, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_729 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 13, 14, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 13, 14, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_730 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 13, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 13, 14, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 13, 14, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_731 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 13, 14, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 13, 14, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 13, 14, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_732 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 13, 14, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 13, 14, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 15, 16, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_733 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 15, 16, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 15, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_734 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 15, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 15, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_735 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 15, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 15, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_736 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 15, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 15, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 17, 18, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_737 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 17, 18, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 17, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_738 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 17, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 17, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_739 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 17, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 17, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 18, 19, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_740 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 18, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 18, 19, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 14, 19, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_741 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 14, 19, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 14, 19, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 12, 15, 21, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_742 : ∃ k : ℕ, Lonely 8 (([3, 10, 12, 15, 21, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 12, 15, 21, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 15, 16, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_743 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 15, 16, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 15, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_744 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 15, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 15, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_745 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 17, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_746 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 17, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_747 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 21, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_748 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 21, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 23, 24]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_749 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 23, 24]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 16, 23, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_750 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 16, 23, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 14, 17, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_751 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 14, 17, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 14, 17, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 15, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_752 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 15, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 15, 21, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_753 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 15, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 15, 21, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 15, 21, 24, 26]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_754 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 15, 21, 24, 26]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 15, 23, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_755 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 15, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 15, 23, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 16, 21, 23, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_756 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 16, 21, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 16, 21, 23, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 17, 21, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_757 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 17, 21, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 17, 21, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 13, 21, 23, 31, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_758 : ∃ k : ℕ, Lonely 8 (([3, 10, 13, 21, 23, 31, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 13, 21, 23, 31, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 15, 16, 17, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_759 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 15, 16, 17, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 15, 16, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_760 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 15, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 15, 16, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 15, 16, 23, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_761 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 15, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 15, 16, 23, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 15, 17, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_762 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 15, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 15, 17, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 15, 17, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_763 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 15, 17, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 15, 17, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 17, 19, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_764 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 17, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 17, 19, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 17, 22, 28]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_765 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 17, 22, 28]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 17, 26, 28]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_766 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 17, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 17, 26, 28]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 19, 26, 32]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_767 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 19, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 19, 26, 32]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 19, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_768 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 19, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 19, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 19, 30, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_769 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 19, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 19, 30, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 22, 25, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_770 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 22, 25, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 16, 23, 26, 52]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_771 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 16, 23, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 16, 23, 26, 52]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 17, 18, 24, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_772 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 17, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 17, 18, 24, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 17, 20, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_773 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 17, 20, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 17, 20, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 17, 24, 27, 35]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_774 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 17, 24, 27, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 17, 24, 27, 35]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 17, 24, 31, 35]`, flank `10`, opening `8`.  Covers 1 census rows. -/
theorem fam_3_775 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 17, 24, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 17, 24, 31, 35]) (e := 10) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 14, 18, 19, 24, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_776 : ∃ k : ℕ, Lonely 8 (([3, 10, 14, 18, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 14, 18, 19, 24, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 15, 17, 21, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_777 : ∃ k : ℕ, Lonely 8 (([3, 10, 15, 17, 21, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 15, 17, 21, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 15, 17, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_778 : ∃ k : ℕ, Lonely 8 (([3, 10, 15, 17, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 15, 17, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 18, 19, 28, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_779 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 18, 19, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 18, 19, 28, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 19, 21, 22, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_780 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 19, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 19, 21, 22, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 19, 22, 28, 32]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_781 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 19, 22, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 19, 22, 28, 32]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 19, 22, 42, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_782 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 19, 22, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 19, 22, 42, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 21, 22, 24, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_783 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 21, 22, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 21, 22, 24, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 21, 23, 26, 52]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_784 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 21, 23, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 21, 23, 26, 52]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 21, 24, 26, 48]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_785 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 21, 24, 26, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 21, 24, 26, 48]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 22, 25, 42, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_786 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 22, 25, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 22, 25, 42, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 16, 26, 29, 42, 52]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_787 : ∃ k : ℕ, Lonely 8 (([3, 10, 16, 26, 29, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 16, 26, 29, 42, 52]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 17, 21, 24, 27, 35]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_788 : ∃ k : ℕ, Lonely 8 (([3, 10, 17, 21, 24, 27, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 17, 21, 24, 27, 35]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 17, 21, 24, 31, 35]`, flank `17`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_789 : ∃ k : ℕ, Lonely 8 (([3, 10, 17, 21, 24, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 17, 21, 24, 31, 35]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 17, 24, 27, 28, 35]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_790 : ∃ k : ℕ, Lonely 8 (([3, 10, 17, 24, 27, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 17, 24, 27, 28, 35]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 17, 24, 28, 31, 35]`, flank `10`, opening `8`.  Covers 1 census rows. -/
theorem fam_3_791 : ∃ k : ℕ, Lonely 8 (([3, 10, 17, 24, 28, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 17, 24, 28, 31, 35]) (e := 10) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 19, 22, 32, 42, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_792 : ∃ k : ℕ, Lonely 8 (([3, 10, 19, 22, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 19, 22, 32, 42, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 22, 24, 32, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_793 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 22, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 22, 24, 32, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 22, 32, 43, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_794 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 22, 32, 43, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 23, 26, 31, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_795 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 23, 26, 31, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 23, 26, 31, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 24, 26, 32, 48]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_796 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 24, 26, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 24, 26, 32, 48]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 26, 31, 41, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_797 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 26, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 26, 31, 41, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 21, 31, 34, 41, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_798 : ∃ k : ℕ, Lonely 8 (([3, 10, 21, 31, 34, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 21, 31, 34, 41, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 22, 25, 32, 42, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_799 : ∃ k : ℕ, Lonely 8 (([3, 10, 22, 25, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 22, 25, 32, 42, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 22, 31, 32, 42, 44]`, flank `22`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_800 : ∃ k : ℕ, Lonely 8 (([3, 10, 22, 31, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 22, 31, 32, 42, 44]) (e := 22) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 23, 26, 35, 36, 52]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_801 : ∃ k : ℕ, Lonely 8 (([3, 10, 23, 26, 35, 36, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 23, 26, 35, 36, 52]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 10, 23, 26, 36, 49, 52]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_802 : ∃ k : ℕ, Lonely 8 (([3, 10, 23, 26, 36, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 10, 23, 26, 36, 49, 52]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 12, 13, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_803 : ∃ k : ℕ, Lonely 8 (([3, 11, 12, 13, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 12, 13, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 12, 14, 15, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_804 : ∃ k : ℕ, Lonely 8 (([3, 11, 12, 14, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 12, 14, 15, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 12, 14, 16, 20, 24]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_3_805 : ∃ k : ℕ, Lonely 8 (([3, 11, 12, 14, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 12, 14, 16, 20, 24]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 12, 14, 21, 25, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_806 : ∃ k : ℕ, Lonely 8 (([3, 11, 12, 14, 21, 25, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 12, 14, 21, 25, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 12, 21, 25, 28, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_807 : ∃ k : ℕ, Lonely 8 (([3, 11, 12, 21, 25, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 12, 21, 25, 28, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 15, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_808 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 15, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 15, 19, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_809 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 15, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 15, 19, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 16, 20, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_810 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 16, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 16, 20, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 17, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_811 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 17, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 17, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_812 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_813 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 19, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_814 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 19, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 19, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_815 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 14, 20, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_816 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 14, 20, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 15, 16, 28, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_817 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 15, 16, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 15, 16, 28, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 15, 19, 28, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_818 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 15, 19, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 15, 19, 28, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 15, 23, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_819 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 15, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 15, 23, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 15, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_820 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 15, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 15, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 16, 19, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_821 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 16, 19, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 16, 19, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 16, 20, 21, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_822 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 16, 20, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 16, 20, 21, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 17, 20, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_823 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 17, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 17, 20, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 19, 24, 35, 40]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_824 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 19, 24, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 19, 24, 35, 40]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 13, 19, 32, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_825 : ∃ k : ℕ, Lonely 8 (([3, 11, 13, 19, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 13, 19, 32, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 17, 18, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_826 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 17, 18, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 17, 18, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 17, 19, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_827 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 17, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 17, 19, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 17, 20, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_828 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 17, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 17, 20, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 17, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_829 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 17, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 17, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_830 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 19, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_831 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 19, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 19, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 15, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_832 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 15, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 15, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 16, 17, 20, 22]`, flank `11`, opening `8`.  Covers 2 census rows. -/
theorem fam_3_833 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 16, 17, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 16, 17, 20, 22]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 16, 19, 25, 50]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_834 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 16, 19, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 16, 19, 25, 50]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 16, 19, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_835 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 16, 19, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 16, 19, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 16, 25, 29, 50]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_836 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 16, 25, 29, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 16, 25, 29, 50]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 16, 25, 48, 50]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_837 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 16, 25, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 16, 25, 48, 50]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 17, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_838 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 17, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 17, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 17, 18, 20, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_839 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 17, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 17, 18, 20, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 17, 20, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_840 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 17, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 17, 20, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 17, 20, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_841 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 17, 20, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 17, 20, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 18, 19, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_842 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 18, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 18, 19, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 19, 20, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_843 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 19, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 19, 20, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 19, 20, 26, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_844 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 19, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 19, 20, 26, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 19, 24, 35, 40]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_845 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 19, 24, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 19, 24, 35, 40]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 14, 19, 32, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_846 : ∃ k : ℕ, Lonely 8 (([3, 11, 14, 19, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 14, 19, 32, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 17, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_847 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 17, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 17, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 17, 19, 28, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_848 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 17, 19, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 17, 19, 28, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 17, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_849 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 17, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 17, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 18, 19, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_850 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 18, 19, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 18, 19, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 19, 21, 28, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_851 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 19, 21, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 19, 21, 28, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 22, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_852 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 22, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 15, 25, 26, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_853 : ∃ k : ℕ, Lonely 8 (([3, 11, 15, 25, 26, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 15, 25, 26, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 16, 19, 27, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_854 : ∃ k : ℕ, Lonely 8 (([3, 11, 16, 19, 27, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 16, 19, 27, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 17, 20, 23, 28, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_855 : ∃ k : ℕ, Lonely 8 (([3, 11, 17, 20, 23, 28, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 17, 20, 23, 28, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 17, 28, 31, 40, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_856 : ∃ k : ℕ, Lonely 8 (([3, 11, 17, 28, 31, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 17, 28, 31, 40, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 19, 21, 25, 32, 50]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_857 : ∃ k : ℕ, Lonely 8 (([3, 11, 19, 21, 25, 32, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 19, 21, 25, 32, 50]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 19, 24, 27, 35, 40]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_858 : ∃ k : ℕ, Lonely 8 (([3, 11, 19, 24, 27, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 19, 24, 27, 35, 40]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 19, 27, 32, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_859 : ∃ k : ℕ, Lonely 8 (([3, 11, 19, 27, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 19, 27, 32, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 23, 24, 35, 47, 48]`, flank `11`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_860 : ∃ k : ℕ, Lonely 8 (([3, 11, 23, 24, 35, 47, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 23, 24, 35, 47, 48]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 24, 27, 35, 46, 48]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_861 : ∃ k : ℕ, Lonely 8 (([3, 11, 24, 27, 35, 46, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 24, 27, 35, 46, 48]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 26, 30, 41, 56, 60]`, flank `11`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_862 : ∃ k : ℕ, Lonely 8 (([3, 11, 26, 30, 41, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 26, 30, 41, 56, 60]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 11, 26, 35, 37, 48, 52]`, flank `11`, opening `8`.  Covers 1 census rows. -/
theorem fam_3_863 : ∃ k : ℕ, Lonely 8 (([3, 11, 26, 35, 37, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [3, 11, 26, 35, 37, 48, 52]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 13, 14, 16, 20, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_864 : ∃ k : ℕ, Lonely 8 (([3, 12, 13, 14, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 13, 14, 16, 20, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 13, 14, 20, 27, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_865 : ∃ k : ℕ, Lonely 8 (([3, 12, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 13, 14, 20, 27, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 13, 15, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_866 : ∃ k : ℕ, Lonely 8 (([3, 12, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 13, 15, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 15, 16, 20, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_867 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 15, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 15, 16, 20, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 15, 16, 20, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_868 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 15, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 15, 16, 20, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 15, 16, 22, 24]`, flank `12`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_869 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 15, 16, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 15, 16, 22, 24]) (e := 12) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 15, 20, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_870 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 15, 20, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 15, 20, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 16, 17, 20, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_871 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 16, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 16, 17, 20, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 16, 17, 20, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_872 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 16, 17, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 16, 17, 20, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 16, 19, 30, 32]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_873 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 16, 19, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 16, 19, 30, 32]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 14, 18, 25, 32, 36]`, flank `12`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_874 : ∃ k : ℕ, Lonely 8 (([3, 12, 14, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 14, 18, 25, 32, 36]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 15, 20, 21, 28, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_875 : ∃ k : ℕ, Lonely 8 (([3, 12, 15, 20, 21, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 15, 20, 21, 28, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 15, 22, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_876 : ∃ k : ℕ, Lonely 8 (([3, 12, 15, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 15, 22, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 17, 20, 21, 23, 24]`, flank `12`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_877 : ∃ k : ℕ, Lonely 8 (([3, 12, 17, 20, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 17, 20, 21, 23, 24]) (e := 12) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 12, 18, 23, 32, 35, 36]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_878 : ∃ k : ℕ, Lonely 8 (([3, 12, 18, 23, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 12, 18, 23, 32, 35, 36]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 15, 17, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_879 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 15, 17, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 15, 20, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_880 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 15, 20, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 15, 20, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 16, 19, 20, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_881 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 16, 19, 20, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 16, 19, 20, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 17, 20, 23, 24]`, flank `14`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_882 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 17, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 17, 20, 23, 24]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 20, 23, 27, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_883 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 20, 23, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 20, 23, 27, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 14, 22, 25, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_884 : ∃ k : ℕ, Lonely 8 (([3, 13, 14, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 14, 22, 25, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 16, 17, 21, 26]`, flank `13`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_885 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 16, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 16, 17, 21, 26]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 16, 19, 21, 26]`, flank `3`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_886 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 16, 19, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 16, 19, 21, 26]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 16, 21, 29, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_887 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 16, 21, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 16, 21, 29, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 17, 18, 21, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_888 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 17, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 17, 18, 21, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 17, 18, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_889 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 17, 18, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 17, 18, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 17, 20, 21, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_890 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 17, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 17, 20, 21, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 17, 21, 22, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_891 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 17, 21, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 17, 21, 22, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 17, 21, 24, 26]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_892 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 17, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 17, 21, 24, 26]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 18, 21, 24, 26]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_893 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 18, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 18, 21, 24, 26]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 19, 21, 24, 26]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_894 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 19, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 19, 21, 24, 26]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 20, 21, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_895 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 20, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 20, 21, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 20, 23, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_896 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 20, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 20, 23, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 21, 23, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_897 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 21, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 21, 23, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 22, 23, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_898 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 22, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 22, 23, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 15, 23, 28, 29, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_899 : ∃ k : ℕ, Lonely 8 (([3, 13, 15, 23, 28, 29, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 15, 23, 28, 29, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 16, 19, 22, 35, 38]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_900 : ∃ k : ℕ, Lonely 8 (([3, 13, 16, 19, 22, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 16, 19, 22, 35, 38]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 16, 19, 22, 35, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_901 : ∃ k : ℕ, Lonely 8 (([3, 13, 16, 19, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 16, 19, 22, 35, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 16, 19, 29, 35, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_902 : ∃ k : ℕ, Lonely 8 (([3, 13, 16, 19, 29, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 16, 19, 29, 35, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 16, 23, 29, 35, 46]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_903 : ∃ k : ℕ, Lonely 8 (([3, 13, 16, 23, 29, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 16, 23, 29, 35, 46]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 16, 29, 35, 38, 58]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_904 : ∃ k : ℕ, Lonely 8 (([3, 13, 16, 29, 35, 38, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 16, 29, 35, 38, 58]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 17, 20, 21, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_905 : ∃ k : ℕ, Lonely 8 (([3, 13, 17, 20, 21, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 17, 20, 21, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 18, 19, 21, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_906 : ∃ k : ℕ, Lonely 8 (([3, 13, 18, 19, 21, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 18, 19, 21, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 18, 24, 35, 44, 55]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_907 : ∃ k : ℕ, Lonely 8 (([3, 13, 18, 24, 35, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 18, 24, 35, 44, 55]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 19, 21, 22, 25, 26]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_908 : ∃ k : ℕ, Lonely 8 (([3, 13, 19, 21, 22, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 19, 21, 22, 25, 26]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 19, 22, 32, 35, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_909 : ∃ k : ℕ, Lonely 8 (([3, 13, 19, 22, 32, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 19, 22, 32, 35, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 13, 19, 29, 32, 35, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_910 : ∃ k : ℕ, Lonely 8 (([3, 13, 19, 29, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 13, 19, 29, 32, 35, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 16, 17, 23, 34]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_911 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 16, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 16, 17, 23, 34]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 16, 18, 22, 24]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_3_912 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 16, 18, 22, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 16, 18, 22, 24]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 16, 19, 23, 28]`, flank `14`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_913 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 16, 19, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 16, 19, 23, 28]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 18, 20, 28]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_914 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 18, 20, 28]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 20, 21, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_915 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 20, 21, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 20, 21, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 20, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_916 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 20, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 20, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_917 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 20, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 20, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 20, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_918 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 20, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 20, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 21, 25, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_919 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 21, 25, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 21, 31, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_920 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 21, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 21, 31, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 17, 23, 29, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_921 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 17, 23, 29, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 17, 23, 29, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 20, 23, 27, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_922 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 20, 23, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 20, 23, 27, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 15, 22, 25, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_923 : ∃ k : ℕ, Lonely 8 (([3, 14, 15, 22, 25, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 15, 22, 25, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 16, 17, 18, 35, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_924 : ∃ k : ℕ, Lonely 8 (([3, 14, 16, 17, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 16, 17, 18, 35, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 16, 17, 23, 30, 34]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_925 : ∃ k : ℕ, Lonely 8 (([3, 14, 16, 17, 23, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 16, 17, 23, 30, 34]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 16, 18, 25, 34, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_926 : ∃ k : ℕ, Lonely 8 (([3, 14, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 16, 18, 25, 34, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 16, 19, 22, 30, 32]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_927 : ∃ k : ℕ, Lonely 8 (([3, 14, 16, 19, 22, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 16, 19, 22, 30, 32]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 18, 20, 22, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_928 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 18, 20, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 18, 20, 22, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 18, 20, 24, 28]`, flank `14`, opening `6`.  Covers 2 census rows. -/
theorem fam_3_929 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 18, 20, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 18, 20, 24, 28]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 18, 32, 35, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_930 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 18, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 18, 32, 35, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 19, 20, 21, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_931 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 19, 20, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 19, 20, 21, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 19, 21, 25, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_932 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 19, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 19, 21, 25, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 22, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_933 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 22, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 23, 24, 28]`, flank `14`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_934 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 23, 24, 28]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 23, 26, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_935 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 23, 26, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 23, 26, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 23, 29, 40]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_936 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 23, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 23, 29, 40]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 23, 37, 40]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_937 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 23, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 23, 37, 40]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 20, 31, 48, 51]`, flank `14`, opening `12`.  Covers 1 census rows. -/
theorem fam_3_938 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 20, 31, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨12, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 20, 31, 48, 51]) (e := 14) (k := 12)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 21, 30, 31, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_939 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 21, 30, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 21, 30, 31, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 23, 29, 30, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_940 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 23, 29, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 23, 29, 30, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 17, 31, 45, 48, 51]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_941 : ∃ k : ℕ, Lonely 8 (([3, 14, 17, 31, 45, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 17, 31, 45, 48, 51]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 19, 20, 22, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_942 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 19, 20, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 19, 20, 22, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 19, 22, 40, 44]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_943 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 19, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 19, 22, 40, 44]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 20, 21, 34, 36]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_944 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 20, 21, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 20, 21, 34, 36]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 20, 23, 32, 40]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_945 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 20, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 20, 23, 32, 40]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 22, 25, 32, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_946 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 22, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 22, 25, 32, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 22, 25, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_947 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 22, 25, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 22, 25, 40, 44]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_948 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 22, 25, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 22, 25, 40, 44]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 24, 25, 32, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_949 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 24, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 24, 25, 32, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 18, 25, 32, 34, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_950 : ∃ k : ℕ, Lonely 8 (([3, 14, 18, 25, 32, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 18, 25, 32, 34, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 19, 20, 22, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_951 : ∃ k : ℕ, Lonely 8 (([3, 14, 19, 20, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 19, 20, 22, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 19, 20, 22, 26, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_952 : ∃ k : ℕ, Lonely 8 (([3, 14, 19, 20, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 19, 20, 22, 26, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 19, 22, 26, 40, 44]`, flank `14`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_953 : ∃ k : ℕ, Lonely 8 (([3, 14, 19, 22, 26, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 19, 22, 26, 40, 44]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 20, 22, 23, 32, 40]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_954 : ∃ k : ℕ, Lonely 8 (([3, 14, 20, 22, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 20, 22, 23, 32, 40]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 20, 23, 26, 32, 40]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_955 : ∃ k : ℕ, Lonely 8 (([3, 14, 20, 23, 26, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 20, 23, 26, 32, 40]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 20, 23, 26, 32, 52]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_956 : ∃ k : ℕ, Lonely 8 (([3, 14, 20, 23, 26, 32, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 20, 23, 26, 32, 52]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 20, 31, 34, 48, 51]`, flank `14`, opening `12`.  Covers 1 census rows. -/
theorem fam_3_957 : ∃ k : ℕ, Lonely 8 (([3, 14, 20, 31, 34, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨12, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 20, 31, 34, 48, 51]) (e := 14) (k := 12)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 20, 34, 39, 48, 60]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_958 : ∃ k : ℕ, Lonely 8 (([3, 14, 20, 34, 39, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 20, 34, 39, 48, 60]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 21, 22, 23, 25, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_959 : ∃ k : ℕ, Lonely 8 (([3, 14, 21, 22, 23, 25, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 21, 22, 23, 25, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 21, 22, 25, 28, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_960 : ∃ k : ℕ, Lonely 8 (([3, 14, 21, 22, 25, 28, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 21, 22, 25, 28, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 21, 22, 25, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_961 : ∃ k : ℕ, Lonely 8 (([3, 14, 21, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 21, 22, 25, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 26, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_962 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 26, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 26, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 26, 40, 44]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_963 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 26, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 26, 40, 44]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 28, 42, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_964 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 28, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 28, 42, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 29, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_965 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 29, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 29, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 31, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_966 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 31, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 31, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 34, 36, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_967 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 34, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 34, 36, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 36, 39, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_968 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 36, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 36, 39, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 25, 36, 42, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_969 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 25, 36, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 25, 36, 42, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 22, 26, 31, 40, 44]`, flank `14`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_970 : ∃ k : ℕ, Lonely 8 (([3, 14, 22, 26, 31, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 22, 26, 31, 40, 44]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 31, 34, 45, 48, 51]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_971 : ∃ k : ℕ, Lonely 8 (([3, 14, 31, 34, 45, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 31, 34, 45, 48, 51]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 14, 34, 39, 40, 48, 60]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_972 : ∃ k : ℕ, Lonely 8 (([3, 14, 34, 39, 40, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 14, 34, 39, 40, 48, 60]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 16, 17, 19, 21, 30]`, flank `3`, opening `0`.  Covers 2 census rows. -/
theorem fam_3_973 : ∃ k : ℕ, Lonely 8 (([3, 15, 16, 17, 19, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 16, 17, 19, 21, 30]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 16, 19, 21, 22, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_974 : ∃ k : ℕ, Lonely 8 (([3, 15, 16, 19, 21, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 16, 19, 21, 22, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 20, 21, 23, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_975 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 20, 21, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 20, 21, 23, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 20, 21, 25, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_976 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 20, 21, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 20, 21, 25, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 20, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_977 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 20, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 20, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 20, 28, 37, 38]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_978 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 20, 28, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 20, 28, 37, 38]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 21, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_979 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 21, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 21, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 21, 28, 31, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_980 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 21, 28, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 21, 28, 31, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 17, 22, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_981 : ∃ k : ℕ, Lonely 8 (([3, 15, 17, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 17, 22, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 18, 21, 22, 32, 44]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_982 : ∃ k : ℕ, Lonely 8 (([3, 15, 18, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 18, 21, 22, 32, 44]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 18, 22, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_983 : ∃ k : ℕ, Lonely 8 (([3, 15, 18, 22, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 18, 22, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 19, 21, 22, 23, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_984 : ∃ k : ℕ, Lonely 8 (([3, 15, 19, 21, 22, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 19, 21, 22, 23, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 19, 21, 23, 26, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_985 : ∃ k : ℕ, Lonely 8 (([3, 15, 19, 21, 23, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 19, 21, 23, 26, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 21, 22, 25, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_986 : ∃ k : ℕ, Lonely 8 (([3, 15, 21, 22, 25, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 21, 22, 25, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 21, 25, 26, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_987 : ∃ k : ℕ, Lonely 8 (([3, 15, 21, 25, 26, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 21, 25, 26, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 21, 25, 27, 28, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_988 : ∃ k : ℕ, Lonely 8 (([3, 15, 21, 25, 27, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 21, 25, 27, 28, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 22, 23, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_989 : ∃ k : ℕ, Lonely 8 (([3, 15, 22, 23, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 22, 23, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 22, 24, 25, 28, 30]`, flank `15`, opening `7`.  Covers 2 census rows. -/
theorem fam_3_990 : ∃ k : ℕ, Lonely 8 (([3, 15, 22, 24, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 22, 24, 25, 28, 30]) (e := 15) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 22, 25, 28, 29, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_991 : ∃ k : ℕ, Lonely 8 (([3, 15, 22, 25, 28, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 22, 25, 28, 29, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 22, 25, 28, 39, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_992 : ∃ k : ℕ, Lonely 8 (([3, 15, 22, 25, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 22, 25, 28, 39, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 22, 31, 32, 35, 44]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_993 : ∃ k : ℕ, Lonely 8 (([3, 15, 22, 31, 32, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 22, 31, 32, 35, 44]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 15, 23, 26, 29, 42, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_994 : ∃ k : ℕ, Lonely 8 (([3, 15, 23, 26, 29, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 15, 23, 26, 29, 42, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 19, 20, 22, 28, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_995 : ∃ k : ℕ, Lonely 8 (([3, 16, 19, 20, 22, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 19, 20, 22, 28, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 19, 21, 22, 30, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_996 : ∃ k : ℕ, Lonely 8 (([3, 16, 19, 21, 22, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 19, 21, 22, 30, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 19, 22, 28, 30, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_997 : ∃ k : ℕ, Lonely 8 (([3, 16, 19, 22, 28, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 19, 22, 28, 30, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 19, 24, 33, 35, 48]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_998 : ∃ k : ℕ, Lonely 8 (([3, 16, 19, 24, 33, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 19, 24, 33, 35, 48]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 21, 25, 27, 28, 32]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_999 : ∃ k : ℕ, Lonely 8 (([3, 16, 21, 25, 27, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 21, 25, 27, 28, 32]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 22, 25, 28, 38, 56]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1000 : ∃ k : ℕ, Lonely 8 (([3, 16, 22, 25, 28, 38, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 22, 25, 28, 38, 56]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 16, 38, 41, 42, 44, 55]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1001 : ∃ k : ℕ, Lonely 8 (([3, 16, 38, 41, 42, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 16, 38, 41, 42, 44, 55]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 19, 20, 21, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1002 : ∃ k : ℕ, Lonely 8 (([3, 17, 19, 20, 21, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 19, 20, 21, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 19, 20, 21, 25, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1003 : ∃ k : ℕ, Lonely 8 (([3, 17, 19, 20, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 19, 20, 21, 25, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 19, 20, 21, 28, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1004 : ∃ k : ℕ, Lonely 8 (([3, 17, 19, 20, 21, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 19, 20, 21, 28, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 19, 21, 25, 26, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1005 : ∃ k : ℕ, Lonely 8 (([3, 17, 19, 21, 25, 26, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 19, 21, 25, 26, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 21, 28, 30, 31, 42]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1006 : ∃ k : ℕ, Lonely 8 (([3, 17, 21, 28, 30, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 21, 28, 30, 31, 42]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 22, 23, 25, 28, 30]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1007 : ∃ k : ℕ, Lonely 8 (([3, 17, 22, 23, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 22, 23, 25, 28, 30]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 22, 25, 28, 39, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1008 : ∃ k : ℕ, Lonely 8 (([3, 17, 22, 25, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 22, 25, 28, 39, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 23, 26, 29, 35, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1009 : ∃ k : ℕ, Lonely 8 (([3, 17, 23, 26, 29, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 23, 26, 29, 35, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 28, 31, 37, 45, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1010 : ∃ k : ℕ, Lonely 8 (([3, 17, 28, 31, 37, 45, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 28, 31, 37, 45, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 17, 28, 31, 41, 45, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1011 : ∃ k : ℕ, Lonely 8 (([3, 17, 28, 31, 41, 45, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 17, 28, 31, 41, 45, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 18, 19, 22, 28, 30, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1012 : ∃ k : ℕ, Lonely 8 (([3, 18, 19, 22, 28, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 18, 19, 22, 28, 30, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 18, 23, 24, 32, 35, 36]`, flank `18`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1013 : ∃ k : ℕ, Lonely 8 (([3, 18, 23, 24, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 18, 23, 24, 32, 35, 36]) (e := 18) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 20, 21, 23, 27, 38]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1014 : ∃ k : ℕ, Lonely 8 (([3, 19, 20, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 20, 21, 23, 27, 38]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 20, 21, 23, 28, 38]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1015 : ∃ k : ℕ, Lonely 8 (([3, 19, 20, 21, 23, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 20, 21, 23, 28, 38]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 21, 22, 23, 25, 38]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1016 : ∃ k : ℕ, Lonely 8 (([3, 19, 21, 22, 23, 25, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 21, 22, 23, 25, 38]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 22, 26, 28, 30, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1017 : ∃ k : ℕ, Lonely 8 (([3, 19, 22, 26, 28, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 22, 26, 28, 30, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 22, 27, 32, 35, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1018 : ∃ k : ℕ, Lonely 8 (([3, 19, 22, 27, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 22, 27, 32, 35, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 22, 28, 30, 34, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1019 : ∃ k : ℕ, Lonely 8 (([3, 19, 22, 28, 30, 34, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 22, 28, 30, 34, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 22, 28, 30, 42, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1020 : ∃ k : ℕ, Lonely 8 (([3, 19, 22, 28, 30, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 22, 28, 30, 42, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 22, 30, 36, 42, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1021 : ∃ k : ℕ, Lonely 8 (([3, 19, 22, 30, 36, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 22, 30, 36, 42, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 24, 32, 33, 35, 48]`, flank `19`, opening `17`.  Covers 1 census rows. -/
theorem fam_3_1022 : ∃ k : ℕ, Lonely 8 (([3, 19, 24, 32, 33, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨17, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 24, 32, 33, 35, 48]) (e := 19) (k := 17)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 25, 28, 29, 31, 40]`, flank `19`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1023 : ∃ k : ℕ, Lonely 8 (([3, 19, 25, 28, 29, 31, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 25, 28, 29, 31, 40]) (e := 19) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 19, 27, 32, 33, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1024 : ∃ k : ℕ, Lonely 8 (([3, 19, 27, 32, 33, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 19, 27, 32, 33, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 20, 23, 26, 28, 32, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1025 : ∃ k : ℕ, Lonely 8 (([3, 20, 23, 26, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 20, 23, 26, 28, 32, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 20, 25, 28, 34, 48, 56]`, flank `20`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_1026 : ∃ k : ℕ, Lonely 8 (([3, 20, 25, 28, 34, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 20, 25, 28, 34, 48, 56]) (e := 20) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 20, 27, 32, 33, 35, 40]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1027 : ∃ k : ℕ, Lonely 8 (([3, 20, 27, 32, 33, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 20, 27, 32, 33, 35, 40]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 20, 28, 31, 34, 48, 56]`, flank `20`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1028 : ∃ k : ℕ, Lonely 8 (([3, 20, 28, 31, 34, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 20, 28, 31, 34, 48, 56]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 21, 22, 23, 25, 28, 42]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1029 : ∃ k : ℕ, Lonely 8 (([3, 21, 22, 23, 25, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 21, 22, 23, 25, 28, 42]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 21, 24, 34, 40, 46, 48]`, flank `21`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1030 : ∃ k : ℕ, Lonely 8 (([3, 21, 24, 34, 40, 46, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 21, 24, 34, 40, 46, 48]) (e := 21) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 21, 26, 29, 32, 33, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1031 : ∃ k : ℕ, Lonely 8 (([3, 21, 26, 29, 32, 33, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 21, 26, 29, 32, 33, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 22, 23, 25, 28, 29, 44]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1032 : ∃ k : ℕ, Lonely 8 (([3, 22, 23, 25, 28, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 22, 23, 25, 28, 29, 44]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 22, 27, 32, 35, 38, 40]`, flank `22`, opening `5`.  Covers 1 census rows. -/
theorem fam_3_1033 : ∃ k : ℕ, Lonely 8 (([3, 22, 27, 32, 35, 38, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [3, 22, 27, 32, 35, 38, 40]) (e := 22) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 22, 28, 31, 34, 40, 56]`, flank `22`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1034 : ∃ k : ℕ, Lonely 8 (([3, 22, 28, 31, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 22, 28, 31, 34, 40, 56]) (e := 22) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 22, 28, 31, 38, 40, 56]`, flank `22`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1035 : ∃ k : ℕ, Lonely 8 (([3, 22, 28, 31, 38, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [3, 22, 28, 31, 38, 40, 56]) (e := 22) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 23, 29, 33, 35, 42, 46]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1036 : ∃ k : ℕ, Lonely 8 (([3, 23, 29, 33, 35, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 23, 29, 33, 35, 42, 46]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 25, 26, 28, 34, 40, 56]`, flank `25`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1037 : ∃ k : ℕ, Lonely 8 (([3, 25, 26, 28, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((25 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 25, 26, 28, 34, 40, 56]) (e := 25) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 25, 28, 34, 40, 52, 56]`, flank `25`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1038 : ∃ k : ℕ, Lonely 8 (([3, 25, 28, 34, 40, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((25 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 25, 28, 34, 40, 52, 56]) (e := 25) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 25, 31, 34, 37, 49, 50]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1039 : ∃ k : ℕ, Lonely 8 (([3, 25, 31, 34, 37, 49, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 25, 31, 34, 37, 49, 50]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 26, 28, 31, 34, 40, 56]`, flank `26`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1040 : ∃ k : ℕ, Lonely 8 (([3, 26, 28, 31, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [3, 26, 28, 31, 34, 40, 56]) (e := 26) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 28, 30, 31, 34, 40, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1041 : ∃ k : ℕ, Lonely 8 (([3, 28, 30, 31, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 28, 30, 31, 34, 40, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 28, 31, 34, 40, 44, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1042 : ∃ k : ℕ, Lonely 8 (([3, 28, 31, 34, 40, 44, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 28, 31, 34, 40, 44, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 28, 31, 34, 40, 48, 56]`, flank `28`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1043 : ∃ k : ℕ, Lonely 8 (([3, 28, 31, 34, 40, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [3, 28, 31, 34, 40, 48, 56]) (e := 28) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 28, 31, 34, 40, 52, 56]`, flank `3`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1044 : ∃ k : ℕ, Lonely 8 (([3, 28, 31, 34, 40, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [3, 28, 31, 34, 40, 52, 56]) (e := 3) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 28, 37, 45, 48, 51, 56]`, flank `28`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1045 : ∃ k : ℕ, Lonely 8 (([3, 28, 37, 45, 48, 51, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [3, 28, 37, 45, 48, 51, 56]) (e := 28) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[3, 29, 35, 37, 40, 43, 48]`, flank `29`, opening `11`.  Covers 1 census rows. -/
theorem fam_3_1046 : ∃ k : ℕ, Lonely 8 (([3, 29, 35, 37, 40, 43, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((29 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [3, 29, 35, 37, 40, 43, 48]) (e := 29) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 6, 11, 16, 28, 32]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1047 : ∃ k : ℕ, Lonely 8 (([4, 5, 6, 11, 16, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 6, 11, 16, 28, 32]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 6, 14, 17, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1048 : ∃ k : ℕ, Lonely 8 (([4, 5, 6, 14, 17, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 6, 14, 17, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 6, 16, 21, 26, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1049 : ∃ k : ℕ, Lonely 8 (([4, 5, 6, 16, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 6, 16, 21, 26, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 6, 16, 21, 28, 32]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1050 : ∃ k : ℕ, Lonely 8 (([4, 5, 6, 16, 21, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 6, 16, 21, 28, 32]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 6, 16, 21, 30, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1051 : ∃ k : ℕ, Lonely 8 (([4, 5, 6, 16, 21, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 6, 16, 21, 30, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 9, 12, 19, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1052 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 9, 12, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 9, 12, 19, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 9, 13, 19, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1053 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 9, 13, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 9, 13, 19, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 9, 19, 25, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1054 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 9, 19, 25, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 9, 19, 25, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 11, 16, 27, 33]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1055 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 11, 16, 27, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 11, 16, 27, 33]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 11, 16, 30, 33]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1056 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 11, 16, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 11, 16, 30, 33]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 11, 18, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1057 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 11, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 11, 18, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 12, 17, 28, 34]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1058 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 12, 17, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 12, 17, 28, 34]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 12, 17, 31, 34]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1059 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 12, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 12, 17, 31, 34]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 12, 19, 20, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1060 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 12, 19, 20, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 12, 19, 20, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 12, 19, 29, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1061 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 12, 19, 29, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 12, 19, 29, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 16, 22, 27, 33]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1062 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 16, 22, 27, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 16, 22, 27, 33]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 16, 22, 30, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1063 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 16, 22, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 16, 22, 30, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 17, 19, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1064 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 17, 19, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 17, 19, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 7, 18, 22, 29, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1065 : ∃ k : ℕ, Lonely 8 (([4, 5, 7, 18, 22, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 7, 18, 22, 29, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 13, 14, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1066 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 13, 14, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 13, 14, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 14, 16, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1067 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 14, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 14, 16, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 14, 19, 23, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1068 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 14, 19, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 14, 19, 23, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 14, 19, 23, 42]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1069 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 14, 19, 23, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 14, 19, 23, 42]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 14, 19, 24, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1070 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 14, 19, 24, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 14, 19, 24, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 14, 24, 32, 48]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1071 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 14, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 14, 24, 32, 48]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 19, 23, 28, 42]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1072 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 19, 23, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 19, 23, 28, 42]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 9, 19, 23, 28, 56]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1073 : ∃ k : ℕ, Lonely 8 (([4, 5, 9, 19, 23, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 9, 19, 23, 28, 56]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 11, 18, 28, 32, 35]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1074 : ∃ k : ℕ, Lonely 8 (([4, 5, 11, 18, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 11, 18, 28, 32, 35]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 12, 16, 21, 26, 32]`, flank `12`, opening `8`.  Covers 1 census rows. -/
theorem fam_3_1075 : ∃ k : ℕ, Lonely 8 (([4, 5, 12, 16, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 12, 16, 21, 26, 32]) (e := 12) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 13, 14, 18, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1076 : ∃ k : ℕ, Lonely 8 (([4, 5, 13, 14, 18, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 13, 14, 18, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 13, 14, 18, 35, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1077 : ∃ k : ℕ, Lonely 8 (([4, 5, 13, 14, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 13, 14, 18, 35, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 13, 17, 18, 21, 42]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1078 : ∃ k : ℕ, Lonely 8 (([4, 5, 13, 17, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 13, 17, 18, 21, 42]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 13, 17, 21, 31, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1079 : ∃ k : ℕ, Lonely 8 (([4, 5, 13, 17, 21, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 13, 17, 21, 31, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 16, 19, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1080 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 16, 19, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 16, 19, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 16, 24, 29, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1081 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 16, 24, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 16, 24, 29, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 18, 19, 23, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1082 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 18, 19, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 18, 19, 23, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 18, 19, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1083 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 18, 19, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 18, 19, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 18, 23, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1084 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 18, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 18, 23, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 18, 23, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1085 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 18, 23, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 18, 23, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 19, 24, 32, 48]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1086 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 19, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 19, 24, 32, 48]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 19, 24, 34, 48]`, flank `14`, opening `9`.  Covers 1 census rows. -/
theorem fam_3_1087 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 19, 24, 34, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 19, 24, 34, 48]) (e := 14) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 14, 24, 29, 32, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1088 : ∃ k : ℕ, Lonely 8 (([4, 5, 14, 24, 29, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 14, 24, 29, 32, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 16, 18, 21, 26, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1089 : ∃ k : ℕ, Lonely 8 (([4, 5, 16, 18, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 16, 18, 21, 26, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 18, 23, 28, 32, 56]`, flank `18`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1090 : ∃ k : ℕ, Lonely 8 (([4, 5, 18, 23, 28, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 18, 23, 28, 32, 56]) (e := 18) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 19, 28, 33, 47, 56]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1091 : ∃ k : ℕ, Lonely 8 (([4, 5, 19, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 19, 28, 33, 47, 56]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 21, 26, 30, 34, 52]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1092 : ∃ k : ℕ, Lonely 8 (([4, 5, 21, 26, 30, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 21, 26, 30, 34, 52]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 23, 24, 28, 33, 46]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1093 : ∃ k : ℕ, Lonely 8 (([4, 5, 23, 24, 28, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 23, 24, 28, 33, 46]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 23, 24, 28, 38, 56]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1094 : ∃ k : ℕ, Lonely 8 (([4, 5, 23, 24, 28, 38, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 23, 24, 28, 38, 56]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 24, 28, 33, 38, 56]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1095 : ∃ k : ℕ, Lonely 8 (([4, 5, 24, 28, 33, 38, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 24, 28, 33, 38, 56]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 5, 27, 32, 35, 37, 54]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1096 : ∃ k : ℕ, Lonely 8 (([4, 5, 27, 32, 35, 37, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 5, 27, 32, 35, 37, 54]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 8, 13, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1097 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 8, 13, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 8, 13, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 8, 15, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1098 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 8, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 8, 15, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 8, 20, 27, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1099 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 8, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 8, 20, 27, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 10, 17, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1100 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 10, 17, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 10, 17, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 13, 16, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1101 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 13, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 13, 16, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 13, 20, 24, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1102 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 13, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 13, 20, 24, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 13, 20, 32, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1103 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 13, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 13, 20, 32, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 15, 18, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1104 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 15, 18, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 15, 18, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 15, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1105 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 15, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 15, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 16, 20, 27, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1106 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 16, 20, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 16, 20, 27, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 20, 24, 27, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1107 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 20, 24, 27, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 20, 24, 27, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 7, 20, 27, 32, 40]`, flank `20`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1108 : ∃ k : ℕ, Lonely 8 (([4, 6, 7, 20, 27, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 7, 20, 27, 32, 40]) (e := 20) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 8, 17, 20, 28, 29]`, flank `4`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1109 : ∃ k : ℕ, Lonely 8 (([4, 6, 8, 17, 20, 28, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 8, 17, 20, 28, 29]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 11, 16, 20, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1110 : ∃ k : ℕ, Lonely 8 (([4, 6, 11, 16, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 11, 16, 20, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 13, 14, 22, 35, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1111 : ∃ k : ℕ, Lonely 8 (([4, 6, 13, 14, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 13, 14, 22, 35, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 16, 20, 23, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1112 : ∃ k : ℕ, Lonely 8 (([4, 6, 16, 20, 23, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 16, 20, 23, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 17, 21, 25, 29, 34]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1113 : ∃ k : ℕ, Lonely 8 (([4, 6, 17, 21, 25, 29, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 17, 21, 25, 29, 34]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 6, 17, 21, 25, 33, 34]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1114 : ∃ k : ℕ, Lonely 8 (([4, 6, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 6, 17, 21, 25, 33, 34]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 8, 10, 15, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1115 : ∃ k : ℕ, Lonely 8 (([4, 7, 8, 10, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 8, 10, 15, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 8, 15, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1116 : ∃ k : ℕ, Lonely 8 (([4, 7, 8, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 8, 15, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 10, 16, 26, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1117 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 10, 16, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 10, 16, 26, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 11, 13, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1118 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 11, 13, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 11, 13, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 11, 16, 25, 50]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1119 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 11, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 11, 16, 25, 50]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 13, 15, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1120 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 13, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 13, 15, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 13, 17, 25, 50]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1121 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 13, 17, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 13, 17, 25, 50]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 15, 18, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1122 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 15, 18, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 15, 18, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 15, 22, 31, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1123 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 15, 22, 31, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 15, 22, 31, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 15, 23, 27, 46]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1124 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 15, 23, 27, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 15, 23, 27, 46]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 16, 25, 28, 50]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1125 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 16, 25, 28, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 16, 25, 28, 50]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 9, 16, 25, 39, 50]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1126 : ∃ k : ℕ, Lonely 8 (([4, 7, 9, 16, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 9, 16, 25, 39, 50]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 15, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1127 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 15, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 15, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1128 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 15, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 15, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 18, 30, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_1129 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 18, 30, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 18, 32, 33]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_3_1130 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 18, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 18, 32, 33]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 18, 32, 36]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1131 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 18, 32, 36]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 11, 18, 34, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_1132 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 11, 18, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 11, 18, 34, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 14, 15, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1133 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 14, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 14, 15, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 14, 17, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1134 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 14, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 14, 17, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 15, 19, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1135 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 15, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 15, 19, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 15, 19, 29, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1136 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 15, 19, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 15, 19, 29, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 15, 22, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1137 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 15, 22, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 15, 22, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 15, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1138 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 15, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 15, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 16, 17, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1139 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 16, 17, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 16, 17, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 16, 24, 31, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1140 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 16, 24, 31, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 16, 24, 31, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 17, 22, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1141 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 17, 22, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 17, 22, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 17, 24, 32, 48]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1142 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 17, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 17, 24, 32, 48]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 17, 24, 38, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1143 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 17, 24, 38, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 17, 24, 38, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 18, 22, 29, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1144 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 18, 22, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 18, 22, 29, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 18, 22, 32, 33]`, flank `18`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1145 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 18, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 18, 22, 32, 33]) (e := 18) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 18, 25, 34, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_1146 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 18, 25, 34, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 10, 24, 31, 32, 48]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1147 : ∃ k : ℕ, Lonely 8 (([4, 7, 10, 24, 31, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 10, 24, 31, 32, 48]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 13, 15, 28, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1148 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 13, 15, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 13, 15, 28, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 13, 15, 29, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1149 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 13, 15, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 13, 15, 29, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 13, 18, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1150 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 13, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 13, 18, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 13, 18, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1151 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 13, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 13, 18, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 18, 29, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_1152 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 18, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 18, 29, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 18, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1153 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 18, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 19, 26, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1154 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 19, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 19, 26, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 19, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1155 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 19, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 19, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1156 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 15, 20, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1157 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 15, 20, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 15, 20, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 16, 18, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1158 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 16, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 16, 18, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 20, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1159 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 20, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 20, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 23, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1160 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 23, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 25, 32, 35]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1161 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 25, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 25, 32, 35]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1162 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 26, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1163 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 26, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 26, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 29, 30, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_3_1164 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 29, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 29, 30, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 29, 40, 55]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1165 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 29, 40, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 29, 40, 55]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 30, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1166 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 30, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 18, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1167 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 18, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 18, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 11, 21, 25, 29, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1168 : ∃ k : ℕ, Lonely 8 (([4, 7, 11, 21, 25, 29, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 11, 21, 25, 29, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 12, 15, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1169 : ∃ k : ℕ, Lonely 8 (([4, 7, 12, 15, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 12, 15, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 12, 16, 23, 30, 32]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1170 : ∃ k : ℕ, Lonely 8 (([4, 7, 12, 16, 23, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 12, 16, 23, 30, 32]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 12, 18, 25, 32, 36]`, flank `12`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1171 : ∃ k : ℕ, Lonely 8 (([4, 7, 12, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 12, 18, 25, 32, 36]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 13, 15, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1172 : ∃ k : ℕ, Lonely 8 (([4, 7, 13, 15, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 13, 15, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 13, 15, 22, 35, 44]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1173 : ∃ k : ℕ, Lonely 8 (([4, 7, 13, 15, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 13, 15, 22, 35, 44]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 13, 20, 22, 24, 39]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1174 : ∃ k : ℕ, Lonely 8 (([4, 7, 13, 20, 22, 24, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 13, 20, 22, 24, 39]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 14, 15, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1175 : ∃ k : ℕ, Lonely 8 (([4, 7, 14, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 14, 15, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 14, 17, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_3_1176 : ∃ k : ℕ, Lonely 8 (([4, 7, 14, 17, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 14, 17, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 14, 18, 22, 35, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1177 : ∃ k : ℕ, Lonely 8 (([4, 7, 14, 18, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 14, 18, 22, 35, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 14, 18, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_3_1178 : ∃ k : ℕ, Lonely 8 (([4, 7, 14, 18, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 14, 18, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 16, 23, 36, 45]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1179 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 16, 23, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 16, 23, 36, 45]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 23, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1180 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 23, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 23, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1181 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 29, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1182 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 29, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 32, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1183 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 32, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 35, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_3_1184 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 35, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 38, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1185 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 38, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 38, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 18, 22, 41, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1186 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 18, 22, 41, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 18, 22, 41, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 19, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1187 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 19, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 19, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 19, 20, 29, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1188 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 19, 20, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 19, 20, 29, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 19, 22, 23, 46]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1189 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 19, 22, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 19, 22, 23, 46]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 19, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1190 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 19, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 19, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 19, 26, 33, 44]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1191 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 19, 26, 33, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 19, 26, 33, 44]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 20, 22, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1192 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 20, 22, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 20, 22, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 20, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_3_1193 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 20, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 20, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 24, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1194 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 24, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 24, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 25, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1195 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 25, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 25, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 26, 31, 44]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1196 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 26, 31, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 26, 31, 44]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 26, 37, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1197 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 26, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 26, 37, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 26, 43, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_3_1198 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 26, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 26, 43, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 15, 22, 31, 35, 44]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_3_1199 : ∃ k : ℕ, Lonely 8 (([4, 7, 15, 22, 31, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 15, 22, 31, 35, 44]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 16, 18, 25, 34, 36]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_3_1200 : ∃ k : ℕ, Lonely 8 (([4, 7, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 16, 18, 25, 34, 36]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

end PinnedBatch3
