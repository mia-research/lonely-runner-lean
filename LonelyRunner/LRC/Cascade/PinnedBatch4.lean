import LonelyRunner.LRC.Cascade.Flanks

/-!
# Fully-pinned census families, part 4 of 4

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Each theorem is one seven-difference arrangement from an `s = 6` census cover — fully pinned,
so there is no free parameter and Existence for the runner is just that some flank has a lonely
opening.  The framework's clearing test (`Flanks.clear_of_residue_band`, Proposition 2.1) makes
that decidable arithmetic, so each family closes by `decide` on the residue band.

Emitted by `experiments/n8/gen_pinned_batch_v1.py`; data recomputed and cross-checked in
`experiments/n8/census_export_v1.py`.
-/

set_option maxHeartbeats 1000000

namespace PinnedBatch4

open MomentIterationN Flanks

/-- Differences `[4, 7, 16, 23, 30, 36, 45]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_1 : ∃ k : ℕ, Lonely 8 (([4, 7, 16, 23, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 16, 23, 30, 36, 45]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 19, 27, 35, 38]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_2 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 19, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 19, 27, 35, 38]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 20, 22, 29, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_3 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 20, 22, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 20, 22, 29, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 25, 29, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_4 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 25, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 25, 29, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 25, 32, 36]`, flank `18`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_5 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 25, 32, 36]) (e := 18) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 29, 30, 44]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_6 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 29, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 29, 30, 44]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 29, 35, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_7 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 29, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 29, 35, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 29, 40, 44]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_8 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 29, 40, 44]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 22, 29, 40, 55]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_9 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 22, 29, 40, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 22, 29, 40, 55]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 23, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_10 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 23, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 23, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 24, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_11 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 24, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 24, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 25, 26, 34, 36]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_12 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 25, 26, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 25, 26, 34, 36]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 25, 32, 34, 36]`, flank `18`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_13 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 25, 32, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 25, 32, 34, 36]) (e := 18) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 25, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_14 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 25, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 25, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 29, 33, 40, 55]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_15 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 29, 33, 40, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 29, 33, 40, 55]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 18, 29, 40, 44, 55]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_16 : ∃ k : ℕ, Lonely 8 (([4, 7, 18, 29, 40, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 18, 29, 40, 44, 55]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 7, 20, 22, 24, 26, 39]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_17 : ∃ k : ℕ, Lonely 8 (([4, 7, 20, 22, 24, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 7, 20, 22, 24, 26, 39]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 9, 11, 14, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_18 : ∃ k : ℕ, Lonely 8 (([4, 8, 9, 11, 14, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 9, 11, 14, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 9, 14, 17, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_19 : ∃ k : ℕ, Lonely 8 (([4, 8, 9, 14, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 9, 14, 17, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 9, 14, 20, 23, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_20 : ∃ k : ℕ, Lonely 8 (([4, 8, 9, 14, 20, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 9, 14, 20, 23, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 16, 20, 28, 29]`, flank `4`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_21 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 16, 20, 28, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 16, 20, 28, 29]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 16, 20, 28, 31]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_22 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 16, 20, 28, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 16, 20, 28, 31]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 16, 20, 28, 41]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_23 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 16, 20, 28, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 16, 20, 28, 41]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 16, 20, 28, 47]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_24 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 16, 20, 28, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 16, 20, 28, 47]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 16, 20, 28, 53]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_25 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 16, 20, 28, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 16, 20, 28, 53]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 20, 28, 32, 35]`, flank `20`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_26 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 20, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 20, 28, 32, 35]) (e := 20) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 12, 20, 28, 32, 53]`, flank `20`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_27 : ∃ k : ℕ, Lonely 8 (([4, 8, 12, 20, 28, 32, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 12, 20, 28, 32, 53]) (e := 20) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 18, 19, 27, 35, 38]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_28 : ∃ k : ℕ, Lonely 8 (([4, 8, 18, 19, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 18, 19, 27, 35, 38]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 8, 20, 24, 28, 32, 39]`, flank `20`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_29 : ∃ k : ℕ, Lonely 8 (([4, 8, 20, 24, 28, 32, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 8, 20, 24, 28, 32, 39]) (e := 20) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 10, 13, 14, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_30 : ∃ k : ℕ, Lonely 8 (([4, 9, 10, 13, 14, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 10, 13, 14, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 10, 13, 17, 28, 34]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_31 : ∃ k : ℕ, Lonely 8 (([4, 9, 10, 13, 17, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 10, 13, 17, 28, 34]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 10, 14, 15, 24, 30]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_32 : ∃ k : ℕ, Lonely 8 (([4, 9, 10, 14, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 10, 14, 15, 24, 30]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 10, 14, 17, 24, 30]`, flank `9`, opening `6`.  Covers 2 census rows. -/
theorem fam_4_33 : ∃ k : ℕ, Lonely 8 (([4, 9, 10, 14, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 10, 14, 17, 24, 30]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 10, 19, 24, 28, 56]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_34 : ∃ k : ℕ, Lonely 8 (([4, 9, 10, 19, 24, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 10, 19, 24, 28, 56]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 11, 14, 16, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_35 : ∃ k : ℕ, Lonely 8 (([4, 9, 11, 14, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 11, 14, 16, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 11, 14, 20, 24, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_36 : ∃ k : ℕ, Lonely 8 (([4, 9, 11, 14, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 11, 14, 20, 24, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 11, 14, 20, 32, 40]`, flank `9`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_37 : ∃ k : ℕ, Lonely 8 (([4, 9, 11, 14, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 11, 14, 20, 32, 40]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 15, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_38 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 15, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 17, 25, 50]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_39 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 17, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 17, 25, 50]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 20, 22, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_40 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 20, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 20, 22, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 22, 25, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_41 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 22, 25, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 22, 30, 44]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_42 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 22, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 22, 30, 44]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 22, 35, 44]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_43 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 22, 35, 44]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 14, 22, 40, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_44 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 14, 22, 40, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 17, 21, 25, 42]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_45 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 17, 21, 25, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 17, 21, 25, 42]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 17, 21, 30, 34]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_46 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 17, 21, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 17, 21, 30, 34]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 13, 17, 21, 30, 42]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_47 : ∃ k : ℕ, Lonely 8 (([4, 9, 13, 17, 21, 30, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 13, 17, 21, 30, 42]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 15, 16, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_48 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 15, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 15, 16, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 15, 20, 24, 30]`, flank `9`, opening `6`.  Covers 2 census rows. -/
theorem fam_4_49 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 15, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 15, 20, 24, 30]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 15, 24, 32, 48]`, flank `9`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_50 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 15, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 15, 24, 32, 48]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 16, 17, 20, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_51 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 16, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 16, 17, 20, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 16, 20, 23, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_52 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 16, 20, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 16, 20, 23, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 17, 20, 24, 30]`, flank `9`, opening `6`.  Covers 2 census rows. -/
theorem fam_4_53 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 17, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 17, 20, 24, 30]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 17, 20, 24, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_54 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 17, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 17, 20, 24, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 17, 20, 32, 40]`, flank `9`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_55 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 17, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 17, 20, 32, 40]) (e := 9) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 20, 23, 24, 40]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_56 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 20, 23, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 20, 23, 24, 40]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 14, 20, 23, 32, 40]`, flank `9`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_57 : ∃ k : ℕ, Lonely 8 (([4, 9, 14, 20, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 14, 20, 23, 32, 40]) (e := 9) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 17, 21, 25, 27, 34]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_58 : ∃ k : ℕ, Lonely 8 (([4, 9, 17, 21, 25, 27, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 17, 21, 25, 27, 34]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 17, 21, 25, 33, 34]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_59 : ∃ k : ℕ, Lonely 8 (([4, 9, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 17, 21, 25, 33, 34]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 17, 21, 26, 30, 52]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_60 : ∃ k : ℕ, Lonely 8 (([4, 9, 17, 21, 26, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 17, 21, 26, 30, 52]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 17, 22, 26, 35, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_61 : ∃ k : ℕ, Lonely 8 (([4, 9, 17, 22, 26, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 17, 22, 26, 35, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 17, 26, 30, 42, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_62 : ∃ k : ℕ, Lonely 8 (([4, 9, 17, 26, 30, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 17, 26, 30, 42, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 19, 23, 27, 35, 38]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_63 : ∃ k : ℕ, Lonely 8 (([4, 9, 19, 23, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 19, 23, 27, 35, 38]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 21, 31, 35, 39, 42]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_64 : ∃ k : ℕ, Lonely 8 (([4, 9, 21, 31, 35, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 21, 31, 35, 39, 42]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 22, 26, 34, 35, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_65 : ∃ k : ℕ, Lonely 8 (([4, 9, 22, 26, 34, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 22, 26, 34, 35, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 9, 22, 26, 35, 45, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_66 : ∃ k : ℕ, Lonely 8 (([4, 9, 22, 26, 35, 45, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 9, 22, 26, 35, 45, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 11, 14, 15, 25, 30]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_67 : ∃ k : ℕ, Lonely 8 (([4, 10, 11, 14, 15, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 11, 14, 15, 25, 30]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 11, 14, 18, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_68 : ∃ k : ℕ, Lonely 8 (([4, 10, 11, 14, 18, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 11, 14, 18, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 11, 15, 21, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_69 : ∃ k : ℕ, Lonely 8 (([4, 10, 11, 15, 21, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 11, 15, 21, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 11, 15, 25, 28, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_70 : ∃ k : ℕ, Lonely 8 (([4, 10, 11, 15, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 11, 15, 25, 28, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 11, 18, 28, 32, 35]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_71 : ∃ k : ℕ, Lonely 8 (([4, 10, 11, 18, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 11, 18, 28, 32, 35]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 13, 17, 18, 21, 42]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_72 : ∃ k : ℕ, Lonely 8 (([4, 10, 13, 17, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 13, 17, 18, 21, 42]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 15, 23, 24, 30]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_73 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 15, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 15, 23, 24, 30]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 15, 24, 25, 30]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_74 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 15, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 15, 24, 25, 30]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 17, 18, 35, 36]`, flank `10`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_75 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 17, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 17, 18, 35, 36]) (e := 10) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 17, 23, 24, 30]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_76 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 17, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 17, 23, 24, 30]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 17, 24, 25, 30]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_77 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 17, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 17, 24, 25, 30]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 18, 22, 32, 33]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_78 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 18, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 18, 22, 32, 33]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 19, 24, 34, 57]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_79 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 19, 24, 34, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 19, 24, 34, 57]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 24, 25, 33, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_80 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 24, 25, 33, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 24, 25, 33, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 24, 27, 35, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_81 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 24, 27, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 24, 27, 35, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 24, 33, 41, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_82 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 24, 33, 41, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 24, 33, 41, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 24, 34, 38, 57]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_83 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 24, 34, 38, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 24, 34, 38, 57]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 14, 24, 35, 43, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_84 : ∃ k : ℕ, Lonely 8 (([4, 10, 14, 24, 35, 43, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 14, 24, 35, 43, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 15, 19, 23, 28, 30]`, flank `4`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_85 : ∃ k : ℕ, Lonely 8 (([4, 10, 15, 19, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 15, 19, 23, 28, 30]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 15, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_86 : ∃ k : ℕ, Lonely 8 (([4, 10, 15, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 15, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 15, 24, 25, 28, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_87 : ∃ k : ℕ, Lonely 8 (([4, 10, 15, 24, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 15, 24, 25, 28, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 16, 17, 21, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_88 : ∃ k : ℕ, Lonely 8 (([4, 10, 16, 17, 21, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 16, 17, 21, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 16, 21, 24, 31, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_89 : ∃ k : ℕ, Lonely 8 (([4, 10, 16, 21, 24, 31, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 16, 21, 24, 31, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 17, 21, 24, 32, 48]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_90 : ∃ k : ℕ, Lonely 8 (([4, 10, 17, 21, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 17, 21, 24, 32, 48]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 19, 23, 27, 28, 54]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_91 : ∃ k : ℕ, Lonely 8 (([4, 10, 19, 23, 27, 28, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 19, 23, 27, 28, 54]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 19, 24, 28, 29, 56]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_92 : ∃ k : ℕ, Lonely 8 (([4, 10, 19, 24, 28, 29, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 19, 24, 28, 29, 56]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 19, 24, 28, 47, 56]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_93 : ∃ k : ℕ, Lonely 8 (([4, 10, 19, 24, 28, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 19, 24, 28, 47, 56]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 21, 22, 32, 43, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_94 : ∃ k : ℕ, Lonely 8 (([4, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 21, 22, 32, 43, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 21, 24, 31, 32, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_95 : ∃ k : ℕ, Lonely 8 (([4, 10, 21, 24, 31, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 21, 24, 31, 32, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 10, 23, 24, 28, 33, 46]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_96 : ∃ k : ℕ, Lonely 8 (([4, 10, 23, 24, 28, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 10, 23, 24, 28, 33, 46]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 13, 14, 16, 30, 33]`, flank `14`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_97 : ∃ k : ℕ, Lonely 8 (([4, 11, 13, 14, 16, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 13, 14, 16, 30, 33]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 15, 19, 23, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_98 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 15, 19, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 15, 19, 23, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 15, 20, 25, 30]`, flank `11`, opening `4`.  Covers 2 census rows. -/
theorem fam_4_99 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 15, 20, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 15, 20, 25, 30]) (e := 11) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 15, 26, 34, 52]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_100 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 15, 26, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 15, 26, 34, 52]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 18, 25, 32, 35]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_101 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 18, 25, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 18, 25, 32, 35]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 18, 29, 30, 36]`, flank `11`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_102 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 18, 29, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 18, 29, 30, 36]) (e := 11) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 14, 19, 26, 30, 60]`, flank `11`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_103 : ∃ k : ℕ, Lonely 8 (([4, 11, 14, 19, 26, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 14, 19, 26, 30, 60]) (e := 11) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 18, 28, 32, 35]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_104 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 18, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 18, 28, 32, 35]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 20, 21, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_105 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 20, 21, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 20, 21, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 20, 25, 28, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_106 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 20, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 20, 25, 28, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 23, 24, 28, 30]`, flank `11`, opening `6`.  Covers 2 census rows. -/
theorem fam_4_107 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 23, 24, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 23, 24, 28, 30]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 24, 26, 28, 31]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_108 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 24, 26, 28, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 24, 26, 28, 31]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 26, 28, 34, 52]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_109 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 26, 28, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 26, 28, 34, 52]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 15, 26, 34, 42, 52]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_110 : ∃ k : ℕ, Lonely 8 (([4, 11, 15, 26, 34, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 15, 26, 34, 42, 52]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 16, 18, 20, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_111 : ∃ k : ℕ, Lonely 8 (([4, 11, 16, 18, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 16, 18, 20, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 18, 20, 28, 32, 35]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_112 : ∃ k : ℕ, Lonely 8 (([4, 11, 18, 20, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 18, 20, 28, 32, 35]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 18, 21, 25, 32, 35]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_113 : ∃ k : ℕ, Lonely 8 (([4, 11, 18, 21, 25, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 18, 21, 25, 32, 35]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 18, 25, 28, 32, 35]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_114 : ∃ k : ℕ, Lonely 8 (([4, 11, 18, 25, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 18, 25, 28, 32, 35]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 18, 28, 30, 32, 35]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_115 : ∃ k : ℕ, Lonely 8 (([4, 11, 18, 28, 30, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 18, 28, 30, 32, 35]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 11, 19, 23, 27, 35, 54]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_116 : ∃ k : ℕ, Lonely 8 (([4, 11, 19, 23, 27, 35, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 11, 19, 23, 27, 35, 54]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 13, 14, 16, 20, 39]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_117 : ∃ k : ℕ, Lonely 8 (([4, 12, 13, 14, 16, 20, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 13, 14, 16, 20, 39]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 13, 14, 16, 20, 41]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_118 : ∃ k : ℕ, Lonely 8 (([4, 12, 13, 14, 16, 20, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 13, 14, 16, 20, 41]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 13, 14, 22, 35, 44]`, flank `13`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_119 : ∃ k : ℕ, Lonely 8 (([4, 12, 13, 14, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 13, 14, 22, 35, 44]) (e := 13) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 14, 16, 20, 26, 39]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_120 : ∃ k : ℕ, Lonely 8 (([4, 12, 14, 16, 20, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 14, 16, 20, 26, 39]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 14, 16, 20, 26, 53]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_121 : ∃ k : ℕ, Lonely 8 (([4, 12, 14, 16, 20, 26, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 14, 16, 20, 26, 53]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 14, 16, 20, 27, 53]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_122 : ∃ k : ℕ, Lonely 8 (([4, 12, 14, 16, 20, 27, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 14, 16, 20, 27, 53]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 36, 41]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_123 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 36, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 36, 41]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 36, 47]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_124 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 36, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 36, 47]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 44, 47]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_125 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 44, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 44, 47]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 44, 49]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_126 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 44, 49].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 44, 49]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 44, 53]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_127 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 44, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 44, 53]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 44, 55]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_128 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 44, 55]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 20, 28, 52, 53]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_129 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 20, 28, 52, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 20, 28, 52, 53]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 28, 40, 44, 47]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_130 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 28, 40, 44, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 28, 40, 44, 47]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 16, 28, 40, 44, 55]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_131 : ∃ k : ℕ, Lonely 8 (([4, 12, 16, 28, 40, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 16, 28, 40, 44, 55]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 12, 17, 21, 25, 33, 34]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_132 : ∃ k : ℕ, Lonely 8 (([4, 12, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 12, 17, 21, 25, 33, 34]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 15, 22, 26, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_133 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 15, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 15, 22, 26, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 15, 22, 35, 44]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_134 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 15, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 15, 22, 35, 44]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 16, 22, 30, 33]`, flank `14`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_135 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 16, 22, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 16, 22, 30, 33]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 18, 22, 35, 44]`, flank `13`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_136 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 18, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 18, 22, 35, 44]) (e := 13) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 21, 22, 35, 44]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_137 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 21, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 21, 22, 35, 44]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 14, 22, 24, 35, 44]`, flank `13`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_138 : ∃ k : ℕ, Lonely 8 (([4, 13, 14, 22, 24, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 14, 22, 24, 35, 44]) (e := 13) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 15, 28, 34, 40, 56]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_139 : ∃ k : ℕ, Lonely 8 (([4, 13, 15, 28, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 15, 28, 34, 40, 56]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 16, 22, 24, 35, 44]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_140 : ∃ k : ℕ, Lonely 8 (([4, 13, 16, 22, 24, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 16, 22, 24, 35, 44]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 18, 22, 31, 35, 36]`, flank `13`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_141 : ∃ k : ℕ, Lonely 8 (([4, 13, 18, 22, 31, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 18, 22, 31, 35, 36]) (e := 13) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 22, 24, 30, 35, 44]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_142 : ∃ k : ℕ, Lonely 8 (([4, 13, 22, 24, 30, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 22, 24, 30, 35, 44]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 13, 22, 24, 32, 35, 44]`, flank `13`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_143 : ∃ k : ℕ, Lonely 8 (([4, 13, 22, 24, 32, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 13, 22, 24, 32, 35, 44]) (e := 13) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 16, 19, 24, 48]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_144 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 16, 19, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 16, 19, 24, 48]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 16, 24, 29, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_145 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 16, 24, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 16, 24, 29, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 19, 22, 23, 46]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_146 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 19, 22, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 19, 22, 23, 46]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 19, 24, 32, 48]`, flank `14`, opening `9`.  Covers 1 census rows. -/
theorem fam_4_147 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 19, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 19, 24, 32, 48]) (e := 14) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 20, 23, 24, 30]`, flank `15`, opening `5`.  Covers 2 census rows. -/
theorem fam_4_148 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 20, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 20, 23, 24, 30]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 20, 24, 25, 30]`, flank `15`, opening `5`.  Covers 2 census rows. -/
theorem fam_4_149 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 20, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 20, 24, 25, 30]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 22, 26, 37, 44]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_150 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 22, 26, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 22, 26, 37, 44]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 15, 24, 29, 32, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_151 : ∃ k : ℕ, Lonely 8 (([4, 14, 15, 24, 29, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 15, 24, 29, 32, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 16, 18, 19, 35, 38]`, flank `14`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_152 : ∃ k : ℕ, Lonely 8 (([4, 14, 16, 18, 19, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 16, 18, 19, 35, 38]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 17, 18, 25, 32, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_153 : ∃ k : ℕ, Lonely 8 (([4, 14, 17, 18, 25, 32, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 17, 18, 25, 32, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 17, 20, 23, 24, 30]`, flank `17`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_154 : ∃ k : ℕ, Lonely 8 (([4, 14, 17, 20, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 17, 20, 23, 24, 30]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 17, 20, 24, 25, 30]`, flank `17`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_155 : ∃ k : ℕ, Lonely 8 (([4, 14, 17, 20, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 17, 20, 24, 25, 30]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 17, 26, 30, 43, 52]`, flank `14`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_156 : ∃ k : ℕ, Lonely 8 (([4, 14, 17, 26, 30, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 17, 26, 30, 43, 52]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 14, 21, 22, 25, 29, 42]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_157 : ∃ k : ℕ, Lonely 8 (([4, 14, 21, 22, 25, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 14, 21, 22, 25, 29, 42]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 16, 19, 21, 29, 32]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_158 : ∃ k : ℕ, Lonely 8 (([4, 15, 16, 19, 21, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 16, 19, 21, 29, 32]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 17, 21, 25, 33, 34]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_159 : ∃ k : ℕ, Lonely 8 (([4, 15, 17, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 17, 21, 25, 33, 34]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 18, 19, 27, 35, 38]`, flank `15`, opening `10`.  Covers 1 census rows. -/
theorem fam_4_160 : ∃ k : ℕ, Lonely 8 (([4, 15, 18, 19, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨10, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 18, 19, 27, 35, 38]) (e := 15) (k := 10)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 19, 20, 23, 28, 30]`, flank `4`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_161 : ∃ k : ℕ, Lonely 8 (([4, 15, 19, 20, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 19, 20, 23, 28, 30]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 19, 21, 23, 24, 30]`, flank `15`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_162 : ∃ k : ℕ, Lonely 8 (([4, 15, 19, 21, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 19, 21, 23, 24, 30]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 19, 21, 23, 27, 30]`, flank `15`, opening `5`.  Covers 2 census rows. -/
theorem fam_4_163 : ∃ k : ℕ, Lonely 8 (([4, 15, 19, 21, 23, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 19, 21, 23, 27, 30]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 19, 23, 34, 35, 46]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_164 : ∃ k : ℕ, Lonely 8 (([4, 15, 19, 23, 34, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 19, 23, 34, 35, 46]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 19, 23, 34, 42, 46]`, flank `15`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_165 : ∃ k : ℕ, Lonely 8 (([4, 15, 19, 23, 34, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 19, 23, 34, 42, 46]) (e := 15) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 20, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_166 : ∃ k : ℕ, Lonely 8 (([4, 15, 20, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 20, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 20, 24, 25, 28, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_4_167 : ∃ k : ℕ, Lonely 8 (([4, 15, 20, 24, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 20, 24, 25, 28, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 20, 33, 35, 37, 40]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_168 : ∃ k : ℕ, Lonely 8 (([4, 15, 20, 33, 35, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 20, 33, 35, 37, 40]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 21, 23, 25, 27, 32]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_169 : ∃ k : ℕ, Lonely 8 (([4, 15, 21, 23, 25, 27, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 21, 23, 25, 27, 32]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 22, 23, 24, 28, 30]`, flank `4`, opening `1`.  Covers 2 census rows. -/
theorem fam_4_170 : ∃ k : ℕ, Lonely 8 (([4, 15, 22, 23, 24, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 22, 23, 24, 28, 30]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 15, 26, 34, 41, 42, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_171 : ∃ k : ℕ, Lonely 8 (([4, 15, 26, 34, 41, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 15, 26, 34, 41, 42, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 18, 20, 23, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_172 : ∃ k : ℕ, Lonely 8 (([4, 16, 18, 20, 23, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 18, 20, 23, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 20, 24, 28, 44, 45]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_173 : ∃ k : ℕ, Lonely 8 (([4, 16, 20, 24, 28, 44, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 20, 24, 28, 44, 45]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 20, 24, 28, 44, 49]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_174 : ∃ k : ℕ, Lonely 8 (([4, 16, 20, 24, 28, 44, 49].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 20, 24, 28, 44, 49]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 20, 24, 28, 44, 55]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_175 : ∃ k : ℕ, Lonely 8 (([4, 16, 20, 24, 28, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 20, 24, 28, 44, 55]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 24, 28, 40, 44, 45]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_176 : ∃ k : ℕ, Lonely 8 (([4, 16, 24, 28, 40, 44, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 24, 28, 40, 44, 45]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 24, 28, 40, 44, 47]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_177 : ∃ k : ℕ, Lonely 8 (([4, 16, 24, 28, 40, 44, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 24, 28, 40, 44, 47]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 16, 24, 28, 40, 44, 55]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_178 : ∃ k : ℕ, Lonely 8 (([4, 16, 24, 28, 40, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 16, 24, 28, 40, 44, 55]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 17, 18, 21, 25, 33, 34]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_179 : ∃ k : ℕ, Lonely 8 (([4, 17, 18, 21, 25, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 17, 18, 21, 25, 33, 34]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 17, 18, 26, 30, 35, 36]`, flank `17`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_180 : ∃ k : ℕ, Lonely 8 (([4, 17, 18, 26, 30, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 17, 18, 26, 30, 35, 36]) (e := 17) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 17, 20, 21, 27, 31, 40]`, flank `17`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_181 : ∃ k : ℕ, Lonely 8 (([4, 17, 20, 21, 27, 31, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [4, 17, 20, 21, 27, 31, 40]) (e := 17) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 17, 26, 28, 30, 43, 52]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_182 : ∃ k : ℕ, Lonely 8 (([4, 17, 26, 28, 30, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 17, 26, 28, 30, 43, 52]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 17, 26, 30, 42, 43, 52]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_183 : ∃ k : ℕ, Lonely 8 (([4, 17, 26, 30, 42, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 17, 26, 30, 42, 43, 52]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 18, 19, 23, 27, 35, 38]`, flank `18`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_184 : ∃ k : ℕ, Lonely 8 (([4, 18, 19, 23, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 18, 19, 23, 27, 35, 38]) (e := 18) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 18, 22, 24, 26, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_185 : ∃ k : ℕ, Lonely 8 (([4, 18, 22, 24, 26, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 18, 22, 24, 26, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 18, 22, 25, 28, 32, 35]`, flank `18`, opening `11`.  Covers 1 census rows. -/
theorem fam_4_186 : ∃ k : ℕ, Lonely 8 (([4, 18, 22, 25, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [4, 18, 22, 25, 28, 32, 35]) (e := 18) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 19, 20, 21, 23, 27, 38]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_187 : ∃ k : ℕ, Lonely 8 (([4, 19, 20, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 19, 20, 21, 23, 27, 38]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 19, 20, 23, 27, 28, 54]`, flank `4`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_188 : ∃ k : ℕ, Lonely 8 (([4, 19, 20, 23, 27, 28, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [4, 19, 20, 23, 27, 28, 54]) (e := 4) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 19, 23, 27, 31, 35, 46]`, flank `19`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_189 : ∃ k : ℕ, Lonely 8 (([4, 19, 23, 27, 31, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [4, 19, 23, 27, 31, 35, 46]) (e := 19) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 20, 23, 27, 31, 35, 46]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_190 : ∃ k : ℕ, Lonely 8 (([4, 20, 23, 27, 31, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 20, 23, 27, 31, 35, 46]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 20, 24, 28, 32, 44, 49]`, flank `20`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_191 : ∃ k : ℕ, Lonely 8 (([4, 20, 24, 28, 32, 44, 49].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 20, 24, 28, 32, 44, 49]) (e := 20) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 20, 24, 28, 32, 52, 53]`, flank `24`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_192 : ∃ k : ℕ, Lonely 8 (([4, 20, 24, 28, 32, 52, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 20, 24, 28, 32, 52, 53]) (e := 24) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 21, 22, 25, 28, 29, 42]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_193 : ∃ k : ℕ, Lonely 8 (([4, 21, 22, 25, 28, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 21, 22, 25, 28, 29, 42]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 21, 25, 33, 40, 41, 50]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_194 : ∃ k : ℕ, Lonely 8 (([4, 21, 25, 33, 40, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 21, 25, 33, 40, 41, 50]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 21, 26, 30, 34, 37, 52]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_195 : ∃ k : ℕ, Lonely 8 (([4, 21, 26, 30, 34, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [4, 21, 26, 30, 34, 37, 52]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 21, 26, 30, 34, 47, 52]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_196 : ∃ k : ℕ, Lonely 8 (([4, 21, 26, 30, 34, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 21, 26, 30, 34, 47, 52]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 21, 27, 29, 31, 33, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_197 : ∃ k : ℕ, Lonely 8 (([4, 21, 27, 29, 31, 33, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 21, 27, 29, 31, 33, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 23, 27, 31, 35, 38, 46]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_198 : ∃ k : ℕ, Lonely 8 (([4, 23, 27, 31, 35, 38, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [4, 23, 27, 31, 35, 38, 46]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 23, 28, 32, 34, 36, 45]`, flank `23`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_199 : ∃ k : ℕ, Lonely 8 (([4, 23, 28, 32, 34, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((23 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 23, 28, 32, 34, 36, 45]) (e := 23) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 24, 31, 32, 35, 39, 42]`, flank `24`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_200 : ∃ k : ℕ, Lonely 8 (([4, 24, 31, 32, 35, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [4, 24, 31, 32, 35, 39, 42]) (e := 24) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 24, 32, 40, 44, 56, 57]`, flank `24`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_201 : ∃ k : ℕ, Lonely 8 (([4, 24, 32, 40, 44, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 24, 32, 40, 44, 56, 57]) (e := 24) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 24, 35, 39, 43, 47, 48]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_202 : ∃ k : ℕ, Lonely 8 (([4, 24, 35, 39, 43, 47, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [4, 24, 35, 39, 43, 47, 48]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[4, 26, 30, 33, 34, 49, 52]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_203 : ∃ k : ℕ, Lonely 8 (([4, 26, 30, 33, 34, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [4, 26, 30, 33, 34, 49, 52]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 7, 13, 19, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_204 : ∃ k : ℕ, Lonely 8 (([5, 6, 7, 13, 19, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 7, 13, 19, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 8, 11, 21, 30, 60]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_205 : ∃ k : ℕ, Lonely 8 (([5, 6, 8, 11, 21, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 8, 11, 21, 30, 60]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 8, 16, 21, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_206 : ∃ k : ℕ, Lonely 8 (([5, 6, 8, 16, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 8, 16, 21, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 8, 18, 21, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_207 : ∃ k : ℕ, Lonely 8 (([5, 6, 8, 18, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 8, 18, 21, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 8, 21, 26, 34, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_208 : ∃ k : ℕ, Lonely 8 (([5, 6, 8, 21, 26, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 8, 21, 26, 34, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 9, 14, 22, 40, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_209 : ∃ k : ℕ, Lonely 8 (([5, 6, 9, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 9, 14, 22, 40, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 16, 17, 28, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_210 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 16, 17, 28, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 16, 17, 28, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 16, 21, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_211 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 16, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 16, 21, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 16, 21, 27, 54]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_212 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 16, 21, 27, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 16, 21, 27, 54]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 16, 21, 27, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_213 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 16, 21, 27, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 16, 21, 27, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 17, 23, 28, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_214 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 17, 23, 28, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 17, 23, 28, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 17, 28, 39, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_215 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 17, 28, 39, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 17, 28, 39, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 11, 30, 43, 56, 60]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_216 : ∃ k : ℕ, Lonely 8 (([5, 6, 11, 30, 43, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 11, 30, 43, 56, 60]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 13, 30, 43, 56, 60]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_217 : ∃ k : ℕ, Lonely 8 (([5, 6, 13, 30, 43, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 13, 30, 43, 56, 60]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 14, 16, 21, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_218 : ∃ k : ℕ, Lonely 8 (([5, 6, 14, 16, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 14, 16, 21, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 14, 17, 22, 36, 44]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_219 : ∃ k : ℕ, Lonely 8 (([5, 6, 14, 17, 22, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 14, 17, 22, 36, 44]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 14, 17, 22, 40, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_220 : ∃ k : ℕ, Lonely 8 (([5, 6, 14, 17, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 14, 17, 22, 40, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 14, 22, 35, 40, 44]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_221 : ∃ k : ℕ, Lonely 8 (([5, 6, 14, 22, 35, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 14, 22, 35, 40, 44]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 17, 22, 28, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_222 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 17, 22, 28, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 17, 22, 28, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 17, 22, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_223 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 17, 22, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 17, 22, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 17, 28, 33, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_224 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 17, 28, 33, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 17, 28, 33, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 17, 28, 44, 55]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_225 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 17, 28, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 17, 28, 44, 55]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 19, 21, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_226 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 19, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 19, 21, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 22, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_227 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 22, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 22, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 22, 27, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_228 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 22, 27, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 22, 27, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_229 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 30, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_230 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 30, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 33, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_231 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 33, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 33, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 36, 52]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_232 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 36, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 36, 52]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 41, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_233 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 41, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 44, 52]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_234 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 44, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 44, 52]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 26, 47, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_235 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 26, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 26, 47, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 27, 33, 55]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_236 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 27, 33, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 27, 33, 55]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 27, 44, 55]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_237 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 27, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 27, 44, 55]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 21, 28, 44, 55]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_238 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 21, 28, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 21, 28, 44, 55]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 22, 27, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_239 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 22, 27, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 22, 27, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 16, 28, 38, 44, 55]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_240 : ∃ k : ℕ, Lonely 8 (([5, 6, 16, 28, 38, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 16, 28, 38, 44, 55]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 17, 22, 28, 37, 44]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_241 : ∃ k : ℕ, Lonely 8 (([5, 6, 17, 22, 28, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 17, 22, 28, 37, 44]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 17, 22, 28, 39, 44]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_242 : ∃ k : ℕ, Lonely 8 (([5, 6, 17, 22, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 17, 22, 28, 39, 44]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 17, 22, 32, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_243 : ∃ k : ℕ, Lonely 8 (([5, 6, 17, 22, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 17, 22, 32, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 22, 27, 32, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_244 : ∃ k : ℕ, Lonely 8 (([5, 6, 22, 27, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 22, 27, 32, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 6, 23, 28, 38, 48, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_245 : ∃ k : ℕ, Lonely 8 (([5, 6, 23, 28, 38, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 6, 23, 28, 38, 48, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 8, 9, 15, 23, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_246 : ∃ k : ℕ, Lonely 8 (([5, 7, 8, 9, 15, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 8, 9, 15, 23, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 8, 13, 20, 33, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_247 : ∃ k : ℕ, Lonely 8 (([5, 7, 8, 13, 20, 33, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 8, 13, 20, 33, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 8, 20, 26, 33, 39]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_248 : ∃ k : ℕ, Lonely 8 (([5, 7, 8, 20, 26, 33, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 8, 20, 26, 33, 39]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 11, 16, 25, 50]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_249 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 11, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 11, 16, 25, 50]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 30, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_250 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 30, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_251 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 32, 38]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_252 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 32, 38]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 33, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_253 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 33, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 33, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 34, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_254 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 34, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 34, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 35, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_255 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 35, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 36, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_256 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 36, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 36, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 12, 19, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_257 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 12, 19, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 12, 19, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 13, 19, 30, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_258 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 13, 19, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 13, 19, 30, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 13, 19, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_259 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 13, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 13, 19, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 13, 19, 34, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_260 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 13, 19, 34, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 13, 19, 34, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 13, 19, 36, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_261 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 13, 19, 36, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 13, 19, 36, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 14, 19, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_262 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 14, 19, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 14, 19, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 15, 16, 25, 50]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_263 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 15, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 15, 16, 25, 50]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 25, 30, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_264 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 25, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 25, 30, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 25, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_265 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 25, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 25, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 25, 34, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_266 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 25, 34, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 25, 34, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 25, 36, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_267 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 25, 36, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 25, 36, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 26, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_268 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 26, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 26, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 9, 19, 28, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_269 : ∃ k : ℕ, Lonely 8 (([5, 7, 9, 19, 28, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 9, 19, 28, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 11, 17, 18, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_270 : ∃ k : ℕ, Lonely 8 (([5, 7, 11, 17, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 11, 17, 18, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 11, 18, 19, 32, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_271 : ∃ k : ℕ, Lonely 8 (([5, 7, 11, 18, 19, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 11, 18, 19, 32, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 11, 18, 21, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_272 : ∃ k : ℕ, Lonely 8 (([5, 7, 11, 18, 21, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 11, 18, 21, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 11, 18, 23, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_273 : ∃ k : ℕ, Lonely 8 (([5, 7, 11, 18, 23, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 11, 18, 23, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 11, 18, 25, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_274 : ∃ k : ℕ, Lonely 8 (([5, 7, 11, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 11, 18, 25, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 17, 22, 29, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_275 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 17, 22, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 17, 22, 29, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 18, 25, 32, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_276 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 18, 25, 32, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 20, 30, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_277 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 20, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 20, 30, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 20, 34, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_278 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 20, 34, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 20, 34, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 26, 31, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_279 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 26, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 26, 31, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 26, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_280 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 26, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 26, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 29, 30, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_281 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 29, 30, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 29, 30, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 29, 34, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_282 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 29, 34, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 29, 34, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 12, 19, 31, 43, 60]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_283 : ∃ k : ℕ, Lonely 8 (([5, 7, 12, 19, 31, 43, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 12, 19, 31, 43, 60]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 13, 17, 24, 29, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_284 : ∃ k : ℕ, Lonely 8 (([5, 7, 13, 17, 24, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 13, 17, 24, 29, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 13, 18, 19, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_285 : ∃ k : ℕ, Lonely 8 (([5, 7, 13, 18, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 13, 18, 19, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 13, 18, 19, 35, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_286 : ∃ k : ℕ, Lonely 8 (([5, 7, 13, 18, 19, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 13, 18, 19, 35, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 16, 18, 25, 34, 36]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_287 : ∃ k : ℕ, Lonely 8 (([5, 7, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 16, 18, 25, 34, 36]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 17, 19, 24, 27, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_288 : ∃ k : ℕ, Lonely 8 (([5, 7, 17, 19, 24, 27, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 17, 19, 24, 27, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 17, 19, 24, 31, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_289 : ∃ k : ℕ, Lonely 8 (([5, 7, 17, 19, 24, 31, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 17, 19, 24, 31, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 17, 22, 24, 29, 36]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_290 : ∃ k : ℕ, Lonely 8 (([5, 7, 17, 22, 24, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 17, 22, 24, 29, 36]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 17, 22, 24, 29, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_291 : ∃ k : ℕ, Lonely 8 (([5, 7, 17, 22, 24, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 17, 22, 24, 29, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 17, 24, 29, 35, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_292 : ∃ k : ℕ, Lonely 8 (([5, 7, 17, 24, 29, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 17, 24, 29, 35, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 19, 26, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_293 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 19, 26, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 19, 26, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 22, 25, 32, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_294 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 22, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 22, 25, 32, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 22, 29, 36, 44]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_295 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 22, 29, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 22, 29, 36, 44]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 22, 29, 40, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_296 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 22, 29, 40, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 23, 25, 32, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_297 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 23, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 23, 25, 32, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 24, 25, 32, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_298 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 24, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 24, 25, 32, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 25, 30, 35, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_299 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 25, 30, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 25, 30, 35, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 25, 32, 34, 36]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_300 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 25, 32, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 25, 32, 34, 36]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 18, 25, 32, 35, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_301 : ∃ k : ℕ, Lonely 8 (([5, 7, 18, 25, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 18, 25, 32, 35, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 24, 25, 32, 50]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_302 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 24, 25, 32, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 24, 25, 32, 50]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 24, 26, 31, 36]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_303 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 24, 26, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 24, 26, 31, 36]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 24, 31, 34, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_304 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 24, 31, 34, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 24, 31, 34, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 24, 31, 35, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_305 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 24, 31, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 24, 31, 35, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 24, 31, 43, 60]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_306 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 24, 31, 43, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 24, 31, 43, 60]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 27, 34, 41, 54]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_307 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 27, 34, 41, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 27, 34, 41, 54]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 31, 36, 43, 60]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_308 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 31, 36, 43, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 31, 36, 43, 60]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 7, 19, 31, 43, 48, 60]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_309 : ∃ k : ℕ, Lonely 8 (([5, 7, 19, 31, 43, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 7, 19, 31, 43, 48, 60]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 9, 14, 19, 35, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_310 : ∃ k : ℕ, Lonely 8 (([5, 8, 9, 14, 19, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 9, 14, 19, 35, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 9, 14, 19, 36, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_311 : ∃ k : ℕ, Lonely 8 (([5, 8, 9, 14, 19, 36, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 9, 14, 19, 36, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 9, 14, 19, 37, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_312 : ∃ k : ℕ, Lonely 8 (([5, 8, 9, 14, 19, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 9, 14, 19, 37, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 9, 19, 27, 35, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_313 : ∃ k : ℕ, Lonely 8 (([5, 8, 9, 19, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 9, 19, 27, 35, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 9, 21, 26, 35, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_314 : ∃ k : ℕ, Lonely 8 (([5, 8, 9, 21, 26, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 9, 21, 26, 35, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 11, 13, 21, 36, 42]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_315 : ∃ k : ℕ, Lonely 8 (([5, 8, 11, 13, 21, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 11, 13, 21, 36, 42]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 11, 27, 35, 37, 54]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_316 : ∃ k : ℕ, Lonely 8 (([5, 8, 11, 27, 35, 37, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 11, 27, 35, 37, 54]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 17, 18, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_317 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 17, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 17, 18, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 18, 21, 31, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_318 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 18, 21, 31, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 18, 21, 31, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 18, 21, 34, 42]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_319 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 18, 21, 34, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 18, 21, 34, 42]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 18, 21, 37, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_320 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 18, 21, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 18, 21, 37, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 18, 25, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_321 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 18, 25, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 18, 25, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 20, 21, 36, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_322 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 20, 21, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 20, 21, 36, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 25, 37, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_323 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 25, 37, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 25, 37, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 25, 38, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_324 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 25, 38, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 25, 38, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 29, 34, 40]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_325 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 29, 34, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 29, 34, 40]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 29, 37, 40]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_326 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 29, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 29, 37, 40]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 29, 37, 42]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_327 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 29, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 29, 37, 42]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 31, 35, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_328 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 31, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 31, 35, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 31, 36, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_329 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 31, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 31, 36, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 13, 21, 31, 41, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_330 : ∃ k : ℕ, Lonely 8 (([5, 8, 13, 21, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 13, 21, 31, 41, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 14, 18, 23, 30, 36]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_331 : ∃ k : ℕ, Lonely 8 (([5, 8, 14, 18, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 14, 18, 23, 30, 36]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 14, 18, 23, 34, 36]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_332 : ∃ k : ℕ, Lonely 8 (([5, 8, 14, 18, 23, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 14, 18, 23, 34, 36]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 16, 21, 31, 41, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_333 : ∃ k : ℕ, Lonely 8 (([5, 8, 16, 21, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 16, 21, 31, 41, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 17, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_334 : ∃ k : ℕ, Lonely 8 (([5, 8, 17, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 17, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 18, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_335 : ∃ k : ℕ, Lonely 8 (([5, 8, 18, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 18, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 18, 21, 26, 31, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_336 : ∃ k : ℕ, Lonely 8 (([5, 8, 18, 21, 26, 31, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 18, 21, 26, 31, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 18, 21, 26, 31, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_337 : ∃ k : ℕ, Lonely 8 (([5, 8, 18, 21, 26, 31, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 18, 21, 26, 31, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 18, 21, 26, 37, 52]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_338 : ∃ k : ℕ, Lonely 8 (([5, 8, 18, 21, 26, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 18, 21, 26, 37, 52]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 18, 26, 31, 42, 52]`, flank `18`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_339 : ∃ k : ℕ, Lonely 8 (([5, 8, 18, 26, 31, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 18, 26, 31, 42, 52]) (e := 18) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 23, 26, 34, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_340 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 23, 26, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 23, 26, 34, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 25, 26, 35, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_341 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 25, 26, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 25, 26, 35, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 25, 26, 37, 39]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_342 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 25, 26, 37, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 25, 26, 37, 39]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 25, 26, 38, 39]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_343 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 25, 26, 38, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 25, 26, 38, 39]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 26, 29, 34, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_344 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 26, 29, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 26, 29, 34, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 26, 31, 35, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_345 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 26, 31, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 26, 31, 35, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 26, 34, 35, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_346 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 26, 34, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 26, 34, 35, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 26, 35, 43, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_347 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 26, 35, 43, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 26, 35, 43, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 29, 31, 39, 42]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_348 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 29, 31, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 29, 31, 39, 42]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 29, 31, 40, 42]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_349 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 29, 31, 40, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 29, 31, 40, 42]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 29, 31, 41, 42]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_350 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 29, 31, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 29, 31, 41, 42]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 21, 31, 35, 39, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_351 : ∃ k : ℕ, Lonely 8 (([5, 8, 21, 31, 35, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 21, 31, 35, 39, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 23, 31, 35, 39, 42]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_352 : ∃ k : ℕ, Lonely 8 (([5, 8, 23, 31, 35, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 23, 31, 35, 39, 42]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 8, 26, 27, 31, 35, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_353 : ∃ k : ℕ, Lonely 8 (([5, 8, 26, 27, 31, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 8, 26, 27, 31, 35, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 11, 14, 16, 25, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_354 : ∃ k : ℕ, Lonely 8 (([5, 9, 11, 14, 16, 25, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 11, 14, 16, 25, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 11, 16, 21, 30, 36]`, flank `9`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_355 : ∃ k : ℕ, Lonely 8 (([5, 9, 11, 16, 21, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 11, 16, 21, 30, 36]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 11, 20, 28, 31, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_356 : ∃ k : ℕ, Lonely 8 (([5, 9, 11, 20, 28, 31, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 11, 20, 28, 31, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 11, 21, 30, 32, 36]`, flank `9`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_357 : ∃ k : ℕ, Lonely 8 (([5, 9, 11, 21, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 11, 21, 30, 32, 36]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 12, 14, 19, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_358 : ∃ k : ℕ, Lonely 8 (([5, 9, 12, 14, 19, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 12, 14, 19, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 12, 14, 19, 32, 38]`, flank `9`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_359 : ∃ k : ℕ, Lonely 8 (([5, 9, 12, 14, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 12, 14, 19, 32, 38]) (e := 9) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 13, 14, 19, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_360 : ∃ k : ℕ, Lonely 8 (([5, 9, 13, 14, 19, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 13, 14, 19, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 13, 14, 19, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_361 : ∃ k : ℕ, Lonely 8 (([5, 9, 13, 14, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 13, 14, 19, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 15, 19, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_362 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 15, 19, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 15, 19, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 16, 19, 37, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_363 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 16, 19, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 16, 19, 37, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 16, 23, 37, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_364 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 16, 23, 37, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 16, 23, 37, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 21, 36, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_365 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 21, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 21, 36, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 22, 40, 44]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_366 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 22, 40, 44]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 23, 33, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_367 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 23, 33, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 23, 33, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 23, 33, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_368 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 23, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 23, 33, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 23, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_369 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 23, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 23, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 23, 37, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_370 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 23, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 23, 37, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 23, 41, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_371 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 23, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 23, 41, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 24, 33, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_372 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 24, 33, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 24, 33, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 24, 33, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_373 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 24, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 24, 33, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 24, 33, 48]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_374 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 24, 33, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 24, 33, 48]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 24, 37, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_375 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 24, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 24, 37, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 25, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_376 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 25, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 25, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 25, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_377 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 25, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 25, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 31, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_378 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 31, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 31, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 19, 32, 37, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_379 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 19, 32, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 19, 32, 37, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 22, 25, 40, 44]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_380 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 22, 25, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 22, 25, 40, 44]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 23, 32, 37, 40]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_381 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 23, 32, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 23, 32, 37, 40]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 23, 32, 37, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_382 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 23, 32, 37, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 23, 32, 37, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 14, 23, 32, 41, 45]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_383 : ∃ k : ℕ, Lonely 8 (([5, 9, 14, 23, 32, 41, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 14, 23, 32, 41, 45]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 17, 25, 42, 43, 50]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_384 : ∃ k : ℕ, Lonely 8 (([5, 9, 17, 25, 42, 43, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 17, 25, 42, 43, 50]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 21, 28, 36, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_385 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 21, 28, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 21, 28, 36, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 23, 28, 33, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_386 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 23, 28, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 23, 28, 33, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 23, 28, 33, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_387 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 23, 28, 33, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 23, 28, 33, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 23, 28, 37, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_388 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 23, 28, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 23, 28, 37, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 23, 28, 37, 56]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_389 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 23, 28, 37, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 23, 28, 37, 56]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 23, 28, 41, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_390 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 23, 28, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 23, 28, 41, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 24, 28, 33, 42]`, flank `9`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_391 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 24, 28, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 24, 28, 33, 42]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 24, 28, 33, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_392 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 24, 28, 33, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 24, 28, 33, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 24, 28, 37, 38]`, flank `9`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_393 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 24, 28, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 24, 28, 37, 38]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 28, 31, 37, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_394 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 28, 31, 37, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 28, 31, 37, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 19, 28, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_395 : ∃ k : ℕ, Lonely 8 (([5, 9, 19, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 19, 28, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 22, 26, 35, 48, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_396 : ∃ k : ℕ, Lonely 8 (([5, 9, 22, 26, 35, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 22, 26, 35, 48, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 23, 28, 32, 37, 40]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_397 : ∃ k : ℕ, Lonely 8 (([5, 9, 23, 28, 32, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 23, 28, 32, 37, 40]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 23, 28, 32, 37, 56]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_398 : ∃ k : ℕ, Lonely 8 (([5, 9, 23, 28, 32, 37, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 23, 28, 32, 37, 56]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 23, 28, 37, 51, 56]`, flank `23`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_399 : ∃ k : ℕ, Lonely 8 (([5, 9, 23, 28, 37, 51, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((23 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 23, 28, 37, 51, 56]) (e := 23) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 9, 25, 34, 43, 49, 50]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_400 : ∃ k : ℕ, Lonely 8 (([5, 9, 25, 34, 43, 49, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 9, 25, 34, 43, 49, 50]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 10, 15, 20, 25, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_401 : ∃ k : ℕ, Lonely 8 (([5, 10, 15, 20, 25, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 10, 15, 20, 25, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 10, 15, 20, 25, 35, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_402 : ∃ k : ℕ, Lonely 8 (([5, 10, 15, 20, 25, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 10, 15, 20, 25, 35, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 10, 21, 22, 32, 43, 44]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_403 : ∃ k : ℕ, Lonely 8 (([5, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 10, 21, 22, 32, 43, 44]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 12, 16, 21, 34, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_404 : ∃ k : ℕ, Lonely 8 (([5, 11, 12, 16, 21, 34, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 12, 16, 21, 34, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 12, 16, 21, 35, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_405 : ∃ k : ℕ, Lonely 8 (([5, 11, 12, 16, 21, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 12, 16, 21, 35, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 13, 21, 24, 35, 42]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_406 : ∃ k : ℕ, Lonely 8 (([5, 11, 13, 21, 24, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 13, 21, 24, 35, 42]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 14, 19, 21, 32, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_407 : ∃ k : ℕ, Lonely 8 (([5, 11, 14, 19, 21, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 14, 19, 21, 32, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 14, 19, 25, 36, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_408 : ∃ k : ℕ, Lonely 8 (([5, 11, 14, 19, 25, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 14, 19, 25, 36, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 17, 27, 42, 54]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_409 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 17, 27, 42, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 17, 27, 42, 54]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 18, 21, 30, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_410 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 18, 21, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 18, 21, 30, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 18, 21, 39, 42]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_411 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 18, 21, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 18, 21, 39, 42]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 19, 30, 35, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_412 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 19, 30, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 19, 30, 35, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 20, 27, 42, 54]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_413 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 20, 27, 42, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 20, 27, 42, 54]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_414 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 21, 26, 31, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_415 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 21, 26, 31, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 21, 26, 31, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 21, 26, 37, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_416 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 21, 26, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 21, 26, 37, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 21, 27, 30, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_417 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 21, 27, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 21, 27, 30, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 16, 27, 37, 42, 54]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_418 : ∃ k : ℕ, Lonely 8 (([5, 11, 16, 27, 37, 42, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 16, 27, 37, 42, 54]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 21, 23, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_419 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 21, 23, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 21, 23, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 21, 30, 32, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_420 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 21, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 21, 30, 32, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 23, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_421 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 23, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 23, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 23, 28, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_422 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 23, 28, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 23, 28, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 23, 28, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_423 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 23, 28, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 23, 28, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 18, 23, 32, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_424 : ∃ k : ℕ, Lonely 8 (([5, 11, 18, 23, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 18, 23, 32, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 19, 25, 28, 36, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_425 : ∃ k : ℕ, Lonely 8 (([5, 11, 19, 25, 28, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 19, 25, 28, 36, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 19, 30, 32, 35, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_426 : ∃ k : ℕ, Lonely 8 (([5, 11, 19, 30, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 19, 30, 32, 35, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 21, 23, 28, 33, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_427 : ∃ k : ℕ, Lonely 8 (([5, 11, 21, 23, 28, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 21, 23, 28, 33, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 21, 26, 32, 37, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_428 : ∃ k : ℕ, Lonely 8 (([5, 11, 21, 26, 32, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 21, 26, 32, 37, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 21, 26, 37, 48, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_429 : ∃ k : ℕ, Lonely 8 (([5, 11, 21, 26, 37, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 21, 26, 37, 48, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 21, 27, 30, 32, 36]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_430 : ∃ k : ℕ, Lonely 8 (([5, 11, 21, 27, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 21, 27, 30, 32, 36]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 11, 23, 30, 35, 41, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_431 : ∃ k : ℕ, Lonely 8 (([5, 11, 23, 30, 35, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 11, 23, 30, 35, 41, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 13, 17, 21, 38, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_432 : ∃ k : ℕ, Lonely 8 (([5, 12, 13, 17, 21, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 13, 17, 21, 38, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 14, 18, 23, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_433 : ∃ k : ℕ, Lonely 8 (([5, 12, 14, 18, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 14, 18, 23, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 14, 18, 23, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_434 : ∃ k : ℕ, Lonely 8 (([5, 12, 14, 18, 23, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 14, 18, 23, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 16, 21, 22, 34, 42]`, flank `12`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_435 : ∃ k : ℕ, Lonely 8 (([5, 12, 16, 21, 22, 34, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 16, 21, 22, 34, 42]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 16, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_436 : ∃ k : ℕ, Lonely 8 (([5, 12, 16, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 16, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 16, 21, 26, 33, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_437 : ∃ k : ℕ, Lonely 8 (([5, 12, 16, 21, 26, 33, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 16, 21, 26, 33, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 18, 23, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_438 : ∃ k : ℕ, Lonely 8 (([5, 12, 18, 23, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 18, 23, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 19, 21, 29, 31, 38]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_439 : ∃ k : ℕ, Lonely 8 (([5, 12, 19, 21, 29, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 19, 21, 29, 31, 38]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 21, 29, 33, 34, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_440 : ∃ k : ℕ, Lonely 8 (([5, 12, 21, 29, 33, 34, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 21, 29, 33, 34, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 22, 27, 32, 42, 44]`, flank `12`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_441 : ∃ k : ℕ, Lonely 8 (([5, 12, 22, 27, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 22, 27, 32, 42, 44]) (e := 12) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 12, 28, 33, 38, 48, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_442 : ∃ k : ℕ, Lonely 8 (([5, 12, 28, 33, 38, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 12, 28, 33, 38, 48, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 14, 18, 19, 32, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_443 : ∃ k : ℕ, Lonely 8 (([5, 13, 14, 18, 19, 32, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 14, 18, 19, 32, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 14, 18, 23, 41, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_444 : ∃ k : ℕ, Lonely 8 (([5, 13, 14, 18, 23, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 14, 18, 23, 41, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 16, 21, 29, 34, 40]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_445 : ∃ k : ℕ, Lonely 8 (([5, 13, 16, 21, 29, 34, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 16, 21, 29, 34, 40]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 16, 21, 29, 37, 40]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_446 : ∃ k : ℕ, Lonely 8 (([5, 13, 16, 21, 29, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 16, 21, 29, 37, 40]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 17, 19, 21, 38, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_447 : ∃ k : ℕ, Lonely 8 (([5, 13, 17, 19, 21, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 17, 19, 21, 38, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 17, 19, 21, 40, 42]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_448 : ∃ k : ℕ, Lonely 8 (([5, 13, 17, 19, 21, 40, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 17, 19, 21, 40, 42]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 17, 21, 31, 34, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_449 : ∃ k : ℕ, Lonely 8 (([5, 13, 17, 21, 31, 34, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 17, 21, 31, 34, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 17, 21, 31, 38, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_450 : ∃ k : ℕ, Lonely 8 (([5, 13, 17, 21, 31, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 17, 21, 31, 38, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 18, 23, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_451 : ∃ k : ℕ, Lonely 8 (([5, 13, 18, 23, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 18, 23, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 18, 23, 28, 33, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_452 : ∃ k : ℕ, Lonely 8 (([5, 13, 18, 23, 28, 33, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 18, 23, 28, 33, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 18, 23, 28, 41, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_453 : ∃ k : ℕ, Lonely 8 (([5, 13, 18, 23, 28, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 18, 23, 28, 41, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 19, 20, 33, 35, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_454 : ∃ k : ℕ, Lonely 8 (([5, 13, 19, 20, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 19, 20, 33, 35, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 19, 28, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_455 : ∃ k : ℕ, Lonely 8 (([5, 13, 19, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 19, 28, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 21, 24, 29, 34, 40]`, flank `13`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_456 : ∃ k : ℕ, Lonely 8 (([5, 13, 21, 24, 29, 34, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 21, 24, 29, 34, 40]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 21, 24, 29, 37, 40]`, flank `13`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_457 : ∃ k : ℕ, Lonely 8 (([5, 13, 21, 24, 29, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 21, 24, 29, 37, 40]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 21, 29, 32, 34, 40]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_458 : ∃ k : ℕ, Lonely 8 (([5, 13, 21, 29, 32, 34, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 21, 29, 32, 34, 40]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 21, 29, 32, 37, 40]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_459 : ∃ k : ℕ, Lonely 8 (([5, 13, 21, 29, 32, 37, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 21, 29, 32, 37, 40]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 30, 31, 43, 56, 60]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_460 : ∃ k : ℕ, Lonely 8 (([5, 13, 30, 31, 43, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 30, 31, 43, 56, 60]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 13, 30, 35, 43, 48, 52]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_461 : ∃ k : ℕ, Lonely 8 (([5, 13, 30, 35, 43, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 13, 30, 35, 43, 48, 52]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 16, 18, 23, 30, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_462 : ∃ k : ℕ, Lonely 8 (([5, 14, 16, 18, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 16, 18, 23, 30, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 16, 18, 23, 34, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_463 : ∃ k : ℕ, Lonely 8 (([5, 14, 16, 18, 23, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 16, 18, 23, 34, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 17, 19, 20, 33, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_464 : ∃ k : ℕ, Lonely 8 (([5, 14, 17, 19, 20, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 17, 19, 20, 33, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 19, 20, 32, 40]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_465 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 19, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 19, 20, 32, 40]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 19, 21, 33, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_466 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 19, 21, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 19, 21, 33, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 20, 23, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_467 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 20, 23, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 20, 23, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 20, 23, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_468 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 20, 23, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 20, 23, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 20, 25, 32, 40]`, flank `14`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_469 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 20, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 20, 25, 32, 40]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 23, 24, 30, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_470 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 23, 24, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 23, 24, 30, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 23, 24, 34, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_471 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 23, 24, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 23, 24, 34, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 23, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_472 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 23, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 23, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 23, 28, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_473 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 23, 28, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 23, 28, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 18, 23, 32, 41, 45]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_474 : ∃ k : ℕ, Lonely 8 (([5, 14, 18, 23, 32, 41, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 18, 23, 32, 41, 45]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 19, 34, 48, 53, 57]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_475 : ∃ k : ℕ, Lonely 8 (([5, 14, 19, 34, 48, 53, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 19, 34, 48, 53, 57]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 23, 27, 32, 41, 45]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_476 : ∃ k : ℕ, Lonely 8 (([5, 14, 23, 27, 32, 41, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 23, 27, 32, 41, 45]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 23, 32, 36, 41, 45]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_477 : ∃ k : ℕ, Lonely 8 (([5, 14, 23, 32, 36, 41, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 23, 32, 36, 41, 45]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 14, 34, 38, 48, 53, 57]`, flank `14`, opening `9`.  Covers 1 census rows. -/
theorem fam_4_478 : ∃ k : ℕ, Lonely 8 (([5, 14, 34, 38, 48, 53, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [5, 14, 34, 38, 48, 53, 57]) (e := 14) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 15, 20, 23, 25, 35, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_479 : ∃ k : ℕ, Lonely 8 (([5, 15, 20, 23, 25, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 15, 20, 23, 25, 35, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 15, 20, 25, 29, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_480 : ∃ k : ℕ, Lonely 8 (([5, 15, 20, 25, 29, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 15, 20, 25, 29, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 15, 20, 25, 33, 35, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_481 : ∃ k : ℕ, Lonely 8 (([5, 15, 20, 25, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 15, 20, 25, 33, 35, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 17, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_482 : ∃ k : ℕ, Lonely 8 (([5, 16, 17, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 17, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 18, 21, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_483 : ∃ k : ℕ, Lonely 8 (([5, 16, 18, 21, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 18, 21, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 18, 25, 30, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_484 : ∃ k : ℕ, Lonely 8 (([5, 16, 18, 25, 30, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 18, 25, 30, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 23, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_485 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 23, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 23, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 23, 33, 37, 46]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_486 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 23, 33, 37, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 23, 33, 37, 46]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 24, 25, 26, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_487 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 24, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 24, 25, 26, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 25, 26, 29, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_488 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 25, 26, 29, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 25, 26, 29, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 25, 26, 30, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_489 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 25, 26, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 25, 26, 30, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 25, 26, 35, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_490 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 25, 26, 35, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 25, 26, 35, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 25, 26, 41, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_491 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 25, 26, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 25, 26, 41, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 25, 26, 47, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_492 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 25, 26, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 25, 26, 47, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 30, 31, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_493 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 30, 31, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 30, 31, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 30, 37, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_494 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 30, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 30, 37, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 31, 36, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_495 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 31, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 31, 36, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 31, 41, 52]`, flank `16`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_496 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 31, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 31, 41, 52]) (e := 16) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 31, 47, 52]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_497 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 31, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 31, 47, 52]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 37, 41, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_498 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 37, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 37, 41, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 21, 26, 37, 47, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_499 : ∃ k : ℕ, Lonely 8 (([5, 16, 21, 26, 37, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 21, 26, 37, 47, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 16, 26, 30, 31, 42, 52]`, flank `16`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_500 : ∃ k : ℕ, Lonely 8 (([5, 16, 26, 30, 31, 42, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 16, 26, 30, 31, 42, 52]) (e := 16) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 19, 20, 28, 33, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_501 : ∃ k : ℕ, Lonely 8 (([5, 17, 19, 20, 28, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 19, 20, 28, 33, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 19, 28, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_502 : ∃ k : ℕ, Lonely 8 (([5, 17, 19, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 19, 28, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 21, 22, 27, 48, 54]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_503 : ∃ k : ℕ, Lonely 8 (([5, 17, 21, 22, 27, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 21, 22, 27, 48, 54]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 21, 22, 32, 43, 44]`, flank `17`, opening `14`.  Covers 1 census rows. -/
theorem fam_4_504 : ∃ k : ℕ, Lonely 8 (([5, 17, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨14, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 21, 22, 32, 43, 44]) (e := 17) (k := 14)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 21, 26, 31, 35, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_505 : ∃ k : ℕ, Lonely 8 (([5, 17, 21, 26, 31, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 21, 26, 31, 35, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 17, 23, 30, 35, 40, 42]`, flank `17`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_506 : ∃ k : ℕ, Lonely 8 (([5, 17, 23, 30, 35, 40, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 17, 23, 30, 35, 40, 42]) (e := 17) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 19, 21, 28, 33, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_507 : ∃ k : ℕ, Lonely 8 (([5, 18, 19, 21, 28, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 19, 21, 28, 33, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 20, 25, 28, 32, 40]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_508 : ∃ k : ℕ, Lonely 8 (([5, 18, 20, 25, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 20, 25, 28, 32, 40]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 20, 27, 28, 32, 40]`, flank `18`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_509 : ∃ k : ℕ, Lonely 8 (([5, 18, 20, 27, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 20, 27, 28, 32, 40]) (e := 18) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 21, 23, 25, 32, 36]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_510 : ∃ k : ℕ, Lonely 8 (([5, 18, 21, 23, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 21, 23, 25, 32, 36]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 22, 27, 32, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_511 : ∃ k : ℕ, Lonely 8 (([5, 18, 22, 27, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 22, 27, 32, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 24, 28, 30, 36]`, flank `18`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_512 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 24, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 24, 28, 30, 36]) (e := 18) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 25, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_513 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 25, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 25, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 25, 28, 32, 36]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_514 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 25, 28, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 25, 28, 32, 36]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 25, 28, 34, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_515 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 25, 28, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 25, 28, 34, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 25, 32, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_516 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 25, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 25, 32, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 23, 26, 28, 30, 36]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_517 : ∃ k : ℕ, Lonely 8 (([5, 18, 23, 26, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 23, 26, 28, 30, 36]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 25, 30, 32, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_518 : ∃ k : ℕ, Lonely 8 (([5, 18, 25, 30, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 25, 30, 32, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 18, 26, 31, 44, 49, 52]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_519 : ∃ k : ℕ, Lonely 8 (([5, 18, 26, 31, 44, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 18, 26, 31, 44, 49, 52]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 21, 23, 26, 31, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_520 : ∃ k : ℕ, Lonely 8 (([5, 19, 21, 23, 26, 31, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 21, 23, 26, 31, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 22, 28, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_521 : ∃ k : ℕ, Lonely 8 (([5, 19, 22, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 22, 28, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 26, 28, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_522 : ∃ k : ℕ, Lonely 8 (([5, 19, 26, 28, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 26, 28, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 30, 33, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_523 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 30, 33, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 30, 33, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 35, 47, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_524 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 35, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 35, 47, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 39, 47, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_525 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 39, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 39, 47, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 43, 47, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_526 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 43, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 43, 47, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 44, 47, 56]`, flank `19`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_527 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 44, 47, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 44, 47, 56]) (e := 19) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 47, 48, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_528 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 47, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 47, 48, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 19, 28, 33, 47, 52, 56]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_529 : ∃ k : ℕ, Lonely 8 (([5, 19, 28, 33, 47, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 19, 28, 33, 47, 52, 56]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 20, 25, 29, 30, 35, 36]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_530 : ∃ k : ℕ, Lonely 8 (([5, 20, 25, 29, 30, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 20, 25, 29, 30, 35, 36]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 22, 27, 32, 43, 44]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_531 : ∃ k : ℕ, Lonely 8 (([5, 21, 22, 27, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 22, 27, 32, 43, 44]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 23, 24, 28, 33, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_532 : ∃ k : ℕ, Lonely 8 (([5, 21, 23, 24, 28, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 23, 24, 28, 33, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 23, 26, 36, 49, 52]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_533 : ∃ k : ℕ, Lonely 8 (([5, 21, 23, 26, 36, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 23, 26, 36, 49, 52]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 23, 28, 33, 35, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_534 : ∃ k : ℕ, Lonely 8 (([5, 21, 23, 28, 33, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 23, 28, 33, 35, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 24, 29, 34, 39, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_535 : ∃ k : ℕ, Lonely 8 (([5, 21, 24, 29, 34, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 24, 29, 34, 39, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 25, 26, 31, 35, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_536 : ∃ k : ℕ, Lonely 8 (([5, 21, 25, 26, 31, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 25, 26, 31, 35, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 26, 29, 31, 33, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_537 : ∃ k : ℕ, Lonely 8 (([5, 21, 26, 29, 31, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 26, 29, 31, 33, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 26, 30, 31, 48, 60]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_538 : ∃ k : ℕ, Lonely 8 (([5, 21, 26, 30, 31, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 26, 30, 31, 48, 60]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 26, 31, 32, 36, 42]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_539 : ∃ k : ℕ, Lonely 8 (([5, 21, 26, 31, 32, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 26, 31, 32, 36, 42]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 21, 26, 31, 33, 35, 42]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_540 : ∃ k : ℕ, Lonely 8 (([5, 21, 26, 31, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 21, 26, 31, 33, 35, 42]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 22, 24, 27, 32, 42, 44]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_541 : ∃ k : ℕ, Lonely 8 (([5, 22, 24, 27, 32, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 22, 24, 27, 32, 42, 44]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 23, 24, 25, 28, 33, 46]`, flank `5`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_542 : ∃ k : ℕ, Lonely 8 (([5, 23, 24, 25, 28, 33, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [5, 23, 24, 25, 28, 33, 46]) (e := 5) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 23, 28, 33, 38, 43, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_543 : ∃ k : ℕ, Lonely 8 (([5, 23, 28, 33, 38, 43, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 23, 28, 33, 38, 43, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 23, 35, 37, 40, 45, 48]`, flank `23`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_544 : ∃ k : ℕ, Lonely 8 (([5, 23, 35, 37, 40, 45, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((23 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [5, 23, 35, 37, 40, 45, 48]) (e := 23) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 24, 28, 33, 38, 44, 56]`, flank `24`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_545 : ∃ k : ℕ, Lonely 8 (([5, 24, 28, 33, 38, 44, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 24, 28, 33, 38, 44, 56]) (e := 24) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 24, 28, 33, 38, 48, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_546 : ∃ k : ℕ, Lonely 8 (([5, 24, 28, 33, 38, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 24, 28, 33, 38, 48, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 24, 28, 33, 38, 52, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_547 : ∃ k : ℕ, Lonely 8 (([5, 24, 28, 33, 38, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 24, 28, 33, 38, 52, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 25, 27, 32, 35, 37, 54]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_548 : ∃ k : ℕ, Lonely 8 (([5, 25, 27, 32, 35, 37, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [5, 25, 27, 32, 35, 37, 54]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 25, 35, 37, 40, 45, 48]`, flank `25`, opening `9`.  Covers 1 census rows. -/
theorem fam_4_549 : ∃ k : ℕ, Lonely 8 (([5, 25, 35, 37, 40, 45, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((25 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [5, 25, 35, 37, 40, 45, 48]) (e := 25) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 26, 27, 31, 35, 36, 52]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_550 : ∃ k : ℕ, Lonely 8 (([5, 26, 27, 31, 35, 36, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 26, 27, 31, 35, 36, 52]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 26, 27, 31, 35, 44, 52]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_551 : ∃ k : ℕ, Lonely 8 (([5, 26, 27, 31, 35, 44, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [5, 26, 27, 31, 35, 44, 52]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 26, 30, 35, 43, 48, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_552 : ∃ k : ℕ, Lonely 8 (([5, 26, 30, 35, 43, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 26, 30, 35, 43, 48, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 27, 29, 32, 35, 37, 54]`, flank `27`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_553 : ∃ k : ℕ, Lonely 8 (([5, 27, 29, 32, 35, 37, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((27 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 27, 29, 32, 35, 37, 54]) (e := 27) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 27, 35, 37, 40, 45, 48]`, flank `27`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_554 : ∃ k : ℕ, Lonely 8 (([5, 27, 35, 37, 40, 45, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((27 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [5, 27, 35, 37, 40, 45, 48]) (e := 27) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 28, 31, 33, 35, 38, 56]`, flank `28`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_555 : ∃ k : ℕ, Lonely 8 (([5, 28, 31, 33, 35, 38, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 28, 31, 33, 35, 38, 56]) (e := 28) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[5, 30, 35, 39, 43, 48, 52]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_556 : ∃ k : ℕ, Lonely 8 (([5, 30, 35, 39, 43, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [5, 30, 35, 39, 43, 48, 52]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 35, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_557 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 35, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_558 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_559 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 37, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_560 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 37, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 38, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_561 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 38, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 38, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_562 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_563 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 41, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_564 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 41, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 41, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 42, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_565 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 42, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 22, 43, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_566 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 22, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 22, 43, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 15, 23, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_567 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 15, 23, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 15, 23, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 22, 29, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_568 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 22, 29, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 22, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_569 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 22, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 22, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 8, 23, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_570 : ∃ k : ℕ, Lonely 8 (([6, 7, 8, 23, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 8, 23, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 9, 13, 20, 30, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_571 : ∃ k : ℕ, Lonely 8 (([6, 7, 9, 13, 20, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 9, 13, 20, 30, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 9, 13, 30, 40, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_572 : ∃ k : ℕ, Lonely 8 (([6, 7, 9, 13, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 9, 13, 30, 40, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 10, 17, 24, 40, 48]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_573 : ∃ k : ℕ, Lonely 8 (([6, 7, 10, 17, 24, 40, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 10, 17, 24, 40, 48]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 10, 17, 24, 44, 48]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_574 : ∃ k : ℕ, Lonely 8 (([6, 7, 10, 17, 24, 44, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 10, 17, 24, 44, 48]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 10, 19, 26, 48, 52]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_575 : ∃ k : ℕ, Lonely 8 (([6, 7, 10, 19, 26, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 10, 19, 26, 48, 52]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 11, 15, 26, 40, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_576 : ∃ k : ℕ, Lonely 8 (([6, 7, 11, 15, 26, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 11, 15, 26, 40, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 13, 19, 25, 32, 57]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_577 : ∃ k : ℕ, Lonely 8 (([6, 7, 13, 19, 25, 32, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 13, 19, 25, 32, 57]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 13, 25, 32, 38, 57]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_578 : ∃ k : ℕ, Lonely 8 (([6, 7, 13, 25, 32, 38, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 13, 25, 32, 38, 57]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 18, 22, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_579 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 18, 22, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 18, 22, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 18, 22, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_580 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 18, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 18, 22, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 22, 26, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_581 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 22, 26, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 22, 26, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 22, 26, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_582 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 22, 26, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 22, 26, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 22, 28, 42, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_583 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 22, 28, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 22, 28, 42, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 22, 34, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_584 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 22, 34, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 22, 34, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 22, 36, 42, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_585 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 22, 36, 42, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 22, 36, 42, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 15, 26, 33, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_586 : ∃ k : ℕ, Lonely 8 (([6, 7, 15, 26, 33, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 15, 26, 33, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 18, 22, 29, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_587 : ∃ k : ℕ, Lonely 8 (([6, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 18, 22, 29, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 19, 26, 32, 50, 52]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_588 : ∃ k : ℕ, Lonely 8 (([6, 7, 19, 26, 32, 50, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 19, 26, 32, 50, 52]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 20, 23, 26, 30, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_589 : ∃ k : ℕ, Lonely 8 (([6, 7, 20, 23, 26, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 20, 23, 26, 30, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 20, 30, 34, 37, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_590 : ∃ k : ℕ, Lonely 8 (([6, 7, 20, 30, 34, 37, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 20, 30, 34, 37, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 22, 25, 29, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_591 : ∃ k : ℕ, Lonely 8 (([6, 7, 22, 25, 29, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 22, 25, 29, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 22, 26, 29, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_592 : ∃ k : ℕ, Lonely 8 (([6, 7, 22, 26, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 22, 26, 29, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 22, 29, 35, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_593 : ∃ k : ℕ, Lonely 8 (([6, 7, 22, 29, 35, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 22, 29, 35, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 23, 26, 30, 40, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_594 : ∃ k : ℕ, Lonely 8 (([6, 7, 23, 26, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 23, 26, 30, 40, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 30, 34, 37, 40, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_595 : ∃ k : ℕ, Lonely 8 (([6, 7, 30, 34, 37, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 30, 34, 37, 40, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 7, 30, 37, 44, 58, 60]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_596 : ∃ k : ℕ, Lonely 8 (([6, 7, 30, 37, 44, 58, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 7, 30, 37, 44, 58, 60]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 11, 14, 19, 30, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_597 : ∃ k : ℕ, Lonely 8 (([6, 8, 11, 14, 19, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 11, 14, 19, 30, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 11, 17, 20, 28, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_598 : ∃ k : ℕ, Lonely 8 (([6, 8, 11, 17, 20, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 11, 17, 20, 28, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 15, 22, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_599 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 15, 22, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 15, 22, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 15, 22, 37, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_600 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 15, 22, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 15, 22, 37, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 15, 23, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_601 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 15, 23, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 15, 23, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 17, 22, 35, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_602 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 17, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 17, 22, 35, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 22, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_603 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 22, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 22, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 14, 23, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_604 : ∃ k : ℕ, Lonely 8 (([6, 8, 14, 23, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 14, 23, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 8, 15, 23, 29, 42, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_605 : ∃ k : ℕ, Lonely 8 (([6, 8, 15, 23, 29, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 8, 15, 23, 29, 42, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 9, 13, 14, 22, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_606 : ∃ k : ℕ, Lonely 8 (([6, 9, 13, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 9, 13, 14, 22, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 9, 14, 22, 31, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_607 : ∃ k : ℕ, Lonely 8 (([6, 9, 14, 22, 31, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 9, 14, 22, 31, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 9, 22, 26, 35, 48, 52]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_608 : ∃ k : ℕ, Lonely 8 (([6, 9, 22, 26, 35, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 9, 22, 26, 35, 48, 52]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 11, 17, 28, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_609 : ∃ k : ℕ, Lonely 8 (([6, 10, 11, 17, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 11, 17, 28, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 16, 21, 22, 43, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_610 : ∃ k : ℕ, Lonely 8 (([6, 10, 16, 21, 22, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 16, 21, 22, 43, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 16, 21, 26, 47, 52]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_611 : ∃ k : ℕ, Lonely 8 (([6, 10, 16, 21, 26, 47, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 16, 21, 26, 47, 52]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 17, 22, 28, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_612 : ∃ k : ℕ, Lonely 8 (([6, 10, 17, 22, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 17, 22, 28, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 21, 22, 32, 43, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_613 : ∃ k : ℕ, Lonely 8 (([6, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 21, 22, 32, 43, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 10, 23, 26, 36, 49, 52]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_614 : ∃ k : ℕ, Lonely 8 (([6, 10, 23, 26, 36, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 10, 23, 26, 36, 49, 52]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 14, 17, 23, 40, 43]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_615 : ∃ k : ℕ, Lonely 8 (([6, 11, 14, 17, 23, 40, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 14, 17, 23, 40, 43]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 16, 17, 20, 28, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_616 : ∃ k : ℕ, Lonely 8 (([6, 11, 16, 17, 20, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 16, 17, 20, 28, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 16, 17, 28, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_617 : ∃ k : ℕ, Lonely 8 (([6, 11, 16, 17, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 16, 17, 28, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 16, 24, 35, 38, 48]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_618 : ∃ k : ℕ, Lonely 8 (([6, 11, 16, 24, 35, 38, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 16, 24, 35, 38, 48]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 16, 24, 35, 46, 48]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_619 : ∃ k : ℕ, Lonely 8 (([6, 11, 16, 24, 35, 46, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 16, 24, 35, 46, 48]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 16, 28, 30, 39, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_620 : ∃ k : ℕ, Lonely 8 (([6, 11, 16, 28, 30, 39, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 16, 28, 30, 39, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 20, 24, 28, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_621 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 20, 24, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 20, 24, 28, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 20, 28, 32, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_622 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 20, 28, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 20, 28, 32, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 20, 28, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_623 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 20, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 20, 28, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 20, 28, 48, 56]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_624 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 20, 28, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 20, 28, 48, 56]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 23, 28, 40, 46]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_625 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 23, 28, 40, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 23, 28, 40, 46]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 23, 28, 45, 46]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_626 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 23, 28, 45, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 23, 28, 45, 46]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 26, 28, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_627 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 26, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 26, 28, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 28, 36, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_628 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 28, 36, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 28, 36, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 28, 40, 46, 56]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_629 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 28, 40, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 28, 40, 46, 56]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 17, 28, 40, 52, 56]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_630 : ∃ k : ℕ, Lonely 8 (([6, 11, 17, 28, 40, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 17, 28, 40, 52, 56]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 24, 32, 35, 38, 48]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_631 : ∃ k : ℕ, Lonely 8 (([6, 11, 24, 32, 35, 38, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 24, 32, 35, 38, 48]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 24, 32, 35, 46, 48]`, flank `11`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_632 : ∃ k : ℕ, Lonely 8 (([6, 11, 24, 32, 35, 46, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 24, 32, 35, 46, 48]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 26, 30, 41, 56, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_633 : ∃ k : ℕ, Lonely 8 (([6, 11, 26, 30, 41, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 26, 30, 41, 56, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 11, 26, 35, 37, 48, 52]`, flank `11`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_634 : ∃ k : ℕ, Lonely 8 (([6, 11, 26, 35, 37, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [6, 11, 26, 35, 37, 48, 52]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 17, 20, 30, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_635 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 17, 20, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 17, 20, 30, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 17, 22, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_636 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 17, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 17, 22, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 17, 30, 40, 60]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_637 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 17, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 17, 30, 40, 60]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 22, 25, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_638 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 22, 25, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 22, 25, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 22, 35, 36, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_639 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 22, 35, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 22, 35, 36, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 14, 22, 35, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_640 : ∃ k : ℕ, Lonely 8 (([6, 13, 14, 22, 35, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 14, 22, 35, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 15, 28, 34, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_641 : ∃ k : ℕ, Lonely 8 (([6, 13, 15, 28, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 15, 28, 34, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 16, 22, 35, 38, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_642 : ∃ k : ℕ, Lonely 8 (([6, 13, 16, 22, 35, 38, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 16, 22, 35, 38, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 22, 32, 35, 38, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_643 : ∃ k : ℕ, Lonely 8 (([6, 13, 22, 32, 35, 38, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 22, 32, 35, 38, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 28, 34, 40, 41, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_644 : ∃ k : ℕ, Lonely 8 (([6, 13, 28, 34, 40, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 28, 34, 40, 41, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 30, 41, 43, 56, 60]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_645 : ∃ k : ℕ, Lonely 8 (([6, 13, 30, 41, 43, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 30, 41, 43, 56, 60]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 13, 30, 43, 46, 56, 60]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_646 : ∃ k : ℕ, Lonely 8 (([6, 13, 30, 43, 46, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 13, 30, 43, 46, 56, 60]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 14, 17, 22, 31, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_647 : ∃ k : ℕ, Lonely 8 (([6, 14, 17, 22, 31, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 14, 17, 22, 31, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 14, 17, 30, 31, 48, 51]`, flank `14`, opening `11`.  Covers 1 census rows. -/
theorem fam_4_648 : ∃ k : ℕ, Lonely 8 (([6, 14, 17, 30, 31, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [6, 14, 17, 30, 31, 48, 51]) (e := 14) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 14, 22, 31, 35, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_649 : ∃ k : ℕ, Lonely 8 (([6, 14, 22, 31, 35, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 14, 22, 31, 35, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 14, 30, 31, 34, 48, 51]`, flank `30`, opening `9`.  Covers 1 census rows. -/
theorem fam_4_650 : ∃ k : ℕ, Lonely 8 (([6, 14, 30, 31, 34, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((30 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [6, 14, 30, 31, 34, 48, 51]) (e := 30) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 17, 22, 28, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_651 : ∃ k : ℕ, Lonely 8 (([6, 15, 17, 22, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 17, 22, 28, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 19, 21, 23, 44, 46]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_652 : ∃ k : ℕ, Lonely 8 (([6, 15, 19, 21, 23, 44, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 19, 21, 23, 44, 46]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 19, 23, 29, 42, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_653 : ∃ k : ℕ, Lonely 8 (([6, 15, 19, 23, 29, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 19, 23, 29, 42, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 22, 28, 34, 37, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_654 : ∃ k : ℕ, Lonely 8 (([6, 15, 22, 28, 34, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 22, 28, 34, 37, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 23, 27, 29, 42, 46]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_655 : ∃ k : ℕ, Lonely 8 (([6, 15, 23, 27, 29, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 23, 27, 29, 42, 46]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 23, 29, 35, 38, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_656 : ∃ k : ℕ, Lonely 8 (([6, 15, 23, 29, 35, 38, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 23, 29, 35, 38, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 15, 28, 34, 39, 40, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_657 : ∃ k : ℕ, Lonely 8 (([6, 15, 28, 34, 39, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 15, 28, 34, 39, 40, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 16, 17, 28, 44, 45, 55]`, flank `16`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_658 : ∃ k : ℕ, Lonely 8 (([6, 16, 17, 28, 44, 45, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [6, 16, 17, 28, 44, 45, 55]) (e := 16) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 16, 17, 28, 44, 50, 55]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_659 : ∃ k : ℕ, Lonely 8 (([6, 16, 17, 28, 44, 50, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 16, 17, 28, 44, 50, 55]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 16, 23, 29, 35, 38, 46]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_660 : ∃ k : ℕ, Lonely 8 (([6, 16, 23, 29, 35, 38, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 16, 23, 29, 35, 38, 46]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 18, 24, 30, 42, 49]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_661 : ∃ k : ℕ, Lonely 8 (([6, 17, 18, 24, 30, 42, 49].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 18, 24, 30, 42, 49]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 20, 22, 28, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_662 : ∃ k : ℕ, Lonely 8 (([6, 17, 20, 22, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 20, 22, 28, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 20, 23, 28, 48, 56]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_663 : ∃ k : ℕ, Lonely 8 (([6, 17, 20, 23, 28, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 20, 23, 28, 48, 56]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 20, 28, 45, 48, 56]`, flank `20`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_664 : ∃ k : ℕ, Lonely 8 (([6, 17, 20, 28, 45, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 20, 28, 45, 48, 56]) (e := 20) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 22, 25, 28, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_665 : ∃ k : ℕ, Lonely 8 (([6, 17, 22, 25, 28, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 22, 25, 28, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 22, 28, 30, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_666 : ∃ k : ℕ, Lonely 8 (([6, 17, 22, 28, 30, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 22, 28, 30, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 22, 28, 35, 39, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_667 : ∃ k : ℕ, Lonely 8 (([6, 17, 22, 28, 35, 39, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 22, 28, 35, 39, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 22, 28, 39, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_668 : ∃ k : ℕ, Lonely 8 (([6, 17, 22, 28, 39, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 22, 28, 39, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 23, 28, 40, 52, 56]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_669 : ∃ k : ℕ, Lonely 8 (([6, 17, 23, 28, 40, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 23, 28, 40, 52, 56]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 23, 29, 35, 41, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_670 : ∃ k : ℕ, Lonely 8 (([6, 17, 23, 29, 35, 41, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 23, 29, 35, 41, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 26, 28, 40, 45, 56]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_671 : ∃ k : ℕ, Lonely 8 (([6, 17, 26, 28, 40, 45, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 26, 28, 40, 45, 56]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 17, 28, 40, 45, 52, 56]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_672 : ∃ k : ℕ, Lonely 8 (([6, 17, 28, 40, 45, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 17, 28, 40, 45, 52, 56]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 18, 23, 24, 30, 42, 43]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_673 : ∃ k : ℕ, Lonely 8 (([6, 18, 23, 24, 30, 42, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 18, 23, 24, 30, 42, 43]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 18, 24, 30, 31, 42, 47]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_674 : ∃ k : ℕ, Lonely 8 (([6, 18, 24, 30, 31, 42, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 18, 24, 30, 31, 42, 47]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 19, 21, 26, 32, 45, 52]`, flank `19`, opening `11`.  Covers 1 census rows. -/
theorem fam_4_675 : ∃ k : ℕ, Lonely 8 (([6, 19, 21, 26, 32, 45, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [6, 19, 21, 26, 32, 45, 52]) (e := 19) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 23, 26, 30, 53, 56, 60]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_676 : ∃ k : ℕ, Lonely 8 (([6, 23, 26, 30, 53, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [6, 23, 26, 30, 53, 56, 60]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 23, 29, 31, 35, 38, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_677 : ∃ k : ℕ, Lonely 8 (([6, 23, 29, 31, 35, 38, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 23, 29, 31, 35, 38, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 23, 29, 33, 35, 42, 46]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_678 : ∃ k : ℕ, Lonely 8 (([6, 23, 29, 33, 35, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [6, 23, 29, 33, 35, 42, 46]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[6, 28, 34, 39, 40, 41, 56]`, flank `6`, opening `0`.  Covers 1 census rows. -/
theorem fam_4_679 : ∃ k : ℕ, Lonely 8 (([6, 28, 34, 39, 40, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [6, 28, 34, 39, 40, 41, 56]) (e := 6) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 9, 16, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_680 : ∃ k : ℕ, Lonely 8 (([7, 8, 9, 16, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 9, 16, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 9, 17, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_681 : ∃ k : ℕ, Lonely 8 (([7, 8, 9, 17, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 9, 17, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 9, 17, 25, 41, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_682 : ∃ k : ℕ, Lonely 8 (([7, 8, 9, 17, 25, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 9, 17, 25, 41, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 9, 17, 25, 43, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_683 : ∃ k : ℕ, Lonely 8 (([7, 8, 9, 17, 25, 43, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 9, 17, 25, 43, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 9, 25, 33, 39, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_684 : ∃ k : ℕ, Lonely 8 (([7, 8, 9, 25, 33, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 9, 25, 33, 39, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 23, 30, 38, 51, 60]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_685 : ∃ k : ℕ, Lonely 8 (([7, 8, 23, 30, 38, 51, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 23, 30, 38, 51, 60]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 8, 23, 30, 38, 53, 60]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_686 : ∃ k : ℕ, Lonely 8 (([7, 8, 23, 30, 38, 53, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 8, 23, 30, 38, 53, 60]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_687 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 40, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_688 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 40, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 41, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_689 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 41, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 42, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_690 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 42, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 42, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 43, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_691 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 43, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 43, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 44, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_692 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 44, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 44, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 45, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_693 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 45, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 45, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 46, 50]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_694 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 46, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 46, 50]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 47, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_695 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 47, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_696 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 11, 16, 25, 49, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_697 : ∃ k : ℕ, Lonely 8 (([7, 9, 11, 16, 25, 49, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 11, 16, 25, 49, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 15, 16, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_698 : ∃ k : ℕ, Lonely 8 (([7, 9, 15, 16, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 15, 16, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 15, 16, 25, 40, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_699 : ∃ k : ℕ, Lonely 8 (([7, 9, 15, 16, 25, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 15, 16, 25, 40, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 15, 16, 25, 45, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_700 : ∃ k : ℕ, Lonely 8 (([7, 9, 15, 16, 25, 45, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 15, 16, 25, 45, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 19, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_701 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 19, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 19, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 23, 25, 39, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_702 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 23, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 23, 25, 39, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 23, 25, 41, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_703 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 23, 25, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 23, 25, 41, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 23, 25, 43, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_704 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 23, 25, 43, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 23, 25, 43, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 27, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_705 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 27, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 27, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 28, 42, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_706 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 28, 42, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 28, 42, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 28, 46, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_707 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 28, 46, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 28, 46, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 34, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_708 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 34, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 34, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 34, 41, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_709 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 34, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 34, 41, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 34, 43, 50]`, flank `9`, opening `8`.  Covers 1 census rows. -/
theorem fam_4_710 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 34, 43, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 34, 43, 50]) (e := 9) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 38, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_711 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 38, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 38, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 39, 42, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_712 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 39, 42, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 39, 42, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 16, 25, 39, 46, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_713 : ∃ k : ℕ, Lonely 8 (([7, 9, 16, 25, 39, 46, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 16, 25, 39, 46, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 19, 25, 32, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_714 : ∃ k : ℕ, Lonely 8 (([7, 9, 19, 25, 32, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 19, 25, 32, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 19, 25, 39, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_715 : ∃ k : ℕ, Lonely 8 (([7, 9, 19, 25, 39, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 19, 25, 39, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 22, 30, 37, 52, 60]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_716 : ∃ k : ℕ, Lonely 8 (([7, 9, 22, 30, 37, 52, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 22, 30, 37, 52, 60]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 25, 32, 34, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_717 : ∃ k : ℕ, Lonely 8 (([7, 9, 25, 32, 34, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 25, 32, 34, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 9, 25, 34, 39, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_718 : ∃ k : ℕ, Lonely 8 (([7, 9, 25, 34, 39, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 9, 25, 34, 39, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 13, 27, 37, 53, 54]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_719 : ∃ k : ℕ, Lonely 8 (([7, 10, 13, 27, 37, 53, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 13, 27, 37, 53, 54]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 24, 27, 41, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_720 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 24, 27, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 24, 27, 41, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 24, 27, 44, 51]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_721 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 24, 27, 44, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 24, 27, 44, 51]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 24, 31, 41, 51]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_722 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 24, 31, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 24, 31, 41, 51]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 24, 41, 47, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_723 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 24, 41, 47, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 24, 41, 47, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 27, 35, 49, 54]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_724 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 27, 35, 49, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 27, 35, 49, 54]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 17, 27, 37, 47, 50]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_725 : ∃ k : ℕ, Lonely 8 (([7, 10, 17, 27, 37, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 17, 27, 37, 47, 50]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 24, 27, 34, 41, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_726 : ∃ k : ℕ, Lonely 8 (([7, 10, 24, 27, 34, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 24, 27, 34, 41, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 24, 27, 34, 44, 51]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_727 : ∃ k : ℕ, Lonely 8 (([7, 10, 24, 27, 34, 44, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 24, 27, 34, 44, 51]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 24, 31, 34, 41, 51]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_728 : ∃ k : ℕ, Lonely 8 (([7, 10, 24, 31, 34, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 24, 31, 34, 41, 51]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 10, 24, 34, 41, 47, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_729 : ∃ k : ℕ, Lonely 8 (([7, 10, 24, 34, 41, 47, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 10, 24, 34, 41, 47, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 12, 18, 25, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_730 : ∃ k : ℕ, Lonely 8 (([7, 11, 12, 18, 25, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 12, 18, 25, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 15, 26, 37, 48, 52]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_731 : ∃ k : ℕ, Lonely 8 (([7, 11, 15, 26, 37, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 15, 26, 37, 48, 52]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 23, 25, 48, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_732 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 23, 25, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 23, 25, 48, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 25, 29, 47, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_733 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 25, 29, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 25, 29, 47, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 25, 32, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_734 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 25, 32, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 25, 32, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 25, 35, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_735 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 25, 35, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 25, 35, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 25, 40, 47, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_736 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 25, 40, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 25, 40, 47, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 25, 47, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_737 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 25, 47, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 25, 47, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 29, 40, 47, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_738 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 29, 40, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 29, 40, 47, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 29, 40, 47, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_739 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 29, 40, 47, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 29, 40, 47, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 18, 29, 40, 51, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_740 : ∃ k : ℕ, Lonely 8 (([7, 11, 18, 29, 40, 51, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 18, 29, 40, 51, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 24, 26, 37, 50, 52]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_741 : ∃ k : ℕ, Lonely 8 (([7, 11, 24, 26, 37, 50, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 24, 26, 37, 50, 52]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 11, 26, 30, 37, 48, 52]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_742 : ∃ k : ℕ, Lonely 8 (([7, 11, 26, 30, 37, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 11, 26, 30, 37, 48, 52]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 13, 20, 27, 50, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_743 : ∃ k : ℕ, Lonely 8 (([7, 12, 13, 20, 27, 50, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 13, 20, 27, 50, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 13, 20, 27, 51, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_744 : ∃ k : ℕ, Lonely 8 (([7, 12, 13, 20, 27, 51, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 13, 20, 27, 51, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 13, 20, 27, 52, 54]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_745 : ∃ k : ℕ, Lonely 8 (([7, 12, 13, 20, 27, 52, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 13, 20, 27, 52, 54]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 13, 20, 27, 53, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_746 : ∃ k : ℕ, Lonely 8 (([7, 12, 13, 20, 27, 53, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 13, 20, 27, 53, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 19, 31, 43, 50, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_747 : ∃ k : ℕ, Lonely 8 (([7, 12, 19, 31, 43, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 19, 31, 43, 50, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 12, 19, 31, 43, 55, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_748 : ∃ k : ℕ, Lonely 8 (([7, 12, 19, 31, 43, 55, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 12, 19, 31, 43, 55, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 13, 18, 20, 27, 45, 54]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_749 : ∃ k : ℕ, Lonely 8 (([7, 13, 18, 20, 27, 45, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 13, 18, 20, 27, 45, 54]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 13, 20, 27, 33, 48, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_750 : ∃ k : ℕ, Lonely 8 (([7, 13, 20, 27, 33, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 13, 20, 27, 33, 48, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 13, 20, 27, 36, 45, 54]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_751 : ∃ k : ℕ, Lonely 8 (([7, 13, 20, 27, 36, 45, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 13, 20, 27, 36, 45, 54]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 13, 20, 27, 43, 53, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_752 : ∃ k : ℕ, Lonely 8 (([7, 13, 20, 27, 43, 53, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 13, 20, 27, 43, 53, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 15, 24, 31, 39, 55, 56]`, flank `15`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_753 : ∃ k : ℕ, Lonely 8 (([7, 15, 24, 31, 39, 55, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 15, 24, 31, 39, 55, 56]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 15, 25, 32, 33, 39, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_754 : ∃ k : ℕ, Lonely 8 (([7, 15, 25, 32, 33, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 15, 25, 32, 33, 39, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 15, 25, 32, 35, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_755 : ∃ k : ℕ, Lonely 8 (([7, 15, 25, 32, 35, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 15, 25, 32, 35, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 16, 17, 20, 24, 41, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_756 : ∃ k : ℕ, Lonely 8 (([7, 16, 17, 20, 24, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 16, 17, 20, 24, 41, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 16, 20, 24, 34, 41, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_757 : ∃ k : ℕ, Lonely 8 (([7, 16, 20, 24, 34, 41, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 16, 20, 24, 34, 41, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 16, 23, 24, 25, 40, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_758 : ∃ k : ℕ, Lonely 8 (([7, 16, 23, 24, 25, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 16, 23, 24, 25, 40, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 17, 20, 27, 37, 47, 50]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_759 : ∃ k : ℕ, Lonely 8 (([7, 17, 20, 27, 37, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 17, 20, 27, 37, 47, 50]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 17, 23, 24, 40, 47, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_760 : ∃ k : ℕ, Lonely 8 (([7, 17, 23, 24, 40, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 17, 23, 24, 40, 47, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 17, 27, 30, 37, 47, 50]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_761 : ∃ k : ℕ, Lonely 8 (([7, 17, 27, 30, 37, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 17, 27, 30, 37, 47, 50]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 17, 27, 37, 40, 47, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_762 : ∃ k : ℕ, Lonely 8 (([7, 17, 27, 37, 40, 47, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 17, 27, 37, 40, 47, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 22, 29, 40, 47, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_763 : ∃ k : ℕ, Lonely 8 (([7, 18, 22, 29, 40, 47, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 22, 29, 40, 47, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 22, 29, 40, 51, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_764 : ∃ k : ℕ, Lonely 8 (([7, 18, 22, 29, 40, 51, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 22, 29, 40, 51, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 25, 27, 43, 48, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_765 : ∃ k : ℕ, Lonely 8 (([7, 18, 25, 27, 43, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 25, 27, 43, 48, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 25, 32, 39, 46, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_766 : ∃ k : ℕ, Lonely 8 (([7, 18, 25, 32, 39, 46, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 25, 32, 39, 46, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 27, 34, 41, 45, 54]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_767 : ∃ k : ℕ, Lonely 8 (([7, 18, 27, 34, 41, 45, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 27, 34, 41, 45, 54]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 29, 33, 40, 47, 55]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_768 : ∃ k : ℕ, Lonely 8 (([7, 18, 29, 33, 40, 47, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 29, 33, 40, 47, 55]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 29, 33, 40, 51, 55]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_769 : ∃ k : ℕ, Lonely 8 (([7, 18, 29, 33, 40, 51, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 29, 33, 40, 51, 55]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 29, 40, 44, 47, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_770 : ∃ k : ℕ, Lonely 8 (([7, 18, 29, 40, 44, 47, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 29, 40, 44, 47, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 18, 29, 40, 44, 51, 55]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_771 : ∃ k : ℕ, Lonely 8 (([7, 18, 29, 40, 44, 51, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 18, 29, 40, 44, 51, 55]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 21, 28, 35, 49, 52]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_772 : ∃ k : ℕ, Lonely 8 (([7, 19, 21, 28, 35, 49, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 21, 28, 35, 49, 52]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 24, 25, 32, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_773 : ∃ k : ℕ, Lonely 8 (([7, 19, 24, 25, 32, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 24, 25, 32, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 24, 31, 43, 50, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_774 : ∃ k : ℕ, Lonely 8 (([7, 19, 24, 31, 43, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 24, 31, 43, 50, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 24, 31, 43, 55, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_775 : ∃ k : ℕ, Lonely 8 (([7, 19, 24, 31, 43, 55, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 24, 31, 43, 55, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 26, 29, 48, 50, 60]`, flank `19`, opening `14`.  Covers 1 census rows. -/
theorem fam_4_776 : ∃ k : ℕ, Lonely 8 (([7, 19, 26, 29, 48, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨14, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 26, 29, 48, 50, 60]) (e := 19) (k := 14)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 31, 36, 43, 50, 60]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_777 : ∃ k : ℕ, Lonely 8 (([7, 19, 31, 36, 43, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 31, 36, 43, 50, 60]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 31, 36, 43, 55, 60]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_778 : ∃ k : ℕ, Lonely 8 (([7, 19, 31, 36, 43, 55, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 31, 36, 43, 55, 60]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 31, 43, 48, 50, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_779 : ∃ k : ℕ, Lonely 8 (([7, 19, 31, 43, 48, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 31, 43, 48, 50, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 19, 31, 43, 48, 55, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_780 : ∃ k : ℕ, Lonely 8 (([7, 19, 31, 43, 48, 55, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [7, 19, 31, 43, 48, 55, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 20, 28, 34, 41, 48, 60]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_781 : ∃ k : ℕ, Lonely 8 (([7, 20, 28, 34, 41, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 20, 28, 34, 41, 48, 60]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 22, 26, 30, 37, 56, 60]`, flank `22`, opening `11`.  Covers 1 census rows. -/
theorem fam_4_782 : ∃ k : ℕ, Lonely 8 (([7, 22, 26, 30, 37, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [7, 22, 26, 30, 37, 56, 60]) (e := 22) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 22, 30, 37, 52, 58, 60]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_783 : ∃ k : ℕ, Lonely 8 (([7, 22, 30, 37, 52, 58, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 22, 30, 37, 52, 58, 60]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 24, 25, 32, 34, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_784 : ∃ k : ℕ, Lonely 8 (([7, 24, 25, 32, 34, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 24, 25, 32, 34, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 25, 27, 32, 33, 39, 50]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_785 : ∃ k : ℕ, Lonely 8 (([7, 25, 27, 32, 33, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 25, 27, 32, 33, 39, 50]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 25, 27, 32, 35, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_786 : ∃ k : ℕ, Lonely 8 (([7, 25, 27, 32, 35, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 25, 27, 32, 35, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 25, 27, 34, 41, 48, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_787 : ∃ k : ℕ, Lonely 8 (([7, 25, 27, 34, 41, 48, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [7, 25, 27, 34, 41, 48, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 25, 27, 36, 43, 48, 54]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_788 : ∃ k : ℕ, Lonely 8 (([7, 25, 27, 36, 43, 48, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [7, 25, 27, 36, 43, 48, 54]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 27, 34, 36, 41, 45, 54]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_789 : ∃ k : ℕ, Lonely 8 (([7, 27, 34, 36, 41, 45, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 27, 34, 36, 41, 45, 54]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 28, 34, 40, 41, 48, 60]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_790 : ∃ k : ℕ, Lonely 8 (([7, 28, 34, 40, 41, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 28, 34, 40, 41, 48, 60]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 29, 30, 37, 44, 59, 60]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_4_791 : ∃ k : ℕ, Lonely 8 (([7, 29, 30, 37, 44, 59, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [7, 29, 30, 37, 44, 59, 60]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[7, 30, 35, 42, 48, 49, 58]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_4_792 : ∃ k : ℕ, Lonely 8 (([7, 30, 35, 42, 48, 49, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [7, 30, 35, 42, 48, 49, 58]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 10, 13, 21, 29, 55, 58]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_793 : ∃ k : ℕ, Lonely 8 (([8, 10, 13, 21, 29, 55, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 10, 13, 21, 29, 55, 58]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 11, 14, 19, 30, 52, 60]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_4_794 : ∃ k : ℕ, Lonely 8 (([8, 11, 14, 19, 30, 52, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [8, 11, 14, 19, 30, 52, 60]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 11, 19, 30, 41, 49, 57]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_795 : ∃ k : ℕ, Lonely 8 (([8, 11, 19, 30, 41, 49, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [8, 11, 19, 30, 41, 49, 57]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 11, 30, 38, 41, 49, 57]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_4_796 : ∃ k : ℕ, Lonely 8 (([8, 11, 30, 38, 41, 49, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [8, 11, 30, 38, 41, 49, 57]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 13, 20, 21, 29, 46, 58]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_797 : ∃ k : ℕ, Lonely 8 (([8, 13, 20, 21, 29, 46, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 13, 20, 21, 29, 46, 58]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 14, 17, 20, 31, 48, 60]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_798 : ∃ k : ℕ, Lonely 8 (([8, 14, 17, 20, 31, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [8, 14, 17, 20, 31, 48, 60]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 14, 17, 31, 40, 48, 60]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_799 : ∃ k : ℕ, Lonely 8 (([8, 14, 17, 31, 40, 48, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [8, 14, 17, 31, 40, 48, 60]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 14, 23, 30, 38, 53, 60]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_800 : ∃ k : ℕ, Lonely 8 (([8, 14, 23, 30, 38, 53, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [8, 14, 23, 30, 38, 53, 60]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 16, 24, 32, 40, 56, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_801 : ∃ k : ℕ, Lonely 8 (([8, 16, 24, 32, 40, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 16, 24, 32, 40, 56, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 18, 20, 21, 28, 48, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_802 : ∃ k : ℕ, Lonely 8 (([8, 18, 20, 21, 28, 48, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 18, 20, 21, 28, 48, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 18, 29, 37, 45, 56, 58]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_803 : ∃ k : ℕ, Lonely 8 (([8, 18, 29, 37, 45, 56, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [8, 18, 29, 37, 45, 56, 58]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 19, 28, 29, 48, 50, 60]`, flank `19`, opening `18`.  Covers 1 census rows. -/
theorem fam_4_804 : ∃ k : ℕ, Lonely 8 (([8, 19, 28, 29, 48, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨18, Flanks.lonely_of_band_list (n := 8) (L := [8, 19, 28, 29, 48, 50, 60]) (e := 19) (k := 18)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 19, 32, 35, 43, 51, 57]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_805 : ∃ k : ℕ, Lonely 8 (([8, 19, 32, 35, 43, 51, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [8, 19, 32, 35, 43, 51, 57]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 20, 28, 32, 40, 48, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_806 : ∃ k : ℕ, Lonely 8 (([8, 20, 28, 32, 40, 48, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 20, 28, 32, 40, 48, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 21, 23, 30, 38, 53, 60]`, flank `8`, opening `7`.  Covers 1 census rows. -/
theorem fam_4_807 : ∃ k : ℕ, Lonely 8 (([8, 21, 23, 30, 38, 53, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [8, 21, 23, 30, 38, 53, 60]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 21, 30, 38, 46, 51, 60]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_808 : ∃ k : ℕ, Lonely 8 (([8, 21, 30, 38, 46, 51, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [8, 21, 30, 38, 46, 51, 60]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 24, 28, 32, 40, 52, 59]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_809 : ∃ k : ℕ, Lonely 8 (([8, 24, 28, 32, 40, 52, 59].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 24, 28, 32, 40, 52, 59]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 24, 28, 32, 40, 56, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_810 : ∃ k : ℕ, Lonely 8 (([8, 24, 28, 32, 40, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 24, 28, 32, 40, 56, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 24, 32, 40, 44, 56, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_811 : ∃ k : ℕ, Lonely 8 (([8, 24, 32, 40, 44, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 24, 32, 40, 44, 56, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 32, 35, 38, 43, 51, 57]`, flank `8`, opening `5`.  Covers 1 census rows. -/
theorem fam_4_812 : ∃ k : ℕ, Lonely 8 (([8, 32, 35, 38, 43, 51, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [8, 32, 35, 38, 43, 51, 57]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[8, 32, 40, 44, 48, 56, 57]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_4_813 : ∃ k : ℕ, Lonely 8 (([8, 32, 40, 44, 48, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [8, 32, 40, 44, 48, 56, 57]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

end PinnedBatch4
