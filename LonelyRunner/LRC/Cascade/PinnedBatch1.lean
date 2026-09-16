import LonelyRunner.LRC.Cascade.Flanks

/-!
# Fully-pinned census families, part 1 of 4

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Each theorem is one seven-difference arrangement from an `s = 6` census cover — fully pinned,
so there is no free parameter and Existence for the runner is just that some flank has a lonely
opening.  The framework's clearing test (`Flanks.clear_of_residue_band`, Proposition 2.1) makes
that decidable arithmetic, so each family closes by `decide` on the residue band.

Emitted by `experiments/n8/gen_pinned_batch_v1.py`; data recomputed and cross-checked in
`experiments/n8/census_export_v1.py`.
-/

set_option maxHeartbeats 1000000

namespace PinnedBatch1

open MomentIterationN Flanks

/-- Differences `[1, 2, 3, 4, 5, 7, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_1 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 4, 5, 7, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 4, 5, 7, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 4, 5, 7, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_2 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 4, 5, 7, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 4, 5, 7, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 4, 5, 7, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_3 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 4, 5, 7, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 4, 5, 7, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 4, 5, 7, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_4 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 4, 5, 7, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 4, 5, 7, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 4, 7, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_5 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 4, 7, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 4, 7, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 8, 9]`, flank `5`, opening `4`.  Covers 6 census rows. -/
theorem fam_1_6 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 8, 9].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 8, 9]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 8, 15]`, flank `5`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_7 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 8, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 8, 15]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 8, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_8 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 8, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 8, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 8, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_9 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 8, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 8, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 8, 33]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_10 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 8, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 8, 33]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_11 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 12, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_12 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 12, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 12, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 12, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_13 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 12, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 12, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 12, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_14 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 12, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 12, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 16, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_15 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 16, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_16 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_17 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 20, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_18 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 20, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_19 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 7, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_20 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 7, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 7, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 12, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_21 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 12, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 5, 12, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_22 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 5, 12, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 5, 12, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 7, 8, 10, 15]`, flank `7`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_23 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 7, 8, 10, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 7, 8, 10, 15]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 7, 8, 15, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_24 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 7, 8, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 7, 8, 15, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 7, 12, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_25 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 7, 12, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 7, 12, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 3, 7, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_26 : ∃ k : ℕ, Lonely 8 (([1, 2, 3, 7, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 3, 7, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 4, 5, 6, 7, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_27 : ∃ k : ℕ, Lonely 8 (([1, 2, 4, 5, 6, 7, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 4, 5, 6, 7, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 4, 5, 6, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_28 : ∃ k : ℕ, Lonely 8 (([1, 2, 4, 5, 6, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 4, 5, 6, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 4, 5, 7, 12, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_29 : ∃ k : ℕ, Lonely 8 (([1, 2, 4, 5, 7, 12, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 4, 5, 7, 12, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 9]`, flank `6`, opening `2`.  Covers 6 census rows. -/
theorem fam_1_30 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 9].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 9]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 11]`, flank `5`, opening `1`.  Covers 5 census rows. -/
theorem fam_1_31 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 11].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 11]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 13]`, flank `6`, opening `2`.  Covers 4 census rows. -/
theorem fam_1_32 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 13].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 13]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 15]`, flank `5`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_33 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 15]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_34 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_35 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 8, 41]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_36 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 8, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 8, 41]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_37 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 16, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_38 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 16, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_39 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 7, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_40 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 7, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 7, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 8, 14, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_41 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 8, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 8, 14, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 8, 21, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_42 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 8, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 8, 21, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 12, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_43 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 12, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 14, 16, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_44 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 14, 16, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 14, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_45 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 14, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 14, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_46 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 14, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 14, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 14, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_47 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 14, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 6, 14, 24, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_48 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 6, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 6, 14, 24, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 8, 9, 15]`, flank `5`, opening `4`.  Covers 4 census rows. -/
theorem fam_1_49 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 8, 9, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 8, 9, 15]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 8, 9, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_50 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 8, 9, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 8, 9, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 8, 9, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_51 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 8, 9, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 8, 9, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 8, 18, 24]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_52 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 8, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 8, 18, 24]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 8, 18, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_53 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 8, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 8, 18, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 9, 11, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_54 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 9, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 9, 11, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 9, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_55 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 9, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 9, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 12, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_56 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 12, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 12, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 12, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_57 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 12, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 12, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 12, 19, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_58 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 12, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 12, 19, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 15, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_59 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 15, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 7, 16, 18, 24]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_60 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 7, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 7, 16, 18, 24]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 8, 9, 14, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_61 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 8, 9, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 8, 9, 14, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 9, 14, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_62 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 9, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 9, 14, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 12, 14, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_63 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 12, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 12, 14, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 12, 14, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_64 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 12, 14, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 12, 14, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 5, 12, 14, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_65 : ∃ k : ℕ, Lonely 8 (([1, 2, 5, 12, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 5, 12, 14, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 7, 8, 10, 11]`, flank `6`, opening `4`.  Covers 5 census rows. -/
theorem fam_1_66 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 7, 8, 10, 11].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 7, 8, 10, 11]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 7, 8, 10, 15]`, flank `6`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_67 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 7, 8, 10, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 7, 8, 10, 15]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 7, 8, 10, 29]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_68 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 7, 8, 10, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 7, 8, 10, 29]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 7, 8, 20, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_69 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 7, 8, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 7, 8, 20, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 7, 32, 35, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_70 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 7, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 7, 32, 35, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 8, 14, 25, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_71 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 8, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 8, 14, 25, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 14, 15, 16, 20]`, flank `14`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_72 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 14, 15, 16, 20]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 6, 14, 20, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_73 : ∃ k : ℕ, Lonely 8 (([1, 2, 6, 14, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 6, 14, 20, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 7, 8, 9, 10, 15]`, flank `7`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_74 : ∃ k : ℕ, Lonely 8 (([1, 2, 7, 8, 9, 10, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 7, 8, 9, 10, 15]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 7, 11, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_75 : ∃ k : ℕ, Lonely 8 (([1, 2, 7, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 7, 11, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 7, 13, 15, 16, 21]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_76 : ∃ k : ℕ, Lonely 8 (([1, 2, 7, 13, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 7, 13, 15, 16, 21]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 7, 16, 18, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_77 : ∃ k : ℕ, Lonely 8 (([1, 2, 7, 16, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 7, 16, 18, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 13, 14, 15, 16, 21]`, flank `13`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_78 : ∃ k : ℕ, Lonely 8 (([1, 2, 13, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 13, 14, 15, 16, 21]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 2, 26, 33, 35, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_79 : ∃ k : ℕ, Lonely 8 (([1, 2, 26, 33, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 2, 26, 33, 35, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 8, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_80 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 8, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 8, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 9, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_81 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 9, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 9, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_82 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_83 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_84 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_85 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_86 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_87 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 11, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_88 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 11, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 11, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 13, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_89 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 13, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 13, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_90 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 13, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 13, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_91 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 13, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 13, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 13, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_92 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 13, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 13, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 15, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_93 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 15, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_94 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_95 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_96 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 18, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_97 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 18, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 18, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_98 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 30]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_99 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 30]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 37]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_100 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 37].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 37]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 46]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_101 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 46]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_102 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 50]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_103 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 50]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 24, 59]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_104 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 24, 59].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 24, 59]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 26, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_105 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 26, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 28, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_106 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 28, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 30, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_107 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 30, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 31, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_108 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 31, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 31, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_109 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 7, 37, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_110 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 7, 37, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 7, 37, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 8, 14, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_111 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 8, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 8, 14, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_112 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 13, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_113 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 13, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 14, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_114 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 14, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 18, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_115 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 18, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 18, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 24, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_116 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 24, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 5, 31, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_117 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 5, 31, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 5, 31, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 6, 7, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_118 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 6, 7, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 6, 7, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 9, 10, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_119 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 9, 10, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 9, 10, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 9, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_120 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 9, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 9, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 11, 12]`, flank `1`, opening `0`.  Covers 5 census rows. -/
theorem fam_1_121 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 11, 12].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 11, 12]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 11, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_122 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 11, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 11, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_123 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 11, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 13, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_124 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 13, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_125 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 10, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_126 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 10, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 10, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 11, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_127 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 11, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 11, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 11, 15, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_128 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 11, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 11, 15, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 11, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_129 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 11, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 11, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 12, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_130 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 12, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 12, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 13, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_131 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 13, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 13, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 15, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_132 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 15, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 15, 24, 25]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_133 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 15, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 15, 24, 25]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 15, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_134 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 15, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_135 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_136 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 7, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_137 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 7, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 7, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 10, 24, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_138 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 10, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 10, 24, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 14, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_139 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 14, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 14, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 14, 24, 25, 30]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_140 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 14, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 14, 24, 25, 30]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 15, 24, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_141 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 15, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 15, 24, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 20, 24, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_142 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 20, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 20, 24, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_143 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 24, 25, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_144 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 24, 25, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 24, 25, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 4, 24, 28, 30, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_145 : ∃ k : ℕ, Lonely 8 (([1, 3, 4, 24, 28, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 4, 24, 28, 30, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 9, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_146 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 9, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 9, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 11, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_147 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 11, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 13, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_148 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 13, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 13, 26]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_149 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 13, 26]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 15, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_150 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 15, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_151 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 8, 17, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_152 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 8, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 8, 17, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 9, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_153 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 9, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 9, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 9, 16, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_154 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 9, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 9, 16, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 11, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_155 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 11, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 11, 16, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_156 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 11, 16, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 13, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_157 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 13, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 13, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_158 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 13, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 13, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 13, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_159 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 13, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 13, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_160 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 15, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_161 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 15, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 15, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 12, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_162 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 12, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 12, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 13, 16, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_163 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 13, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 13, 16, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 15, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_164 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 15, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 15, 20, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_165 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 15, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 15, 20, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 15, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_166 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 15, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 15, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 15, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_167 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 15, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 15, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 16, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_168 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 16, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 17, 20, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_169 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 17, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 17, 20, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 17, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_170 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 17, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 17, 24, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_171 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 17, 24, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 17, 24, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 17, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_172 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 17, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 17, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 19, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_173 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 19, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 19, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 7, 21, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_174 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 7, 21, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 7, 21, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 8, 9, 14, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_175 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 8, 9, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 8, 9, 14, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 8, 11, 14, 16]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_176 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 8, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 8, 11, 14, 16]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 9, 14, 15, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_177 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 9, 14, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 9, 14, 15, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 11, 12, 21, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_178 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 11, 12, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 11, 12, 21, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 11, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_179 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 11, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 11, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 12, 13, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_180 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 12, 13, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 12, 13, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 12, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_181 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 12, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 12, 15, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_182 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 12, 15, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 12, 15, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 13, 14, 16, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_183 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 13, 14, 16, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 14, 17, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_184 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 14, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 14, 17, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 15, 18, 21, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_185 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 15, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 15, 18, 21, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 17, 21, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_186 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 17, 21, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 17, 21, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 21, 30, 31, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_187 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 21, 30, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 21, 30, 31, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 5, 25, 35, 38, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_188 : ∃ k : ℕ, Lonely 8 (([1, 3, 5, 25, 35, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 5, 25, 35, 38, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 6, 7, 8, 15, 16]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_189 : ∃ k : ℕ, Lonely 8 (([1, 3, 6, 7, 8, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 6, 7, 8, 15, 16]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 6, 7, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_190 : ∃ k : ℕ, Lonely 8 (([1, 3, 6, 7, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 6, 7, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 6, 7, 15, 17, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_191 : ∃ k : ℕ, Lonely 8 (([1, 3, 6, 7, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 6, 7, 15, 17, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 9, 10, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_192 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 9, 10, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 9, 10, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 9, 15, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_193 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 9, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 9, 15, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 10, 11, 12]`, flank `8`, opening `4`.  Covers 5 census rows. -/
theorem fam_1_194 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 10, 11, 12].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 10, 11, 12]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 10, 11, 16]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_195 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 10, 11, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 10, 11, 16]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 10, 11, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_196 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 10, 11, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 10, 13, 20]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_197 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 10, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 10, 13, 20]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 10, 17, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_198 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 10, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 10, 17, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 11, 15, 16]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_199 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 11, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 11, 15, 16]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 11, 15, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_200 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 11, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 11, 15, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 8, 13, 15, 20]`, flank `7`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_201 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 8, 13, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 8, 13, 15, 20]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 9, 10, 11, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_202 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 9, 10, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 9, 10, 11, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 9, 10, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_203 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 9, 10, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 9, 10, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 9, 10, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_204 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 9, 10, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 9, 10, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 9, 12, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_205 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 9, 12, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 9, 12, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 9, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_206 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 9, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 9, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 11, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_207 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 11, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 11, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_208 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 11, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 11, 13, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_209 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 11, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 11, 13, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 11, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_210 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 11, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 11, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 11, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_211 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 11, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 12, 13, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_212 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 12, 13, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 12, 13, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 13, 16, 20]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_213 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 13, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 13, 16, 20]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 10, 13, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_214 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 10, 13, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 10, 13, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 11, 12, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_215 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 11, 12, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 11, 12, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 11, 13, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_216 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 11, 13, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 11, 13, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 11, 13, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_217 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 11, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 11, 13, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 11, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_218 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 11, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 11, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 12, 13, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_219 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 12, 13, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 12, 13, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 12, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_220 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 12, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 12, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 12, 15, 17, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_221 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 12, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 12, 15, 17, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 15, 16, 20]`, flank `7`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_222 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 15, 16, 20]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 15, 16, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_223 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 15, 16, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 15, 16, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 15, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_224 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 15, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 15, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_225 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 15, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 20, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_226 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 20, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 13, 20, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_227 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 13, 20, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 13, 20, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 15, 17, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_228 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 15, 17, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 15, 17, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 7, 15, 17, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_229 : ∃ k : ℕ, Lonely 8 (([1, 3, 7, 15, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 7, 15, 17, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 10, 11, 14, 16]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_230 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 10, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 10, 11, 14, 16]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 11, 14, 15, 16]`, flank `8`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_231 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 11, 14, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 11, 14, 15, 16]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 11, 14, 15, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_232 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 11, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 11, 14, 15, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 11, 14, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_1_233 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 11, 14, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 11, 14, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 14, 15, 17, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_234 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 14, 15, 17, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 14, 22, 25, 33]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_235 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 14, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 14, 22, 25, 33]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 8, 28, 30, 31, 35]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_236 : ∃ k : ℕ, Lonely 8 (([1, 3, 8, 28, 30, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 8, 28, 30, 31, 35]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 10, 13, 14, 16, 20]`, flank `10`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_237 : ∃ k : ℕ, Lonely 8 (([1, 3, 10, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 10, 13, 14, 16, 20]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 10, 21, 23, 31, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_238 : ∃ k : ℕ, Lonely 8 (([1, 3, 10, 21, 23, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 10, 21, 23, 31, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 11, 13, 14, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_239 : ∃ k : ℕ, Lonely 8 (([1, 3, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 11, 13, 14, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 11, 14, 15, 17, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_240 : ∃ k : ℕ, Lonely 8 (([1, 3, 11, 14, 15, 17, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 11, 14, 15, 17, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 12, 13, 14, 15, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_241 : ∃ k : ℕ, Lonely 8 (([1, 3, 12, 13, 14, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 12, 13, 14, 15, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 12, 13, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_242 : ∃ k : ℕ, Lonely 8 (([1, 3, 12, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 12, 13, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 13, 14, 15, 16, 20]`, flank `13`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_243 : ∃ k : ℕ, Lonely 8 (([1, 3, 13, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 13, 14, 15, 16, 20]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 13, 14, 15, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_244 : ∃ k : ℕ, Lonely 8 (([1, 3, 13, 14, 15, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 13, 14, 15, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 13, 14, 16, 17, 20]`, flank `13`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_245 : ∃ k : ℕ, Lonely 8 (([1, 3, 13, 14, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 13, 14, 16, 17, 20]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 13, 15, 21, 24, 26]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_246 : ∃ k : ℕ, Lonely 8 (([1, 3, 13, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 13, 15, 21, 24, 26]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 13, 15, 23, 28, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_247 : ∃ k : ℕ, Lonely 8 (([1, 3, 13, 15, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 13, 15, 23, 28, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 14, 15, 17, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_248 : ∃ k : ℕ, Lonely 8 (([1, 3, 14, 15, 17, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 14, 15, 17, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 15, 17, 18, 21, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_249 : ∃ k : ℕ, Lonely 8 (([1, 3, 15, 17, 18, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 15, 17, 18, 21, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 15, 17, 25, 28, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_250 : ∃ k : ℕ, Lonely 8 (([1, 3, 15, 17, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 15, 17, 25, 28, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 21, 23, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_251 : ∃ k : ℕ, Lonely 8 (([1, 3, 21, 23, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 21, 23, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 21, 35, 37, 38, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_252 : ∃ k : ℕ, Lonely 8 (([1, 3, 21, 35, 37, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 21, 35, 37, 38, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 3, 27, 32, 33, 35, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_253 : ∃ k : ℕ, Lonely 8 (([1, 3, 27, 32, 33, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 3, 27, 32, 33, 35, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 8, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_254 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 8, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 8, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 11, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_255 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 11, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 11, 24]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_256 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 11, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 11, 24]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 11, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_257 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 11, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 11, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 11, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_258 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 11, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 11, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 11, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_259 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 11, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 11, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 13, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_260 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 13, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_261 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 16, 23]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_262 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 16, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 16, 23]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_263 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 22, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_264 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 22, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 28, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_265 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 28, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 7, 33, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_266 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 7, 33, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 7, 33, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 8, 14, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_267 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 8, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 8, 14, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 9, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_268 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 9, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 9, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_269 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 13, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_270 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 13, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 13, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_271 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 13, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_272 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 14, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_273 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 14, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 14, 16, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_274 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 14, 16, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 14, 16, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 6, 16, 28, 32]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_275 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 6, 16, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 6, 16, 28, 32]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 9, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_276 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 9, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 9, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 9, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_277 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 9, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 9, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 12, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_278 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 12, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 12, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 15, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_279 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 15, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_280 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 8, 18, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_281 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 8, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 8, 18, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 11, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_282 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 11, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 11, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_283 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 11, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 11, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_284 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_285 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_286 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 9, 19, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_287 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 9, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 9, 19, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 11, 12, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_288 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 11, 12, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 11, 12, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 11, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_289 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 11, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 11, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 11, 18, 24]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_290 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 11, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 11, 18, 24]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 11, 24, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_291 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 11, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 11, 24, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 12, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_292 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 12, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 12, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 15, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_293 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 15, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 16, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_294 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 16, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 7, 22, 24, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_295 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 7, 22, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 7, 22, 24, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 8, 9, 14, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_296 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 8, 9, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 8, 9, 14, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 8, 12, 14, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_297 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 8, 12, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 8, 12, 14, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 8, 14, 15, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_298 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 8, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 8, 14, 15, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 8, 14, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_299 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 8, 14, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 8, 14, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 9, 12, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_300 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 9, 12, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 9, 12, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 9, 13, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_301 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 9, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 9, 13, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 9, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_302 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 9, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 9, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 9, 14, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_303 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 9, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 9, 14, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 9, 14, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_304 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 9, 14, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 9, 14, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 11, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_305 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 11, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 11, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 12, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_306 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 12, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 12, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 12, 14, 16, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_307 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 12, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 12, 14, 16, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 13, 14, 18, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_308 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 13, 14, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 13, 14, 18, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 13, 14, 18, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_309 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 13, 14, 18, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 13, 14, 18, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 13, 18, 28, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_310 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 13, 18, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 13, 18, 28, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 15, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_311 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 15, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 16, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_312 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 16, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 16, 24, 48]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_313 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 16, 24, 48]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 23, 24, 30]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_314 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 23, 24, 30]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 24, 29, 42]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_315 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 24, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 24, 29, 42]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 14, 24, 32, 48]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_316 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 14, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 14, 24, 32, 48]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 20, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_317 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 20, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 20, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 24, 28, 29, 42]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_318 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 24, 28, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 24, 28, 29, 42]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 31, 33, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_319 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 31, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 31, 33, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 31, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_320 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 31, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 31, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 5, 31, 35, 39, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_321 : ∃ k : ℕ, Lonely 8 (([1, 4, 5, 31, 35, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 5, 31, 35, 39, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 10, 14]`, flank `4`, opening `2`.  Covers 4 census rows. -/
theorem fam_1_322 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 10, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 10, 14]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 10, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_323 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 10, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 10, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 10, 23]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_324 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 10, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 10, 23]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 15, 17]`, flank `4`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_325 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 15, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 15, 17]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 15, 21]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_326 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 15, 21]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 20, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_327 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 20, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_328 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 8, 20, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_329 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 8, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 8, 20, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 10, 11, 14]`, flank `1`, opening `0`.  Covers 4 census rows. -/
theorem fam_1_330 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 10, 11, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 10, 11, 14]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 10, 11, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_331 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 10, 11, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 10, 11, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_332 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 10, 11, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 10, 11, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 11, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_333 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 11, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 11, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 16, 20, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_334 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 16, 20, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 20, 24, 40]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_335 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 20, 24, 40]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 7, 20, 32, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_336 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 7, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 7, 20, 32, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 8, 10, 14, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_337 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 8, 10, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 8, 10, 14, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 8, 14, 15, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_338 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 8, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 8, 14, 15, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 8, 14, 20, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_339 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 8, 14, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 8, 14, 20, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 8, 14, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_340 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 8, 14, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 8, 14, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 9, 10, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_341 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 9, 10, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 10, 11, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_342 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 10, 11, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 10, 11, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 10, 13, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_343 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 10, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 10, 13, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 10, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_344 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 10, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 10, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 10, 14, 16, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_345 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 10, 14, 16, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 10, 14, 16, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 13, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_346 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 13, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 13, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 13, 14, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_347 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 13, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 13, 14, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 15, 16, 25]`, flank `14`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_348 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 15, 16, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 15, 16, 25]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 15, 18, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_349 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 15, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 15, 18, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 15, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_350 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 15, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 15, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 15, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_351 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 15, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 15, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 16, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_352 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 16, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 16, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 14, 20, 24, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_353 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 14, 20, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 14, 20, 24, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 6, 16, 20, 28, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_354 : ∃ k : ℕ, Lonely 8 (([1, 4, 6, 16, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 6, 16, 20, 28, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 8, 10, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_355 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 8, 10, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 8, 10, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 8, 11, 15, 21]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_356 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 8, 11, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 8, 11, 15, 21]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 8, 15, 16, 21]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_357 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 8, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 8, 15, 16, 21]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 8, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_358 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 8, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 8, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 9, 10, 11, 12]`, flank `1`, opening `0`.  Covers 5 census rows. -/
theorem fam_1_359 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 9, 10, 11, 12].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 9, 10, 11, 12]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 9, 10, 11, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_360 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 9, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 9, 10, 11, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 9, 10, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_361 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 9, 10, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 9, 10, 17, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_362 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 9, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 9, 10, 17, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 11, 12, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_363 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 11, 12, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 11, 12, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 11, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_364 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 11, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 11, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 11, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_365 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 11, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 11, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 14, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_366 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 14, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 14, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 16, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_367 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 16, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 19, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_368 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 19, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 22, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_369 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 22, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 22, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 10, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_370 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 10, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 10, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 12, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_371 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 12, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 12, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_372 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 15, 16, 45]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_373 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 15, 16, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 15, 16, 45]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 15, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_374 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 15, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 15, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 16, 30, 45]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_375 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 16, 30, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 16, 30, 45]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 18, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_376 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 18, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 11, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_377 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 11, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 11, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 13, 15, 16, 21]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_378 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 13, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 13, 15, 16, 21]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 13, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_379 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 13, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 13, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 13, 39, 40, 45]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_380 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 13, 39, 40, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 13, 39, 40, 45]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 14, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_381 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 14, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 14, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 15, 16, 18, 21]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_382 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 15, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 15, 16, 18, 21]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 15, 19, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_383 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 15, 19, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 15, 19, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 16, 18, 20, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_384 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 16, 18, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 16, 18, 20, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 16, 39, 40, 45]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_385 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 16, 39, 40, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 16, 39, 40, 45]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 19, 20, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_386 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 19, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 19, 20, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 20, 22, 24, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_387 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 20, 22, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 20, 22, 24, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 20, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_388 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 20, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 20, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 23, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_389 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 23, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 23, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 23, 30, 31, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_390 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 23, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 23, 30, 31, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 24, 25, 26, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_391 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 24, 25, 26, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 7, 29, 39, 40, 45]`, flank `4`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_392 : ∃ k : ℕ, Lonely 8 (([1, 4, 7, 29, 39, 40, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 7, 29, 39, 40, 45]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 8, 11, 14, 15, 21]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_393 : ∃ k : ℕ, Lonely 8 (([1, 4, 8, 11, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 8, 11, 14, 15, 21]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 8, 14, 15, 16, 21]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_394 : ∃ k : ℕ, Lonely 8 (([1, 4, 8, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 8, 14, 15, 16, 21]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 10, 13, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_395 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 10, 13, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 10, 14, 19, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_396 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 10, 14, 19, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 10, 14, 24, 30]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_397 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 10, 14, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 10, 14, 24, 30]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 13, 14, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_398 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 13, 14, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 13, 14, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 14, 20, 24, 30]`, flank `9`, opening `6`.  Covers 2 census rows. -/
theorem fam_1_399 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 14, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 14, 20, 24, 30]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 16, 28, 30, 35]`, flank `4`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_400 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 16, 28, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 16, 28, 30, 35]) (e := 4) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 17, 20, 21, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_401 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 17, 20, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 17, 20, 21, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 9, 28, 30, 32, 35]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_1_402 : ∃ k : ℕ, Lonely 8 (([1, 4, 9, 28, 30, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 9, 28, 30, 32, 35]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 10, 14, 16, 18, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_403 : ∃ k : ℕ, Lonely 8 (([1, 4, 10, 14, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 10, 14, 16, 18, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 10, 14, 17, 18, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_404 : ∃ k : ℕ, Lonely 8 (([1, 4, 10, 14, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 10, 14, 17, 18, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 10, 14, 23, 24, 30]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_405 : ∃ k : ℕ, Lonely 8 (([1, 4, 10, 14, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 10, 14, 23, 24, 30]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 10, 14, 24, 25, 30]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_406 : ∃ k : ℕ, Lonely 8 (([1, 4, 10, 14, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 10, 14, 24, 25, 30]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 10, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_407 : ∃ k : ℕ, Lonely 8 (([1, 4, 10, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 10, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 11, 13, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_408 : ∃ k : ℕ, Lonely 8 (([1, 4, 11, 13, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 11, 13, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 12, 13, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_409 : ∃ k : ℕ, Lonely 8 (([1, 4, 12, 13, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 12, 13, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 12, 14, 16, 20, 25]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_410 : ∃ k : ℕ, Lonely 8 (([1, 4, 12, 14, 16, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 12, 14, 16, 20, 25]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 12, 14, 16, 20, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_411 : ∃ k : ℕ, Lonely 8 (([1, 4, 12, 14, 16, 20, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 12, 14, 16, 20, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 12, 14, 16, 20, 53]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_412 : ∃ k : ℕ, Lonely 8 (([1, 4, 12, 14, 16, 20, 53].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 12, 14, 16, 20, 53]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 13, 14, 15, 16, 21]`, flank `13`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_413 : ∃ k : ℕ, Lonely 8 (([1, 4, 13, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 13, 14, 15, 16, 21]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 13, 14, 15, 17, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_414 : ∃ k : ℕ, Lonely 8 (([1, 4, 13, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 13, 14, 15, 17, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 13, 14, 24, 25, 30]`, flank `13`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_415 : ∃ k : ℕ, Lonely 8 (([1, 4, 13, 14, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 13, 14, 24, 25, 30]) (e := 13) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 13, 15, 17, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_416 : ∃ k : ℕ, Lonely 8 (([1, 4, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 13, 15, 17, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 13, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_417 : ∃ k : ℕ, Lonely 8 (([1, 4, 13, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 13, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 15, 16, 18, 21]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_418 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 15, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 15, 16, 18, 21]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 15, 16, 24, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_419 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 15, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 15, 16, 24, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 15, 22, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_420 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 15, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 15, 22, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 15, 23, 24, 30]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_421 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 15, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 15, 23, 24, 30]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 15, 24, 32, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_422 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 15, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 15, 24, 32, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 16, 18, 20, 21]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_423 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 16, 18, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 16, 18, 20, 21]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 16, 20, 24, 27]`, flank `4`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_424 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 16, 20, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 16, 20, 24, 27]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 20, 23, 24, 30]`, flank `20`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_425 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 20, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 20, 23, 24, 30]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 20, 24, 25, 30]`, flank `20`, opening `6`.  Covers 2 census rows. -/
theorem fam_1_426 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 20, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 20, 24, 25, 30]) (e := 20) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 23, 24, 25, 30]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_427 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 23, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 23, 24, 25, 30]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 14, 24, 25, 26, 30]`, flank `24`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_428 : ∃ k : ℕ, Lonely 8 (([1, 4, 14, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 14, 24, 25, 26, 30]) (e := 24) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 16, 18, 20, 28, 35]`, flank `4`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_429 : ∃ k : ℕ, Lonely 8 (([1, 4, 16, 18, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 16, 18, 20, 28, 35]) (e := 4) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 19, 20, 21, 23, 40]`, flank `19`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_430 : ∃ k : ℕ, Lonely 8 (([1, 4, 19, 20, 21, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 19, 20, 21, 23, 40]) (e := 19) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 20, 21, 24, 25, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_431 : ∃ k : ℕ, Lonely 8 (([1, 4, 20, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 20, 21, 24, 25, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 21, 23, 24, 25, 30]`, flank `21`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_432 : ∃ k : ℕ, Lonely 8 (([1, 4, 21, 23, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 21, 23, 24, 25, 30]) (e := 21) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 21, 24, 25, 26, 30]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_433 : ∃ k : ℕ, Lonely 8 (([1, 4, 21, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 21, 24, 25, 26, 30]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 31, 32, 33, 35, 42]`, flank `31`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_434 : ∃ k : ℕ, Lonely 8 (([1, 4, 31, 32, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((31 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 31, 32, 33, 35, 42]) (e := 31) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 4, 31, 33, 35, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_435 : ∃ k : ℕ, Lonely 8 (([1, 4, 31, 33, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 4, 31, 33, 35, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 11, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_436 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 11, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 11, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 11, 37]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_437 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 11, 37].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 11, 37]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_438 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 19]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_439 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 19]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_440 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 24]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_441 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 24]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 26]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_442 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 26]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_443 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 30]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_444 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 30]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_445 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 41]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_446 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 41]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 13, 43]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_447 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 13, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 13, 43]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 15, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_448 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 15, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 15, 41]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_449 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 15, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 15, 41]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 17, 21]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_450 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 17, 21]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 17, 25]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_451 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 17, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 17, 25]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 17, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_452 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 17, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 19, 23]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_453 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 19, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 19, 23]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 8, 28, 41]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_454 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 8, 28, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 8, 28, 41]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_455 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_456 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 13, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_457 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 13, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_458 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 16, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_459 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 16, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 16, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_460 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 16, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_461 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 11, 20, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_462 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 11, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 11, 20, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 15, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_463 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 15, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 16, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_464 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 16, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 16, 24]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_465 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 16, 24]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 19, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_466 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 19, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 19, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_467 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 13, 23, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_468 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 13, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 13, 23, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 15, 16, 23]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_469 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 15, 16, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 15, 16, 23]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 15, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_470 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 15, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 15, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_471 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 15, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 16, 17, 21]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_472 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 16, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 16, 17, 21]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 16, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_473 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 16, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 16, 19, 23]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_474 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 16, 19, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 16, 19, 23]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 17, 19, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_475 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 17, 19, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 17, 23, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_476 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 17, 23, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 17, 27, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_477 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 17, 27, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 17, 27, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 17, 31, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_478 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 17, 31, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 20, 30, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_479 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 20, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 20, 30, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 22, 36, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_480 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 22, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 22, 36, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 22, 40, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_481 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 22, 40, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 7, 30, 40, 60]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_482 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 7, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 7, 30, 40, 60]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 9, 14, 31]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_483 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 9, 14, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 9, 14, 31]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 14, 21]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_484 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 14, 21]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 14, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_485 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 14, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 14, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_486 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 14, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 14, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 21, 28]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_487 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 21, 28]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 21, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_488 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 21, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 13, 28, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_489 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 13, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 13, 28, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 14, 17, 21]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_490 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 14, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 14, 17, 21]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 8, 15, 21, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_491 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 8, 15, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 8, 15, 21, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 9, 11, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_492 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 9, 11, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 9, 11, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 9, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_493 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 9, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 9, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 9, 14, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_494 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 9, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 9, 14, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_495 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 13, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_496 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 13, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 13, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 14, 16, 20]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_497 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 14, 16, 20]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 16, 21, 22]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_498 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 16, 21, 22]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 16, 21, 25]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_499 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 16, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 16, 21, 25]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 16, 21, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_500 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 16, 21, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 21, 23, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_501 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 21, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 21, 23, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 28, 30, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_502 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 28, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 28, 30, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 11, 30, 56, 60]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_503 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 11, 30, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 11, 30, 56, 60]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 12, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_504 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 12, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 13, 14, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_505 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 13, 14, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 13, 14, 16, 21]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_506 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 13, 14, 16, 21]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 13, 14, 16, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_507 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 13, 14, 16, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 13, 14, 24, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_508 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 13, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 13, 14, 24, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 13, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_509 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 13, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 15, 16, 19]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_510 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 15, 16, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 15, 16, 19]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 15, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_511 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 15, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 15, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_512 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 15, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 15, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_513 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 15, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 15, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_514 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 15, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 16, 17, 21]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_515 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 16, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 16, 17, 21]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 16, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_516 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 16, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 17, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_517 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 17, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_518 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 20, 30, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_519 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 20, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 20, 30, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 22, 40, 44]`, flank `6`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_520 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 22, 40, 44]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 14, 30, 40, 60]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_521 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 14, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 14, 30, 40, 60]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 16, 21, 22, 29]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_522 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 16, 21, 22, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 16, 21, 22, 29]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 16, 21, 44, 55]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_523 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 16, 21, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 16, 21, 44, 55]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 20, 21, 30, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_524 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 20, 21, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 20, 21, 30, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 21, 30, 40, 60]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_525 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 21, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 21, 30, 40, 60]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 6, 30, 53, 56, 60]`, flank `5`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_526 : ∃ k : ℕ, Lonely 8 (([1, 5, 6, 30, 53, 56, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 6, 30, 53, 56, 60]) (e := 5) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 10, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_527 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 10, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 10, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 11, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_528 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 11, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 13, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_529 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 13, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_530 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 17, 27]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_531 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 17, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 17, 27]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 17, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_532 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 17, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 19, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_533 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 19, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 19, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 19, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_534 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 19, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 19, 44]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_535 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 19, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 19, 44]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 21, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_536 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 21, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 23, 27]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_537 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 23, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 23, 27]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 9, 25, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_538 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 9, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 9, 25, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 11, 18, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_539 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 11, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 11, 18, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 12, 13, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_540 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 12, 13, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 12, 13, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 12, 13, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_541 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 12, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 12, 13, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 13, 18, 24]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_542 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 13, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 13, 18, 24]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 13, 18, 30]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_543 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 13, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 13, 18, 30]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 13, 24, 30]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_544 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 13, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 13, 24, 30]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 17, 18, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_545 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 17, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 17, 18, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 18, 19, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_546 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 18, 19, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 18, 19, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 18, 21, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_547 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 18, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 18, 21, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 18, 23, 27]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_548 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 18, 23, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 18, 23, 27]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 18, 25, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_549 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 18, 25, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 21, 22, 27]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_550 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 21, 22, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 21, 22, 27]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 8, 24, 29, 33]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_551 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 8, 24, 29, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 8, 24, 29, 33]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 10, 11, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_552 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 10, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 10, 11, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 10, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_553 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 10, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 10, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 11, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_554 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 11, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 11, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 11, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_555 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 11, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 11, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 11, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_556 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 11, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 11, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_557 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 11, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 11, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 12, 19, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_558 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 12, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 12, 19, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 14, 16, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_559 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 14, 16, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 14, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_560 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 14, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 14, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 16, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_561 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 16, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 16, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 16, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_562 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 16, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 16, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_563 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 16, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 19, 28, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_564 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 19, 28, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 19, 28, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 19, 36, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_565 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 19, 36, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 19, 36, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 9, 23, 32, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_566 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 9, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 9, 23, 32, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_567 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_568 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 13, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_569 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 13, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 13, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_570 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_571 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 19, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_572 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 19, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 12, 25, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_573 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 12, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 12, 25, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 13, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_574 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 13, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 13, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 13, 24, 30]`, flank `11`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_575 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 13, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 13, 24, 30]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 15, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_576 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 15, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 16, 18, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_577 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 16, 18, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 11, 18, 20, 24]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_578 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 11, 18, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 11, 18, 20, 24]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 13, 16, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_579 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 13, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 13, 16, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 13, 19, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_580 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 13, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 13, 19, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 13, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_581 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 13, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 13, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 13, 23, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_582 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 13, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 13, 23, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 16, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_583 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 16, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 17, 19, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_584 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 17, 19, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 17, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_585 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 17, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 17, 31, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_586 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 17, 31, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 19, 26, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_587 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 19, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 19, 26, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 12, 22, 23, 44]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_588 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 12, 22, 23, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 12, 22, 23, 44]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 13, 15, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_589 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 13, 15, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 13, 15, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 13, 16, 18, 24]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_590 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 13, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 13, 16, 18, 24]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 13, 18, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_591 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 13, 18, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 13, 18, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 13, 19, 24, 30]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_592 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 13, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 13, 19, 24, 30]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 17, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_593 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 17, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 17, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_594 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 17, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 20, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_595 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 20, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 23, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_596 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 23, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 26, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_597 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 26, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 16, 29, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_598 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 16, 29, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 17, 22, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_599 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 17, 22, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 17, 22, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 15, 17, 28, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_600 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 15, 17, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 15, 17, 28, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 16, 17, 18, 32]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_601 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 16, 17, 18, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 16, 17, 18, 32]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 17, 18, 19, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_602 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 17, 18, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 17, 18, 19, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 17, 18, 31, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_603 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 17, 18, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 17, 18, 31, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 18, 19, 20, 40]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_604 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 18, 19, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 18, 19, 20, 40]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 19, 20, 21, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_605 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 19, 20, 21, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 19, 20, 21, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 22, 23, 24, 44]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_606 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 22, 23, 24, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 22, 23, 24, 44]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 23, 24, 25, 50]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_607 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 23, 24, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 23, 24, 25, 50]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 7, 25, 26, 27, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_608 : ∃ k : ℕ, Lonely 8 (([1, 5, 7, 25, 26, 27, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 7, 25, 26, 27, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 9, 10, 14, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_609 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 9, 10, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 9, 10, 14, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 9, 13, 14, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_610 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 9, 13, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 9, 13, 14, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 9, 13, 14, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_611 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 9, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 9, 13, 14, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 9, 14, 19, 38]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_612 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 9, 14, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 9, 14, 19, 38]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 11, 13, 21, 33]`, flank `11`, opening `6`.  Covers 1 census rows. -/
theorem fam_1_613 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 11, 13, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 11, 13, 21, 33]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 13, 17, 21, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_614 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 13, 17, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 13, 17, 21, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 13, 21, 22, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_615 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 13, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 13, 21, 22, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 13, 21, 25, 39]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_616 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 13, 21, 25, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 13, 21, 25, 39]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 21, 25, 26, 39]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_617 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 21, 25, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 21, 25, 26, 39]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 8, 21, 29, 31, 42]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_618 : ∃ k : ℕ, Lonely 8 (([1, 5, 8, 21, 29, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 8, 21, 29, 31, 42]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 11, 12, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_619 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 11, 12, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 11, 12, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 11, 13, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_620 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 11, 13, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 11, 13, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 11, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_621 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 11, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 11, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 11, 14, 16, 22]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_622 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 11, 14, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 11, 14, 16, 22]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 11, 16, 21, 22]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_623 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 11, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 11, 16, 21, 22]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 12, 13, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_624 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 12, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 12, 13, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 12, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_625 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 12, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 12, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 13, 14, 16, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_626 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 13, 14, 16, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 15, 16, 22]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_627 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 15, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 15, 16, 22]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 15, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_628 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 15, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 15, 19, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_629 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 15, 19, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 16, 19, 20]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_630 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 16, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 16, 19, 20]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 17, 19, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_631 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 17, 19, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 14, 19, 29, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_632 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 14, 19, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 14, 19, 29, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 9, 19, 28, 29, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_633 : ∃ k : ℕ, Lonely 8 (([1, 5, 9, 19, 28, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 9, 19, 28, 29, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 10, 11, 21, 32, 33]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_634 : ∃ k : ℕ, Lonely 8 (([1, 5, 10, 11, 21, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 10, 11, 21, 32, 33]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 10, 21, 22, 32, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_635 : ∃ k : ℕ, Lonely 8 (([1, 5, 10, 21, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 10, 21, 22, 32, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_636 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 13, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_637 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 13, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 13, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 13, 21, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_638 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 13, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 13, 21, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 14, 19, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_639 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 14, 19, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 16, 21, 22]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_640 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 16, 21, 22]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 16, 21, 42]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_641 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 16, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 16, 21, 42]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 19, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_642 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 19, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 19, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 12, 21, 29, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_643 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 12, 21, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 12, 21, 29, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 14, 15, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_644 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 14, 15, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 15, 16, 21, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_645 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 15, 16, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 15, 16, 21, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 19, 21, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_646 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 19, 21, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 19, 21, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 21, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_647 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 21, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 21, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 11, 25, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_648 : ∃ k : ℕ, Lonely 8 (([1, 5, 11, 25, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 11, 25, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 15, 16, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_649 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 15, 16, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 15, 19, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_650 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 15, 19, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 15, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_651 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 15, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 15, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_652 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 15, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 15, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 17, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_653 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 17, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 19, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_654 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 19, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 19, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 19, 24, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_655 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 19, 24, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 14, 19, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_656 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 14, 19, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 14, 19, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 12, 17, 21, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_657 : ∃ k : ℕ, Lonely 8 (([1, 5, 12, 17, 21, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 12, 17, 21, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 13, 15, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_658 : ∃ k : ℕ, Lonely 8 (([1, 5, 13, 15, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 13, 15, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 13, 15, 27, 28, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_659 : ∃ k : ℕ, Lonely 8 (([1, 5, 13, 15, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 13, 15, 27, 28, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 13, 16, 17, 21, 24]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_660 : ∃ k : ℕ, Lonely 8 (([1, 5, 13, 16, 17, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 13, 16, 17, 21, 24]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 14, 15, 16, 17, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_661 : ∃ k : ℕ, Lonely 8 (([1, 5, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 14, 15, 16, 17, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 14, 15, 16, 17, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_662 : ∃ k : ℕ, Lonely 8 (([1, 5, 14, 15, 16, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 14, 15, 16, 17, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 14, 15, 17, 25, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_663 : ∃ k : ℕ, Lonely 8 (([1, 5, 14, 15, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 14, 15, 17, 25, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 14, 24, 25, 26, 48]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_664 : ∃ k : ℕ, Lonely 8 (([1, 5, 14, 24, 25, 26, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 14, 24, 25, 26, 48]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 15, 20, 25, 35, 54]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_665 : ∃ k : ℕ, Lonely 8 (([1, 5, 15, 20, 25, 35, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 15, 20, 25, 35, 54]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 16, 18, 21, 26, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_666 : ∃ k : ℕ, Lonely 8 (([1, 5, 16, 18, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 16, 18, 21, 26, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 17, 18, 23, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_667 : ∃ k : ℕ, Lonely 8 (([1, 5, 17, 18, 23, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 17, 18, 23, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 17, 29, 30, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_668 : ∃ k : ℕ, Lonely 8 (([1, 5, 17, 29, 30, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 17, 29, 30, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 18, 19, 23, 28, 32]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_669 : ∃ k : ℕ, Lonely 8 (([1, 5, 18, 19, 23, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 18, 19, 23, 28, 32]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 18, 19, 23, 28, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_670 : ∃ k : ℕ, Lonely 8 (([1, 5, 18, 19, 23, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 18, 19, 23, 28, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 18, 23, 28, 30, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_671 : ∃ k : ℕ, Lonely 8 (([1, 5, 18, 23, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 18, 23, 28, 30, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 19, 20, 21, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_672 : ∃ k : ℕ, Lonely 8 (([1, 5, 19, 20, 21, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 19, 20, 21, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 19, 21, 24, 29, 38]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_673 : ∃ k : ℕ, Lonely 8 (([1, 5, 19, 21, 24, 29, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 19, 21, 24, 29, 38]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 19, 21, 31, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_674 : ∃ k : ℕ, Lonely 8 (([1, 5, 19, 21, 31, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 19, 21, 31, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 20, 21, 30, 41, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_675 : ∃ k : ℕ, Lonely 8 (([1, 5, 20, 21, 30, 41, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 20, 21, 30, 41, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 21, 30, 40, 41, 60]`, flank `21`, opening `15`.  Covers 1 census rows. -/
theorem fam_1_676 : ∃ k : ℕ, Lonely 8 (([1, 5, 21, 30, 40, 41, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨15, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 21, 30, 40, 41, 60]) (e := 21) (k := 15)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 5, 29, 34, 35, 36, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_677 : ∃ k : ℕ, Lonely 8 (([1, 5, 29, 34, 35, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 5, 29, 34, 35, 36, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 10, 14]`, flank `6`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_678 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 10, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 10, 14]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 10, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_679 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 10, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 10, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_680 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_681 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 24]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_682 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 24]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_683 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 41]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_684 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 41]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_685 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 15, 60]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_686 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 15, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 15, 60]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 30, 60]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_687 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 30, 60]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 9, 45, 60]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_688 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 9, 45, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 9, 45, 60]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 11, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_689 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 11, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 13, 14]`, flank `6`, opening `1`.  Covers 4 census rows. -/
theorem fam_1_690 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 13, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 13, 14]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 13, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_691 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 13, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 13, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 13, 30]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_692 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 13, 30]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 13, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_693 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 13, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 13, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 13, 43]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_694 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 13, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 13, 43]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 17, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_695 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 17, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 17, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_696 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 17, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 17, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 10, 17, 34]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_697 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 10, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 10, 17, 34]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 15, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_698 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 15, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 15, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_699 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 15, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 15, 30]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_700 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 15, 30]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 15, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_701 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 15, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 15, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 20, 21]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_702 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 20, 21]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 20, 30]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_703 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 20, 30]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 20, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_704 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 20, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 20, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 25, 30]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_705 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 25, 30]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 25, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_706 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 25, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 25, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 13, 30, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_707 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 13, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 13, 30, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 14, 15, 41]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_708 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 14, 15, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 14, 15, 41]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 17, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_709 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 17, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 17, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_710 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 17, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 17, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 18, 41]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_711 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 18, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 18, 41]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 22, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_712 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 22, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 23, 41]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_713 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 23, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 23, 41]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 26, 30]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_714 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 26, 30]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 32, 41]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_715 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 32, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 32, 41]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 15, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_716 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 15, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 15, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 17, 20, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_717 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 17, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 17, 20, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 17, 20, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_718 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 17, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 17, 20, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 19, 20, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_719 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 19, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 19, 20, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 20, 21, 25]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_720 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 20, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 20, 21, 25]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 20, 23, 25]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_721 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 20, 23, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 20, 23, 25]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 8, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_722 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 8, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 8, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 10, 11, 14]`, flank `1`, opening `0`.  Covers 4 census rows. -/
theorem fam_1_723 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 10, 11, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 10, 11, 14]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 10, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_724 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 10, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 10, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 10, 16, 18]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_725 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 10, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 10, 16, 18]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 13, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_726 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 13, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 13, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 15, 16, 18]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_727 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 15, 16, 18]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 15, 16, 24]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_728 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 15, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 15, 16, 24]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 15, 16, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_729 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 15, 16, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 15, 16, 43]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_730 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 15, 16, 43].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 15, 16, 43]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 9, 25, 32, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_731 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 9, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 9, 25, 32, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_732 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 13, 14]`, flank `1`, opening `0`.  Covers 4 census rows. -/
theorem fam_1_733 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 13, 14].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 13, 14]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_734 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 13, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_735 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 13, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_736 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_737 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 11, 17, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_738 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 11, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 11, 17, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 13, 16, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_739 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 13, 16, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 10, 13, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_740 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 10, 13, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 10, 13, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 15, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_741 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 15, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 15, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_742 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 15, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_743 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 20, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_744 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 20, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_745 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_746 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 25, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_747 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 25, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 13, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_748 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 13, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 13, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 15, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_749 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 15, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 11, 17, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_750 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 11, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 11, 17, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 14, 15, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_751 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 14, 15, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 14, 15, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 15, 16, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_752 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 15, 16, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 15, 16, 26]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_753 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 15, 16, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 15, 16, 26]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 15, 16, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_754 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 15, 16, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 15, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_755 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 15, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 15, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_756 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 16, 20, 21]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_757 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 16, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 16, 20, 21]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 19, 20, 24]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_758 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 19, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 19, 20, 24]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 19, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_759 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 19, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 19, 20, 40]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_760 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 19, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 19, 20, 40]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 19, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_761 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 19, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 19, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 23, 25, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_762 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 23, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 23, 25, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 13, 25, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_763 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 13, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 13, 25, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 14, 15, 16, 19]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_764 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 14, 15, 16, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 14, 15, 16, 19]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 15, 16, 22, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_765 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 15, 16, 22, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 15, 16, 22, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 15, 22, 32, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_766 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 15, 22, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 15, 22, 32, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 7, 19, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_767 : ∃ k : ℕ, Lonely 8 (([1, 6, 7, 19, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 7, 19, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 10, 14, 16]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_768 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 10, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 10, 14, 16]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 10, 14, 20]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_769 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 10, 14, 20]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 10, 21, 27]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_770 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 10, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 10, 21, 27]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 10, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_771 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 10, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 10, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 14, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_772 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 14, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 14, 15, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_773 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 14, 15, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 9, 15, 21, 28]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_774 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 9, 15, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 9, 15, 21, 28]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 11, 14, 16]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_775 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 11, 14, 16]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 11, 14, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_776 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 11, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 11, 14, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 11, 14, 24]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_777 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 11, 14, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 11, 14, 24]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 11, 14, 33]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_778 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 11, 14, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 11, 14, 33]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 11, 14, 37]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_779 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 11, 14, 37].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 11, 14, 37]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 14, 21]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_780 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 14, 21]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 14, 24]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_781 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 14, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 14, 24]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 14, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_782 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 14, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 14, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_783 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 14, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 14, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 21, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_784 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 21, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 13, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_785 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 13, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 13, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 14, 17, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_786 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 14, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 14, 17, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 14, 22, 33]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_787 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 14, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 14, 22, 33]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 18, 21, 27]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_788 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 18, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 18, 21, 27]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 10, 22, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_789 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 10, 22, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 10, 22, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 15, 21]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_790 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 15, 21]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 15, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_791 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 15, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 15, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 20, 21]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_792 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 20, 21]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 20, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_793 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 20, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 20, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 25, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_794 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 25, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 25, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_795 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 25, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 25, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 14, 30, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_796 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 14, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 14, 30, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 15, 21, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_797 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 15, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 15, 21, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 15, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_798 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 15, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 15, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 20, 21, 35]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_799 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 20, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 20, 21, 35]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 20, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_800 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 20, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 21, 25, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_801 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 21, 25, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 21, 25, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 21, 30, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_802 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 21, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 21, 30, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 25, 28, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_803 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 25, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 25, 28, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 13, 28, 30, 35]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_804 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 13, 28, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 13, 28, 30, 35]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 14, 15, 17, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_805 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 14, 15, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 14, 15, 17, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 14, 15, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_806 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 14, 15, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 14, 15, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 14, 17, 20, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_807 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 14, 17, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 14, 17, 20, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 14, 17, 20, 24]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_808 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 14, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 14, 17, 20, 24]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 8, 14, 30, 36, 45]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_809 : ∃ k : ℕ, Lonely 8 (([1, 6, 8, 14, 30, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 8, 14, 30, 36, 45]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 10, 12, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_810 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 10, 12, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 10, 12, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 10, 14, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_811 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 10, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 10, 14, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 13, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_812 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 13, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 14, 15, 16, 18]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_813 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 14, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 14, 15, 16, 18]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 14, 15, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_814 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 14, 15, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 14, 15, 16, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_815 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 14, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 14, 15, 16, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 15, 16, 21, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_816 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 15, 16, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 15, 16, 21, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 15, 16, 28, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_817 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 15, 16, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 15, 16, 28, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 9, 15, 17, 21, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_818 : ∃ k : ℕ, Lonely 8 (([1, 6, 9, 15, 17, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 9, 15, 17, 21, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 11, 12, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_819 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 11, 12, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 11, 12, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 11, 14, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_820 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 11, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 11, 14, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 11, 14, 16, 24]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_821 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 11, 14, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 11, 14, 16, 24]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 11, 16, 21, 25]`, flank `10`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_822 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 11, 16, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 11, 16, 21, 25]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 12, 13, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_823 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 12, 13, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 12, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_824 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 12, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 12, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 13, 14, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_825 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 13, 14, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 13, 14, 16, 21]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_826 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 13, 14, 16, 21]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 13, 14, 16, 24]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_827 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 13, 14, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 13, 14, 16, 24]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 13, 14, 16, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_828 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 13, 14, 16, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 13, 14, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_829 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 13, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 13, 14, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 15, 16, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_830 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 15, 16, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 15, 16, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_831 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 15, 16, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 15, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_832 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 15, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 15, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_833 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 15, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 16, 17, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_834 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 16, 17, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 17, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_835 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 17, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 14, 19, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_836 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 14, 19, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 16, 21, 22, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_837 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 16, 21, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 16, 21, 22, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 10, 21, 22, 32, 44]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_838 : ∃ k : ℕ, Lonely 8 (([1, 6, 10, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 10, 21, 22, 32, 44]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 11, 14, 15, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_839 : ∃ k : ℕ, Lonely 8 (([1, 6, 11, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 11, 14, 15, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 11, 15, 16, 21, 25]`, flank `15`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_840 : ∃ k : ℕ, Lonely 8 (([1, 6, 11, 15, 16, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 11, 15, 16, 21, 25]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 11, 16, 20, 21, 25]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_841 : ∃ k : ℕ, Lonely 8 (([1, 6, 11, 16, 20, 21, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 11, 16, 20, 21, 25]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 11, 17, 23, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_842 : ∃ k : ℕ, Lonely 8 (([1, 6, 11, 17, 23, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 11, 17, 23, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 13, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_843 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 13, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 13, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 13, 14, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_844 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 13, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 13, 14, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 13, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_845 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 13, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 13, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 14, 15, 16, 19]`, flank `12`, opening `9`.  Covers 3 census rows. -/
theorem fam_1_846 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 14, 15, 16, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 14, 15, 16, 19]) (e := 12) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 14, 15, 16, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_847 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 14, 15, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 14, 15, 16, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 14, 15, 18, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_848 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 14, 15, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 14, 15, 18, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 14, 15, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_849 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 14, 15, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 14, 15, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 12, 14, 15, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_850 : ∃ k : ℕ, Lonely 8 (([1, 6, 12, 14, 15, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 12, 14, 15, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 16, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_851 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 16, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 16, 21]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_1_852 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 16, 21]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 16, 23]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_853 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 16, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 16, 23]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 16, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_854 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 16, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 16, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_855 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 16, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_856 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 15, 32, 37]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_857 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 15, 32, 37].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 15, 32, 37]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 16, 17, 20]`, flank `6`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_858 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 16, 17, 20]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 16, 20, 21]`, flank `14`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_859 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 16, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 16, 20, 21]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 16, 25, 28]`, flank `13`, opening `6`.  Covers 2 census rows. -/
theorem fam_1_860 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 16, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 16, 25, 28]) (e := 13) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 22, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_861 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 22, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 14, 24, 25, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_862 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 14, 24, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 14, 24, 25, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 15, 16, 21, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_863 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 15, 16, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 15, 16, 21, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 15, 16, 28, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_864 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 15, 16, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 15, 16, 28, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 15, 17, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_865 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 15, 17, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 15, 19, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_866 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 15, 19, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 15, 19, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 13, 15, 21, 24, 26]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_867 : ∃ k : ℕ, Lonely 8 (([1, 6, 13, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 13, 15, 21, 24, 26]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 17, 19]`, flank `14`, opening `3`.  Covers 3 census rows. -/
theorem fam_1_868 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 17, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 17, 19]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 17, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_869 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 17, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 18, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_870 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 18, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 22, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_871 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 22, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 22, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_872 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 22, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 22, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 26, 28]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_873 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 26, 28]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 27, 32]`, flank `14`, opening `8`.  Covers 1 census rows. -/
theorem fam_1_874 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 27, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 27, 32]) (e := 14) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 16, 29, 32]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_875 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 16, 29, 32]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 18, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_876 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 18, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 18, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_877 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 18, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 18, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 20, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_878 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 20, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 20, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_879 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 20, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 22, 32, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_880 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 22, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 22, 32, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 23, 24, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_881 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 23, 24, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 24, 26, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_882 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 24, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 24, 26, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 15, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_883 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 15, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 15, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 16, 17, 20, 24]`, flank `6`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_884 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 16, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 16, 17, 20, 24]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 16, 17, 20, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_885 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 16, 17, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 16, 17, 20, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 16, 17, 25, 32]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_886 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 16, 17, 25, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 16, 17, 25, 32]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 16, 17, 30, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_887 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 16, 17, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 16, 17, 30, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 17, 20, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_888 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 17, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 17, 20, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 19, 20, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_889 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 19, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 19, 20, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 14, 22, 31, 40, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_890 : ∃ k : ℕ, Lonely 8 (([1, 6, 14, 22, 31, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 14, 22, 31, 40, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 15, 16, 21, 22, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_891 : ∃ k : ℕ, Lonely 8 (([1, 6, 15, 16, 21, 22, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 15, 16, 21, 22, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 15, 16, 22, 28, 32]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_892 : ∃ k : ℕ, Lonely 8 (([1, 6, 15, 16, 22, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 15, 16, 22, 28, 32]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 15, 16, 22, 28, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_893 : ∃ k : ℕ, Lonely 8 (([1, 6, 15, 16, 22, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 15, 16, 22, 28, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 15, 21, 22, 32, 35]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_894 : ∃ k : ℕ, Lonely 8 (([1, 6, 15, 21, 22, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 15, 21, 22, 32, 35]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 15, 22, 28, 32, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_895 : ∃ k : ℕ, Lonely 8 (([1, 6, 15, 22, 28, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 15, 22, 28, 32, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 16, 20, 21, 22, 25]`, flank `16`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_896 : ∃ k : ℕ, Lonely 8 (([1, 6, 16, 20, 21, 22, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 16, 20, 21, 22, 25]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 16, 28, 30, 31, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_897 : ∃ k : ℕ, Lonely 8 (([1, 6, 16, 28, 30, 31, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 16, 28, 30, 31, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 17, 19, 21, 25, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_898 : ∃ k : ℕ, Lonely 8 (([1, 6, 17, 19, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 17, 19, 21, 25, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 18, 21, 24, 30, 41]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_899 : ∃ k : ℕ, Lonely 8 (([1, 6, 18, 21, 24, 30, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 18, 21, 24, 30, 41]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 20, 21, 22, 24, 29]`, flank `20`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_900 : ∃ k : ℕ, Lonely 8 (([1, 6, 20, 21, 22, 24, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 20, 21, 22, 24, 29]) (e := 20) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 20, 21, 26, 32, 40]`, flank `20`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_901 : ∃ k : ℕ, Lonely 8 (([1, 6, 20, 21, 26, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 20, 21, 26, 32, 40]) (e := 20) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 24, 26, 27, 28, 35]`, flank `24`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_902 : ∃ k : ℕ, Lonely 8 (([1, 6, 24, 26, 27, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 24, 26, 27, 28, 35]) (e := 24) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 24, 28, 29, 30, 33]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_903 : ∃ k : ℕ, Lonely 8 (([1, 6, 24, 28, 29, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 24, 28, 29, 30, 33]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 27, 32, 33, 35, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_904 : ∃ k : ℕ, Lonely 8 (([1, 6, 27, 32, 33, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 27, 32, 33, 35, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 28, 30, 31, 32, 35]`, flank `6`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_905 : ∃ k : ℕ, Lonely 8 (([1, 6, 28, 30, 31, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 28, 30, 31, 32, 35]) (e := 6) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 6, 42, 43, 44, 45, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_906 : ∃ k : ℕ, Lonely 8 (([1, 6, 42, 43, 44, 45, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 6, 42, 43, 44, 45, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 11, 12]`, flank `8`, opening `4`.  Covers 5 census rows. -/
theorem fam_1_907 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 11, 12].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 11, 12]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 11, 16]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_908 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 11, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 11, 16]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 11, 18]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_909 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 11, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 11, 18]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 11, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_910 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 11, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 12, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_911 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 12, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 12, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 14, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_912 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 14, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 17, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_913 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 17, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_914 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 17, 27]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_915 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 17, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 17, 27]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 10, 17, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_916 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 10, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 10, 17, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 11, 15, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_917 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 11, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 11, 15, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 11, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_918 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 11, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 11, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 11, 25, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_919 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 11, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 11, 25, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 12, 15, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_920 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 12, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 12, 15, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 12, 15, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_921 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 12, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 12, 15, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 15, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_922 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 15, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 15, 17, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_923 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 15, 17, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 15, 18, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_924 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 15, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 15, 18, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 15, 23, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_925 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 15, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 15, 23, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 16, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_926 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 16, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 16, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 17, 20, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_927 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 17, 20, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 17, 20, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 17, 25, 34]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_928 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 17, 25, 34]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 17, 25, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_929 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 17, 25, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 17, 25, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 17, 30, 34]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_930 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 17, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 17, 30, 34]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 25, 28, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_931 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 25, 28, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 25, 28, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 9, 25, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_932 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 9, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 9, 25, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 12, 13, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_933 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 12, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 12, 13, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 13, 18, 30]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_934 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 13, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 13, 18, 30]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 13, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_935 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 13, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 13, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 17, 18, 27]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_936 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 17, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 17, 18, 27]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 17, 18, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_1_937 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 17, 18, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 10, 17, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_938 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 10, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 10, 17, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 11, 13, 15, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_939 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 11, 13, 15, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 11, 15, 19, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_940 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 11, 15, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 11, 15, 19, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 11, 18, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_941 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 11, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 11, 18, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 11, 35, 36, 45]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_942 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 11, 35, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 11, 35, 36, 45]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 13, 15, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_943 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 13, 15, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 13, 20, 30]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_944 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 13, 20, 30]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 13, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_945 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 13, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 13, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 15, 26, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_946 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 15, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 15, 26, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 19, 20, 25]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_947 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 19, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 19, 20, 25]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 12, 19, 20, 29]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_948 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 12, 19, 20, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 12, 19, 20, 29]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 17, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_949 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 17, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 18, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_950 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 18, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_951 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 23, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_952 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 23, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_953 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 15, 29, 30]`, flank `8`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_954 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 15, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 15, 29, 30]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 18, 20, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_955 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 18, 20, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 18, 25, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_956 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 18, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 18, 25, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 20, 24, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_957 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 20, 24, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 13, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_958 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 13, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 13, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 17, 19, 34]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_959 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 17, 19, 34]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 18, 26, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_960 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 18, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 18, 26, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 22, 23, 46]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_961 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 22, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 22, 23, 46]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 23, 31, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_962 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 23, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 23, 31, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 24, 26, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_963 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 24, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 24, 26, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 15, 27, 29, 58]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_964 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 15, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 15, 27, 29, 58]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 16, 18, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_965 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 16, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 16, 18, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 17, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_966 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 17, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 17, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 17, 35, 36, 45]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_967 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 17, 35, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 17, 35, 36, 45]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 23, 30, 31, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_968 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 23, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 23, 30, 31, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 28, 35, 36, 45]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_969 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 28, 35, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 28, 35, 36, 45]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 8, 32, 39, 40, 45]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_970 : ∃ k : ℕ, Lonely 8 (([1, 7, 8, 32, 39, 40, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 8, 32, 39, 40, 45]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 12, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_971 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 12, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_972 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_973 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_974 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 16, 18]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_975 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 16, 18]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_976 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_977 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 11, 19, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_978 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 11, 19, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 12, 13, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_979 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 12, 13, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 12, 13, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 12, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_980 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 12, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 12, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 12, 16, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_981 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 12, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 12, 16, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 12, 17, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_982 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 12, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 12, 17, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 13, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_983 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 13, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 13, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 14, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_984 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 14, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 16, 17, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_1_985 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 16, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 16, 17, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 16, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_986 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 16, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 16, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_987 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 16, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 16, 17, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_988 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 16, 17, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 16, 17, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 16, 34, 51]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_989 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 16, 34, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 16, 34, 51]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 10, 23, 32, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_990 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 10, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 10, 23, 32, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 13, 20, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_991 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 13, 20, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 13, 20, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_992 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 13, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 13, 20, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 13, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_993 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 13, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 13, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 13, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_994 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 13, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 13, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 13, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_995 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 13, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 15, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_996 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 15, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_997 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 15, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_998 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 15, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 15, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 16, 20, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_999 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 16, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 16, 20, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 16, 25, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1000 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 16, 25, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 19, 20, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1001 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 19, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 19, 20, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 20, 21, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1002 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 20, 21, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 20, 21, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 11, 25, 32, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1003 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 11, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 11, 25, 32, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 12, 13, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_1004 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 12, 13, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 12, 13, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 12, 15, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_1005 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 12, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 12, 15, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 12, 15, 16, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1006 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 12, 15, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 12, 15, 16, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 14, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_1007 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 14, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_1008 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_1_1009 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 17, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_1010 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 17, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 17, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1011 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 18, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1012 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 18, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 23, 26]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_1013 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 23, 26]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 23, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1014 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 23, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 16, 29, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1015 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 16, 29, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 23, 24, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1016 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 23, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 23, 24, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 15, 23, 32, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1017 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 15, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 15, 23, 32, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 16, 17, 20, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1018 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 16, 17, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 16, 17, 20, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 16, 17, 25, 32]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1019 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 16, 17, 25, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 16, 17, 25, 32]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 16, 17, 25, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1020 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 16, 17, 25, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 16, 17, 25, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 16, 17, 30, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1021 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 16, 17, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 16, 17, 30, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 17, 24, 25, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1022 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 17, 24, 25, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 17, 24, 25, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 17, 25, 32, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1023 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 17, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 17, 25, 32, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 20, 23, 32, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1024 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 20, 23, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 20, 23, 32, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 21, 28, 35, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1025 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 21, 28, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 21, 28, 35, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 23, 25, 32, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1026 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 23, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 23, 25, 32, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 23, 30, 32, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1027 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 23, 30, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 23, 30, 32, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 9, 23, 32, 35, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1028 : ∃ k : ℕ, Lonely 8 (([1, 7, 9, 23, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 9, 23, 32, 35, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 12, 13, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1029 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 12, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 12, 13, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 12, 13, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1030 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 12, 13, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 12, 13, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 12, 17, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1031 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 12, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 12, 17, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1032 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 13, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1033 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 13, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 13, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 13, 21, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1034 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 13, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 13, 21, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 13, 24, 30]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_1035 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 13, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 13, 24, 30]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 13, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1036 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 13, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 13, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 17, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1037 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 17, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 17, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 17, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_1038 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 17, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 17, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 11, 21, 32, 33]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1039 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 11, 21, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 11, 21, 32, 33]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 12, 13, 19, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1040 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 12, 13, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 12, 13, 19, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 12, 13, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1041 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 12, 13, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 12, 13, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 13, 18, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1042 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 13, 18, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 13, 18, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 13, 19, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1043 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 13, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 13, 19, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 15, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1044 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 15, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 15, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 15, 17, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1045 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 15, 17, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 15, 17, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 17, 19, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1046 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 17, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 17, 19, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 18, 19, 28, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1047 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 18, 19, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 18, 19, 28, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 10, 21, 22, 32, 33]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1048 : ∃ k : ℕ, Lonely 8 (([1, 7, 10, 21, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 10, 21, 22, 32, 33]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 15, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1049 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 15, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1050 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 20, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1051 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 20, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1052 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1053 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 13, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1054 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 13, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 13, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 17, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1055 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 17, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 17, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 23, 25, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1056 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 23, 25, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 23, 25, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 12, 23, 30, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1057 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 12, 23, 30, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 12, 23, 30, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_1_1058 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 14, 15, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1059 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 14, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 14, 15, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 14, 15, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1060 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 14, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 14, 15, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 16, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1061 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 16, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 16, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 18, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1062 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 18, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 18, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1063 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1064 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 22, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1065 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 22, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 22, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 24, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1066 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 24, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1067 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 15, 28, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1068 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 15, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 15, 28, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 18, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1069 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 18, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 18, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1070 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 18, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 18, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 20, 21, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1071 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 20, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 20, 21, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 20, 24, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1072 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 20, 24, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 20, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1073 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 20, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 20, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 13, 24, 25, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1074 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 13, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 13, 24, 25, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 15, 16, 19, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1075 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 15, 16, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 15, 16, 19, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 15, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1076 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 15, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 15, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 17, 18, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1077 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 17, 18, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 17, 18, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 17, 20, 24, 30]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_1078 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 17, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 17, 20, 24, 30]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 18, 25, 32, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1079 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 18, 25, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 18, 25, 32, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 19, 20, 21, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1080 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 19, 20, 21, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 20, 21, 22, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1081 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 20, 21, 22, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 20, 21, 22, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 11, 21, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1082 : ∃ k : ℕ, Lonely 8 (([1, 7, 11, 21, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 11, 21, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 15, 19, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1083 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 15, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 15, 19, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 15, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1084 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 15, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 15, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 19, 20, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1085 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 19, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 19, 20, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 19, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1086 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 19, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 19, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1087 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 19, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 19, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 20, 27, 54]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1088 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 20, 27, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 20, 27, 54]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 13, 25, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1089 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 13, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 13, 25, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 15, 16, 23, 32]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1090 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 15, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 15, 16, 23, 32]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 19, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1091 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 19, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 19, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 12, 23, 30, 31, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1092 : ∃ k : ℕ, Lonely 8 (([1, 7, 12, 23, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 12, 23, 30, 31, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 14, 15, 16, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1093 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 14, 15, 16, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 14, 15, 16, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 14, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1094 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 14, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 14, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 14, 15, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1095 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 14, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 14, 15, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 16, 17, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1096 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 16, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 16, 17, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 16, 20, 26]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1097 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 16, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 16, 20, 26]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 16, 23, 24]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1098 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 16, 23, 24]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 16, 23, 26]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1099 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 16, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 16, 23, 26]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 18, 19, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1100 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 18, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 18, 19, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 19, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1101 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 19, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 19, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1102 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 22, 24, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1103 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 22, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 22, 24, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1104 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 15, 27, 28, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1105 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 15, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 15, 27, 28, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 16, 18, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1106 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 16, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 16, 18, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 18, 19, 20, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1107 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 18, 19, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 18, 19, 20, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 18, 19, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1108 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 18, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 18, 19, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 18, 19, 25, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1109 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 18, 19, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 18, 19, 25, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 18, 25, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1110 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 18, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 18, 25, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 19, 20, 24, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1111 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 19, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 19, 20, 24, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 19, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1112 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 19, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 19, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 23, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1113 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 23, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 23, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 13, 24, 25, 27, 30]`, flank `13`, opening `5`.  Covers 2 census rows. -/
theorem fam_1_1114 : ∃ k : ℕ, Lonely 8 (([1, 7, 13, 24, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 13, 24, 25, 27, 30]) (e := 13) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 14, 15, 16, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1115 : ∃ k : ℕ, Lonely 8 (([1, 7, 14, 15, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 14, 15, 16, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 14, 15, 16, 29, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1116 : ∃ k : ℕ, Lonely 8 (([1, 7, 14, 15, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 14, 15, 16, 29, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 14, 15, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1117 : ∃ k : ℕ, Lonely 8 (([1, 7, 14, 15, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 14, 15, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 17, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1118 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 17, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 17, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 18, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1119 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 18, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 22, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1120 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 22, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 22, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 22, 29, 58]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1121 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 22, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 22, 29, 58]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 23, 27, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1122 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 23, 27, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 23, 27, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 16, 23, 29, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1123 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 16, 23, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 16, 23, 29, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 17, 19, 20, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1124 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 17, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 17, 19, 20, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 17, 19, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1125 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 17, 19, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 17, 19, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 17, 24, 31, 34]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1126 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 17, 24, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 17, 24, 31, 34]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 19, 26, 29, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1127 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 19, 26, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 19, 26, 29, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 22, 23, 24, 28]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_1_1128 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 22, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 22, 23, 24, 28]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 22, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1129 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 22, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 22, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 22, 29, 43, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1130 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 22, 29, 43, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 22, 29, 43, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 22, 31, 32, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1131 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 22, 31, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 22, 31, 32, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 24, 25, 26, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1132 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 24, 25, 26, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 26, 28, 29, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1133 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 26, 28, 29, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 26, 28, 29, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 15, 27, 29, 36, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1134 : ∃ k : ℕ, Lonely 8 (([1, 7, 15, 27, 29, 36, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 15, 27, 29, 36, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 17, 18, 25, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_1_1135 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 17, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 17, 18, 25, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 17, 18, 30, 36]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1136 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 17, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 17, 18, 30, 36]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 18, 19, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1137 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 18, 19, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 18, 19, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 18, 25, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1138 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 18, 25, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 18, 25, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 18, 25, 34, 36]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1139 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 18, 25, 34, 36]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 23, 24, 25, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1140 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 23, 24, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 23, 24, 25, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 23, 30, 31, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1141 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 23, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 23, 30, 31, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 16, 23, 30, 31, 60]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1142 : ∃ k : ℕ, Lonely 8 (([1, 7, 16, 23, 30, 31, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 16, 23, 30, 31, 60]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 17, 18, 30, 32, 36]`, flank `17`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1143 : ∃ k : ℕ, Lonely 8 (([1, 7, 17, 18, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 17, 18, 30, 32, 36]) (e := 17) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 17, 19, 20, 21, 24]`, flank `17`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1144 : ∃ k : ℕ, Lonely 8 (([1, 7, 17, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 17, 19, 20, 21, 24]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 17, 19, 20, 24, 30]`, flank `17`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1145 : ∃ k : ℕ, Lonely 8 (([1, 7, 17, 19, 20, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 17, 19, 20, 24, 30]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 17, 23, 24, 25, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1146 : ∃ k : ℕ, Lonely 8 (([1, 7, 17, 23, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 17, 23, 24, 25, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 17, 25, 26, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1147 : ∃ k : ℕ, Lonely 8 (([1, 7, 17, 25, 26, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 17, 25, 26, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 18, 19, 25, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_1_1148 : ∃ k : ℕ, Lonely 8 (([1, 7, 18, 19, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 18, 19, 25, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 18, 22, 29, 40, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1149 : ∃ k : ℕ, Lonely 8 (([1, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 18, 22, 29, 40, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 19, 20, 21, 28, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1150 : ∃ k : ℕ, Lonely 8 (([1, 7, 19, 20, 21, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 19, 20, 21, 28, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 19, 20, 21, 33, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1151 : ∃ k : ℕ, Lonely 8 (([1, 7, 19, 20, 21, 33, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 19, 20, 21, 33, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 19, 24, 25, 26, 30]`, flank `7`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1152 : ∃ k : ℕ, Lonely 8 (([1, 7, 19, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 19, 24, 25, 26, 30]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 20, 21, 22, 35, 40]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1153 : ∃ k : ℕ, Lonely 8 (([1, 7, 20, 21, 22, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 20, 21, 22, 35, 40]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 20, 23, 30, 31, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1154 : ∃ k : ℕ, Lonely 8 (([1, 7, 20, 23, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 20, 23, 30, 31, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 21, 22, 23, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1155 : ∃ k : ℕ, Lonely 8 (([1, 7, 21, 22, 23, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 21, 22, 23, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 21, 22, 23, 40, 46]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1156 : ∃ k : ℕ, Lonely 8 (([1, 7, 21, 22, 23, 40, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 21, 22, 23, 40, 46]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 23, 24, 25, 39, 50]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1157 : ∃ k : ℕ, Lonely 8 (([1, 7, 23, 24, 25, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 23, 24, 25, 39, 50]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 23, 24, 30, 31, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1158 : ∃ k : ℕ, Lonely 8 (([1, 7, 23, 24, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 23, 24, 30, 31, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 23, 28, 30, 31, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1159 : ∃ k : ℕ, Lonely 8 (([1, 7, 23, 28, 30, 31, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 23, 28, 30, 31, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 23, 30, 31, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1160 : ∃ k : ℕ, Lonely 8 (([1, 7, 23, 30, 31, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 23, 30, 31, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 24, 25, 26, 43, 48]`, flank `7`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1161 : ∃ k : ℕ, Lonely 8 (([1, 7, 24, 25, 26, 43, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 24, 25, 26, 43, 48]) (e := 7) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 29, 30, 31, 53, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_1_1162 : ∃ k : ℕ, Lonely 8 (([1, 7, 29, 30, 31, 53, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 29, 30, 31, 53, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 7, 41, 42, 48, 49, 60]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_1_1163 : ∃ k : ℕ, Lonely 8 (([1, 7, 41, 42, 48, 49, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [1, 7, 41, 42, 48, 49, 60]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 10, 11, 14, 16]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_1164 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 10, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 10, 11, 14, 16]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 10, 13, 14, 20]`, flank `8`, opening `2`.  Covers 3 census rows. -/
theorem fam_1_1165 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 10, 13, 14, 20]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 10, 14, 19, 20]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_1166 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 10, 14, 19, 20]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 10, 19, 28, 45]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1167 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 10, 19, 28, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 10, 19, 28, 45]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 12, 14, 15, 18]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_1168 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 12, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 12, 14, 15, 18]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 13, 14, 15, 20]`, flank `8`, opening `4`.  Covers 3 census rows. -/
theorem fam_1_1169 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 13, 14, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 13, 14, 15, 20]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 14, 15, 17, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1170 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 14, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 14, 15, 17, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 14, 17, 30, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1171 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 14, 17, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 14, 17, 30, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 17, 20, 21, 27]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1172 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 17, 20, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 17, 20, 21, 27]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 17, 26, 35, 45]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1173 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 17, 26, 35, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 17, 26, 35, 45]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 28, 29, 30, 35]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1174 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 28, 29, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 28, 29, 30, 35]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 9, 28, 31, 40, 50]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1175 : ∃ k : ℕ, Lonely 8 (([1, 8, 9, 28, 31, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 9, 28, 31, 40, 50]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 11, 12, 14, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1176 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 11, 12, 14, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 11, 12, 14, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 11, 14, 18, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1177 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 11, 14, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 11, 14, 18, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 11, 19, 21, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1178 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 11, 19, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 11, 19, 21, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 11, 19, 21, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1179 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 11, 19, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 11, 19, 21, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 12, 13, 14, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1180 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 12, 13, 14, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 12, 13, 14, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 13, 14, 18, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1181 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 13, 14, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 13, 14, 18, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 14, 17, 18, 36]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1182 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 14, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 14, 17, 18, 36]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 18, 19, 28, 45]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1183 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 18, 19, 28, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 18, 19, 28, 45]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 19, 21, 22, 33]`, flank `19`, opening `3`.  Covers 1 census rows. -/
theorem fam_1_1184 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 19, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 19, 21, 22, 33]) (e := 19) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 19, 27, 28, 45]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_1_1185 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 19, 27, 28, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 19, 27, 28, 45]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 10, 19, 28, 36, 45]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_1_1186 : ∃ k : ℕ, Lonely 8 (([1, 8, 10, 19, 28, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 10, 19, 28, 36, 45]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 12, 14, 20, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1187 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 12, 14, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 12, 14, 20, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 13, 14, 15, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1188 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 13, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 13, 14, 15, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 14, 15, 16, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1189 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 14, 15, 16, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 14, 15, 19, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1190 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 14, 15, 19, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 14, 15, 22, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1191 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 14, 15, 22, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 11, 14, 15, 25, 28]`, flank `8`, opening `6`.  Covers 2 census rows. -/
theorem fam_1_1192 : ∃ k : ℕ, Lonely 8 (([1, 8, 11, 14, 15, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 11, 14, 15, 25, 28]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 13, 14, 20, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1193 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 13, 14, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 13, 14, 20, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 14, 15, 16, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1194 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 14, 15, 16, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 14, 15, 20, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_1_1195 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 14, 15, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 14, 15, 20, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 14, 15, 22, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1196 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 14, 15, 22, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 14, 17, 20, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_1_1197 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 14, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 14, 17, 20, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 12, 20, 21, 22, 40]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_1_1198 : ∃ k : ℕ, Lonely 8 (([1, 8, 12, 20, 21, 22, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 12, 20, 21, 22, 40]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 13, 14, 15, 17, 24]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1199 : ∃ k : ℕ, Lonely 8 (([1, 8, 13, 14, 15, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 13, 14, 15, 17, 24]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 13, 14, 15, 17, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_1_1200 : ∃ k : ℕ, Lonely 8 (([1, 8, 13, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 13, 14, 15, 17, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

end PinnedBatch1
