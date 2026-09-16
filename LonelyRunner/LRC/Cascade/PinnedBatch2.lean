import LonelyRunner.LRC.Cascade.Flanks

/-!
# Fully-pinned census families, part 2 of 4

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Each theorem is one seven-difference arrangement from an `s = 6` census cover — fully pinned,
so there is no free parameter and Existence for the runner is just that some flank has a lonely
opening.  The framework's clearing test (`Flanks.clear_of_residue_band`, Proposition 2.1) makes
that decidable arithmetic, so each family closes by `decide` on the residue band.

Emitted by `experiments/n8/gen_pinned_batch_v1.py`; data recomputed and cross-checked in
`experiments/n8/census_export_v1.py`.
-/

set_option maxHeartbeats 1000000

namespace PinnedBatch2

open MomentIterationN Flanks

/-- Differences `[1, 8, 13, 15, 17, 21, 26]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_1 : ∃ k : ℕ, Lonely 8 (([1, 8, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 13, 15, 17, 21, 26]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 16, 17, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_2 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 16, 17, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 16, 17, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_3 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 16, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 16, 17, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 17, 19, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_4 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 17, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 17, 19, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 17, 22, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_5 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 17, 22, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 17, 25, 28]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_6 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 17, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 17, 25, 28]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 17, 25, 34]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_7 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 17, 25, 34]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 15, 22, 23, 28]`, flank `8`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_8 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 15, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 15, 22, 23, 28]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 14, 17, 18, 20, 24]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_9 : ∃ k : ℕ, Lonely 8 (([1, 8, 14, 17, 18, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 14, 17, 18, 20, 24]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 18, 20, 21, 27]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_10 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 18, 20, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 18, 20, 21, 27]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 18, 26, 35, 45]`, flank `17`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_11 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 18, 26, 35, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 18, 26, 35, 45]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 19, 20, 21, 24]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_12 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 19, 20, 21, 24]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 19, 35, 36, 45]`, flank `17`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_13 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 19, 35, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 19, 35, 36, 45]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 21, 25, 26, 30]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_14 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 21, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 21, 25, 26, 30]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 26, 27, 35, 45]`, flank `8`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_15 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 26, 27, 35, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 26, 27, 35, 45]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 17, 26, 35, 36, 45]`, flank `17`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_16 : ∃ k : ℕ, Lonely 8 (([1, 8, 17, 26, 35, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 17, 26, 35, 36, 45]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 18, 19, 20, 28, 40]`, flank `8`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_17 : ∃ k : ℕ, Lonely 8 (([1, 8, 18, 19, 20, 28, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 18, 19, 20, 28, 40]) (e := 8) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 8, 21, 24, 25, 26, 30]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_18 : ∃ k : ℕ, Lonely 8 (([1, 8, 21, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 8, 21, 24, 25, 26, 30]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 11, 13, 14, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_19 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 11, 13, 14, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 11, 13, 14, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 11, 21, 24, 30]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_20 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 11, 21, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 11, 21, 24, 30]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 12, 13, 14, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_21 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 12, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 12, 13, 14, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 12, 14, 19, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_22 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 12, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 12, 14, 19, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 13, 14, 16, 20]`, flank `10`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_23 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 13, 14, 16, 20]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 14, 16, 19, 20]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_24 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 14, 16, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 14, 16, 19, 20]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 17, 19, 21, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_25 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 17, 19, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 17, 19, 21, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 19, 28, 29, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_26 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 19, 28, 29, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 19, 28, 29, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 10, 24, 27, 28, 35]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_27 : ∃ k : ℕ, Lonely 8 (([1, 9, 10, 24, 27, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 10, 24, 27, 28, 35]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 11, 13, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_28 : ∃ k : ℕ, Lonely 8 (([1, 9, 11, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 11, 13, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 11, 13, 14, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_29 : ∃ k : ℕ, Lonely 8 (([1, 9, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 11, 13, 14, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 11, 13, 20, 21, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_30 : ∃ k : ℕ, Lonely 8 (([1, 9, 11, 13, 20, 21, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 11, 13, 20, 21, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 11, 14, 15, 19, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_31 : ∃ k : ℕ, Lonely 8 (([1, 9, 11, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 11, 14, 15, 19, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 11, 20, 21, 24, 30]`, flank `9`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_32 : ∃ k : ℕ, Lonely 8 (([1, 9, 11, 20, 21, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 11, 20, 21, 24, 30]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 12, 13, 14, 15, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_33 : ∃ k : ℕ, Lonely 8 (([1, 9, 12, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 12, 13, 14, 15, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 12, 13, 14, 15, 20]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_34 : ∃ k : ℕ, Lonely 8 (([1, 9, 12, 13, 14, 15, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 12, 13, 14, 15, 20]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 12, 14, 15, 16, 18]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_35 : ∃ k : ℕ, Lonely 8 (([1, 9, 12, 14, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 12, 14, 15, 16, 18]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 12, 14, 15, 16, 22]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_36 : ∃ k : ℕ, Lonely 8 (([1, 9, 12, 14, 15, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 12, 14, 15, 16, 22]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 15, 16, 20]`, flank `13`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_37 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 15, 16, 20]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 15, 17, 18]`, flank `1`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_38 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 15, 17, 18]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 15, 17, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_39 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 15, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 15, 17, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 15, 24, 30]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_40 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 15, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 15, 24, 30]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 16, 17, 20]`, flank `13`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_41 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 16, 17, 20]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 14, 17, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_42 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 14, 17, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 13, 15, 17, 28, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_43 : ∃ k : ℕ, Lonely 8 (([1, 9, 13, 15, 17, 28, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 13, 15, 17, 28, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 14, 15, 16, 17, 22]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_44 : ∃ k : ℕ, Lonely 8 (([1, 9, 14, 15, 16, 17, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 14, 15, 16, 17, 22]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 14, 15, 16, 19, 20]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_45 : ∃ k : ℕ, Lonely 8 (([1, 9, 14, 15, 16, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 14, 15, 16, 19, 20]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 14, 15, 17, 21, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_46 : ∃ k : ℕ, Lonely 8 (([1, 9, 14, 15, 17, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 14, 15, 17, 21, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 15, 17, 20, 21, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_47 : ∃ k : ℕ, Lonely 8 (([1, 9, 15, 17, 20, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 15, 17, 20, 21, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 15, 17, 21, 26, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_48 : ∃ k : ℕ, Lonely 8 (([1, 9, 15, 17, 21, 26, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 15, 17, 21, 26, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 17, 19, 20, 21, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_49 : ∃ k : ℕ, Lonely 8 (([1, 9, 17, 19, 20, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 17, 19, 20, 21, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 17, 21, 27, 30, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_50 : ∃ k : ℕ, Lonely 8 (([1, 9, 17, 21, 27, 30, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 17, 21, 27, 30, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 19, 20, 28, 29, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_51 : ∃ k : ℕ, Lonely 8 (([1, 9, 19, 20, 28, 29, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 19, 20, 28, 29, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 19, 28, 29, 30, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_52 : ∃ k : ℕ, Lonely 8 (([1, 9, 19, 28, 29, 30, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 19, 28, 29, 30, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 9, 19, 28, 29, 40, 50]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_53 : ∃ k : ℕ, Lonely 8 (([1, 9, 19, 28, 29, 40, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 9, 19, 28, 29, 40, 50]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 13, 14, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_54 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 13, 14, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 13, 14, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_55 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 13, 14, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 14, 16, 24]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_56 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 14, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 14, 16, 24]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 14, 19, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_57 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 14, 19, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 21, 23, 24]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_58 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 21, 23, 24]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 21, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_59 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 21, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 21, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 12, 21, 32, 42]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_60 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 12, 21, 32, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 12, 21, 32, 42]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 13, 16, 21, 30]`, flank `10`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_61 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 13, 16, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 13, 16, 21, 30]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 13, 21, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_62 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 13, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 13, 21, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 14, 15, 16, 28]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_63 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 14, 15, 16, 28]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 14, 16, 18, 24]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_64 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 14, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 14, 16, 18, 24]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 14, 21, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_65 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 14, 21, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 14, 21, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 14, 24, 25, 33]`, flank `10`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_66 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 14, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 14, 24, 25, 33]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 16, 19, 21, 24]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_67 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 16, 19, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 16, 19, 21, 24]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 16, 19, 21, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_68 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 16, 19, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 16, 19, 21, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 18, 19, 21, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_69 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 18, 19, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 18, 19, 21, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 18, 21, 35, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_70 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 18, 21, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 18, 21, 35, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 19, 21, 23, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_71 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 19, 21, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 19, 21, 23, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 19, 21, 23, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_72 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 19, 21, 23, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 19, 21, 23, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 19, 21, 24, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_73 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 19, 21, 24, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 19, 21, 24, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 19, 21, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_74 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 19, 21, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 19, 21, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 19, 21, 41, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_75 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 19, 21, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 19, 21, 41, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 21, 24, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_76 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 21, 24, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 21, 24, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 21, 26, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_77 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 21, 26, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 21, 26, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 21, 31, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_78 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 21, 31, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 21, 31, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 21, 31, 32, 40]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_79 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 21, 31, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 21, 31, 32, 40]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 11, 21, 35, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_80 : ∃ k : ℕ, Lonely 8 (([1, 10, 11, 21, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 11, 21, 35, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 13, 14, 16, 24]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_81 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 13, 14, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 13, 14, 16, 24]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 13, 14, 16, 28]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_82 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 13, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 13, 14, 16, 28]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 13, 14, 17, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_83 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 13, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 13, 14, 17, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 13, 14, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_84 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 13, 14, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 13, 14, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 13, 14, 27, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_85 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 13, 14, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 13, 14, 27, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 15, 16, 28]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_86 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 15, 16, 28]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 15, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_87 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 15, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 17, 18, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_88 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 17, 18, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 17, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_89 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 17, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 17, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 18, 19, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_90 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 18, 19, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 18, 19, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 14, 19, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_91 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 14, 19, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 14, 19, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 21, 22, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_92 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 21, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 21, 22, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 12, 21, 22, 32, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_93 : ∃ k : ℕ, Lonely 8 (([1, 10, 12, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 12, 21, 22, 32, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 13, 14, 16, 18, 24]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_94 : ∃ k : ℕ, Lonely 8 (([1, 10, 13, 14, 16, 18, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 13, 14, 16, 18, 24]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 13, 15, 17, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_95 : ∃ k : ℕ, Lonely 8 (([1, 10, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 13, 15, 17, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 13, 21, 22, 32, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_96 : ∃ k : ℕ, Lonely 8 (([1, 10, 13, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 13, 21, 22, 32, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 15, 16, 17, 28]`, flank `10`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_97 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 15, 16, 17, 28]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 16, 17, 18, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_98 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 16, 17, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 16, 17, 18, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 17, 18, 20, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_99 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 17, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 17, 18, 20, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 17, 18, 24, 36]`, flank `10`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_100 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 17, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 17, 18, 24, 36]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 17, 18, 28, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_101 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 17, 18, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 17, 18, 28, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 17, 18, 32, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_102 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 17, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 17, 18, 32, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 18, 19, 24, 36]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_103 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 18, 19, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 18, 19, 24, 36]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 21, 22, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_104 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 21, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 21, 22, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 22, 23, 24, 48]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_105 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 22, 23, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 22, 23, 24, 48]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 22, 24, 25, 33]`, flank `10`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_106 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 22, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 22, 24, 25, 33]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 14, 22, 24, 25, 48]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_107 : ∃ k : ℕ, Lonely 8 (([1, 10, 14, 22, 24, 25, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 14, 22, 24, 25, 48]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 16, 19, 21, 22, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_108 : ∃ k : ℕ, Lonely 8 (([1, 10, 16, 19, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 16, 19, 21, 22, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 16, 19, 21, 29, 38]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_109 : ∃ k : ℕ, Lonely 8 (([1, 10, 16, 19, 21, 29, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 16, 19, 21, 29, 38]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 18, 19, 22, 28, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_110 : ∃ k : ℕ, Lonely 8 (([1, 10, 18, 19, 22, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 18, 19, 22, 28, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 18, 19, 28, 29, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_111 : ∃ k : ℕ, Lonely 8 (([1, 10, 18, 19, 28, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 18, 19, 28, 29, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 18, 21, 22, 32, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_112 : ∃ k : ℕ, Lonely 8 (([1, 10, 18, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 18, 21, 22, 32, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 19, 21, 22, 24, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_113 : ∃ k : ℕ, Lonely 8 (([1, 10, 19, 21, 22, 24, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 19, 21, 22, 24, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 19, 21, 22, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_114 : ∃ k : ℕ, Lonely 8 (([1, 10, 19, 21, 22, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 19, 21, 22, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 19, 21, 22, 32, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_115 : ∃ k : ℕ, Lonely 8 (([1, 10, 19, 21, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 19, 21, 22, 32, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 19, 21, 23, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_116 : ∃ k : ℕ, Lonely 8 (([1, 10, 19, 21, 23, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 19, 21, 23, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 24, 32, 33]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_117 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 24, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 24, 32, 33]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 24, 32, 44]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_118 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 24, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 24, 32, 44]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 25, 32, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_119 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 25, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 25, 32, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 26, 32, 33]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_120 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 26, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 26, 32, 33]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 31, 32, 33]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_121 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 31, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 31, 32, 33]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 31, 32, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_122 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 31, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 31, 32, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 32, 37, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_123 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 32, 37, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 32, 37, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 21, 22, 32, 43, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_124 : ∃ k : ℕ, Lonely 8 (([1, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 21, 22, 32, 43, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 24, 26, 27, 28, 56]`, flank `10`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_125 : ∃ k : ℕ, Lonely 8 (([1, 10, 24, 26, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 24, 26, 27, 28, 56]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 24, 26, 28, 29, 56]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_126 : ∃ k : ℕ, Lonely 8 (([1, 10, 24, 26, 28, 29, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 24, 26, 28, 29, 56]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 25, 26, 28, 30, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_127 : ∃ k : ℕ, Lonely 8 (([1, 10, 25, 26, 28, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 25, 26, 28, 30, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 26, 27, 28, 30, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_128 : ∃ k : ℕ, Lonely 8 (([1, 10, 26, 27, 28, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 26, 27, 28, 30, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 10, 28, 29, 30, 32, 56]`, flank `10`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_129 : ∃ k : ℕ, Lonely 8 (([1, 10, 28, 29, 30, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 10, 28, 29, 30, 32, 56]) (e := 10) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 15, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_130 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 15, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 15, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_131 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 15, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 15, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_132 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 15, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 20, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_133 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 20, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_134 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 25, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_135 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 25, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 25, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_136 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 14, 25, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_137 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 14, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 14, 25, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 15, 21, 22]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_138 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 15, 21, 22]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_139 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 13, 23, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_140 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 13, 23, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 13, 23, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 14, 16, 20, 24]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_141 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 14, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 14, 16, 20, 24]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 20, 21, 23, 24]`, flank `11`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_142 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 20, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 20, 21, 23, 24]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 20, 21, 23, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_143 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 20, 21, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 20, 21, 23, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 20, 23, 42, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_144 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 20, 23, 42, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 20, 23, 42, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 12, 23, 34, 35, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_145 : ∃ k : ℕ, Lonely 8 (([1, 11, 12, 23, 34, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 12, 23, 34, 35, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 16, 18]`, flank `13`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_146 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 16, 18]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 16, 28]`, flank `11`, opening `9`.  Covers 2 census rows. -/
theorem fam_2_147 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 16, 28]) (e := 11) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 17, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_148 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 17, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 19, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_149 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 19, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 19, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_150 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 24, 26]`, flank `11`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_151 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 24, 26]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 15, 24, 28]`, flank `11`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_152 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 15, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 15, 24, 28]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 24, 25, 30]`, flank `11`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_153 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 24, 25, 30]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 24, 25, 36]`, flank `11`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_154 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 24, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 24, 25, 36]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 14, 24, 25, 48]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_155 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 14, 24, 25, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 14, 24, 25, 48]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 16, 20, 21, 30]`, flank `11`, opening `8`.  Covers 2 census rows. -/
theorem fam_2_156 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 16, 20, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 16, 20, 21, 30]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 20, 21, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_157 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 20, 21, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 20, 21, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 21, 24, 25, 30]`, flank `11`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_158 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 21, 24, 25, 30]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 13, 23, 24, 35, 48]`, flank `11`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_159 : ∃ k : ℕ, Lonely 8 (([1, 11, 13, 23, 24, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 13, 23, 24, 35, 48]) (e := 11) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 14, 15, 16, 18, 28]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_160 : ∃ k : ℕ, Lonely 8 (([1, 11, 14, 15, 16, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 14, 15, 16, 18, 28]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 14, 15, 16, 26, 28]`, flank `11`, opening `9`.  Covers 2 census rows. -/
theorem fam_2_161 : ∃ k : ℕ, Lonely 8 (([1, 11, 14, 15, 16, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 14, 15, 16, 26, 28]) (e := 11) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 21, 24, 25, 26, 30]`, flank `11`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_162 : ∃ k : ℕ, Lonely 8 (([1, 11, 21, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 21, 24, 25, 26, 30]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 21, 30, 31, 32, 40]`, flank `11`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_163 : ∃ k : ℕ, Lonely 8 (([1, 11, 21, 30, 31, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 21, 30, 31, 32, 40]) (e := 11) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 11, 23, 24, 34, 35, 36]`, flank `11`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_164 : ∃ k : ℕ, Lonely 8 (([1, 11, 23, 24, 34, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 11, 23, 24, 34, 35, 36]) (e := 11) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 16, 26]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_165 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 16, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 16, 26]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 16, 28]`, flank `12`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_166 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 16, 28]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 17, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_167 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 17, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_168 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_169 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 15, 27, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_170 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 15, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 15, 27, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 16, 20, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_171 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 16, 20, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 16, 20, 28]`, flank `12`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_172 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 16, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 16, 20, 28]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 16, 25, 28]`, flank `12`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_173 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 16, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 16, 25, 28]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 16, 25, 39]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_174 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 16, 25, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 16, 25, 39]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 16, 35, 39]`, flank `12`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_175 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 16, 35, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 16, 35, 39]) (e := 12) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 17, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_176 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 17, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 17, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_177 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 17, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 17, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 20, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_178 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 20, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 20, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 20, 27, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_179 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 20, 27, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 22, 25, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_180 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 22, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 22, 25, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 14, 25, 27, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_181 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 14, 25, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 14, 25, 27, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 15, 17, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_182 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 15, 17, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 15, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_183 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 15, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 15, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 15, 21, 23, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_184 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 15, 21, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 15, 21, 23, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 13, 15, 27, 28, 56]`, flank `12`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_185 : ∃ k : ℕ, Lonely 8 (([1, 12, 13, 15, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 13, 15, 27, 28, 56]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 16, 18, 28]`, flank `12`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_186 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 16, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 16, 18, 28]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 16, 20, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_187 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 16, 20, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 16, 20, 32]`, flank `12`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_188 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 16, 20, 32]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 16, 26, 28]`, flank `12`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_189 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 16, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 16, 26, 28]) (e := 12) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 16, 26, 32]`, flank `12`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_190 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 16, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 16, 26, 32]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 18, 22, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_191 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 18, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 18, 22, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 22, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_192 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 22, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 22, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_193 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 22, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 22, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 15, 26, 27, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_194 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 15, 26, 27, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 15, 26, 27, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 16, 17, 20, 24]`, flank `12`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_195 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 16, 17, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 16, 17, 20, 24]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 16, 17, 20, 32]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_196 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 16, 17, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 16, 17, 20, 32]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 16, 25, 26, 39]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_197 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 16, 25, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 16, 25, 26, 39]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 16, 26, 35, 39]`, flank `12`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_198 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 16, 26, 35, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 16, 26, 35, 39]) (e := 12) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 17, 25, 26, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_199 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 17, 25, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 17, 25, 26, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 22, 25, 26, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_200 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 22, 25, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 22, 25, 26, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 26, 27, 30, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_201 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 26, 27, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 26, 27, 30, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 14, 26, 27, 45, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_202 : ∃ k : ℕ, Lonely 8 (([1, 12, 14, 26, 27, 45, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 14, 26, 27, 45, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 15, 19, 20, 21, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_203 : ∃ k : ℕ, Lonely 8 (([1, 12, 15, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 15, 19, 20, 21, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 16, 20, 21, 22, 40]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_204 : ∃ k : ℕ, Lonely 8 (([1, 12, 16, 20, 21, 22, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 16, 20, 21, 22, 40]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 16, 27, 28, 30, 56]`, flank `12`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_205 : ∃ k : ℕ, Lonely 8 (([1, 12, 16, 27, 28, 30, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 16, 27, 28, 30, 56]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 16, 28, 29, 30, 56]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_206 : ∃ k : ℕ, Lonely 8 (([1, 12, 16, 28, 29, 30, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 16, 28, 29, 30, 56]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 16, 28, 30, 31, 56]`, flank `12`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_207 : ∃ k : ℕ, Lonely 8 (([1, 12, 16, 28, 30, 31, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 16, 28, 30, 31, 56]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 20, 21, 22, 24, 40]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_208 : ∃ k : ℕ, Lonely 8 (([1, 12, 20, 21, 22, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 20, 21, 22, 24, 40]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 20, 21, 22, 32, 40]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_209 : ∃ k : ℕ, Lonely 8 (([1, 12, 20, 21, 22, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 20, 21, 22, 32, 40]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 21, 23, 33, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_210 : ∃ k : ℕ, Lonely 8 (([1, 12, 21, 23, 33, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 21, 23, 33, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 25, 26, 28, 40, 56]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_211 : ∃ k : ℕ, Lonely 8 (([1, 12, 25, 26, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 25, 26, 28, 40, 56]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 26, 27, 28, 40, 56]`, flank `12`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_212 : ∃ k : ℕ, Lonely 8 (([1, 12, 26, 27, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 26, 27, 28, 40, 56]) (e := 12) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 12, 26, 28, 29, 40, 56]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_213 : ∃ k : ℕ, Lonely 8 (([1, 12, 26, 28, 29, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 12, 26, 28, 29, 40, 56]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 24]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_214 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 24]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 26]`, flank `13`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_215 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 26]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 28]`, flank `13`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_216 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 28]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 30]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_217 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 30]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 32]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_218 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 32]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 17, 34]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_219 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 17, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 17, 34]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 19, 26]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_220 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 19, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 19, 26]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 24, 26]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_221 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 24, 26]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 24, 30]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_222 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 24, 30]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 16, 29, 32]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_223 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 16, 29, 32]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 17, 20, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_224 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 17, 20, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 17, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_225 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 17, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 17, 24, 28]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_226 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 17, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 17, 24, 28]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 17, 25, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_227 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 17, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 17, 25, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 18, 21, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_228 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 18, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 18, 21, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 19, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_229 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 19, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 19, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 21, 24, 26]`, flank `13`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_230 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 21, 24, 26]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 23, 24, 30]`, flank `13`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_231 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 23, 24, 30]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 23, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_232 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 23, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 23, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 24, 25, 30]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_233 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 24, 25, 30]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_234 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 15, 29, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_235 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 15, 29, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 15, 29, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 23, 25, 27, 54]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_236 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 23, 25, 27, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 23, 25, 27, 54]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 14, 27, 40, 41, 50]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_237 : ∃ k : ℕ, Lonely 8 (([1, 13, 14, 27, 40, 41, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 14, 27, 40, 41, 50]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 16, 17, 21, 26]`, flank `13`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_238 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 16, 17, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 16, 17, 21, 26]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 16, 28, 29, 32]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_239 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 16, 28, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 16, 28, 29, 32]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 17, 18, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_240 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 17, 18, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 17, 18, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 17, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_241 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 17, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 17, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 17, 21, 22, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_242 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 17, 21, 22, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 17, 21, 22, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 17, 21, 24, 26]`, flank `13`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_243 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 17, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 17, 21, 24, 26]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 17, 27, 28, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_244 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 17, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 17, 27, 28, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 18, 21, 28, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_245 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 18, 21, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 18, 21, 28, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 19, 20, 21, 26]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_246 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 19, 20, 21, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 19, 20, 21, 26]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 20, 21, 24, 26]`, flank `13`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_247 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 20, 21, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 20, 21, 24, 26]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 21, 23, 24, 26]`, flank `13`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_248 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 21, 23, 24, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 21, 23, 24, 26]) (e := 13) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 21, 24, 25, 30]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_249 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 21, 24, 25, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 21, 24, 25, 30]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 22, 27, 28, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_250 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 22, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 22, 27, 28, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 24, 25, 28, 30]`, flank `13`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_251 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 24, 25, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 24, 25, 28, 30]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 24, 27, 28, 56]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_252 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 24, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 24, 27, 28, 56]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 29, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_253 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 29, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 29, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 34, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_254 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 34, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 34, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 39, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_255 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 39, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 39, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 41, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_256 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 41, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 46, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_257 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 46, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 51, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_258 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 51, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 51, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 27, 28, 53, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_259 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 27, 28, 53, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 27, 28, 53, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 28, 29, 32, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_260 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 28, 29, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 28, 29, 32, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 15, 28, 29, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_261 : ∃ k : ℕ, Lonely 8 (([1, 13, 15, 28, 29, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 15, 28, 29, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 21, 24, 25, 37, 48]`, flank `13`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_262 : ∃ k : ℕ, Lonely 8 (([1, 13, 21, 24, 25, 37, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 21, 24, 25, 37, 48]) (e := 13) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 22, 23, 24, 35, 44]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_263 : ∃ k : ℕ, Lonely 8 (([1, 13, 22, 23, 24, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 22, 23, 24, 35, 44]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 27, 28, 40, 41, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_264 : ∃ k : ℕ, Lonely 8 (([1, 13, 27, 28, 40, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 27, 28, 40, 41, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 13, 27, 28, 41, 55, 56]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_265 : ∃ k : ℕ, Lonely 8 (([1, 13, 27, 28, 41, 55, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 13, 27, 28, 41, 55, 56]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 18, 28]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_266 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 18, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 18, 28]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 18, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_267 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 18, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 18, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 19, 32]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_268 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 19, 32]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 21, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_269 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 21, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 23, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_270 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 23, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 26, 28]`, flank `14`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_271 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 26, 28]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 26, 34]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_272 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 26, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 26, 34]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 31, 34]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_273 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 31, 34]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 17, 31, 56]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_274 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 17, 31, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 17, 31, 56]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 16, 19, 29, 32]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_275 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 16, 19, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 16, 19, 29, 32]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 17, 19, 23, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_276 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 17, 19, 23, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 17, 19, 23, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 17, 21, 25, 34]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_277 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 17, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 17, 21, 25, 34]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 17, 23, 24, 30]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_278 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 17, 23, 24, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 17, 23, 24, 30]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 19, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_279 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 19, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 19, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 20, 22, 23, 28]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_280 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 20, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 20, 22, 23, 28]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 21, 24, 29, 42]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_281 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 21, 24, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 21, 24, 29, 42]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 21, 29, 31, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_282 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 21, 29, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 21, 29, 31, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 22, 23, 24, 28]`, flank `14`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_283 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 22, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 22, 23, 24, 28]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 24, 25, 26, 30]`, flank `14`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_284 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 24, 25, 26, 30]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 26, 27, 29, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_285 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 26, 27, 29, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 26, 27, 29, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 27, 29, 32, 58]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_286 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 27, 29, 32, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 27, 29, 32, 58]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 27, 29, 45, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_287 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 27, 29, 45, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 27, 29, 45, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 15, 29, 51, 53, 58]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_288 : ∃ k : ℕ, Lonely 8 (([1, 14, 15, 29, 51, 53, 58].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 15, 29, 51, 53, 58]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 17, 18, 20, 24]`, flank `14`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_289 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 17, 18, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 17, 18, 20, 24]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 17, 18, 20, 32]`, flank `14`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_290 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 17, 18, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 17, 18, 20, 32]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 17, 18, 20, 36]`, flank `14`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_291 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 17, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 17, 18, 20, 36]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 17, 18, 30, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_292 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 17, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 17, 18, 30, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 26, 29, 30, 60]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_293 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 26, 29, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 26, 29, 30, 60]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 16, 30, 31, 46, 60]`, flank `14`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_294 : ∃ k : ℕ, Lonely 8 (([1, 14, 16, 30, 31, 46, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 16, 30, 31, 46, 60]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 17, 18, 20, 26, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_295 : ∃ k : ℕ, Lonely 8 (([1, 14, 17, 18, 20, 26, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 17, 18, 20, 26, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 17, 18, 20, 32, 36]`, flank `14`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_296 : ∃ k : ℕ, Lonely 8 (([1, 14, 17, 18, 20, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 17, 18, 20, 32, 36]) (e := 14) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 17, 18, 30, 32, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_297 : ∃ k : ℕ, Lonely 8 (([1, 14, 17, 18, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 17, 18, 30, 32, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 19, 24, 25, 26, 30]`, flank `14`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_298 : ∃ k : ℕ, Lonely 8 (([1, 14, 19, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 19, 24, 25, 26, 30]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 23, 26, 27, 40, 52]`, flank `14`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_299 : ∃ k : ℕ, Lonely 8 (([1, 14, 23, 26, 27, 40, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 23, 26, 27, 40, 52]) (e := 14) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 24, 25, 26, 33, 48]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_300 : ∃ k : ℕ, Lonely 8 (([1, 14, 24, 25, 26, 33, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 24, 25, 26, 33, 48]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 24, 25, 26, 38, 48]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_301 : ∃ k : ℕ, Lonely 8 (([1, 14, 24, 25, 26, 38, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 24, 25, 26, 38, 48]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 24, 25, 26, 43, 48]`, flank `14`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_302 : ∃ k : ℕ, Lonely 8 (([1, 14, 24, 25, 26, 43, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 24, 25, 26, 43, 48]) (e := 14) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 26, 27, 28, 30, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_303 : ∃ k : ℕ, Lonely 8 (([1, 14, 26, 27, 28, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 26, 27, 28, 30, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 26, 27, 30, 40, 52]`, flank `14`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_304 : ∃ k : ℕ, Lonely 8 (([1, 14, 26, 27, 30, 40, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 26, 27, 30, 40, 52]) (e := 14) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 14, 29, 30, 38, 52, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_305 : ∃ k : ℕ, Lonely 8 (([1, 14, 29, 30, 38, 52, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 14, 29, 30, 38, 52, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 16, 17, 21, 33, 34]`, flank `15`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_306 : ∃ k : ℕ, Lonely 8 (([1, 15, 16, 17, 21, 33, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 16, 17, 21, 33, 34]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 16, 17, 28, 31, 56]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_307 : ∃ k : ℕ, Lonely 8 (([1, 15, 16, 17, 28, 31, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 16, 17, 28, 31, 56]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 16, 17, 31, 42, 56]`, flank `15`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_308 : ∃ k : ℕ, Lonely 8 (([1, 15, 16, 17, 31, 42, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 16, 17, 31, 42, 56]) (e := 15) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 17, 19, 20, 21, 24]`, flank `15`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_309 : ∃ k : ℕ, Lonely 8 (([1, 15, 17, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 17, 19, 20, 21, 24]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 17, 19, 23, 28, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_310 : ∃ k : ℕ, Lonely 8 (([1, 15, 17, 19, 23, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 17, 19, 23, 28, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 21, 22, 23, 24, 28]`, flank `15`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_311 : ∃ k : ℕ, Lonely 8 (([1, 15, 21, 22, 23, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 21, 22, 23, 24, 28]) (e := 15) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 21, 24, 25, 26, 30]`, flank `15`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_312 : ∃ k : ℕ, Lonely 8 (([1, 15, 21, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 21, 24, 25, 26, 30]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 21, 24, 28, 29, 42]`, flank `15`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_313 : ∃ k : ℕ, Lonely 8 (([1, 15, 21, 24, 28, 29, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 21, 24, 28, 29, 42]) (e := 15) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 21, 28, 29, 31, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_314 : ∃ k : ℕ, Lonely 8 (([1, 15, 21, 28, 29, 31, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 21, 28, 29, 31, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 15, 24, 25, 26, 28, 30]`, flank `15`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_315 : ∃ k : ℕ, Lonely 8 (([1, 15, 24, 25, 26, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 15, 24, 25, 26, 28, 30]) (e := 15) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 17, 18, 19, 35, 42]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_316 : ∃ k : ℕ, Lonely 8 (([1, 16, 17, 18, 19, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 17, 18, 19, 35, 42]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 17, 18, 20, 28, 32]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_317 : ∃ k : ℕ, Lonely 8 (([1, 16, 17, 18, 20, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 17, 18, 20, 28, 32]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 17, 19, 20, 21, 24]`, flank `16`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_318 : ∃ k : ℕ, Lonely 8 (([1, 16, 17, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 17, 19, 20, 21, 24]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 18, 19, 20, 28, 40]`, flank `16`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_319 : ∃ k : ℕ, Lonely 8 (([1, 16, 18, 19, 20, 28, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 18, 19, 20, 28, 40]) (e := 16) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 28, 29, 30, 32, 56]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_320 : ∃ k : ℕ, Lonely 8 (([1, 16, 28, 29, 30, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 28, 29, 30, 32, 56]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 16, 28, 29, 30, 44, 56]`, flank `16`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_321 : ∃ k : ℕ, Lonely 8 (([1, 16, 28, 29, 30, 44, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 16, 28, 29, 30, 44, 56]) (e := 16) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 18, 26, 28, 30, 36]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_322 : ∃ k : ℕ, Lonely 8 (([1, 17, 18, 26, 28, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 18, 26, 28, 30, 36]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 19, 20, 21, 23, 24]`, flank `17`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_323 : ∃ k : ℕ, Lonely 8 (([1, 17, 19, 20, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 19, 20, 21, 23, 24]) (e := 17) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 19, 20, 21, 23, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_324 : ∃ k : ℕ, Lonely 8 (([1, 17, 19, 20, 21, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 19, 20, 21, 23, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 19, 20, 21, 23, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_325 : ∃ k : ℕ, Lonely 8 (([1, 17, 19, 20, 21, 23, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 19, 20, 21, 23, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 21, 23, 25, 26, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_326 : ∃ k : ℕ, Lonely 8 (([1, 17, 21, 23, 25, 26, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 21, 23, 25, 26, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 17, 24, 25, 41, 49, 56]`, flank `17`, opening `13`.  Covers 1 census rows. -/
theorem fam_2_327 : ∃ k : ℕ, Lonely 8 (([1, 17, 24, 25, 41, 49, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨13, Flanks.lonely_of_band_list (n := 8) (L := [1, 17, 24, 25, 41, 49, 56]) (e := 17) (k := 13)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 20, 21, 23, 40]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_328 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 20, 21, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 20, 21, 23, 40]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 20, 21, 39, 40]`, flank `18`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_329 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 20, 21, 39, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 20, 21, 39, 40]) (e := 18) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 20, 21, 39, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_330 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 20, 21, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 20, 21, 39, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 20, 24, 28, 40]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_331 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 20, 24, 28, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 20, 24, 28, 40]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 20, 28, 32, 40]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_332 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 20, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 20, 28, 32, 40]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 19, 37, 55, 56, 57]`, flank `18`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_333 : ∃ k : ℕ, Lonely 8 (([1, 18, 19, 37, 55, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 19, 37, 55, 56, 57]) (e := 18) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 18, 37, 38, 55, 56, 57]`, flank `18`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_334 : ∃ k : ℕ, Lonely 8 (([1, 18, 37, 38, 55, 56, 57].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 18, 37, 38, 55, 56, 57]) (e := 18) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 22, 23, 40]`, flank `19`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_335 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 22, 23, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 22, 23, 40]) (e := 19) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 22, 23, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_336 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 22, 23, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 22, 23, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 22, 23, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_337 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 22, 23, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 22, 23, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 23, 26, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_338 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 23, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 23, 26, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 23, 27, 38]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_339 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 23, 27, 38]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 23, 39, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_340 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 23, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 23, 39, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 27, 30, 60]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_341 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 27, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 27, 30, 60]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 32, 36, 42]`, flank `19`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_342 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 32, 36, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 32, 36, 42]) (e := 19) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 36, 37, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_343 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 36, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 36, 37, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 20, 21, 39, 41, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_344 : ∃ k : ℕ, Lonely 8 (([1, 19, 20, 21, 39, 41, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 20, 21, 39, 41, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 21, 22, 23, 40, 46]`, flank `19`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_345 : ∃ k : ℕ, Lonely 8 (([1, 19, 21, 22, 23, 40, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 21, 22, 23, 40, 46]) (e := 19) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 21, 23, 26, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_346 : ∃ k : ℕ, Lonely 8 (([1, 19, 21, 23, 26, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 21, 23, 26, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 21, 23, 34, 35, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_347 : ∃ k : ℕ, Lonely 8 (([1, 19, 21, 23, 34, 35, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 21, 23, 34, 35, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 21, 24, 25, 26, 30]`, flank `19`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_348 : ∃ k : ℕ, Lonely 8 (([1, 19, 21, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 21, 24, 25, 26, 30]) (e := 19) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 21, 27, 30, 40, 60]`, flank `19`, opening `11`.  Covers 1 census rows. -/
theorem fam_2_349 : ∃ k : ℕ, Lonely 8 (([1, 19, 21, 27, 30, 40, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((19 : ℕ) : ℝ) k) :=
  ⟨11, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 21, 27, 30, 40, 60]) (e := 19) (k := 11)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 19, 23, 25, 27, 28, 54]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_350 : ∃ k : ℕ, Lonely 8 (([1, 19, 23, 25, 27, 28, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 19, 23, 25, 27, 28, 54]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 21, 22, 23, 24, 46]`, flank `20`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_351 : ∃ k : ℕ, Lonely 8 (([1, 20, 21, 22, 23, 24, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 21, 22, 23, 24, 46]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 21, 22, 23, 43, 46]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_352 : ∃ k : ℕ, Lonely 8 (([1, 20, 21, 22, 23, 43, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 21, 22, 23, 43, 46]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 21, 22, 31, 35, 40]`, flank `20`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_353 : ∃ k : ℕ, Lonely 8 (([1, 20, 21, 22, 31, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 21, 22, 31, 35, 40]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 22, 23, 24, 42, 48]`, flank `20`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_354 : ∃ k : ℕ, Lonely 8 (([1, 20, 22, 23, 24, 42, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 22, 23, 24, 42, 48]) (e := 20) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 24, 26, 27, 28, 56]`, flank `20`, opening `10`.  Covers 1 census rows. -/
theorem fam_2_355 : ∃ k : ℕ, Lonely 8 (([1, 20, 24, 26, 27, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨10, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 24, 26, 27, 28, 56]) (e := 20) (k := 10)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 20, 28, 29, 30, 32, 56]`, flank `20`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_356 : ∃ k : ℕ, Lonely 8 (([1, 20, 28, 29, 30, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((20 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 20, 28, 29, 30, 32, 56]) (e := 20) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 22, 23, 24, 45, 48]`, flank `21`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_357 : ∃ k : ℕ, Lonely 8 (([1, 21, 22, 23, 24, 45, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 22, 23, 24, 45, 48]) (e := 21) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 22, 24, 26, 30, 44]`, flank `21`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_358 : ∃ k : ℕ, Lonely 8 (([1, 21, 22, 24, 26, 30, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 22, 24, 26, 30, 44]) (e := 21) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 23, 24, 25, 26, 30]`, flank `21`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_359 : ∃ k : ℕ, Lonely 8 (([1, 21, 23, 24, 25, 26, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 23, 24, 25, 26, 30]) (e := 21) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 23, 24, 25, 26, 48]`, flank `21`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_360 : ∃ k : ℕ, Lonely 8 (([1, 21, 23, 24, 25, 26, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 23, 24, 25, 26, 48]) (e := 21) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 23, 25, 26, 27, 30]`, flank `1`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_361 : ∃ k : ℕ, Lonely 8 (([1, 21, 23, 25, 26, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 23, 25, 26, 27, 30]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 24, 25, 26, 27, 30]`, flank `21`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_362 : ∃ k : ℕ, Lonely 8 (([1, 21, 24, 25, 26, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 24, 25, 26, 27, 30]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 24, 39, 40, 41, 48]`, flank `21`, opening `10`.  Covers 1 census rows. -/
theorem fam_2_363 : ∃ k : ℕ, Lonely 8 (([1, 21, 24, 39, 40, 41, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨10, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 24, 39, 40, 41, 48]) (e := 21) (k := 10)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 30, 31, 32, 33, 42]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_364 : ∃ k : ℕ, Lonely 8 (([1, 21, 30, 31, 32, 33, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 30, 31, 32, 33, 42]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 33, 35, 37, 38, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_365 : ∃ k : ℕ, Lonely 8 (([1, 21, 33, 35, 37, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 33, 35, 37, 38, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 35, 36, 37, 38, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_366 : ∃ k : ℕ, Lonely 8 (([1, 21, 35, 36, 37, 38, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 35, 36, 37, 38, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 35, 37, 38, 39, 42]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_367 : ∃ k : ℕ, Lonely 8 (([1, 21, 35, 37, 38, 39, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 35, 37, 38, 39, 42]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 21, 37, 39, 40, 41, 44]`, flank `21`, opening `10`.  Covers 1 census rows. -/
theorem fam_2_368 : ∃ k : ℕ, Lonely 8 (([1, 21, 37, 39, 40, 41, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨10, Flanks.lonely_of_band_list (n := 8) (L := [1, 21, 37, 39, 40, 41, 44]) (e := 21) (k := 10)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 22, 23, 24, 40, 42, 48]`, flank `22`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_369 : ∃ k : ℕ, Lonely 8 (([1, 22, 23, 24, 40, 42, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [1, 22, 23, 24, 40, 42, 48]) (e := 22) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 22, 24, 25, 26, 28, 52]`, flank `22`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_370 : ∃ k : ℕ, Lonely 8 (([1, 22, 24, 25, 26, 28, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((22 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 22, 24, 25, 26, 28, 52]) (e := 22) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 24, 26, 27, 28, 30, 52]`, flank `24`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_371 : ∃ k : ℕ, Lonely 8 (([1, 24, 26, 27, 28, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 24, 26, 27, 28, 30, 52]) (e := 24) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 24, 26, 27, 28, 30, 56]`, flank `24`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_372 : ∃ k : ℕ, Lonely 8 (([1, 24, 26, 27, 28, 30, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 24, 26, 27, 28, 30, 56]) (e := 24) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 24, 26, 27, 28, 40, 56]`, flank `24`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_373 : ∃ k : ℕ, Lonely 8 (([1, 24, 26, 27, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 24, 26, 27, 28, 40, 56]) (e := 24) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 24, 26, 27, 28, 50, 56]`, flank `24`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_374 : ∃ k : ℕ, Lonely 8 (([1, 24, 26, 27, 28, 50, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((24 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [1, 24, 26, 27, 28, 50, 56]) (e := 24) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 25, 27, 28, 29, 33, 50]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_375 : ∃ k : ℕ, Lonely 8 (([1, 25, 27, 28, 29, 33, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 25, 27, 28, 29, 33, 50]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 26, 27, 28, 30, 34, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_376 : ∃ k : ℕ, Lonely 8 (([1, 26, 27, 28, 30, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 26, 27, 28, 30, 34, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 26, 27, 28, 30, 38, 52]`, flank `1`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_377 : ∃ k : ℕ, Lonely 8 (([1, 26, 27, 28, 30, 38, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((1 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [1, 26, 27, 28, 30, 38, 52]) (e := 1) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 26, 27, 28, 30, 48, 52]`, flank `26`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_378 : ∃ k : ℕ, Lonely 8 (([1, 26, 27, 28, 30, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 26, 27, 28, 30, 48, 52]) (e := 26) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 26, 27, 28, 53, 55, 56]`, flank `26`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_379 : ∃ k : ℕ, Lonely 8 (([1, 26, 27, 28, 53, 55, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [1, 26, 27, 28, 53, 55, 56]) (e := 26) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 26, 28, 29, 30, 32, 56]`, flank `26`, opening `9`.  Covers 1 census rows. -/
theorem fam_2_380 : ∃ k : ℕ, Lonely 8 (([1, 26, 28, 29, 30, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [1, 26, 28, 29, 30, 32, 56]) (e := 26) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 27, 28, 29, 31, 40, 54]`, flank `27`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_381 : ∃ k : ℕ, Lonely 8 (([1, 27, 28, 29, 31, 40, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((27 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 27, 28, 29, 31, 40, 54]) (e := 27) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 27, 28, 30, 32, 46, 56]`, flank `27`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_382 : ∃ k : ℕ, Lonely 8 (([1, 27, 28, 30, 32, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((27 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [1, 27, 28, 30, 32, 46, 56]) (e := 27) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 28, 29, 30, 32, 36, 56]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_383 : ∃ k : ℕ, Lonely 8 (([1, 28, 29, 30, 32, 36, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 28, 29, 30, 32, 36, 56]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 28, 29, 30, 32, 46, 56]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_384 : ∃ k : ℕ, Lonely 8 (([1, 28, 29, 30, 32, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 28, 29, 30, 32, 46, 56]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 28, 29, 30, 32, 52, 56]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_385 : ∃ k : ℕ, Lonely 8 (([1, 28, 29, 30, 32, 52, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 28, 29, 30, 32, 52, 56]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 28, 29, 30, 39, 51, 56]`, flank `28`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_386 : ∃ k : ℕ, Lonely 8 (([1, 28, 29, 30, 39, 51, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((28 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 28, 29, 30, 39, 51, 56]) (e := 28) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 30, 33, 48, 49, 50, 60]`, flank `30`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_387 : ∃ k : ℕ, Lonely 8 (([1, 30, 33, 48, 49, 50, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((30 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [1, 30, 33, 48, 49, 50, 60]) (e := 30) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[1, 30, 37, 48, 49, 53, 60]`, flank `30`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_388 : ∃ k : ℕ, Lonely 8 (([1, 30, 37, 48, 49, 53, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((30 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [1, 30, 37, 48, 49, 53, 60]) (e := 30) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 5, 7, 11, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_389 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 5, 7, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 5, 7, 11, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 5, 8, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_390 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 5, 8, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 5, 8, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 7, 10, 11, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_391 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 7, 10, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 7, 10, 11, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 7, 11, 15, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_392 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 7, 11, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 7, 11, 15, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 8, 10, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_393 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 8, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 8, 10, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 10, 11, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_394 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 10, 11, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 10, 11, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 10, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_395 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 10, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 10, 14, 17, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_396 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 10, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 10, 14, 17, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 10, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_397 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 10, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 4, 12, 15, 21, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_398 : ∃ k : ℕ, Lonely 8 (([2, 3, 4, 12, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 4, 12, 15, 21, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 12, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_399 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 12, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 12, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 13, 15]`, flank `5`, opening `4`.  Covers 4 census rows. -/
theorem fam_2_400 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 13, 15]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 13, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_401 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 13, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 13, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_402 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 13, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 14, 15]`, flank `5`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_403 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 14, 15]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 8, 15, 16]`, flank `5`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_404 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 8, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 8, 15, 16]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 9, 11, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_405 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 9, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 9, 11, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 9, 12, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_406 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 9, 12, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 9, 12, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 9, 12, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_407 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 9, 12, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 9, 12, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 9, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_408 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 9, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 9, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 10, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_409 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 10, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 10, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 10, 17, 18]`, flank `3`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_410 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 10, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 10, 17, 18]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_411 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 11, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_412 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 11, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 11, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 11, 17, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_413 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 11, 17, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 11, 17, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 11, 21, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_414 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 11, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 11, 21, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 12, 17, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_415 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 12, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 12, 17, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 12, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_416 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 12, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 12, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 12, 27, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_417 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 12, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 12, 27, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 13, 19, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_418 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 13, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 13, 19, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 16, 21, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_419 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 16, 21, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 17, 23, 34]`, flank `3`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_420 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 17, 23, 34]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 18, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_421 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 18, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 7, 24, 27, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_422 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 7, 24, 27, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 7, 24, 27, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 8, 11, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_423 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 8, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 8, 11, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 8, 12, 14, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_424 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 8, 12, 14, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 8, 12, 14, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 8, 12, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_425 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 8, 12, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 8, 12, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 9, 12, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_426 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 9, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 9, 12, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 10, 12, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_427 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 10, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 10, 12, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 11, 15, 21, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_428 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 11, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 11, 15, 21, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 12, 14, 16, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_429 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 12, 14, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 12, 14, 16, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 12, 14, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_430 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 12, 14, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 12, 14, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 12, 16, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_431 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 12, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 12, 16, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_432 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 5, 14, 18, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_433 : ∃ k : ℕ, Lonely 8 (([2, 3, 5, 14, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 5, 14, 18, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 6, 7, 8, 15, 16]`, flank `7`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_434 : ∃ k : ℕ, Lonely 8 (([2, 3, 6, 7, 8, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 6, 7, 8, 15, 16]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 6, 8, 14, 15, 16]`, flank `8`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_435 : ∃ k : ℕ, Lonely 8 (([2, 3, 6, 8, 14, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 6, 8, 14, 15, 16]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 10, 12, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_436 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 10, 12, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 10, 12, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 10, 13, 15]`, flank `10`, opening `2`.  Covers 4 census rows. -/
theorem fam_2_437 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 10, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 10, 13, 15]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 10, 14, 15]`, flank `7`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_438 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 10, 14, 15]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 10, 18, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_439 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 10, 18, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 10, 18, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 11, 15, 16]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_440 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 11, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 11, 15, 16]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 12, 15, 25]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_441 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 12, 15, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 12, 15, 25]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 8, 12, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_442 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 8, 12, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 8, 12, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 9, 10, 11, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_443 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 9, 10, 11, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 9, 10, 11, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 9, 10, 16, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_444 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 9, 10, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 9, 10, 16, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 9, 11, 15, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_445 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 9, 11, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 9, 11, 15, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_446 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 12, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_447 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 12, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 12, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 13, 16, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_448 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 13, 16, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 14, 16, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_449 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 14, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 14, 16, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 16, 18, 19]`, flank `10`, opening `9`.  Covers 3 census rows. -/
theorem fam_2_450 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 16, 18, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 16, 18, 19]) (e := 10) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_451 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 10, 18, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_452 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 10, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 10, 18, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 11, 13, 15, 22]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_453 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 11, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 11, 13, 15, 22]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 11, 18, 20, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_454 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 11, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 11, 18, 20, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 7, 13, 17, 20, 40]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_455 : ∃ k : ℕ, Lonely 8 (([2, 3, 7, 13, 17, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 7, 13, 17, 20, 40]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 11, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_456 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 11, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 11, 14, 16]`, flank `8`, opening `6`.  Covers 3 census rows. -/
theorem fam_2_457 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 11, 14, 16]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 11, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_458 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 11, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 11, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_459 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 14, 17, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_460 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 14, 17, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 10, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_461 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 10, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 11, 14, 15, 16]`, flank `8`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_462 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 11, 14, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 11, 14, 15, 16]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 11, 14, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_463 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 11, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 11, 14, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 11, 14, 20, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_464 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 11, 14, 20, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 11, 14, 20, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 11, 14, 25, 33]`, flank `8`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_465 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 11, 14, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 11, 14, 25, 33]) (e := 8) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 12, 14, 15, 24]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_466 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 12, 14, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 12, 14, 15, 24]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_467 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 14, 20, 22, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_468 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 14, 20, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 14, 20, 22, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 14, 22, 25, 33]`, flank `8`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_469 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 14, 22, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 14, 22, 25, 33]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 8, 14, 22, 25, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_470 : ∃ k : ℕ, Lonely 8 (([2, 3, 8, 14, 22, 25, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 8, 14, 22, 25, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 11, 12, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_471 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 11, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 11, 12, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 11, 14, 16, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_472 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 11, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 11, 14, 16, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 11, 14, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_473 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 11, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 11, 14, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 11, 14, 24, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_474 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 11, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 11, 14, 24, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 12, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_475 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 12, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 12, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 12, 14, 17, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_476 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 12, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 12, 14, 17, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 12, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_477 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 12, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 12, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 12, 14, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_478 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 12, 14, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 12, 14, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 13, 14, 16, 20]`, flank `10`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_479 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 13, 14, 16, 20]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 13, 14, 16, 21]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_480 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 13, 14, 16, 21]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 13, 14, 16, 32]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_481 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 13, 14, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 13, 14, 16, 32]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 14, 16, 17, 28]`, flank `10`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_482 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 14, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 14, 16, 17, 28]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 14, 16, 19, 20]`, flank `10`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_483 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 14, 16, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 14, 16, 19, 20]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 14, 16, 19, 32]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_484 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 14, 16, 19, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 14, 16, 19, 32]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 14, 16, 23, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_485 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 14, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 14, 16, 23, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 10, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_486 : ∃ k : ℕ, Lonely 8 (([2, 3, 10, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 10, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 11, 14, 15, 17, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_487 : ∃ k : ℕ, Lonely 8 (([2, 3, 11, 14, 15, 17, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 11, 14, 15, 17, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 11, 14, 18, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_488 : ∃ k : ℕ, Lonely 8 (([2, 3, 11, 14, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 11, 14, 18, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 11, 14, 20, 26, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_489 : ∃ k : ℕ, Lonely 8 (([2, 3, 11, 14, 20, 26, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 11, 14, 20, 26, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 12, 14, 15, 16, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_490 : ∃ k : ℕ, Lonely 8 (([2, 3, 12, 14, 15, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 12, 14, 15, 16, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 12, 14, 15, 21, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_491 : ∃ k : ℕ, Lonely 8 (([2, 3, 12, 14, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 12, 14, 15, 21, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 13, 15, 21, 24, 31]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_492 : ∃ k : ℕ, Lonely 8 (([2, 3, 13, 15, 21, 24, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 13, 15, 21, 24, 31]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 14, 17, 18, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_493 : ∃ k : ℕ, Lonely 8 (([2, 3, 14, 17, 18, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 14, 17, 18, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 14, 17, 20, 23, 28]`, flank `3`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_494 : ∃ k : ℕ, Lonely 8 (([2, 3, 14, 17, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 14, 17, 20, 23, 28]) (e := 3) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 14, 20, 23, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_495 : ∃ k : ℕ, Lonely 8 (([2, 3, 14, 20, 23, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 14, 20, 23, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 26, 28, 29, 32, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_496 : ∃ k : ℕ, Lonely 8 (([2, 3, 26, 28, 29, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 26, 28, 29, 32, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 3, 26, 28, 32, 35, 40]`, flank `3`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_497 : ∃ k : ℕ, Lonely 8 (([2, 3, 26, 28, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((3 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 3, 26, 28, 32, 35, 40]) (e := 3) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 6, 8, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_498 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 6, 8, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 6, 8, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 6, 9, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_499 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 6, 9, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 6, 9, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 6, 14, 19, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_500 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 6, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 6, 14, 19, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 6, 16, 21, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_501 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 6, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 6, 16, 21, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 8, 9, 14, 15]`, flank `5`, opening `4`.  Covers 4 census rows. -/
theorem fam_2_502 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 8, 9, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 8, 9, 14, 15]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 8, 12, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_503 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 8, 12, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 8, 12, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 9, 13, 14, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_504 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 9, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 9, 13, 14, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 14, 18, 23, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_505 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 14, 18, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 14, 18, 23, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 5, 14, 19, 24, 48]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_506 : ∃ k : ℕ, Lonely 8 (([2, 4, 5, 14, 19, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 5, 14, 19, 24, 48]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 7, 8, 10, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_507 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 7, 8, 10, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 7, 8, 10, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 7, 8, 15, 17]`, flank `4`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_508 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 7, 8, 15, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 7, 8, 15, 17]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 7, 10, 11, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_509 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 7, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 7, 10, 11, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 7, 10, 17, 20]`, flank `4`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_510 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 7, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 7, 10, 17, 20]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 8, 10, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_511 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 8, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 8, 10, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 8, 10, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_512 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 8, 10, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 8, 10, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 6, 8, 10, 14, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_513 : ∃ k : ℕ, Lonely 8 (([2, 4, 6, 8, 10, 14, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 6, 8, 10, 14, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 8, 11, 15, 21]`, flank `4`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_514 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 8, 11, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((4 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 8, 11, 15, 21]) (e := 4) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 9, 10, 11, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_515 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 9, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 9, 10, 11, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 9, 10, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_516 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 9, 10, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 9, 10, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_517 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 9, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 9, 10, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 10, 11, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_518 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 10, 11, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 10, 11, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 7, 10, 16, 18, 21]`, flank `10`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_519 : ∃ k : ℕ, Lonely 8 (([2, 4, 7, 10, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 7, 10, 16, 18, 21]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 8, 9, 10, 14, 15]`, flank `9`, opening `3`.  Covers 4 census rows. -/
theorem fam_2_520 : ∃ k : ℕ, Lonely 8 (([2, 4, 8, 9, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 8, 9, 10, 14, 15]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 8, 10, 12, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_521 : ∃ k : ℕ, Lonely 8 (([2, 4, 8, 10, 12, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 8, 10, 12, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 8, 11, 14, 15, 21]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_522 : ∃ k : ℕ, Lonely 8 (([2, 4, 8, 11, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 8, 11, 14, 15, 21]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 9, 10, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_523 : ∃ k : ℕ, Lonely 8 (([2, 4, 9, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 9, 10, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 9, 10, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_524 : ∃ k : ℕ, Lonely 8 (([2, 4, 9, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 9, 10, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 10, 12, 14, 16, 39]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_525 : ∃ k : ℕ, Lonely 8 (([2, 4, 10, 12, 14, 16, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 10, 12, 14, 16, 39]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 4, 10, 14, 16, 18, 21]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_526 : ∃ k : ℕ, Lonely 8 (([2, 4, 10, 14, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 4, 10, 14, 16, 18, 21]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 8, 10, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_527 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 8, 10, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 8, 10, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 8, 13, 15]`, flank `6`, opening `2`.  Covers 4 census rows. -/
theorem fam_2_528 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 8, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 8, 13, 15]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 8, 13, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_529 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 8, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 8, 13, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 8, 13, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_530 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 8, 13, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 8, 13, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 8, 14, 15]`, flank `5`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_531 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 8, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 8, 14, 15]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 9, 15, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_532 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 9, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 9, 15, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 9, 16, 18]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_533 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 9, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 9, 16, 18]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 10, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_534 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 10, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 10, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 10, 17, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_535 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 10, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 10, 17, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_536 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 11, 16, 23]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_537 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 11, 16, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 11, 16, 23]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 11, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_538 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 11, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 11, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 13, 19, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_539 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 13, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 13, 19, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 16, 21, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_540 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 16, 21, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 7, 17, 23, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_541 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 7, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 7, 17, 23, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 9, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_542 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 9, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 9, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 11, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_543 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 11, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 11, 14, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_544 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 11, 14, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 11, 14, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 13, 14, 16]`, flank `8`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_545 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 13, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 13, 14, 16]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 13, 14, 17]`, flank `2`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_546 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 13, 14, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 13, 14, 17]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 14, 19, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_547 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 14, 19, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 21, 26, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_548 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 21, 26, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 8, 21, 29, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_549 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 8, 21, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 8, 21, 29, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 9, 12, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_550 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 9, 12, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 9, 12, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 9, 14, 15, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_551 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 9, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 9, 14, 15, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 9, 14, 16, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_552 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 9, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 9, 14, 16, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 9, 14, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_553 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 9, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 9, 14, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 9, 14, 24, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_554 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 9, 14, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 9, 14, 24, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 11, 14, 16, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_555 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 11, 14, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 11, 14, 16, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 11, 16, 21, 22]`, flank `11`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_556 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 11, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 11, 16, 21, 22]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 11, 16, 21, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_557 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 11, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 11, 16, 21, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 11, 16, 28, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_558 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 11, 16, 28, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 11, 16, 28, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 16, 19, 28]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_559 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 16, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 16, 19, 28]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 16, 21, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_560 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 16, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 16, 21, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_561 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 19, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_562 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 19, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 19, 24, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_563 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 19, 24, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 19, 24, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 14, 20, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_564 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 14, 20, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 16, 18, 21, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_565 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 16, 18, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 16, 18, 21, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 16, 21, 22, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_566 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 16, 21, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 16, 21, 22, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 16, 21, 25, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_567 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 16, 21, 25, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 16, 21, 25, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 16, 21, 29, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_568 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 16, 21, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 16, 21, 29, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 6, 21, 24, 29, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_569 : ∃ k : ℕ, Lonely 8 (([2, 5, 6, 21, 24, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 6, 21, 24, 29, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 10, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_570 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 10, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 10, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 11, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_571 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 11, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 11, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 12, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_572 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 12, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 12, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 13, 15]`, flank `5`, opening `4`.  Covers 4 census rows. -/
theorem fam_2_573 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 13, 15]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 13, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_574 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 13, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 13, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_575 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 13, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 13, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 14, 15]`, flank `5`, opening `4`.  Covers 4 census rows. -/
theorem fam_2_576 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 14, 15]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 9, 14, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_577 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 9, 14, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 9, 14, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 13, 18, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_578 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 13, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 13, 18, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 8, 14, 18, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_579 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 8, 14, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 8, 14, 18, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 10, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_580 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 10, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 10, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 12, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_581 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 12, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 12, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_582 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 15, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_583 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 15, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_584 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_585 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 16, 21]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_586 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 16, 21]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_587 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 11, 19, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_588 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 11, 19, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 12, 15, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_589 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 12, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 12, 15, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 12, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_590 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 12, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 12, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 12, 16, 21]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_591 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 12, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 12, 16, 21]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 12, 19, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_592 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 12, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 12, 19, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 12, 19, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_593 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 12, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 12, 19, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 13, 19, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_594 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 13, 19, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 13, 19, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 13, 23, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_595 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 13, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 13, 23, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_596 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 17, 23, 34]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_597 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 17, 23, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 17, 23, 34]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 9, 19, 25, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_598 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 9, 19, 25, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 9, 19, 25, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 10, 12, 17, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_599 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 10, 12, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 10, 12, 17, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 10, 15, 17, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_600 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 10, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 10, 15, 17, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 12, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_601 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 12, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 12, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 12, 16, 23]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_602 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 12, 16, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 12, 16, 23]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 12, 17, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_603 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 12, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 12, 17, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 12, 26, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_604 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 12, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 12, 26, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 16, 18, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_605 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 16, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 16, 18, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 16, 21, 33]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_606 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 16, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 16, 21, 33]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 11, 18, 32, 36]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_607 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 11, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 11, 18, 32, 36]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 12, 16, 20, 32]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_608 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 12, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 12, 16, 20, 32]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 12, 17, 19, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_609 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 12, 17, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 12, 17, 19, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 12, 17, 19, 34]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_610 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 12, 17, 19, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 12, 17, 19, 34]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 12, 17, 31, 34]`, flank `5`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_611 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 12, 17, 31, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 12, 17, 31, 34]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 12, 19, 26, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_612 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 12, 19, 26, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 12, 19, 26, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 13, 15, 17, 26]`, flank `5`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_613 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 13, 15, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 13, 15, 17, 26]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 7, 16, 21, 22, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_614 : ∃ k : ℕ, Lonely 8 (([2, 5, 7, 16, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 7, 16, 21, 22, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 10, 14, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_615 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 10, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 10, 14, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 10, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_616 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 10, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 10, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 11, 14, 15]`, flank `9`, opening `3`.  Covers 4 census rows. -/
theorem fam_2_617 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 11, 14, 15]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 11, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_618 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 11, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 11, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 12, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_619 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 12, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 12, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 13, 14, 16]`, flank `5`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_620 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 13, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 13, 14, 16]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 13, 14, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_621 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 13, 14, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 13, 14, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 13, 14, 39]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_622 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 13, 14, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 13, 14, 39]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 14, 20, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_623 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 14, 20, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 14, 20, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 9, 14, 26, 39]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_624 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 9, 14, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 9, 14, 26, 39]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 10, 12, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_625 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 10, 12, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 10, 12, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 10, 13, 21, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_626 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 10, 13, 21, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 10, 13, 21, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 11, 12, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_627 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 11, 12, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 11, 12, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 12, 14, 17, 24]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_628 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 12, 14, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 12, 14, 17, 24]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 12, 17, 21, 24]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_629 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 12, 17, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 12, 17, 21, 24]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 12, 20, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_630 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 12, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 12, 20, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 12, 21, 26, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_631 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 12, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 12, 21, 26, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 13, 14, 15, 26]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_632 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 13, 14, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 13, 14, 15, 26]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 13, 14, 18, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_633 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 13, 14, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 13, 14, 18, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 14, 18, 20, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_634 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 14, 18, 20, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 14, 18, 20, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 8, 14, 18, 23, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_635 : ∃ k : ℕ, Lonely 8 (([2, 5, 8, 14, 18, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 8, 14, 18, 23, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 10, 14, 16, 21]`, flank `5`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_636 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 10, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 10, 14, 16, 21]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 11, 13, 14, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_637 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 11, 13, 14, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 11, 13, 14, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 11, 14, 16, 21]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_638 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 11, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 11, 14, 16, 21]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 11, 14, 16, 22]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_639 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 11, 14, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 11, 14, 16, 22]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 11, 14, 16, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_640 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 11, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 11, 14, 16, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 11, 16, 21, 22]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_641 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 11, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 11, 16, 21, 22]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 13, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_642 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 13, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 14, 15, 18]`, flank `5`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_643 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 14, 15, 18]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 14, 16, 21]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_644 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 14, 16, 21]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 14, 16, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_645 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 14, 16, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 14, 22, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_646 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 14, 22, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 14, 22, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 12, 14, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_647 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 12, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 12, 14, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 13, 14, 15, 26]`, flank `5`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_648 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 13, 14, 15, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 13, 14, 15, 26]) (e := 5) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 14, 16, 17, 28]`, flank `9`, opening `8`.  Covers 2 census rows. -/
theorem fam_2_649 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 14, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 14, 16, 17, 28]) (e := 9) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 14, 16, 23, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_650 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 14, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 14, 16, 23, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 9, 14, 23, 32, 39]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_651 : ∃ k : ℕ, Lonely 8 (([2, 5, 9, 14, 23, 32, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 9, 14, 23, 32, 39]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 10, 12, 13, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_652 : ∃ k : ℕ, Lonely 8 (([2, 5, 10, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 10, 12, 13, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 10, 12, 14, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_653 : ∃ k : ℕ, Lonely 8 (([2, 5, 10, 12, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 10, 12, 14, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 10, 12, 16, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_654 : ∃ k : ℕ, Lonely 8 (([2, 5, 10, 12, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 10, 12, 16, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 11, 12, 16, 21, 22]`, flank `11`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_655 : ∃ k : ℕ, Lonely 8 (([2, 5, 11, 12, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 11, 12, 16, 21, 22]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 11, 13, 16, 21, 33]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_656 : ∃ k : ℕ, Lonely 8 (([2, 5, 11, 13, 16, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 11, 13, 16, 21, 33]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 11, 16, 20, 21, 33]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_657 : ∃ k : ℕ, Lonely 8 (([2, 5, 11, 16, 20, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 11, 16, 20, 21, 33]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 11, 18, 23, 28, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_658 : ∃ k : ℕ, Lonely 8 (([2, 5, 11, 18, 23, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 11, 18, 23, 28, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 13, 14, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_659 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 13, 14, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 13, 14, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 14, 16, 17, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_660 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 14, 16, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 14, 16, 17, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 14, 18, 23, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_661 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 14, 18, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 14, 18, 23, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 16, 17, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_662 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 16, 17, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 16, 17, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 16, 20, 21, 24]`, flank `5`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_663 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 16, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 16, 20, 21, 24]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 21, 22, 26, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_664 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 21, 22, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 21, 22, 26, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 12, 21, 26, 30, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_665 : ∃ k : ℕ, Lonely 8 (([2, 5, 12, 21, 26, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 12, 21, 26, 30, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 13, 14, 15, 17, 26]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_666 : ∃ k : ℕ, Lonely 8 (([2, 5, 13, 14, 15, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 13, 14, 15, 17, 26]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 13, 14, 18, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_667 : ∃ k : ℕ, Lonely 8 (([2, 5, 13, 14, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 13, 14, 18, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 13, 16, 21, 22, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_668 : ∃ k : ℕ, Lonely 8 (([2, 5, 13, 16, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 13, 16, 21, 22, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 13, 17, 19, 21, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_669 : ∃ k : ℕ, Lonely 8 (([2, 5, 13, 17, 19, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 13, 17, 19, 21, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 13, 18, 22, 28, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_670 : ∃ k : ℕ, Lonely 8 (([2, 5, 13, 18, 22, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 13, 18, 22, 28, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 16, 18, 23, 36]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_671 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 16, 18, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 16, 18, 23, 36]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 18, 20, 23, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_672 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 18, 20, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 18, 20, 23, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 18, 23, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_673 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 18, 23, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 18, 23, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 18, 23, 28, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_674 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 18, 23, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 18, 23, 28, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 19, 21, 23, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_675 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 19, 21, 23, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 19, 21, 23, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 19, 22, 24, 48]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_676 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 19, 22, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 19, 22, 24, 48]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 19, 24, 26, 48]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_677 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 19, 24, 26, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 19, 24, 26, 48]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 22, 24, 29, 48]`, flank `14`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_678 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 22, 24, 29, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 22, 24, 29, 48]) (e := 14) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 14, 30, 33, 35, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_679 : ∃ k : ℕ, Lonely 8 (([2, 5, 14, 30, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 14, 30, 33, 35, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 16, 18, 20, 21, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_680 : ∃ k : ℕ, Lonely 8 (([2, 5, 16, 18, 20, 21, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 16, 18, 20, 21, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 16, 18, 21, 26, 32]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_681 : ∃ k : ℕ, Lonely 8 (([2, 5, 16, 18, 21, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 16, 18, 21, 26, 32]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 16, 20, 21, 22, 33]`, flank `5`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_682 : ∃ k : ℕ, Lonely 8 (([2, 5, 16, 20, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 16, 20, 21, 22, 33]) (e := 5) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 18, 23, 25, 28, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_683 : ∃ k : ℕ, Lonely 8 (([2, 5, 18, 23, 25, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 18, 23, 25, 28, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 19, 21, 23, 27, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_684 : ∃ k : ℕ, Lonely 8 (([2, 5, 19, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 19, 21, 23, 27, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 21, 26, 28, 30, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_685 : ∃ k : ℕ, Lonely 8 (([2, 5, 21, 26, 28, 30, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 21, 26, 28, 30, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 21, 26, 30, 40, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_686 : ∃ k : ℕ, Lonely 8 (([2, 5, 21, 26, 30, 40, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 21, 26, 30, 40, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 23, 24, 26, 28, 56]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_687 : ∃ k : ℕ, Lonely 8 (([2, 5, 23, 24, 26, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 23, 24, 26, 28, 56]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 23, 28, 30, 32, 56]`, flank `5`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_688 : ∃ k : ℕ, Lonely 8 (([2, 5, 23, 28, 30, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((5 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 23, 28, 30, 32, 56]) (e := 5) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 24, 26, 28, 33, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_689 : ∃ k : ℕ, Lonely 8 (([2, 5, 24, 26, 28, 33, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 24, 26, 28, 33, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 24, 26, 28, 43, 56]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_690 : ∃ k : ℕ, Lonely 8 (([2, 5, 24, 26, 28, 43, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 24, 26, 28, 43, 56]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 26, 28, 30, 31, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_691 : ∃ k : ℕ, Lonely 8 (([2, 5, 26, 28, 30, 31, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 26, 28, 30, 31, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 26, 31, 33, 35, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_692 : ∃ k : ℕ, Lonely 8 (([2, 5, 26, 31, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 26, 31, 33, 35, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 28, 30, 33, 35, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_693 : ∃ k : ℕ, Lonely 8 (([2, 5, 28, 30, 33, 35, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 28, 30, 33, 35, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 5, 35, 37, 40, 45, 48]`, flank `35`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_694 : ∃ k : ℕ, Lonely 8 (([2, 5, 35, 37, 40, 45, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((35 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 5, 35, 37, 40, 45, 48]) (e := 35) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 9, 10, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_695 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 9, 10, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 9, 10, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 9, 10, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_696 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 9, 10, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 9, 10, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 9, 15, 17]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_697 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 9, 15, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 9, 15, 17]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 9, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_698 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 9, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 9, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 11, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_699 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 11, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 13, 15]`, flank `6`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_700 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 13, 15]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 13, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_701 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 13, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 13, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 13, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_702 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 13, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 13, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 13, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_703 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 13, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 13, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 13, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_704 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 13, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 13, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 14, 15]`, flank `6`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_705 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 14, 15]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 14, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_706 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 14, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 14, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 14, 29]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_707 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 14, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 14, 29]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 14, 41]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_708 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 14, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 14, 41]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 15, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_709 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 15, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 15, 29]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_710 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 15, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 15, 29]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 17, 20]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_711 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 17, 20]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 17, 21]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_712 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 17, 21]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 10, 18, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_713 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 10, 18, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 10, 18, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 12, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_714 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 12, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 12, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 13, 15, 16]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_715 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 13, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 13, 15, 16]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 13, 15, 17]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_716 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 13, 15, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 13, 15, 17]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 13, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_717 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 13, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 13, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 13, 20, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_718 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 13, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 13, 20, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 13, 30, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_719 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 13, 30, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 13, 30, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 8, 15, 22, 44]`, flank `6`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_720 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 8, 15, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 8, 15, 22, 44]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 9, 10, 16, 18]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_721 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 9, 10, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 9, 10, 16, 18]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 9, 10, 16, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_722 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 9, 10, 16, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 9, 10, 16, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 9, 13, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_723 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 9, 13, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 9, 13, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 9, 15, 16, 18]`, flank `6`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_724 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 9, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 9, 15, 16, 18]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 11, 12, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_725 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 11, 12, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_726 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 11, 16, 20]`, flank `10`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_727 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 11, 16, 20]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 12, 17, 20]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_728 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 12, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 12, 17, 20]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 13, 16, 21]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_729 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 13, 16, 21]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 13, 16, 29]`, flank `6`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_730 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 13, 16, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 13, 16, 29]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 13, 16, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_731 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 13, 16, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 13, 16, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 13, 24, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_732 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 13, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 13, 24, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 13, 32, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_733 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 13, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 13, 32, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 14, 16, 19]`, flank `10`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_734 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 14, 16, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 14, 16, 19]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 16, 17, 20]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_735 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 16, 17, 20]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 10, 16, 23, 32]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_736 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 10, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 10, 16, 23, 32]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 11, 13, 15, 22]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_737 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 11, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 11, 13, 15, 22]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 11, 13, 20, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_738 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 11, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 11, 13, 20, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 16, 20, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_739 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 16, 20, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 16, 30, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_740 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 16, 30, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 16, 30, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 20, 24, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_741 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 20, 24, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 20, 32, 40]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_742 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 20, 32, 40]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 24, 30, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_743 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 24, 30, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 24, 30, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 13, 30, 32, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_744 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 13, 30, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 13, 30, 32, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 7, 15, 32, 39, 40]`, flank `6`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_745 : ∃ k : ℕ, Lonely 8 (([2, 6, 7, 15, 32, 39, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 7, 15, 32, 39, 40]) (e := 6) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 9, 10, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_746 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 9, 10, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 9, 10, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 9, 10, 14, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_747 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 9, 10, 14, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 9, 10, 14, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 9, 14, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_748 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 9, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 9, 14, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 9, 14, 15, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_749 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 9, 14, 15, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 9, 14, 15, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 9, 14, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_750 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 9, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 9, 14, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_751 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 23]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_752 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 23]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_753 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_754 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 37]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_755 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 37].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 37]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 11, 14, 59]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_756 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 11, 14, 59].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 11, 14, 59]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 13, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_757 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 13, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 13, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 13, 14, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_758 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 13, 14, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 13, 14, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 13, 14, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_759 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 13, 14, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 13, 14, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 13, 21, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_760 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 13, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 13, 21, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 13, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_761 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 13, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 13, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 17, 21]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_762 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 17, 21]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 17, 31]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_763 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 17, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 17, 31]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 18, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_764 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 18, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 22, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_765 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 22, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 22, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 22, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_766 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 22, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 10, 14, 26, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_767 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 10, 14, 26, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 10, 14, 26, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 11, 14, 15, 25]`, flank `6`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_768 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 11, 14, 15, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 11, 14, 15, 25]) (e := 6) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 11, 14, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_769 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 11, 14, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 11, 14, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 13, 14, 15, 16]`, flank `8`, opening `7`.  Covers 3 census rows. -/
theorem fam_2_770 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 13, 14, 15, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 13, 14, 15, 16]) (e := 8) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 14, 15, 19, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_771 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 14, 15, 19, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 8, 14, 19, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_772 : ∃ k : ℕ, Lonely 8 (([2, 6, 8, 14, 19, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 8, 14, 19, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 9, 13, 14, 15, 18]`, flank `6`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_773 : ∃ k : ℕ, Lonely 8 (([2, 6, 9, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 9, 13, 14, 15, 18]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 9, 13, 14, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_774 : ∃ k : ℕ, Lonely 8 (([2, 6, 9, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 9, 13, 14, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 9, 14, 15, 16, 18]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_775 : ∃ k : ℕ, Lonely 8 (([2, 6, 9, 14, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 9, 14, 15, 16, 18]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 9, 14, 20, 23, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_776 : ∃ k : ℕ, Lonely 8 (([2, 6, 9, 14, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 9, 14, 20, 23, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 10, 13, 14, 16, 21]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_777 : ∃ k : ℕ, Lonely 8 (([2, 6, 10, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 10, 13, 14, 16, 21]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 10, 15, 21, 24, 29]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_778 : ∃ k : ℕ, Lonely 8 (([2, 6, 10, 15, 21, 24, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 10, 15, 21, 24, 29]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 13, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_779 : ∃ k : ℕ, Lonely 8 (([2, 6, 13, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 13, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 13, 14, 19, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_780 : ∃ k : ℕ, Lonely 8 (([2, 6, 13, 14, 19, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 13, 14, 19, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 13, 14, 20, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_781 : ∃ k : ℕ, Lonely 8 (([2, 6, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 13, 14, 20, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 14, 17, 20, 23, 28]`, flank `6`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_782 : ∃ k : ℕ, Lonely 8 (([2, 6, 14, 17, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((6 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 14, 17, 20, 23, 28]) (e := 6) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 14, 19, 20, 23, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_783 : ∃ k : ℕ, Lonely 8 (([2, 6, 14, 19, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 14, 19, 20, 23, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 14, 20, 23, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_784 : ∃ k : ℕ, Lonely 8 (([2, 6, 14, 20, 23, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 14, 20, 23, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 6, 17, 19, 21, 25, 34]`, flank `17`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_785 : ∃ k : ℕ, Lonely 8 (([2, 6, 17, 19, 21, 25, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((17 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 6, 17, 19, 21, 25, 34]) (e := 17) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 11, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_786 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 11, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 11, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 11, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_787 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 11, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 11, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 12, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_788 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 12, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 12, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 12, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_789 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 12, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 12, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 13, 15]`, flank `8`, opening `5`.  Covers 4 census rows. -/
theorem fam_2_790 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 13, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 13, 15]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 14, 15]`, flank `7`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_791 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 14, 15]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_792 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 16, 21]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_793 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 16, 21]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 17, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_794 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 17, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_795 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 10, 18, 19]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_796 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 10, 18, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 10, 18, 19]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 11, 15, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_797 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 11, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 11, 15, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 11, 15, 21]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_798 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 11, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 11, 15, 21]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 11, 20, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_799 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 11, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 11, 20, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 12, 15, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_800 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 12, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 12, 15, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 12, 15, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_801 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 12, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 12, 15, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 12, 20, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_802 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 12, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 12, 20, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 15, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_803 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 15, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 16, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_804 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 16, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 16, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 9, 17, 25, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_805 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 9, 17, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 9, 17, 25, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 10, 11, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_806 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 10, 11, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 10, 11, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 10, 12, 19, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_807 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 10, 12, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 10, 12, 19, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 10, 12, 23, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_808 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 10, 12, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 10, 12, 23, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 11, 13, 15, 21]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_809 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 11, 13, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 11, 13, 15, 21]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 11, 15, 17, 21]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_810 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 11, 15, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 11, 15, 17, 21]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 13, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_811 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 13, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 13, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 14, 15, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_812 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 14, 15, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 14, 15, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 15, 19, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_813 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 15, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 15, 19, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 15, 23, 24]`, flank `8`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_814 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 15, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 15, 23, 24]) (e := 8) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 16, 20, 25]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_815 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 16, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 16, 20, 25]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 19, 20, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_816 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 19, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 19, 20, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 19, 20, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_817 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 19, 20, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 19, 20, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 20, 22, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_818 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 20, 22, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 20, 22, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 12, 20, 23, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_819 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 12, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 12, 20, 23, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 13, 15, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_820 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 13, 15, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 13, 15, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 16, 18, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_821 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 16, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 16, 18, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 8, 23, 30, 38, 60]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_822 : ∃ k : ℕ, Lonely 8 (([2, 7, 8, 23, 30, 38, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 8, 23, 30, 38, 60]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 12, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_823 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 12, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 12, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_824 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 16, 18]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_825 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 16, 18]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_826 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_827 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 11, 19, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_828 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 11, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 11, 19, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 12, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_829 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 12, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 12, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 12, 16, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_830 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 12, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 12, 16, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 12, 16, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_831 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 12, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 12, 16, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 12, 17, 20]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_832 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 12, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 12, 17, 20]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 13, 16, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_833 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 13, 16, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 13, 17, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_834 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 13, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 13, 17, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 14, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_835 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 14, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 17, 18]`, flank `7`, opening `5`.  Covers 3 census rows. -/
theorem fam_2_836 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 17, 18]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 17, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_837 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 17, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 17, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 17, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_838 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 17, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 17, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 18, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_839 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 18, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 20, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_840 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 20, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_841 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 26, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_842 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 26, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 26, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 10, 16, 29, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_843 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 10, 16, 29, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 10, 16, 29, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 15, 18]`, flank `7`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_844 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 15, 18]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 15, 22]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_845 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 15, 22]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 15, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_846 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 15, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 20, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_847 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 20, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 20, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_848 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 20, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 20, 26]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_849 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 20, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 20, 26]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 13, 20, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_850 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 13, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 13, 20, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 15, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_851 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 15, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 15, 16, 20]`, flank `7`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_852 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 15, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 15, 16, 20]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 15, 16, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_853 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 15, 16, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 15, 16, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 15, 19, 22]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_854 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 15, 19, 22]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 15, 24, 27]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_855 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 15, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 15, 24, 27]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 16, 20, 22]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_856 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 16, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 16, 20, 22]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 16, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_857 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 16, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 16, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 16, 25, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_858 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 16, 25, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 16, 25, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 16, 25, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_859 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 16, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 16, 25, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 11, 19, 20, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_860 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 11, 19, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 11, 19, 20, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 13, 15, 18]`, flank `7`, opening `6`.  Covers 3 census rows. -/
theorem fam_2_861 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 13, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 13, 15, 18]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 15, 16, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_862 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 15, 16, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 15, 16, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_863 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 15, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 15, 16, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 15, 16, 35]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_864 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 15, 16, 35]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 16, 20, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_865 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 16, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 16, 20, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 12, 16, 20, 32]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_866 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 12, 16, 20, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 12, 16, 20, 32]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 13, 15, 17, 18]`, flank `7`, opening `6`.  Covers 3 census rows. -/
theorem fam_2_867 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 13, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 13, 15, 17, 18]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 14, 15, 16, 27]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_868 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 14, 15, 16, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 14, 15, 16, 27]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 15, 16, 17, 18]`, flank `7`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_869 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 15, 16, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 15, 16, 17, 18]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 15, 16, 23, 26]`, flank `7`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_870 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 15, 16, 23, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 15, 16, 23, 26]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 19, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_871 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 19, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 19, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 20, 22, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_872 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 20, 22, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 20, 22, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 23, 25, 28]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_873 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 23, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 23, 25, 28]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 23, 25, 45]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_874 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 23, 25, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 23, 25, 45]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 23, 25, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_875 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 23, 25, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 23, 25, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 23, 30, 35]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_876 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 23, 30, 35]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 25, 34, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_877 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 25, 34, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 25, 34, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 9, 16, 25, 34, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_878 : ∃ k : ℕ, Lonely 8 (([2, 7, 9, 16, 25, 34, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 9, 16, 25, 34, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 12, 13, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_879 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 12, 13, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 12, 13, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 12, 18, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_880 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 12, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 12, 18, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 13, 15, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_881 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 13, 15, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 13, 15, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 16, 18, 36]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_882 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 16, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 16, 18, 36]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 18, 20, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_883 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 18, 20, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 18, 24, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_884 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 18, 24, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 18, 24, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 18, 28, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_885 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 18, 28, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 18, 28, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 11, 18, 32, 36]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_886 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 11, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 11, 18, 32, 36]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 13, 16, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_887 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 13, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 13, 16, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 16, 19, 24]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_888 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 16, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 16, 19, 24]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 16, 23, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_889 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 16, 23, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 16, 23, 32]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_890 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 16, 23, 32]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 18, 25, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_891 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 18, 25, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 12, 19, 26, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_892 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 12, 19, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 12, 19, 26, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 13, 15, 16, 21]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_893 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 13, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 13, 15, 16, 21]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 13, 16, 18, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_894 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 13, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 13, 16, 18, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 15, 16, 23, 32]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_895 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 15, 16, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 15, 16, 23, 32]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 15, 17, 19, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_896 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 15, 17, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 15, 17, 19, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 16, 17, 18, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_897 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 16, 17, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 16, 17, 18, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 16, 18, 23, 32]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_898 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 16, 18, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 16, 18, 23, 32]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 17, 19, 27, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_899 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 17, 19, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 17, 19, 27, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 17, 22, 24, 48]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_900 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 17, 22, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 17, 22, 24, 48]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 17, 25, 27, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_901 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 17, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 17, 25, 27, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 18, 24, 25, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_902 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 18, 24, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 18, 24, 25, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 10, 22, 24, 31, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_903 : ∃ k : ℕ, Lonely 8 (([2, 7, 10, 22, 24, 31, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 10, 22, 24, 31, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 12, 13, 15, 22]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_904 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 12, 13, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 12, 13, 15, 22]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 12, 13, 20, 22]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_905 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 12, 13, 20, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 12, 13, 20, 22]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 16, 21]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_906 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 16, 21]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 17, 26]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_907 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 17, 26]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 19, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_908 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 19, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 19, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 20, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_909 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 20, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 28, 30]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_910 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 28, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 28, 30]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 15, 29, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_911 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 15, 29, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 15, 29, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 13, 18, 20, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_912 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 13, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 13, 18, 20, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 15, 16, 18, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_913 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 15, 16, 18, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 15, 16, 18, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 15, 18, 24, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_914 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 15, 18, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 15, 18, 24, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 15, 18, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_915 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 15, 18, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 15, 18, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 20, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_916 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 20, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 20, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_917 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_918 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 25, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_919 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 25, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 25, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 30, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_920 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 30, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 30, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 18, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_921 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 18, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 25, 27, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_922 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 25, 27, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 25, 27, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 16, 25, 36, 45]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_923 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 16, 25, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 16, 25, 36, 45]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 20, 23, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_924 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 20, 23, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 20, 23, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 20, 26, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_925 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 20, 26, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 20, 26, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 20, 29, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_926 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 20, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 20, 29, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 20, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_927 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 20, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 20, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_928 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 30, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_929 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 30, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 30, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 11, 18, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_930 : ∃ k : ℕ, Lonely 8 (([2, 7, 11, 18, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 11, 18, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 13, 16, 20, 21]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_931 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 13, 16, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 13, 16, 20, 21]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 13, 20, 27, 54]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_932 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 13, 20, 27, 54].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 13, 20, 27, 54]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 14, 15, 16, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_933 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 14, 15, 16, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 14, 15, 16, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 15, 16, 19, 24]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_934 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 15, 16, 19, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 15, 16, 19, 24]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 15, 16, 23, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_935 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 15, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 15, 16, 23, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 15, 22, 26, 44]`, flank `7`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_936 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 15, 22, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 15, 22, 26, 44]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 16, 18, 25, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_937 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 16, 18, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 16, 18, 25, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 16, 19, 20, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_938 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 16, 19, 20, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 16, 19, 20, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 16, 20, 23, 24]`, flank `7`, opening `5`.  Covers 2 census rows. -/
theorem fam_2_939 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 16, 20, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 16, 20, 23, 24]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 16, 20, 23, 32]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_940 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 16, 20, 23, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 16, 20, 23, 32]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 16, 23, 30, 32]`, flank `12`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_941 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 16, 23, 30, 32].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 16, 23, 30, 32]) (e := 12) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 18, 25, 26, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_942 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 18, 25, 26, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 18, 25, 26, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 18, 25, 32, 36]`, flank `7`, opening `5`.  Covers 1 census rows. -/
theorem fam_2_943 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 18, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨5, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 18, 25, 32, 36]) (e := 7) (k := 5)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 12, 28, 32, 35, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_944 : ∃ k : ℕ, Lonely 8 (([2, 7, 12, 28, 32, 35, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 12, 28, 32, 35, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 13, 15, 16, 17, 26]`, flank `13`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_945 : ∃ k : ℕ, Lonely 8 (([2, 7, 13, 15, 16, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 13, 15, 16, 17, 26]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 13, 15, 16, 23, 24]`, flank `7`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_946 : ∃ k : ℕ, Lonely 8 (([2, 7, 13, 15, 16, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 13, 15, 16, 23, 24]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 14, 15, 16, 18, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_947 : ∃ k : ℕ, Lonely 8 (([2, 7, 14, 15, 16, 18, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 14, 15, 16, 18, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 14, 16, 18, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_948 : ∃ k : ℕ, Lonely 8 (([2, 7, 14, 16, 18, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 14, 16, 18, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 14, 18, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_949 : ∃ k : ℕ, Lonely 8 (([2, 7, 14, 18, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 14, 18, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 15, 17, 19, 20, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_950 : ∃ k : ℕ, Lonely 8 (([2, 7, 15, 17, 19, 20, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 15, 17, 19, 20, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 15, 18, 22, 32, 44]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_951 : ∃ k : ℕ, Lonely 8 (([2, 7, 15, 18, 22, 32, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 15, 18, 22, 32, 44]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 15, 22, 24, 26, 44]`, flank `15`, opening `9`.  Covers 1 census rows. -/
theorem fam_2_952 : ∃ k : ℕ, Lonely 8 (([2, 7, 15, 22, 24, 26, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((15 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 15, 22, 24, 26, 44]) (e := 15) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 15, 25, 32, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_953 : ∃ k : ℕ, Lonely 8 (([2, 7, 15, 25, 32, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 15, 25, 32, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 19, 25, 27]`, flank `7`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_954 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 19, 25, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 19, 25, 27]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 22, 25, 36]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_955 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 22, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 22, 25, 36]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 23, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_956 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 23, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 23, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 23, 25, 45]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_957 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 23, 25, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 23, 25, 45]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 23, 30, 35]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_958 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 23, 30, 35]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 24, 25, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_959 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 24, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 24, 25, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 25, 34, 36]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_960 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 25, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 25, 34, 36]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 25, 34, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_961 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 25, 34, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 25, 34, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 18, 25, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_962 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 18, 25, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 18, 25, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 23, 25, 27, 45]`, flank `16`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_963 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 23, 25, 27, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 23, 25, 27, 45]) (e := 16) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 23, 25, 36, 45]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_964 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 23, 25, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 23, 25, 36, 45]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 23, 26, 30, 60]`, flank `7`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_965 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 23, 26, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 23, 26, 30, 60]) (e := 7) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 25, 27, 34, 45]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_966 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 25, 27, 34, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 25, 27, 34, 45]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 16, 25, 34, 36, 45]`, flank `16`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_967 : ∃ k : ℕ, Lonely 8 (([2, 7, 16, 25, 34, 36, 45].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((16 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 16, 25, 34, 36, 45]) (e := 16) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 17, 19, 20, 27, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_968 : ∃ k : ℕ, Lonely 8 (([2, 7, 17, 19, 20, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 17, 19, 20, 27, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 17, 20, 25, 27, 30]`, flank `7`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_969 : ∃ k : ℕ, Lonely 8 (([2, 7, 17, 20, 25, 27, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 17, 20, 25, 27, 30]) (e := 7) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 20, 22, 29, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_970 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 20, 22, 29, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 20, 22, 29, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 22, 25, 32, 36]`, flank `18`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_971 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 22, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 22, 25, 32, 36]) (e := 18) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 22, 29, 40, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_972 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 22, 29, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 22, 29, 40, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 23, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_973 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 23, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 23, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 24, 25, 26, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_974 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 24, 25, 26, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 24, 25, 26, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 24, 25, 32, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_975 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 24, 25, 32, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 24, 25, 32, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 25, 28, 32, 40]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_976 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 25, 28, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 25, 28, 32, 40]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 25, 32, 34, 36]`, flank `18`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_977 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 25, 32, 34, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((18 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 25, 32, 34, 36]) (e := 18) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 18, 25, 32, 35, 36]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_978 : ∃ k : ℕ, Lonely 8 (([2, 7, 18, 25, 32, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 18, 25, 32, 35, 36]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 19, 21, 28, 35, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_979 : ∃ k : ℕ, Lonely 8 (([2, 7, 19, 21, 28, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 19, 21, 28, 35, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 21, 23, 25, 49, 50]`, flank `7`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_980 : ∃ k : ℕ, Lonely 8 (([2, 7, 21, 23, 25, 49, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 21, 23, 25, 49, 50]) (e := 7) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 7, 25, 27, 32, 39, 50]`, flank `7`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_981 : ∃ k : ℕ, Lonely 8 (([2, 7, 25, 27, 32, 39, 50].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((7 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 7, 25, 27, 32, 39, 50]) (e := 7) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 11, 14, 15]`, flank `9`, opening `3`.  Covers 4 census rows. -/
theorem fam_2_982 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 11, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 11, 14, 15]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 11, 14, 16]`, flank `9`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_983 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 11, 14, 16].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 11, 14, 16]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 11, 14, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_984 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 11, 14, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 11, 14, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 12, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_985 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 12, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 12, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 12, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_986 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 12, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 12, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_987 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 14, 16, 21]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_988 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 14, 16, 21]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_989 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 10, 24, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_990 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 10, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 10, 24, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 11, 14, 15, 21]`, flank `8`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_991 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 11, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 11, 14, 15, 21]) (e := 8) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 11, 14, 20, 21]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_992 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 11, 14, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 11, 14, 20, 21]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 11, 14, 20, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_993 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 11, 14, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 11, 14, 20, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 11, 14, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_994 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 11, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 11, 14, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 12, 14, 15, 18]`, flank `9`, opening `3`.  Covers 3 census rows. -/
theorem fam_2_995 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 12, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 12, 14, 15, 18]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 12, 20, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_996 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 12, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 12, 20, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 9, 14, 17, 25, 28]`, flank `8`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_997 : ∃ k : ℕ, Lonely 8 (([2, 8, 9, 14, 17, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((8 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 9, 14, 17, 25, 28]) (e := 8) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 11, 12, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_998 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 11, 12, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 11, 12, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 11, 12, 14, 23]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_999 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 11, 12, 14, 23].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 11, 12, 14, 23]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 12, 14, 22, 29]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1000 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 12, 14, 22, 29].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 12, 14, 22, 29]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 12, 14, 22, 31]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1001 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 12, 14, 22, 31].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 12, 14, 22, 31]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 12, 14, 22, 47]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1002 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 12, 14, 22, 47].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 12, 14, 22, 47]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 12, 19, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1003 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 12, 19, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 12, 19, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 12, 21, 23, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1004 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 12, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 12, 21, 23, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 13, 28, 36, 39]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1005 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 13, 28, 36, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 13, 28, 36, 39]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 15, 35, 37, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1006 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 15, 35, 37, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 15, 35, 37, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 10, 26, 28, 36, 39]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1007 : ∃ k : ℕ, Lonely 8 (([2, 8, 10, 26, 28, 36, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 10, 26, 28, 36, 39]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 12, 13, 14, 15]`, flank `2`, opening `1`.  Covers 4 census rows. -/
theorem fam_2_1008 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 12, 13, 14, 15].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 12, 13, 14, 15]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 13, 14, 15, 21]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1009 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 13, 14, 15, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 13, 14, 15, 21]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 13, 14, 15, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1010 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 13, 14, 15, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 13, 14, 15, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 13, 14, 30, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1011 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 13, 14, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 13, 14, 30, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 14, 15, 17, 21]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1012 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 14, 15, 17, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 14, 15, 17, 21]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 14, 15, 19, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1013 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 14, 15, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 14, 15, 19, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 11, 14, 26, 30, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1014 : ∃ k : ℕ, Lonely 8 (([2, 8, 11, 14, 26, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 11, 14, 26, 30, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 13, 15, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1015 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 13, 15, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 13, 15, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 13, 20, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1016 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 13, 20, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 13, 20, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 14, 15, 17, 24]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1017 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 14, 15, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 14, 15, 17, 24]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 14, 20, 22, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1018 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 14, 20, 22, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 14, 20, 22, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 19, 20, 21, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1019 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 19, 20, 21, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 12, 20, 21, 23, 24]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1020 : ∃ k : ℕ, Lonely 8 (([2, 8, 12, 20, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 12, 20, 21, 23, 24]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 13, 14, 15, 22, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1021 : ∃ k : ℕ, Lonely 8 (([2, 8, 13, 14, 15, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 13, 14, 15, 22, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 13, 14, 22, 30, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1022 : ∃ k : ℕ, Lonely 8 (([2, 8, 13, 14, 22, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 13, 14, 22, 30, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 13, 15, 22, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1023 : ∃ k : ℕ, Lonely 8 (([2, 8, 13, 15, 22, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 13, 15, 22, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 13, 15, 28, 29, 39]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1024 : ∃ k : ℕ, Lonely 8 (([2, 8, 13, 15, 28, 29, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 13, 15, 28, 29, 39]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 13, 15, 28, 34, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1025 : ∃ k : ℕ, Lonely 8 (([2, 8, 13, 15, 28, 34, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 13, 15, 28, 34, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 14, 15, 17, 19, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1026 : ∃ k : ℕ, Lonely 8 (([2, 8, 14, 15, 17, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 14, 15, 17, 19, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 14, 22, 26, 30, 33]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1027 : ∃ k : ℕ, Lonely 8 (([2, 8, 14, 22, 26, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 14, 22, 26, 30, 33]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 8, 15, 26, 28, 29, 39]`, flank `26`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1028 : ∃ k : ℕ, Lonely 8 (([2, 8, 15, 26, 28, 29, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((26 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 8, 15, 26, 28, 29, 39]) (e := 26) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 11, 14, 16, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1029 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 11, 14, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 11, 14, 16, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 11, 14, 32, 40]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1030 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 11, 14, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 11, 14, 32, 40]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 12, 13, 14, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_1031 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 12, 13, 14, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 12, 13, 14, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 12, 14, 16, 17]`, flank `10`, opening `6`.  Covers 3 census rows. -/
theorem fam_2_1032 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 12, 14, 16, 17].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 12, 14, 16, 17]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 12, 14, 16, 39]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1033 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 12, 14, 16, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 12, 14, 16, 39]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 12, 14, 19, 20]`, flank `2`, opening `0`.  Covers 3 census rows. -/
theorem fam_2_1034 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 12, 14, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 12, 14, 19, 20]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 12, 16, 21, 24]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_1035 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 12, 16, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 12, 16, 21, 24]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 13, 14, 16, 20]`, flank `10`, opening `4`.  Covers 3 census rows. -/
theorem fam_2_1036 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 13, 14, 16, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 13, 14, 16, 20]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 13, 14, 16, 21]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_1037 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 13, 14, 16, 21]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 14, 16, 17, 28]`, flank `10`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_1038 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 14, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 14, 16, 17, 28]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 14, 16, 18, 21]`, flank `9`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_1039 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 14, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 14, 16, 18, 21]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 14, 16, 19, 20]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_1040 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 14, 16, 19, 20].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 14, 16, 19, 20]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 14, 16, 19, 27]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1041 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 14, 16, 19, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 14, 16, 19, 27]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 14, 16, 23, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1042 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 14, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 14, 16, 23, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 19, 24, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1043 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 19, 24, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 19, 24, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 10, 24, 27, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1044 : ∃ k : ℕ, Lonely 8 (([2, 9, 10, 24, 27, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 10, 24, 27, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 13, 14, 15, 18]`, flank `9`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_1045 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 13, 14, 15, 18]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 13, 14, 20, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1046 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 13, 14, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 13, 14, 20, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 15, 19, 22]`, flank `9`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1047 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 15, 19, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 15, 19, 22]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 16, 20, 40]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1048 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 16, 20, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 16, 20, 40]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 20, 24, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1049 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 20, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 20, 24, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 20, 24, 40]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1050 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 20, 24, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 20, 24, 40]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 20, 32, 40]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1051 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 20, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 20, 32, 40]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 14, 30, 32, 40]`, flank `9`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_1052 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 14, 30, 32, 40].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 14, 30, 32, 40]) (e := 9) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 15, 19, 21, 22]`, flank `9`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1053 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 15, 19, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 15, 19, 21, 22]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 11, 31, 40, 42, 55]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1054 : ∃ k : ℕ, Lonely 8 (([2, 9, 11, 31, 40, 42, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 11, 31, 40, 42, 55]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 13, 14, 15, 18]`, flank `9`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_1055 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 13, 14, 15, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 13, 14, 15, 18]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 14, 15, 16, 18]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_1056 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 14, 15, 16, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 14, 15, 16, 18]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 14, 15, 16, 19]`, flank `9`, opening `2`.  Covers 3 census rows. -/
theorem fam_2_1057 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 14, 15, 16, 19].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 14, 15, 16, 19]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 14, 15, 16, 35]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1058 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 14, 15, 16, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 14, 15, 16, 35]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 14, 15, 16, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1059 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 14, 15, 16, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 14, 15, 16, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 14, 15, 32, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1060 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 14, 15, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 14, 15, 32, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 15, 16, 21, 35]`, flank `9`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_1061 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 15, 16, 21, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 15, 16, 21, 35]) (e := 9) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 15, 16, 28, 35]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1062 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 15, 16, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 15, 16, 28, 35]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 12, 16, 20, 21, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1063 : ∃ k : ℕ, Lonely 8 (([2, 9, 12, 16, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 12, 16, 20, 21, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 13, 14, 15, 17, 18]`, flank `9`, opening `1`.  Covers 3 census rows. -/
theorem fam_2_1064 : ∃ k : ℕ, Lonely 8 (([2, 9, 13, 14, 15, 17, 18].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 13, 14, 15, 17, 18]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 13, 14, 17, 20, 28]`, flank `9`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1065 : ∃ k : ℕ, Lonely 8 (([2, 9, 13, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 13, 14, 17, 20, 28]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 13, 14, 20, 22, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1066 : ∃ k : ℕ, Lonely 8 (([2, 9, 13, 14, 20, 22, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 13, 14, 20, 22, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 13, 14, 22, 40, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1067 : ∃ k : ℕ, Lonely 8 (([2, 9, 13, 14, 22, 40, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 13, 14, 22, 40, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 13, 15, 17, 21, 34]`, flank `9`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1068 : ∃ k : ℕ, Lonely 8 (([2, 9, 13, 15, 17, 21, 34].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 13, 15, 17, 21, 34]) (e := 9) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 15, 16, 23, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1069 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 15, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 15, 16, 23, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 15, 16, 24, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1070 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 15, 16, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 15, 16, 24, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 15, 16, 36, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1071 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 15, 16, 36, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 15, 16, 36, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 15, 24, 32, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1072 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 15, 24, 32, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 15, 24, 32, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 15, 32, 36, 48]`, flank `9`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1073 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 15, 32, 36, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 15, 32, 36, 48]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 16, 20, 23, 28]`, flank `9`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1074 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 16, 20, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 16, 20, 23, 28]) (e := 9) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 16, 23, 25, 28]`, flank `9`, opening `8`.  Covers 2 census rows. -/
theorem fam_2_1075 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 16, 23, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 16, 23, 25, 28]) (e := 9) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 16, 23, 30, 35]`, flank `14`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1076 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 16, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 16, 23, 30, 35]) (e := 14) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 20, 22, 23, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1077 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 20, 22, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 20, 22, 23, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 14, 20, 22, 24, 25]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1078 : ∃ k : ℕ, Lonely 8 (([2, 9, 14, 20, 22, 24, 25].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 14, 20, 22, 24, 25]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 16, 21, 23, 25, 28]`, flank `9`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_1079 : ∃ k : ℕ, Lonely 8 (([2, 9, 16, 21, 23, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 16, 21, 23, 25, 28]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 16, 21, 23, 30, 35]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1080 : ∃ k : ℕ, Lonely 8 (([2, 9, 16, 21, 23, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 16, 21, 23, 30, 35]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 16, 23, 28, 30, 35]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1081 : ∃ k : ℕ, Lonely 8 (([2, 9, 16, 23, 28, 30, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 16, 23, 28, 30, 35]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 22, 31, 40, 42, 55]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1082 : ∃ k : ℕ, Lonely 8 (([2, 9, 22, 31, 40, 42, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 22, 31, 40, 42, 55]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 23, 28, 30, 32, 35]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1083 : ∃ k : ℕ, Lonely 8 (([2, 9, 23, 28, 30, 32, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 23, 28, 30, 32, 35]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 31, 33, 40, 42, 55]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1084 : ∃ k : ℕ, Lonely 8 (([2, 9, 31, 33, 40, 42, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 31, 33, 40, 42, 55]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 9, 31, 40, 42, 44, 55]`, flank `9`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1085 : ∃ k : ℕ, Lonely 8 (([2, 9, 31, 40, 42, 44, 55].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((9 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 9, 31, 40, 42, 44, 55]) (e := 9) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 12, 13, 14, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1086 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 12, 13, 14, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 12, 13, 14, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 12, 14, 19, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1087 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 12, 14, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 12, 14, 19, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 12, 14, 25, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1088 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 12, 14, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 12, 14, 25, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 13, 14, 24, 48]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1089 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 13, 14, 24, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 13, 14, 24, 48]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 13, 16, 21, 30]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1090 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 13, 16, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 13, 16, 21, 30]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 14, 15, 16, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1091 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 14, 15, 16, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 14, 15, 16, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 14, 24, 25, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1092 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 14, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 14, 24, 25, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 14, 24, 26, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1093 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 14, 24, 26, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 14, 24, 26, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 14, 24, 35, 48]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_1094 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 14, 24, 35, 48].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 14, 24, 35, 48]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 15, 26, 28, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1095 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 15, 26, 28, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 15, 26, 28, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 16, 19, 21, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1096 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 16, 19, 21, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 16, 19, 21, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 11, 21, 26, 32, 33]`, flank `10`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_1097 : ∃ k : ℕ, Lonely 8 (([2, 10, 11, 21, 26, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 11, 21, 26, 32, 33]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 13, 14, 16, 21]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1098 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 13, 14, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 13, 14, 16, 21]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 13, 14, 16, 39]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1099 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 13, 14, 16, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 13, 14, 16, 39]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 13, 14, 17, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1100 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 13, 14, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 13, 14, 17, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 13, 14, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1101 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 13, 14, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 13, 14, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 16, 26, 39]`, flank `12`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_1102 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 16, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 16, 26, 39]) (e := 12) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 16, 26, 41]`, flank `12`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1103 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 16, 26, 41].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 16, 26, 41]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 17, 19, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1104 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 17, 19, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 17, 19, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 17, 25, 28]`, flank `10`, opening `3`.  Covers 2 census rows. -/
theorem fam_2_1105 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 17, 25, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 17, 25, 28]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 19, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1106 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 19, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 19, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 14, 25, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1107 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 14, 25, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 14, 25, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 16, 19, 21, 24]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1108 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 16, 19, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 16, 19, 21, 24]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 12, 16, 21, 23, 24]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1109 : ∃ k : ℕ, Lonely 8 (([2, 10, 12, 16, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 12, 16, 21, 23, 24]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 13, 14, 15, 16, 21]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1110 : ∃ k : ℕ, Lonely 8 (([2, 10, 13, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 13, 14, 15, 16, 21]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 13, 14, 16, 18, 21]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_1111 : ∃ k : ℕ, Lonely 8 (([2, 10, 13, 14, 16, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 13, 14, 16, 18, 21]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 13, 15, 24, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1112 : ∃ k : ℕ, Lonely 8 (([2, 10, 13, 15, 24, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 13, 15, 24, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 13, 24, 28, 41, 56]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1113 : ∃ k : ℕ, Lonely 8 (([2, 10, 13, 24, 28, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 13, 24, 28, 41, 56]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 15, 16, 17, 28]`, flank `10`, opening `6`.  Covers 2 census rows. -/
theorem fam_2_1114 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 15, 16, 17, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 15, 16, 17, 28]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 15, 16, 23, 28]`, flank `10`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1115 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 15, 16, 23, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 15, 16, 23, 28]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 15, 16, 26, 27]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_1116 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 15, 16, 26, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 15, 16, 26, 27]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 16, 17, 18, 21]`, flank `10`, opening `9`.  Covers 2 census rows. -/
theorem fam_2_1117 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 16, 17, 18, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 16, 17, 18, 21]) (e := 10) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 16, 18, 19, 27]`, flank `10`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_1118 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 16, 18, 19, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 16, 18, 19, 27]) (e := 10) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 17, 19, 21, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1119 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 17, 19, 21, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 17, 19, 21, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 17, 19, 48, 51]`, flank `10`, opening `6`.  Covers 1 census rows. -/
theorem fam_2_1120 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 17, 19, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨6, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 17, 19, 48, 51]) (e := 10) (k := 6)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 19, 34, 48, 51]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1121 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 19, 34, 48, 51].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 19, 34, 48, 51]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 14, 22, 24, 25, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1122 : ∃ k : ℕ, Lonely 8 (([2, 10, 14, 22, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 14, 22, 24, 25, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 15, 26, 28, 41, 52]`, flank `10`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_1123 : ∃ k : ℕ, Lonely 8 (([2, 10, 15, 26, 28, 41, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 15, 26, 28, 41, 52]) (e := 10) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 16, 19, 21, 22, 33]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1124 : ∃ k : ℕ, Lonely 8 (([2, 10, 16, 19, 21, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 16, 19, 21, 22, 33]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 17, 19, 21, 28, 42]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1125 : ∃ k : ℕ, Lonely 8 (([2, 10, 17, 19, 21, 28, 42].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 17, 19, 21, 28, 42]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 19, 21, 23, 27, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1126 : ∃ k : ℕ, Lonely 8 (([2, 10, 19, 21, 23, 27, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 19, 21, 23, 27, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 19, 21, 23, 28, 38]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1127 : ∃ k : ℕ, Lonely 8 (([2, 10, 19, 21, 23, 28, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 19, 21, 23, 28, 38]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 21, 22, 26, 32, 33]`, flank `21`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1128 : ∃ k : ℕ, Lonely 8 (([2, 10, 21, 22, 26, 32, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((21 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 21, 22, 26, 32, 33]) (e := 21) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 21, 22, 32, 43, 44]`, flank `10`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1129 : ∃ k : ℕ, Lonely 8 (([2, 10, 21, 22, 32, 43, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 21, 22, 32, 43, 44]) (e := 10) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 10, 21, 23, 33, 43, 46]`, flank `10`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1130 : ∃ k : ℕ, Lonely 8 (([2, 10, 21, 23, 33, 43, 46].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((10 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 10, 21, 23, 33, 43, 46]) (e := 10) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 12, 13, 14, 15, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1131 : ∃ k : ℕ, Lonely 8 (([2, 11, 12, 13, 14, 15, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 12, 13, 14, 15, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 12, 13, 15, 21, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1132 : ∃ k : ℕ, Lonely 8 (([2, 11, 12, 13, 15, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 12, 13, 15, 21, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 12, 14, 15, 26, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1133 : ∃ k : ℕ, Lonely 8 (([2, 11, 12, 14, 15, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 12, 14, 15, 26, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 12, 18, 23, 35, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1134 : ∃ k : ℕ, Lonely 8 (([2, 11, 12, 18, 23, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 12, 18, 23, 35, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 14, 15, 16, 21]`, flank `11`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1135 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 14, 15, 16, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 14, 15, 16, 21]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 14, 15, 16, 33]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1136 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 14, 15, 16, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 14, 15, 16, 33]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 14, 15, 17, 26]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1137 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 14, 15, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 14, 15, 17, 26]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 14, 16, 30, 33]`, flank `11`, opening `8`.  Covers 1 census rows. -/
theorem fam_2_1138 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 14, 16, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 14, 16, 30, 33]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 14, 24, 25, 33]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1139 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 14, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 14, 24, 25, 33]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 15, 17, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1140 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 15, 17, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 15, 17, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 15, 24, 28, 39]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1141 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 15, 24, 28, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 15, 24, 28, 39]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 13, 16, 20, 21, 30]`, flank `11`, opening `8`.  Covers 2 census rows. -/
theorem fam_2_1142 : ∃ k : ℕ, Lonely 8 (([2, 11, 13, 16, 20, 21, 30].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨8, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 13, 16, 20, 21, 30]) (e := 11) (k := 8)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 14, 15, 26, 28, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1143 : ∃ k : ℕ, Lonely 8 (([2, 11, 14, 15, 26, 28, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 14, 15, 26, 28, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 14, 15, 26, 40, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1144 : ∃ k : ℕ, Lonely 8 (([2, 11, 14, 15, 26, 40, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 14, 15, 26, 40, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 14, 18, 20, 24, 27]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1145 : ∃ k : ℕ, Lonely 8 (([2, 11, 14, 18, 20, 24, 27].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 14, 18, 20, 24, 27]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 14, 18, 20, 29, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1146 : ∃ k : ℕ, Lonely 8 (([2, 11, 14, 18, 20, 29, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 14, 18, 20, 29, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 14, 23, 24, 25, 33]`, flank `11`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1147 : ∃ k : ℕ, Lonely 8 (([2, 11, 14, 23, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 14, 23, 24, 25, 33]) (e := 11) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 15, 24, 26, 28, 39]`, flank `11`, opening `7`.  Covers 1 census rows. -/
theorem fam_2_1148 : ∃ k : ℕ, Lonely 8 (([2, 11, 15, 24, 26, 28, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 15, 24, 26, 28, 39]) (e := 11) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 15, 24, 26, 28, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1149 : ∃ k : ℕ, Lonely 8 (([2, 11, 15, 24, 26, 28, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 15, 24, 26, 28, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 15, 26, 28, 34, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1150 : ∃ k : ℕ, Lonely 8 (([2, 11, 15, 26, 28, 34, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 15, 26, 28, 34, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 15, 26, 28, 38, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1151 : ∃ k : ℕ, Lonely 8 (([2, 11, 15, 26, 28, 38, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 15, 26, 28, 38, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 15, 26, 28, 48, 52]`, flank `11`, opening `9`.  Covers 1 census rows. -/
theorem fam_2_1152 : ∃ k : ℕ, Lonely 8 (([2, 11, 15, 26, 28, 48, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((11 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 15, 26, 28, 48, 52]) (e := 11) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 18, 23, 24, 35, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1153 : ∃ k : ℕ, Lonely 8 (([2, 11, 18, 23, 24, 35, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 18, 23, 24, 35, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 11, 24, 26, 35, 37, 52]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1154 : ∃ k : ℕ, Lonely 8 (([2, 11, 24, 26, 35, 37, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 11, 24, 26, 35, 37, 52]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 14, 16, 20, 21]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1155 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 14, 16, 20, 21].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 14, 16, 20, 21]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 14, 16, 20, 39]`, flank `12`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1156 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 14, 16, 20, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 14, 16, 20, 39]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 14, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1157 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 14, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 14, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 14, 20, 27, 28]`, flank `2`, opening `0`.  Covers 2 census rows. -/
theorem fam_2_1158 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 14, 20, 27, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 14, 20, 27, 28]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 14, 22, 35, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1159 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 14, 22, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 14, 22, 35, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 15, 16, 28, 56]`, flank `12`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1160 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 15, 16, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 15, 16, 28, 56]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 15, 24, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1161 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 15, 24, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 15, 24, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 15, 28, 32, 56]`, flank `13`, opening `9`.  Covers 1 census rows. -/
theorem fam_2_1162 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 15, 28, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 15, 28, 32, 56]) (e := 13) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 15, 28, 40, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1163 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 15, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 15, 28, 40, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 15, 28, 48, 56]`, flank `12`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1164 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 15, 28, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 15, 28, 48, 56]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 13, 28, 40, 41, 56]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1165 : ∃ k : ℕ, Lonely 8 (([2, 12, 13, 28, 40, 41, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 13, 28, 40, 41, 56]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 14, 15, 16, 17, 24]`, flank `12`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1166 : ∃ k : ℕ, Lonely 8 (([2, 12, 14, 15, 16, 17, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 14, 15, 16, 17, 24]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 14, 15, 16, 21, 22]`, flank `12`, opening `4`.  Covers 2 census rows. -/
theorem fam_2_1167 : ∃ k : ℕ, Lonely 8 (([2, 12, 14, 15, 16, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 14, 15, 16, 21, 22]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 14, 15, 19, 21, 22]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1168 : ∃ k : ℕ, Lonely 8 (([2, 12, 14, 15, 19, 21, 22].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 14, 15, 19, 21, 22]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 14, 16, 20, 26, 39]`, flank `12`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1169 : ∃ k : ℕ, Lonely 8 (([2, 12, 14, 16, 20, 26, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 14, 16, 20, 26, 39]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 15, 16, 17, 28, 56]`, flank `12`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1170 : ∃ k : ℕ, Lonely 8 (([2, 12, 15, 16, 17, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 15, 16, 17, 28, 56]) (e := 12) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 15, 16, 28, 43, 56]`, flank `12`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_1171 : ∃ k : ℕ, Lonely 8 (([2, 12, 15, 16, 28, 43, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 15, 16, 28, 43, 56]) (e := 12) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 15, 17, 19, 21, 24]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1172 : ∃ k : ℕ, Lonely 8 (([2, 12, 15, 17, 19, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 15, 17, 19, 21, 24]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 15, 19, 21, 26, 52]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1173 : ∃ k : ℕ, Lonely 8 (([2, 12, 15, 19, 21, 26, 52].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 15, 19, 21, 26, 52]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 16, 19, 20, 21, 24]`, flank `12`, opening `2`.  Covers 2 census rows. -/
theorem fam_2_1174 : ∃ k : ℕ, Lonely 8 (([2, 12, 16, 19, 20, 21, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 16, 19, 20, 21, 24]) (e := 12) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 16, 20, 21, 23, 24]`, flank `12`, opening `7`.  Covers 2 census rows. -/
theorem fam_2_1175 : ∃ k : ℕ, Lonely 8 (([2, 12, 16, 20, 21, 23, 24].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((12 : ℕ) : ℝ) k) :=
  ⟨7, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 16, 20, 21, 23, 24]) (e := 12) (k := 7)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 18, 21, 23, 25, 36]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1176 : ∃ k : ℕ, Lonely 8 (([2, 12, 18, 21, 23, 25, 36].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 18, 21, 23, 25, 36]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 12, 24, 26, 27, 28, 35]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1177 : ∃ k : ℕ, Lonely 8 (([2, 12, 24, 26, 27, 28, 35].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 12, 24, 26, 27, 28, 35]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 15, 16, 17, 26]`, flank `13`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1178 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 15, 16, 17, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 15, 16, 17, 26]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 15, 16, 19, 26]`, flank `13`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1179 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 15, 16, 19, 26].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 15, 16, 19, 26]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 15, 16, 22, 33]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1180 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 15, 16, 22, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 15, 16, 22, 33]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 15, 16, 29, 39]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1181 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 15, 16, 29, 39].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 15, 16, 29, 39]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 15, 17, 20, 28]`, flank `2`, opening `1`.  Covers 2 census rows. -/
theorem fam_2_1182 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 15, 17, 20, 28].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 15, 17, 20, 28]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 16, 17, 30, 60]`, flank `13`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1183 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 16, 17, 30, 60].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 16, 17, 30, 60]) (e := 13) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 16, 22, 30, 33]`, flank `14`, opening `4`.  Covers 1 census rows. -/
theorem fam_2_1184 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 16, 22, 30, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((14 : ℕ) : ℝ) k) :=
  ⟨4, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 16, 22, 30, 33]) (e := 14) (k := 4)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 22, 24, 25, 33]`, flank `13`, opening `9`.  Covers 1 census rows. -/
theorem fam_2_1185 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 22, 24, 25, 33].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨9, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 22, 24, 25, 33]) (e := 13) (k := 9)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 14, 22, 24, 35, 44]`, flank `2`, opening `0`.  Covers 1 census rows. -/
theorem fam_2_1186 : ∃ k : ℕ, Lonely 8 (([2, 13, 14, 22, 24, 35, 44].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨0, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 14, 22, 24, 35, 44]) (e := 2) (k := 0)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 16, 22, 28, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1187 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 16, 22, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 16, 22, 28, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 16, 28, 34, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1188 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 16, 28, 34, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 16, 28, 34, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 19, 27, 35, 38]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1189 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 19, 27, 35, 38].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 19, 27, 35, 38]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 22, 24, 28, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1190 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 22, 24, 28, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 22, 24, 28, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 22, 28, 32, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1191 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 22, 28, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 22, 28, 32, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 22, 28, 40, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1192 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 22, 28, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 22, 28, 40, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 22, 28, 48, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1193 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 22, 28, 48, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 22, 28, 48, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 24, 28, 32, 56]`, flank `13`, opening `3`.  Covers 1 census rows. -/
theorem fam_2_1194 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 24, 28, 32, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨3, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 24, 28, 32, 56]) (e := 13) (k := 3)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 24, 28, 34, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1195 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 24, 28, 34, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 24, 28, 34, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 24, 28, 44, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1196 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 24, 28, 44, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 24, 28, 44, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 24, 28, 54, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1197 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 24, 28, 54, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 24, 28, 54, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 28, 32, 34, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1198 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 28, 32, 34, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 28, 32, 34, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 28, 32, 46, 56]`, flank `13`, opening `2`.  Covers 1 census rows. -/
theorem fam_2_1199 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 28, 32, 46, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((13 : ℕ) : ℝ) k) :=
  ⟨2, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 28, 32, 46, 56]) (e := 13) (k := 2)
    (by norm_num) (by decide)⟩

/-- Differences `[2, 13, 15, 28, 34, 40, 56]`, flank `2`, opening `1`.  Covers 1 census rows. -/
theorem fam_2_1200 : ∃ k : ℕ, Lonely 8 (([2, 13, 15, 28, 34, 40, 56].map (Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 ((2 : ℕ) : ℝ) k) :=
  ⟨1, Flanks.lonely_of_band_list (n := 8) (L := [2, 13, 15, 28, 34, 40, 56]) (e := 2) (k := 1)
    (by norm_num) (by decide)⟩

end PinnedBatch2
