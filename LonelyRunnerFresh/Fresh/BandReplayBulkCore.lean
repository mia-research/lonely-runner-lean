import Fresh.BandNoCarve

/-!
# The band-bulk compressed template (Track B): one decide-backed table instead of
per-box instances

Written 2026-11-21.  New file; nothing existing is edited.  This is the compression
E916 named as the fix for the compile-bound band bulk (the faithful per-box projection
for `[25,41)` was ≈ 70 h at the measured 0.253 s/box): instead of one per-box theorem
per root, ONE row record per root is emitted as Lean data and the per-row certificate
condition is discharged ONCE per table chunk by kernel `decide` — the
`Fresh.MechDataBatch.M4ResData` pattern (a table decides the per-record case).

## Row semantics (the `[25,29)` D = 1 fixed-R0 re-dump, `bandrep_r0dump_v1.py`)

A row is one exact-certified root of the E916 r0 instrument: the cell 6-tuple
`k = (k1..k6)` over ρ₂..ρ₇ (`k6 ∈ [25,29)`, depth D = 1), the scaled clear point
`R₀ = r / bulkBASE` (`bulkBASE = 2^20`, `r = ceil(lo·bulkBASE)` at the root's lowest
feasible interval `[lo, hi]`), and the per-reading gap indices `j1..j6` with

  `(8·j_i + 1)·bulkBASE ≤ r·k_i`  and  `r·(k_i + 1) ≤ (8·j_i + 7)·bulkBASE`.

The E832 Lean convention (`Fresh.Certs.FixedClearCert`) pins the seventh reading
ρ₁ = 1 (`lo 0 = hi 0 = 1`, `j 0 = 0`), so a row is a genuine `BandFixedR0` certificate
exactly when additionally `bulkBASE ≤ r ≤ 7·bulkBASE` (i.e. `R₀ ∈ [1,7]`; `j 0 = 0` is
then forced).  Honest census (E916's 555,170 exact-certified roots reproduced
bit-for-bit by `bandrep_r0dump_v1.py`): 83,641 rows are ρ₁-pinned-valid; the other
471,529 have `R₀ < 1` and their `R₀·1` lies in no closed gap `[8j+1, 8j+7]` of the
pinned reading — they are 6-reading-feasible but NOT `BandFixedR0` instances (the
schema-2 window-type layer is what E833 used for these bands; named residue).

## The compressed theorem

`bandBulk_of_rowOK` builds the `FixedClearCert` from a row + `rowOK`; the emitted
table files (`Fresh/BandReplayBulkT1.lean`, `Fresh/BandReplayBulkCompressed.lean`)
prove `rowOK` for every table row by one `decide` per chunk and compose the
membership form: any row of the table certifies every arrangement in its cell box.
Nothing existing is edited.
-/

namespace Fresh.BandNoCarve

/-- The row scale `2^20` (the r0 instrument's `base`; `R₀ = r / bulkBASE`). -/
def bulkBASE : ℤ := 1048576

/-- One bulk row: the root's cell 6-tuple over ρ₂..ρ₇ at depth D = 1, the scaled clear
point `r` (`R₀ = r / bulkBASE`), and the per-reading gap indices `j1..j6`. -/
structure BulkRow where
  k1 : ℤ
  k2 : ℤ
  k3 : ℤ
  k4 : ℤ
  k5 : ℤ
  k6 : ℤ
  r : ℤ
  j1 : ℤ
  j2 : ℤ
  j3 : ℤ
  j4 : ℤ
  j5 : ℤ
  j6 : ℤ

/-- The row's seven cell tuple in Lean index order (ρ₁ pinned to cell 1 at D = 1, so
the pinned face is the single point `[1, 1]`; ρ₂..ρ₇ carry the root's cells). -/
def rowK (row : BulkRow) : Fin 7 → ℤ := ![1, row.k1, row.k2, row.k3, row.k4, row.k5, row.k6]

/-- The row's seven gap indices (`j 0 = 0`: the pinned ρ₁ = 1 reading sits in the
first gap whenever `R₀ ∈ [1,7]`). -/
def rowJ (row : BulkRow) : Fin 7 → ℤ := ![0, row.j1, row.j2, row.j3, row.j4, row.j5, row.j6]

/-- The row's box faces at D = 1: `[k_i, k_i + 1]` per reading (ρ₁ pinned to 1). -/
def rowLo (row : BulkRow) : Fin 7 → ℝ := fun i => ((rowK row i : ℤ) : ℝ)

/-- The row's upper cell tuple (ρ₁ pinned: the upper face at index 0 is also 1, the
single point `[1, 1]`; ρ₂..ρ₇ carry `k_i + 1`). -/
def rowHiK (row : BulkRow) : Fin 7 → ℤ :=
  ![1, row.k1 + 1, row.k2 + 1, row.k3 + 1, row.k4 + 1, row.k5 + 1, row.k6 + 1]

/-- The row's box faces at D = 1, upper. -/
def rowHi (row : BulkRow) : Fin 7 → ℝ := fun i => ((rowHiK row i : ℤ) : ℝ)

/-- The row's cell tuple is dominated by its upper cell tuple (indexwise). -/
theorem rowK_le_rowHiK (row : BulkRow) (i : Fin 7) : rowK row i ≤ rowHiK row i := by
  fin_cases i <;>
    norm_num [rowK, rowHiK, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> omega

/-- **The row certificate condition** — everything the r0 instrument certifies about one
root, in the seven-reading Lean form: ρ₁ pinned (`R₀ ∈ [1,7]`, gap 0), and the two
integer faces per cell reading ρ₂..ρ₇ (E832 item 1's `FixedClearIntCond` restricted to
the cell readings, D = 1, base = `bulkBASE`). -/
def rowOK (row : BulkRow) : Prop :=
  bulkBASE ≤ row.r ∧ row.r ≤ 7 * bulkBASE ∧
  (8 * row.j1 + 1) * bulkBASE ≤ row.r * row.k1 ∧
    row.r * (row.k1 + 1) ≤ (8 * row.j1 + 7) * bulkBASE ∧
  (8 * row.j2 + 1) * bulkBASE ≤ row.r * row.k2 ∧
    row.r * (row.k2 + 1) ≤ (8 * row.j2 + 7) * bulkBASE ∧
  (8 * row.j3 + 1) * bulkBASE ≤ row.r * row.k3 ∧
    row.r * (row.k3 + 1) ≤ (8 * row.j3 + 7) * bulkBASE ∧
  (8 * row.j4 + 1) * bulkBASE ≤ row.r * row.k4 ∧
    row.r * (row.k4 + 1) ≤ (8 * row.j4 + 7) * bulkBASE ∧
  (8 * row.j5 + 1) * bulkBASE ≤ row.r * row.k5 ∧
    row.r * (row.k5 + 1) ≤ (8 * row.j5 + 7) * bulkBASE ∧
  (8 * row.j6 + 1) * bulkBASE ≤ row.r * row.k6 ∧
    row.r * (row.k6 + 1) ≤ (8 * row.j6 + 7) * bulkBASE

/-- The computable row condition (the per-row `decide` target; the hand-built Bool
mirror of `rowOK` — the `Fresh.MechDataBatch.InLeafEnvB` pattern). -/
def rowOKB (row : BulkRow) : Bool :=
  bulkBASE ≤ row.r && row.r ≤ 7 * bulkBASE &&
  (8 * row.j1 + 1) * bulkBASE ≤ row.r * row.k1 &&
    row.r * (row.k1 + 1) ≤ (8 * row.j1 + 7) * bulkBASE &&
  (8 * row.j2 + 1) * bulkBASE ≤ row.r * row.k2 &&
    row.r * (row.k2 + 1) ≤ (8 * row.j2 + 7) * bulkBASE &&
  (8 * row.j3 + 1) * bulkBASE ≤ row.r * row.k3 &&
    row.r * (row.k3 + 1) ≤ (8 * row.j3 + 7) * bulkBASE &&
  (8 * row.j4 + 1) * bulkBASE ≤ row.r * row.k4 &&
    row.r * (row.k4 + 1) ≤ (8 * row.j4 + 7) * bulkBASE &&
  (8 * row.j5 + 1) * bulkBASE ≤ row.r * row.k5 &&
    row.r * (row.k5 + 1) ≤ (8 * row.j5 + 7) * bulkBASE &&
  (8 * row.j6 + 1) * bulkBASE ≤ row.r * row.k6 &&
    row.r * (row.k6 + 1) ≤ (8 * row.j6 + 7) * bulkBASE

/-- The Bool/Prop bridge for the row condition. -/
theorem rowOKB_iff (row : BulkRow) : rowOKB row = true ↔ rowOK row := by
  simp only [rowOKB, Bool.and_eq_true, decide_eq_true_eq, rowOK]
  tauto

#print axioms rowOKB_iff

/-- The `rowOK` predicate is decidable (the kernel's per-row decide target for the
worked examples; the table chunks decide `rowOKB` directly). -/
instance instDecidableRowOK (row : BulkRow) : Decidable (rowOK row) := by
  unfold rowOK
  infer_instance

/-- **The row certificate**: a row satisfying `rowOK` builds the E832 `FixedClearCert`
with faces `[k_i, k_i+1]` (D = 1), ρ₁ pinned to the single point 1, and `R₀ = r /
bulkBASE`.  This is the compressed replacement of the per-box
`fixedClearCert_of_dyadic_int` instantiation. -/
noncomputable def certOfRow (row : BulkRow) (h : rowOK row) : Fresh.Certs.FixedClearCert where
  lo := rowLo row
  hi := rowHi row
  R₀ := (row.r : ℝ) / (bulkBASE : ℝ)
  j := rowJ row
  hR₁ := by
    obtain ⟨h1, -, -⟩ := h
    have hB : (0 : ℝ) < (bulkBASE : ℝ) := by norm_num [bulkBASE]
    have hr : (1 : ℝ) * (bulkBASE : ℝ) ≤ (row.r : ℝ) := by
      rw [one_mul]
      exact_mod_cast h1
    exact (le_div_iff₀ hB).mpr hr
  hR₇ := by
    obtain ⟨-, h2, -⟩ := h
    have hB : (0 : ℝ) < (bulkBASE : ℝ) := by norm_num [bulkBASE]
    have hr : (row.r : ℝ) ≤ 7 * (bulkBASE : ℝ) := by exact_mod_cast h2
    exact (div_le_iff₀ hB).mpr hr
  hface := by
    intro i
    show ((rowK row i : ℤ) : ℝ) ≤ ((rowHiK row i : ℤ) : ℝ)
    exact_mod_cast rowK_le_rowHiK row i
  hgap := by
    intro i
    obtain ⟨h1, h2, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, h5a, h5b, h6a, h6b⟩ := h
    have hB : (0 : ℝ) < (bulkBASE : ℝ) := by norm_num [bulkBASE]
    fin_cases i
    · -- i = 0: ρ₁ pinned to 1, gap 0: 1 ≤ R₀ ≤ 7
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      refine ⟨(le_div_iff₀ hB).mpr ?_, (div_le_iff₀ hB).mpr ?_⟩
      · exact_mod_cast h1
      · exact_mod_cast h2
    · -- i = 1 (ρ₂)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h1a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h1b
    · -- i = 2 (ρ₃)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h2a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h2b
    · -- i = 3 (ρ₄)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h3a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h3b
    · -- i = 4 (ρ₅)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h4a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h4b
    · -- i = 5 (ρ₆)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h5a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h5b
    · -- i = 6 (ρ₇)
      norm_num [rowJ, rowK, rowHiK, rowLo, rowHi, Matrix.cons_val_zero, Matrix.cons_val_succ]
      constructor
      · rw [div_mul_eq_mul_div]
        refine (le_div_iff₀ hB).mpr ?_
        exact_mod_cast h6a
      · rw [div_mul_eq_mul_div]
        refine (div_le_iff₀ hB).mpr ?_
        exact_mod_cast h6b

#print axioms certOfRow

/-- **The compressed band-bulk theorem (row form)**: a row satisfying `rowOK` certifies
every arrangement in its cell box — schema class 1 (`BandFixedR0`) directly. -/
theorem bandBulk_of_rowOK (row : BulkRow) (h : rowOK row) {g : Fin 7 → ℝ}
    (hbox : ∀ i, rowLo row i ≤ g i ∧ g i ≤ rowHi row i) : BandFixedR0 g :=
  ⟨certOfRow row h, hbox⟩

#print axioms bandBulk_of_rowOK

/-- **The compressed band-bulk theorem (tuple-membership form)**: a cell tuple + clear
point appearing in a table certifies every arrangement in its cell box.  This is the
`InBulkBand`-membership form of the compression: the table lookup is the hypothesis,
the per-root certificate is decided once for the whole table.  `hrow` is the
decide-discharged table theorem (`rowOKB_iff` + `List.all_eq_true`), so the table file
emits only data + one `decide` per chunk. -/
theorem bandBulk_of_mem {row : BulkRow} (hrow : rowOKB row = true) {g : Fin 7 → ℝ}
    (hbox : ∀ i, rowLo row i ≤ g i ∧ g i ≤ rowHi row i) : BandFixedR0 g :=
  bandBulk_of_rowOK row ((rowOKB_iff row).mp hrow) hbox

#print axioms bandBulk_of_mem

end Fresh.BandNoCarve
