import Fresh.M4CertSound
import Fresh.M4FixResBank_v1
import Fresh.ReachUtcProof

/-!
# M4FixRung2_1_1_1_2_4_6_8: per-box M4 certificate transcription, box (1, 1, 1, 2, 4, 6, 8)

Written 2026-11-20 by `m4fix_gen_v1.py` from the per-box reconstruction
(`experiments/n8/m4fix_recon_v1.py`, [T]-verified against both checkpoint artifacts
(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the
CONSTRUCTED record `Fresh.M4FixResBank_v1.m4res_1_1_1_2_4_6_8`).  No existing file is edited.

This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a
WHOLE certificate FOREST: all 2 nodes of the box's reconstructed DFS certificate
tree(s) -- 1 internal, 0 reach-prune leaves,
1 dead-end leaves, 1 start-zone root(s) -- transcribed as literal `DfsCert` data: tables as
49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,
seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,
and the composed theorems through the GENERIC data connection
(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).

OWED (named, not discharged by any existing artifact):
* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`'s header: the E810 strict-monotone
  opening side (hypothesis-identity stub here, as in rung 1).
-/

namespace Fresh.M4FixRung2_1_1_1_2_4_6_8

open Fresh.FilterAssembly Fresh.UClosure Fresh.MechDataBatch Fresh.M4Cert

-- the 49-point propagation checks and the interval splits need headroom
set_option maxHeartbeats 4000000

/-- The `uAdd` rejection: keep-cur ground-false and the back-check ground-true, verbatim
`uAdd`'s two `if`s. -/
theorem uAdd_eq_none {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = true) :
    uAdd U i j c s = none := by
  unfold uAdd
  rw [if_neg (by simp [hK]), if_pos (by simp [hB])]

/-- The keep-current survival: the stored bound is already tighter, the table unchanged. -/
theorem uAdd_eq_some_self {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hK : uKeepCur U i j c s = true) : uAdd U i j c s = some U := by
  unfold uAdd
  rw [if_pos (by simp [hK])]

/-- The propagation assembly: keep-cur and back checks ground-false, the propagated
table is the transcribed one pointwise (local copy of `Fresh.ChainDomBase.uAdd_eq_some`;
that file's namespace is not opened here). -/
theorem uAdd_eq_some {U V : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = false)
    (hpt : ∀ p q, uProp U i j c s p q = V p q) : uAdd U i j c s = some V := by
  unfold uAdd
  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]
  exact congrArg some (funext fun p => funext fun q => hpt p q)

/-- A step whose first `uGt` fails. -/
theorem uStep_eq_none_left {U : UTable} {a b : Fin 7} {Aex A B : ℚ} (hAex : 0 < Aex)
    (hA : 0 < A) (h : uAdd U a b (Aex / A) true = none) : uStep U a b Aex A B = none := by
  unfold uStep
  rw [uGt_pos U a b hAex hA, h]
  rfl

/-- A step whose second `uGt` fails on the surviving table. -/
theorem uStep_eq_none_right {U V : UTable} {a b : Fin 7} {Aex A B : ℚ} (hAex : 0 < Aex)
    (hA : 0 < A) (hB : 0 < B) (h1 : uAdd U a b (Aex / A) true = some V)
    (h2 : uAdd V b a (B / Aex) true = none) : uStep U a b Aex A B = none := by
  unfold uStep
  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]

/-- A surviving step is its two `uAdd`s (`uGt_pos` twice). -/
theorem uStep_eq_some' {U V W : UTable} {a b : Fin 7} {Aex A B : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (h1 : uAdd U a b (Aex / A) true = some V) (h2 : uAdd V b a (B / Aex) true = some W) :
    uStep U a b Aex A B = some W := by
  show (uGt U Aex a A b).bind (fun V => uGt V B b Aex a) = some W
  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]

/-- The zone bound: `(8j-1)/hi < 7` with `hi > 0` gives `8j-1 < 7·hi` over ℚ. -/
theorem lt_of_zone {hi : ℚ} {j : ℕ} (hpos : 0 < hi)
    (hzone : (((8 * j - 1 : ℕ) : ℚ) : ℝ) / (hi : ℝ) < 7) :
    ((8 * j - 1 : ℕ) : ℚ) < 7 * hi := by
  have h2 : (((8 * j - 1 : ℕ) : ℚ) : ℝ) < (7 : ℝ) * (hi : ℝ) :=
    (div_lt_iff₀ (by exact_mod_cast hpos)).mp hzone
  exact_mod_cast h2

#print axioms uAdd_eq_none
#print axioms uAdd_eq_some_self
#print axioms uAdd_eq_some
#print axioms uStep_eq_none_left
#print axioms uStep_eq_none_right
#print axioms uStep_eq_some'
#print axioms lt_of_zone

/-! ## 1. The forest tables, node states and certificate literals (verbatim data) -/

/-- Table of DFS node 0 (internal, depth 1, last reading row 6, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 3 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 11 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 11 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((5 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((5 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 11 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 11 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl0_c_0_0 : tbl0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_0_1 : tbl0 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_2 : tbl0 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_3 : tbl0 (0 : Fin 7) (3 : Fin 7) = some ((2 / 3 : ℚ), false) := rfl
theorem tbl0_c_0_4 : tbl0 (0 : Fin 7) (4 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl0_c_0_5 : tbl0 (0 : Fin 7) (5 : Fin 7) = some ((2 / 11 : ℚ), false) := rfl
theorem tbl0_c_0_6 : tbl0 (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl0_c_1_0 : tbl0 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_1_1 : tbl0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_1_2 : tbl0 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_1_3 : tbl0 (1 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_1_4 : tbl0 (1 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl0_c_1_5 : tbl0 (1 : Fin 7) (5 : Fin 7) = some ((3 / 11 : ℚ), true) := rfl
theorem tbl0_c_1_6 : tbl0 (1 : Fin 7) (6 : Fin 7) = some ((1 / 5 : ℚ), true) := rfl
theorem tbl0_c_2_0 : tbl0 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl0_c_2_1 : tbl0 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_2_2 : tbl0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_2_3 : tbl0 (2 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_2_4 : tbl0 (2 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl0_c_2_5 : tbl0 (2 : Fin 7) (5 : Fin 7) = some ((3 / 11 : ℚ), false) := rfl
theorem tbl0_c_2_6 : tbl0 (2 : Fin 7) (6 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl0_c_3_0 : tbl0 (3 : Fin 7) (0 : Fin 7) = some ((5 / 2 : ℚ), false) := rfl
theorem tbl0_c_3_1 : tbl0 (3 : Fin 7) (1 : Fin 7) = some ((5 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_2 : tbl0 (3 : Fin 7) (2 : Fin 7) = some ((5 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_3 : tbl0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_3_4 : tbl0 (3 : Fin 7) (4 : Fin 7) = some ((5 / 7 : ℚ), false) := rfl
theorem tbl0_c_3_5 : tbl0 (3 : Fin 7) (5 : Fin 7) = some ((5 / 11 : ℚ), false) := rfl
theorem tbl0_c_3_6 : tbl0 (3 : Fin 7) (6 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl0_c_4_0 : tbl0 (4 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl0_c_4_1 : tbl0 (4 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_2 : tbl0 (4 : Fin 7) (2 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_3 : tbl0 (4 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl0_c_4_4 : tbl0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_4_5 : tbl0 (4 : Fin 7) (5 : Fin 7) = some ((9 / 11 : ℚ), false) := rfl
theorem tbl0_c_4_6 : tbl0 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl0_c_5_0 : tbl0 (5 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl0_c_5_1 : tbl0 (5 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_2 : tbl0 (5 : Fin 7) (2 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_3 : tbl0 (5 : Fin 7) (3 : Fin 7) = some ((13 / 3 : ℚ), false) := rfl
theorem tbl0_c_5_4 : tbl0 (5 : Fin 7) (4 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl0_c_5_5 : tbl0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_5_6 : tbl0 (5 : Fin 7) (6 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl0_c_6_0 : tbl0 (6 : Fin 7) (0 : Fin 7) = some ((17 / 2 : ℚ), false) := rfl
theorem tbl0_c_6_1 : tbl0 (6 : Fin 7) (1 : Fin 7) = some ((17 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_2 : tbl0 (6 : Fin 7) (2 : Fin 7) = some ((17 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_3 : tbl0 (6 : Fin 7) (3 : Fin 7) = some ((17 / 3 : ℚ), false) := rfl
theorem tbl0_c_6_4 : tbl0 (6 : Fin 7) (4 : Fin 7) = some ((17 / 7 : ℚ), false) := rfl
theorem tbl0_c_6_5 : tbl0 (6 : Fin 7) (5 : Fin 7) = some ((17 / 11 : ℚ), false) := rfl
theorem tbl0_c_6_6 : tbl0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 1 (deadend, depth 2, last reading row 5, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 3 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((5 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((5 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 3 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((39 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl1_c_0_0 : tbl1 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_0_1 : tbl1 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_0_2 : tbl1 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_0_3 : tbl1 (0 : Fin 7) (3 : Fin 7) = some ((2 / 3 : ℚ), false) := rfl
theorem tbl1_c_0_4 : tbl1 (0 : Fin 7) (4 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl1_c_0_5 : tbl1 (0 : Fin 7) (5 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl1_c_0_6 : tbl1 (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl1_c_1_0 : tbl1 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl1_c_1_1 : tbl1 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_1_2 : tbl1 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_1_3 : tbl1 (1 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_1_4 : tbl1 (1 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl1_c_1_5 : tbl1 (1 : Fin 7) (5 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl1_c_1_6 : tbl1 (1 : Fin 7) (6 : Fin 7) = some ((1 / 5 : ℚ), true) := rfl
theorem tbl1_c_2_0 : tbl1 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl1_c_2_1 : tbl1 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl1_c_2_2 : tbl1 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_2_3 : tbl1 (2 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_2_4 : tbl1 (2 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl1_c_2_5 : tbl1 (2 : Fin 7) (5 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl1_c_2_6 : tbl1 (2 : Fin 7) (6 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl1_c_3_0 : tbl1 (3 : Fin 7) (0 : Fin 7) = some ((5 / 2 : ℚ), false) := rfl
theorem tbl1_c_3_1 : tbl1 (3 : Fin 7) (1 : Fin 7) = some ((5 / 2 : ℚ), true) := rfl
theorem tbl1_c_3_2 : tbl1 (3 : Fin 7) (2 : Fin 7) = some ((5 / 2 : ℚ), true) := rfl
theorem tbl1_c_3_3 : tbl1 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_3_4 : tbl1 (3 : Fin 7) (4 : Fin 7) = some ((5 / 7 : ℚ), false) := rfl
theorem tbl1_c_3_5 : tbl1 (3 : Fin 7) (5 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl1_c_3_6 : tbl1 (3 : Fin 7) (6 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl1_c_4_0 : tbl1 (4 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl1_c_4_1 : tbl1 (4 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl1_c_4_2 : tbl1 (4 : Fin 7) (2 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl1_c_4_3 : tbl1 (4 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl1_c_4_4 : tbl1 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_4_5 : tbl1 (4 : Fin 7) (5 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl1_c_4_6 : tbl1 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl1_c_5_0 : tbl1 (5 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl1_c_5_1 : tbl1 (5 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl1_c_5_2 : tbl1 (5 : Fin 7) (2 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl1_c_5_3 : tbl1 (5 : Fin 7) (3 : Fin 7) = some ((13 / 3 : ℚ), false) := rfl
theorem tbl1_c_5_4 : tbl1 (5 : Fin 7) (4 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl1_c_5_5 : tbl1 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_5_6 : tbl1 (5 : Fin 7) (6 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl1_c_6_0 : tbl1 (6 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl1_c_6_1 : tbl1 (6 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl1_c_6_2 : tbl1 (6 : Fin 7) (2 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl1_c_6_3 : tbl1 (6 : Fin 7) (3 : Fin 7) = some ((39 / 7 : ℚ), true) := rfl
theorem tbl1_c_6_4 : tbl1 (6 : Fin 7) (4 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl1_c_6_5 : tbl1 (6 : Fin 7) (5 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl1_c_6_6 : tbl1 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-! ## 1b. The node states and the certificate trees -/

/-- The start-zone root: DFS node 0 (depth 1, last reading row 6, exit numerator 9, frontier sup 6 / 5). -/
-- STANDING: DATA
def node0 : DfsNode := ⟨tbl0, (6 : Fin 7), (9 : ℚ), (6 / 5 : ℚ), {((6 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 1 (deadend, depth 2, last reading row 5, exit numerator 9): child of node 0 by the step (5, 7, 9). -/
-- STANDING: DATA
def node1 : DfsNode := ⟨tbl1, (5 : Fin 7), (9 : ℚ), (18 / 11 : ℚ), node0.seen ∪ {((5 : Fin 7), (9 : ℚ))}⟩

/-- The dead-end leaf, DFS node 1: no filter-passing step. -/
-- STANDING: DATA
def tree1 : DfsCert := DfsCert.deadend node1

def children0 : List DfsCert := [tree1]
/-- The subtree rooted at internal node 0: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree0 : DfsCert := DfsCert.node node0 children0

/-- The box's WHOLE certificate forest (1 start-zone root(s), 2 nodes),
transcribed verbatim from the reconstruction. -/
-- STANDING: DATA
def forest : List DfsCert := [tree0]

/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/

theorem nodeOK_0 : DfsNodeOK node0 := by
  show uExitOK tbl0 (6 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl0_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_0
theorem nodeOK_1 : DfsNodeOK node1 := by
  show uExitOK tbl1 (5 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl1_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_1

/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/

/-- Node 1's step (5, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_1_1 : uAdd tbl0 (6 : Fin 7) (5 : Fin 7) ((9 / 7 : ℚ)) true = some tbl1 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tbl1] <;> norm_num)

/-- Node 1's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_1_2 : uAdd tbl1 (5 : Fin 7) (6 : Fin 7) ((9 / 9 : ℚ)) true = some tbl1 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_5_6] <;> norm_num)

/-- Node 1's full step equation. -/
theorem stepEq_1 : uStep tbl0 (6 : Fin 7) (5 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1 addEq_1_2

/-- Node 1's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_1 : childState (boxN m4res_1_1_1_2_4_6_8) node0 (5 : Fin 7) (9 : ℚ) tbl1 = DfsCert.root tree1 :=
  by
    simp only [childState, DfsCert.root, tree1, node1]
    have hlo : dfsLo (boxN m4res_1_1_1_2_4_6_8) node0.U (5 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_2_4_6_8, node0, tbl0_c_0_5]
    norm_num [hlo]

#print axioms addEq_1_1
#print axioms addEq_1_2
#print axioms stepEq_1
#print axioms childEq_1

/-! ## 3b. The seam kills -/

/-- Seam-failure kills at node 1 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk1_seam_4_1 : uStep tbl1 (5 : Fin 7) (4 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl1_c_5_4] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl1_c_4_5] <;> norm_num


#print axioms sk1_seam_4_1

/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/

/-- The `match-completeness` at node 0: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_0 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_2_4_6_8) node0 b A B) : ∃ c ∈ children0, DfsMatch (boxN m4res_1_1_1_2_4_6_8) node0 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 2, M = ceil(7·hi) = 18)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (3 : Fin 7) = (5 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨3, by norm_num⟩ : Fin 7) = (5 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 18 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5 / 2 : ℚ)) ≤ (18 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (4 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨4, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (5 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨5, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact ⟨tree1, by simp [children0], tbl1, stepEq_1, childEq_1⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 7, M = ceil(7·hi) = 60)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (6 : Fin 7) = (17 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl0_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl0 (⟨6, by norm_num⟩ : Fin 7) = (17 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((17 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 60 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((17 / 2 : ℚ)) ≤ (60 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 1: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_1 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_2_4_6_8) node1 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 2, M = ceil(7·hi) = 18)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (3 : Fin 7) = (5 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨3, by norm_num⟩ : Fin 7) = (5 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 18 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5 / 2 : ℚ)) ≤ (18 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (4 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨4, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hseam sk1_seam_4_1
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (5 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨5, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (6 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_2_4_6_8, tbl1_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_2_4_6_8) tbl1 (⟨6, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


#print axioms enumMatch_0
#print axioms enumDead_1

/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/

theorem closed_1 : DfsClosed tree1 := by
  simp only [tree1, DfsClosed]
  exact nodeOK_1

#print axioms closed_1
theorem closed_0 : DfsClosed tree0 := by
  simp only [tree0, DfsClosed]
  refine ⟨nodeOK_0, ?_⟩
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_1
  · exact absurd ht'1 (by simp)

#print axioms closed_0

theorem enum_1 : DfsEnum (boxN m4res_1_1_1_2_4_6_8) tree1 := by
  simp only [tree1, DfsEnum]
  exact fun b A B hf => enumDead_1 b A B hf

#print axioms enum_1
theorem enum_0 : DfsEnum (boxN m4res_1_1_1_2_4_6_8) tree0 := by
  simp only [tree0, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_0 b A B hf, ?_⟩
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_1
  · exact absurd ht'1 (by simp)

#print axioms enum_0

/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_1 : DfsPruneDom tree1 := by
  simp only [tree1, DfsPruneDom]

#print axioms pd_1
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_0 : DfsPruneDom tree0 := by
  simp only [tree0, DfsPruneDom]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_1
  · exact absurd ht'1 (by simp)

#print axioms pd_0

/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions

VACUOUS for this box: the forest has no reach-prune leaves, so there are no
per-leaf `reach_utc` verdicts to transcribe (`DfsPruneDom` holds vacuously at the
dead-end leaves). -/

theorem pdZone_1 : DfsPruneDomZone (boxN m4res_1_1_1_2_4_6_8) tree1 := by
  simp only [tree1, DfsPruneDomZone]

#print axioms pdZone_1
theorem pdZone_0 : DfsPruneDomZone (boxN m4res_1_1_1_2_4_6_8) tree0 := by
  simp only [tree0, DfsPruneDomZone]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_1
  · exact absurd ht'1 (by simp)

#print axioms pdZone_0

/-! ## 6. The forest assemblies -/

/-- The FOREST is closed (the form the data connection consumes). -/
theorem hforestClosed : ∀ t ∈ forest, DfsClosed t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_0
  · exact absurd ht'1 (by simp)

/-- The FOREST enumerates. -/
theorem hforestEnum : ∀ t ∈ forest, DfsEnum (boxN m4res_1_1_1_2_4_6_8) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_0
  · exact absurd ht'1 (by simp)

/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly
OWED (b) -- VACUOUS here: the forest has no reach-prune leaves,
so this proof needs no hypotheses; at dead ends and internal nodes the condition is
inherited/vacuous. -/
theorem hforestPruneDom : ∀ t ∈ forest, DfsPruneDom t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_0
  · exact absurd ht'1 (by simp)

/-- The zone-form per-prune-leaf domination over the FOREST: at the reach-prune
leaves exactly OWED (b)'s zone-form remainder (the per-leaf zone-form stubs of
section 5b; the UNRESTRICTED form is false --
`Fresh.ReachUtcProof.unrestricted_false`). -/
theorem hforestPruneDomZone : ∀ t ∈ forest, DfsPruneDomZone (boxN m4res_1_1_1_2_4_6_8) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_0
  · exact absurd ht'1 (by simp)

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;
the artifacts give only the reconstructed root states, no opening-match record.
Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade
statement of E810's strict-monotone reading for this box. -/
-- STANDING: OWED
theorem m4fix_1_1_1_2_4_6_8_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_1_1_2_4_6_8) forest) :
    DfsRootAdm (boxN m4res_1_1_1_2_4_6_8) forest := hcadm

/-! ## 7. The census envelope and the composed theorems (generic data connection) -/

/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the
record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists
only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise
exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /
`m4boxClear_of_data` directly). -/
theorem hn17_1_1_1_2_4_6_8 : ∀ i : Fin 7, boxN m4res_1_1_1_2_4_6_8 i ≤ 17 := by
  intro i
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
    i.val = 6 := by
    have := i.isLt
    omega
  rcases hv with h | h | h | h | h | h | h
  · have e : i = ⟨0, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨1, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨2, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨3, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨4, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨5, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨6, by decide⟩ := Fin.ext h; subst e; decide

#print axioms hn17_1_1_1_2_4_6_8

/-- **The composed certificate theorem**: the banked record (`m4resData_1_1_1_2_4_6_8`,
[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the
90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim.  The
per-prune-leaf domination hypotheses are the reach_utc projection instances
(`hproj_<l> : reachutcProj_1_1_1_2_4_6_8_<l>`, OWED (b)'s per-leaf remainder); the verdict side
of each leaf is discharged inside `m4fix_1_1_1_2_4_6_8_pruneDom_<l>` from the transcribed
`reachutc_1_1_1_2_4_6_8.json` verdicts. -/
theorem m4fix_1_1_1_2_4_6_8_cert (hcadm : DfsRootAdm (boxN m4res_1_1_1_2_4_6_8) forest) :
    M4CertSound (boxN m4res_1_1_1_2_4_6_8) ∧
      ∀ k ∈ m4res_1_1_1_2_4_6_8.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  ⟨m4CertSound_of_forest_zone (boxN m4res_1_1_1_2_4_6_8) forest hforestClosed hforestEnum
    hforestPruneDomZone hcadm, leafKeys_env90 m4res_1_1_1_2_4_6_8 m4resData_1_1_1_2_4_6_8⟩

/-- **The composed clear-point theorem (the scaling target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --
the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest
instead of a crown. -/
theorem m4fix_1_1_1_2_4_6_8_boxClear (hcadm : DfsRootAdm (boxN m4res_1_1_1_2_4_6_8) forest)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_1_1_2_4_6_8) hn17_1_1_1_2_4_6_8)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_1_1_2_4_6_8) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_1_1_2_4_6_8) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_cert hn17_1_1_1_2_4_6_8 hcc
    (m4CertSound_of_forest_zone (boxN m4res_1_1_1_2_4_6_8) forest hforestClosed hforestEnum hforestPruneDomZone hcadm)
    g hface

#print axioms m4fix_1_1_1_2_4_6_8_cert
#print axioms m4fix_1_1_1_2_4_6_8_boxClear

end Fresh.M4FixRung2_1_1_1_2_4_6_8

