import Fresh.M4CertSound

/-!
# M4CertRung2_1_3_10_12_13_15_16: per-box M4 certificate transcription, box (1, 3, 10, 12, 13, 15, 16)

Written 2026-11-20 by `m4rung2_gen_v1.py` from the per-box reconstruction
(`experiments/n8/m4rung2_recon_v1.py`, [T]-verified against both checkpoint artifacts
(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the banked record
`Fresh.MechDataBatch.m4res_1_3_10_12_13_15_16`).  No existing file is edited.

This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a
WHOLE certificate FOREST: all 27 nodes of the box's reconstructed DFS certificate
tree(s) -- 19 internal, 6 reach-prune leaves,
2 dead-end leaves, 2 start-zone root(s) -- transcribed as literal `DfsCert` data: tables as
49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,
seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,
and the composed theorems through the GENERIC data connection
(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).

OWED (named, not discharged by any existing artifact):
* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`'s header: the E810 strict-monotone
  opening side (hypothesis-identity stub here, as in rung 1).
* `DfsPruneDom tree4` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
* `DfsPruneDom tree7` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
* `DfsPruneDom tree8` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
* `DfsPruneDom tree11` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
* `DfsPruneDom tree18` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
* `DfsPruneDom tree23` at the reach-prune leaf -- OWED (b): the per-leaf
  `reach_utc` domination; no per-leaf state-graph dump exists in the artifacts.
-/

namespace Fresh.M4CertRung2_1_3_10_12_13_15_16

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

/-- Table of DFS node 0 (internal, depth 1, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((21 / 25 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 6 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((31 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((31 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((31 / 19 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((31 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((31 / 25 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 25 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl0_c_0_0 : tbl0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_0_1 : tbl0 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl0_c_0_2 : tbl0 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl0_c_0_3 : tbl0 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl0_c_0_4 : tbl0 (0 : Fin 7) (4 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl0_c_0_5 : tbl0 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl0_c_0_6 : tbl0 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl0_c_1_0 : tbl0 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl0_c_1_1 : tbl0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_1_2 : tbl0 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl0_c_1_3 : tbl0 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl0_c_1_4 : tbl0 (1 : Fin 7) (4 : Fin 7) = some ((7 / 25 : ℚ), false) := rfl
theorem tbl0_c_1_5 : tbl0 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl0_c_1_6 : tbl0 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl0_c_2_0 : tbl0 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl0_c_2_1 : tbl0 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl0_c_2_2 : tbl0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_2_3 : tbl0 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl0_c_2_4 : tbl0 (2 : Fin 7) (4 : Fin 7) = some ((21 / 25 : ℚ), false) := rfl
theorem tbl0_c_2_5 : tbl0 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl0_c_2_6 : tbl0 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl0_c_3_0 : tbl0 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl0_c_3_1 : tbl0 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl0_c_3_2 : tbl0 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl0_c_3_3 : tbl0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_3_4 : tbl0 (3 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_3_5 : tbl0 (3 : Fin 7) (5 : Fin 7) = some ((5 / 6 : ℚ), true) := rfl
theorem tbl0_c_3_6 : tbl0 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl0_c_4_0 : tbl0 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl0_c_4_1 : tbl0 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl0_c_4_2 : tbl0 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl0_c_4_3 : tbl0 (4 : Fin 7) (3 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl0_c_4_4 : tbl0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_4_5 : tbl0 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl0_c_4_6 : tbl0 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl0_c_5_0 : tbl0 (5 : Fin 7) (0 : Fin 7) = some ((31 / 2 : ℚ), false) := rfl
theorem tbl0_c_5_1 : tbl0 (5 : Fin 7) (1 : Fin 7) = some ((31 / 5 : ℚ), false) := rfl
theorem tbl0_c_5_2 : tbl0 (5 : Fin 7) (2 : Fin 7) = some ((31 / 19 : ℚ), false) := rfl
theorem tbl0_c_5_3 : tbl0 (5 : Fin 7) (3 : Fin 7) = some ((31 / 23 : ℚ), false) := rfl
theorem tbl0_c_5_4 : tbl0 (5 : Fin 7) (4 : Fin 7) = some ((31 / 25 : ℚ), false) := rfl
theorem tbl0_c_5_5 : tbl0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_5_6 : tbl0 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_6_0 : tbl0 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl0_c_6_1 : tbl0 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl0_c_6_2 : tbl0 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl0_c_6_3 : tbl0 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl0_c_6_4 : tbl0 (6 : Fin 7) (4 : Fin 7) = some ((33 / 25 : ℚ), false) := rfl
theorem tbl0_c_6_5 : tbl0 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl0_c_6_6 : tbl0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 1 (internal, depth 2, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 18 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 6 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 115 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 155 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl1_c_0_0 : tbl1 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_0_1 : tbl1 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl1_c_0_2 : tbl1 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl1_c_0_3 : tbl1 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl1_c_0_4 : tbl1 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl1_c_0_5 : tbl1 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl1_c_0_6 : tbl1 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl1_c_1_0 : tbl1 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl1_c_1_1 : tbl1 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_1_2 : tbl1 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl1_c_1_3 : tbl1 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl1_c_1_4 : tbl1 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl1_c_1_5 : tbl1 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl1_c_1_6 : tbl1 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl1_c_2_0 : tbl1 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl1_c_2_1 : tbl1 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl1_c_2_2 : tbl1 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_2_3 : tbl1 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl1_c_2_4 : tbl1 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl1_c_2_5 : tbl1 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl1_c_2_6 : tbl1 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl1_c_3_0 : tbl1 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl1_c_3_1 : tbl1 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl1_c_3_2 : tbl1 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl1_c_3_3 : tbl1 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_3_4 : tbl1 (3 : Fin 7) (4 : Fin 7) = some ((17 / 18 : ℚ), true) := rfl
theorem tbl1_c_3_5 : tbl1 (3 : Fin 7) (5 : Fin 7) = some ((5 / 6 : ℚ), true) := rfl
theorem tbl1_c_3_6 : tbl1 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl1_c_4_0 : tbl1 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl1_c_4_1 : tbl1 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl1_c_4_2 : tbl1 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl1_c_4_3 : tbl1 (4 : Fin 7) (3 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl1_c_4_4 : tbl1 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_4_5 : tbl1 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl1_c_4_6 : tbl1 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl1_c_5_0 : tbl1 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl1_c_5_1 : tbl1 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl1_c_5_2 : tbl1 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl1_c_5_3 : tbl1 (5 : Fin 7) (3 : Fin 7) = some ((153 / 115 : ℚ), true) := rfl
theorem tbl1_c_5_4 : tbl1 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl1_c_5_5 : tbl1 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_5_6 : tbl1 (5 : Fin 7) (6 : Fin 7) = some ((153 / 155 : ℚ), true) := rfl
theorem tbl1_c_6_0 : tbl1 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl1_c_6_1 : tbl1 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl1_c_6_2 : tbl1 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl1_c_6_3 : tbl1 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl1_c_6_4 : tbl1 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl1_c_6_5 : tbl1 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl1_c_6_6 : tbl1 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 2 (internal, depth 3, last reading row 3, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 18 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 6 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 155 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl2_c_0_0 : tbl2 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_0_1 : tbl2 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl2_c_0_2 : tbl2 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl2_c_0_3 : tbl2 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl2_c_0_4 : tbl2 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl2_c_0_5 : tbl2 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl2_c_0_6 : tbl2 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl2_c_1_0 : tbl2 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl2_c_1_1 : tbl2 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_1_2 : tbl2 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl2_c_1_3 : tbl2 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl2_c_1_4 : tbl2 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl2_c_1_5 : tbl2 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl2_c_1_6 : tbl2 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl2_c_2_0 : tbl2 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl2_c_2_1 : tbl2 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl2_c_2_2 : tbl2 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_2_3 : tbl2 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl2_c_2_4 : tbl2 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl2_c_2_5 : tbl2 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl2_c_2_6 : tbl2 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl2_c_3_0 : tbl2 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl2_c_3_1 : tbl2 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl2_c_3_2 : tbl2 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl2_c_3_3 : tbl2 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_3_4 : tbl2 (3 : Fin 7) (4 : Fin 7) = some ((17 / 18 : ℚ), true) := rfl
theorem tbl2_c_3_5 : tbl2 (3 : Fin 7) (5 : Fin 7) = some ((5 / 6 : ℚ), true) := rfl
theorem tbl2_c_3_6 : tbl2 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl2_c_4_0 : tbl2 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl2_c_4_1 : tbl2 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl2_c_4_2 : tbl2 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl2_c_4_3 : tbl2 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl2_c_4_4 : tbl2 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_4_5 : tbl2 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl2_c_4_6 : tbl2 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl2_c_5_0 : tbl2 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl2_c_5_1 : tbl2 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl2_c_5_2 : tbl2 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl2_c_5_3 : tbl2 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl2_c_5_4 : tbl2 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl2_c_5_5 : tbl2 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_5_6 : tbl2 (5 : Fin 7) (6 : Fin 7) = some ((153 / 155 : ℚ), true) := rfl
theorem tbl2_c_6_0 : tbl2 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl2_c_6_1 : tbl2 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl2_c_6_2 : tbl2 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl2_c_6_3 : tbl2 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl2_c_6_4 : tbl2 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl2_c_6_5 : tbl2 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl2_c_6_6 : tbl2 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 3 (internal, depth 4, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 50625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((34391 / 101250 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((119 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 155 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 150 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 375 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2325 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((34391 / 2250 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((34391 / 5625 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 34875 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 33750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl3_c_0_0 : tbl3 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_0_1 : tbl3 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl3_c_0_2 : tbl3 (0 : Fin 7) (2 : Fin 7) = some ((4913 / 50625 : ℚ), true) := rfl
theorem tbl3_c_0_3 : tbl3 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl3_c_0_4 : tbl3 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl3_c_0_5 : tbl3 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl3_c_0_6 : tbl3 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl3_c_1_0 : tbl3 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl3_c_1_1 : tbl3 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_1_2 : tbl3 (1 : Fin 7) (2 : Fin 7) = some ((34391 / 101250 : ℚ), true) := rfl
theorem tbl3_c_1_3 : tbl3 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl3_c_1_4 : tbl3 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl3_c_1_5 : tbl3 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl3_c_1_6 : tbl3 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl3_c_2_0 : tbl3 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl3_c_2_1 : tbl3 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl3_c_2_2 : tbl3 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_2_3 : tbl3 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl3_c_2_4 : tbl3 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl3_c_2_5 : tbl3 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl3_c_2_6 : tbl3 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl3_c_3_0 : tbl3 (3 : Fin 7) (0 : Fin 7) = some ((119 / 10 : ℚ), true) := rfl
theorem tbl3_c_3_1 : tbl3 (3 : Fin 7) (1 : Fin 7) = some ((119 / 25 : ℚ), true) := rfl
theorem tbl3_c_3_2 : tbl3 (3 : Fin 7) (2 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl3_c_3_3 : tbl3 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_3_4 : tbl3 (3 : Fin 7) (4 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl3_c_3_5 : tbl3 (3 : Fin 7) (5 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl3_c_3_6 : tbl3 (3 : Fin 7) (6 : Fin 7) = some ((119 / 155 : ℚ), true) := rfl
theorem tbl3_c_4_0 : tbl3 (4 : Fin 7) (0 : Fin 7) = some ((2023 / 150 : ℚ), true) := rfl
theorem tbl3_c_4_1 : tbl3 (4 : Fin 7) (1 : Fin 7) = some ((2023 / 375 : ℚ), true) := rfl
theorem tbl3_c_4_2 : tbl3 (4 : Fin 7) (2 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl3_c_4_3 : tbl3 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl3_c_4_4 : tbl3 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_4_5 : tbl3 (4 : Fin 7) (5 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl3_c_4_6 : tbl3 (4 : Fin 7) (6 : Fin 7) = some ((2023 / 2325 : ℚ), true) := rfl
theorem tbl3_c_5_0 : tbl3 (5 : Fin 7) (0 : Fin 7) = some ((34391 / 2250 : ℚ), true) := rfl
theorem tbl3_c_5_1 : tbl3 (5 : Fin 7) (1 : Fin 7) = some ((34391 / 5625 : ℚ), true) := rfl
theorem tbl3_c_5_2 : tbl3 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3375 : ℚ), true) := rfl
theorem tbl3_c_5_3 : tbl3 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl3_c_5_4 : tbl3 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl3_c_5_5 : tbl3 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_5_6 : tbl3 (5 : Fin 7) (6 : Fin 7) = some ((34391 / 34875 : ℚ), true) := rfl
theorem tbl3_c_6_0 : tbl3 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl3_c_6_1 : tbl3 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl3_c_6_2 : tbl3 (6 : Fin 7) (2 : Fin 7) = some ((54043 / 33750 : ℚ), true) := rfl
theorem tbl3_c_6_3 : tbl3 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl3_c_6_4 : tbl3 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl3_c_6_5 : tbl3 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl3_c_6_6 : tbl3 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 4 (reach, depth 5, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 50625 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((34391 / 101250 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((119 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 155 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 150 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 375 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2325 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((34391 / 2250 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((34391 / 5625 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 34875 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 33750 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl4_c_0_0 : tbl4 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_0_1 : tbl4 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl4_c_0_2 : tbl4 (0 : Fin 7) (2 : Fin 7) = some ((4913 / 50625 : ℚ), true) := rfl
theorem tbl4_c_0_3 : tbl4 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl4_c_0_4 : tbl4 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl4_c_0_5 : tbl4 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl4_c_0_6 : tbl4 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl4_c_1_0 : tbl4 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl4_c_1_1 : tbl4 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_1_2 : tbl4 (1 : Fin 7) (2 : Fin 7) = some ((34391 / 101250 : ℚ), true) := rfl
theorem tbl4_c_1_3 : tbl4 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl4_c_1_4 : tbl4 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl4_c_1_5 : tbl4 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl4_c_1_6 : tbl4 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl4_c_2_0 : tbl4 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl4_c_2_1 : tbl4 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl4_c_2_2 : tbl4 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_2_3 : tbl4 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl4_c_2_4 : tbl4 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl4_c_2_5 : tbl4 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl4_c_2_6 : tbl4 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl4_c_3_0 : tbl4 (3 : Fin 7) (0 : Fin 7) = some ((119 / 10 : ℚ), true) := rfl
theorem tbl4_c_3_1 : tbl4 (3 : Fin 7) (1 : Fin 7) = some ((119 / 25 : ℚ), true) := rfl
theorem tbl4_c_3_2 : tbl4 (3 : Fin 7) (2 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl4_c_3_3 : tbl4 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_3_4 : tbl4 (3 : Fin 7) (4 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl4_c_3_5 : tbl4 (3 : Fin 7) (5 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl4_c_3_6 : tbl4 (3 : Fin 7) (6 : Fin 7) = some ((119 / 155 : ℚ), true) := rfl
theorem tbl4_c_4_0 : tbl4 (4 : Fin 7) (0 : Fin 7) = some ((2023 / 150 : ℚ), true) := rfl
theorem tbl4_c_4_1 : tbl4 (4 : Fin 7) (1 : Fin 7) = some ((2023 / 375 : ℚ), true) := rfl
theorem tbl4_c_4_2 : tbl4 (4 : Fin 7) (2 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl4_c_4_3 : tbl4 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl4_c_4_4 : tbl4 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_4_5 : tbl4 (4 : Fin 7) (5 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl4_c_4_6 : tbl4 (4 : Fin 7) (6 : Fin 7) = some ((2023 / 2325 : ℚ), true) := rfl
theorem tbl4_c_5_0 : tbl4 (5 : Fin 7) (0 : Fin 7) = some ((34391 / 2250 : ℚ), true) := rfl
theorem tbl4_c_5_1 : tbl4 (5 : Fin 7) (1 : Fin 7) = some ((34391 / 5625 : ℚ), true) := rfl
theorem tbl4_c_5_2 : tbl4 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3375 : ℚ), true) := rfl
theorem tbl4_c_5_3 : tbl4 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl4_c_5_4 : tbl4 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl4_c_5_5 : tbl4 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_5_6 : tbl4 (5 : Fin 7) (6 : Fin 7) = some ((34391 / 34875 : ℚ), true) := rfl
theorem tbl4_c_6_0 : tbl4 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl4_c_6_1 : tbl4 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl4_c_6_2 : tbl4 (6 : Fin 7) (2 : Fin 7) = some ((54043 / 33750 : ℚ), true) := rfl
theorem tbl4_c_6_3 : tbl4 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl4_c_6_4 : tbl4 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl4_c_6_5 : tbl4 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl4_c_6_6 : tbl4 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 5 (internal, depth 4, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 51750 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 3450 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 230 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl5_c_0_0 : tbl5 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_0_1 : tbl5 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl5_c_0_2 : tbl5 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl5_c_0_3 : tbl5 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl5_c_0_4 : tbl5 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl5_c_0_5 : tbl5 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl5_c_0_6 : tbl5 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl5_c_1_0 : tbl5 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl5_c_1_1 : tbl5 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_1_2 : tbl5 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl5_c_1_3 : tbl5 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl5_c_1_4 : tbl5 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl5_c_1_5 : tbl5 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl5_c_1_6 : tbl5 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl5_c_2_0 : tbl5 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl5_c_2_1 : tbl5 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl5_c_2_2 : tbl5 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_2_3 : tbl5 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl5_c_2_4 : tbl5 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl5_c_2_5 : tbl5 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl5_c_2_6 : tbl5 (2 : Fin 7) (6 : Fin 7) = some ((34391 / 51750 : ℚ), true) := rfl
theorem tbl5_c_3_0 : tbl5 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl5_c_3_1 : tbl5 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl5_c_3_2 : tbl5 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl5_c_3_3 : tbl5 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_3_4 : tbl5 (3 : Fin 7) (4 : Fin 7) = some ((3179 / 3450 : ℚ), true) := rfl
theorem tbl5_c_3_5 : tbl5 (3 : Fin 7) (5 : Fin 7) = some ((187 / 230 : ℚ), true) := rfl
theorem tbl5_c_3_6 : tbl5 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl5_c_4_0 : tbl5 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl5_c_4_1 : tbl5 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl5_c_4_2 : tbl5 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl5_c_4_3 : tbl5 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl5_c_4_4 : tbl5 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_4_5 : tbl5 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl5_c_4_6 : tbl5 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl5_c_5_0 : tbl5 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl5_c_5_1 : tbl5 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl5_c_5_2 : tbl5 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl5_c_5_3 : tbl5 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl5_c_5_4 : tbl5 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl5_c_5_5 : tbl5 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_5_6 : tbl5 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl5_c_6_0 : tbl5 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl5_c_6_1 : tbl5 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl5_c_6_2 : tbl5 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl5_c_6_3 : tbl5 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl5_c_6_4 : tbl5 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl5_c_6_5 : tbl5 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl5_c_6_6 : tbl5 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 6 (internal, depth 5, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 51750 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 3450 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 230 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl6_c_0_0 : tbl6 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_0_1 : tbl6 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl6_c_0_2 : tbl6 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl6_c_0_3 : tbl6 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl6_c_0_4 : tbl6 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl6_c_0_5 : tbl6 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl6_c_0_6 : tbl6 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl6_c_1_0 : tbl6 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl6_c_1_1 : tbl6 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_1_2 : tbl6 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl6_c_1_3 : tbl6 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl6_c_1_4 : tbl6 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl6_c_1_5 : tbl6 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl6_c_1_6 : tbl6 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl6_c_2_0 : tbl6 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl6_c_2_1 : tbl6 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl6_c_2_2 : tbl6 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_2_3 : tbl6 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl6_c_2_4 : tbl6 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl6_c_2_5 : tbl6 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl6_c_2_6 : tbl6 (2 : Fin 7) (6 : Fin 7) = some ((34391 / 51750 : ℚ), true) := rfl
theorem tbl6_c_3_0 : tbl6 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl6_c_3_1 : tbl6 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl6_c_3_2 : tbl6 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl6_c_3_3 : tbl6 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_3_4 : tbl6 (3 : Fin 7) (4 : Fin 7) = some ((3179 / 3450 : ℚ), true) := rfl
theorem tbl6_c_3_5 : tbl6 (3 : Fin 7) (5 : Fin 7) = some ((187 / 230 : ℚ), true) := rfl
theorem tbl6_c_3_6 : tbl6 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl6_c_4_0 : tbl6 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl6_c_4_1 : tbl6 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl6_c_4_2 : tbl6 (4 : Fin 7) (2 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl6_c_4_3 : tbl6 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl6_c_4_4 : tbl6 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_4_5 : tbl6 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl6_c_4_6 : tbl6 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl6_c_5_0 : tbl6 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl6_c_5_1 : tbl6 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl6_c_5_2 : tbl6 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3105 : ℚ), true) := rfl
theorem tbl6_c_5_3 : tbl6 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl6_c_5_4 : tbl6 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl6_c_5_5 : tbl6 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_5_6 : tbl6 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl6_c_6_0 : tbl6 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl6_c_6_1 : tbl6 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl6_c_6_2 : tbl6 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl6_c_6_3 : tbl6 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl6_c_6_4 : tbl6 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl6_c_6_5 : tbl6 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl6_c_6_6 : tbl6 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 7 (reach, depth 6, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 115 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 230 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 7935 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 230 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl7_c_0_0 : tbl7 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_0_1 : tbl7 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl7_c_0_2 : tbl7 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl7_c_0_3 : tbl7 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl7_c_0_4 : tbl7 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl7_c_0_5 : tbl7 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl7_c_0_6 : tbl7 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl7_c_1_0 : tbl7 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl7_c_1_1 : tbl7 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_1_2 : tbl7 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl7_c_1_3 : tbl7 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl7_c_1_4 : tbl7 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl7_c_1_5 : tbl7 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl7_c_1_6 : tbl7 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl7_c_2_0 : tbl7 (2 : Fin 7) (0 : Fin 7) = some ((459 / 46 : ℚ), true) := rfl
theorem tbl7_c_2_1 : tbl7 (2 : Fin 7) (1 : Fin 7) = some ((459 / 115 : ℚ), true) := rfl
theorem tbl7_c_2_2 : tbl7 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_2_3 : tbl7 (2 : Fin 7) (3 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl7_c_2_4 : tbl7 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl7_c_2_5 : tbl7 (2 : Fin 7) (5 : Fin 7) = some ((153 / 230 : ℚ), true) := rfl
theorem tbl7_c_2_6 : tbl7 (2 : Fin 7) (6 : Fin 7) = some ((4913 / 7935 : ℚ), true) := rfl
theorem tbl7_c_3_0 : tbl7 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl7_c_3_1 : tbl7 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl7_c_3_2 : tbl7 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl7_c_3_3 : tbl7 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_3_4 : tbl7 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl7_c_3_5 : tbl7 (3 : Fin 7) (5 : Fin 7) = some ((187 / 230 : ℚ), true) := rfl
theorem tbl7_c_3_6 : tbl7 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl7_c_4_0 : tbl7 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl7_c_4_1 : tbl7 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl7_c_4_2 : tbl7 (4 : Fin 7) (2 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl7_c_4_3 : tbl7 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl7_c_4_4 : tbl7 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_4_5 : tbl7 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl7_c_4_6 : tbl7 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl7_c_5_0 : tbl7 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl7_c_5_1 : tbl7 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl7_c_5_2 : tbl7 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3105 : ℚ), true) := rfl
theorem tbl7_c_5_3 : tbl7 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl7_c_5_4 : tbl7 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl7_c_5_5 : tbl7 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_5_6 : tbl7 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl7_c_6_0 : tbl7 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl7_c_6_1 : tbl7 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl7_c_6_2 : tbl7 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl7_c_6_3 : tbl7 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl7_c_6_4 : tbl7 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl7_c_6_5 : tbl7 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl7_c_6_6 : tbl7 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 8 (reach, depth 6, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 51 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((35 / 102 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 51750 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((55 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 3450 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 230 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((45 / 34 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 17 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((55 / 34 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 2250 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 150 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 10 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl8_c_0_0 : tbl8 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_0_1 : tbl8 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl8_c_0_2 : tbl8 (0 : Fin 7) (2 : Fin 7) = some ((5 / 51 : ℚ), true) := rfl
theorem tbl8_c_0_3 : tbl8 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl8_c_0_4 : tbl8 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl8_c_0_5 : tbl8 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl8_c_0_6 : tbl8 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl8_c_1_0 : tbl8 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl8_c_1_1 : tbl8 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_1_2 : tbl8 (1 : Fin 7) (2 : Fin 7) = some ((35 / 102 : ℚ), true) := rfl
theorem tbl8_c_1_3 : tbl8 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl8_c_1_4 : tbl8 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl8_c_1_5 : tbl8 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl8_c_1_6 : tbl8 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl8_c_2_0 : tbl8 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl8_c_2_1 : tbl8 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl8_c_2_2 : tbl8 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_2_3 : tbl8 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl8_c_2_4 : tbl8 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl8_c_2_5 : tbl8 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl8_c_2_6 : tbl8 (2 : Fin 7) (6 : Fin 7) = some ((34391 / 51750 : ℚ), true) := rfl
theorem tbl8_c_3_0 : tbl8 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl8_c_3_1 : tbl8 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl8_c_3_2 : tbl8 (3 : Fin 7) (2 : Fin 7) = some ((55 / 46 : ℚ), true) := rfl
theorem tbl8_c_3_3 : tbl8 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_3_4 : tbl8 (3 : Fin 7) (4 : Fin 7) = some ((3179 / 3450 : ℚ), true) := rfl
theorem tbl8_c_3_5 : tbl8 (3 : Fin 7) (5 : Fin 7) = some ((187 / 230 : ℚ), true) := rfl
theorem tbl8_c_3_6 : tbl8 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl8_c_4_0 : tbl8 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl8_c_4_1 : tbl8 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl8_c_4_2 : tbl8 (4 : Fin 7) (2 : Fin 7) = some ((45 / 34 : ℚ), true) := rfl
theorem tbl8_c_4_3 : tbl8 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl8_c_4_4 : tbl8 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_4_5 : tbl8 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl8_c_4_6 : tbl8 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl8_c_5_0 : tbl8 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl8_c_5_1 : tbl8 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl8_c_5_2 : tbl8 (5 : Fin 7) (2 : Fin 7) = some ((25 / 17 : ℚ), true) := rfl
theorem tbl8_c_5_3 : tbl8 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl8_c_5_4 : tbl8 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl8_c_5_5 : tbl8 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_5_6 : tbl8 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl8_c_6_0 : tbl8 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl8_c_6_1 : tbl8 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl8_c_6_2 : tbl8 (6 : Fin 7) (2 : Fin 7) = some ((55 / 34 : ℚ), true) := rfl
theorem tbl8_c_6_3 : tbl8 (6 : Fin 7) (3 : Fin 7) = some ((3179 / 2250 : ℚ), true) := rfl
theorem tbl8_c_6_4 : tbl8 (6 : Fin 7) (4 : Fin 7) = some ((187 / 150 : ℚ), true) := rfl
theorem tbl8_c_6_5 : tbl8 (6 : Fin 7) (5 : Fin 7) = some ((11 / 10 : ℚ), true) := rfl
theorem tbl8_c_6_6 : tbl8 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 9 (internal, depth 5, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 2250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 150 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 51750 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl9_c_0_0 : tbl9 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_0_1 : tbl9 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl9_c_0_2 : tbl9 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl9_c_0_3 : tbl9 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl9_c_0_4 : tbl9 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl9_c_0_5 : tbl9 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl9_c_0_6 : tbl9 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl9_c_1_0 : tbl9 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl9_c_1_1 : tbl9 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_1_2 : tbl9 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl9_c_1_3 : tbl9 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl9_c_1_4 : tbl9 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl9_c_1_5 : tbl9 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl9_c_1_6 : tbl9 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl9_c_2_0 : tbl9 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl9_c_2_1 : tbl9 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl9_c_2_2 : tbl9 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_2_3 : tbl9 (2 : Fin 7) (3 : Fin 7) = some ((2023 / 2250 : ℚ), true) := rfl
theorem tbl9_c_2_4 : tbl9 (2 : Fin 7) (4 : Fin 7) = some ((119 / 150 : ℚ), true) := rfl
theorem tbl9_c_2_5 : tbl9 (2 : Fin 7) (5 : Fin 7) = some ((7 / 10 : ℚ), true) := rfl
theorem tbl9_c_2_6 : tbl9 (2 : Fin 7) (6 : Fin 7) = some ((34391 / 51750 : ℚ), true) := rfl
theorem tbl9_c_3_0 : tbl9 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_1 : tbl9 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl9_c_3_2 : tbl9 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl9_c_3_3 : tbl9 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_3_4 : tbl9 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl9_c_3_5 : tbl9 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl9_c_3_6 : tbl9 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl9_c_4_0 : tbl9 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl9_c_4_1 : tbl9 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl9_c_4_2 : tbl9 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl9_c_4_3 : tbl9 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl9_c_4_4 : tbl9 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_4_5 : tbl9 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl9_c_4_6 : tbl9 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl9_c_5_0 : tbl9 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl9_c_5_1 : tbl9 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl9_c_5_2 : tbl9 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl9_c_5_3 : tbl9 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl9_c_5_4 : tbl9 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl9_c_5_5 : tbl9 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_5_6 : tbl9 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl9_c_6_0 : tbl9 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl9_c_6_1 : tbl9 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl9_c_6_2 : tbl9 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl9_c_6_3 : tbl9 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl9_c_6_4 : tbl9 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl9_c_6_5 : tbl9 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl9_c_6_6 : tbl9 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 10 (internal, depth 6, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 625 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((83521 / 129375 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl10_c_0_0 : tbl10 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_0_1 : tbl10 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl10_c_0_2 : tbl10 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl10_c_0_3 : tbl10 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl10_c_0_4 : tbl10 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl10_c_0_5 : tbl10 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl10_c_0_6 : tbl10 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl10_c_1_0 : tbl10 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl10_c_1_1 : tbl10 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_1_2 : tbl10 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl10_c_1_3 : tbl10 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl10_c_1_4 : tbl10 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl10_c_1_5 : tbl10 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl10_c_1_6 : tbl10 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl10_c_2_0 : tbl10 (2 : Fin 7) (0 : Fin 7) = some ((2601 / 250 : ℚ), true) := rfl
theorem tbl10_c_2_1 : tbl10 (2 : Fin 7) (1 : Fin 7) = some ((2601 / 625 : ℚ), true) := rfl
theorem tbl10_c_2_2 : tbl10 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_2_3 : tbl10 (2 : Fin 7) (3 : Fin 7) = some ((4913 / 5625 : ℚ), true) := rfl
theorem tbl10_c_2_4 : tbl10 (2 : Fin 7) (4 : Fin 7) = some ((289 / 375 : ℚ), true) := rfl
theorem tbl10_c_2_5 : tbl10 (2 : Fin 7) (5 : Fin 7) = some ((17 / 25 : ℚ), true) := rfl
theorem tbl10_c_2_6 : tbl10 (2 : Fin 7) (6 : Fin 7) = some ((83521 / 129375 : ℚ), true) := rfl
theorem tbl10_c_3_0 : tbl10 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_1 : tbl10 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl10_c_3_2 : tbl10 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl10_c_3_3 : tbl10 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_3_4 : tbl10 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl10_c_3_5 : tbl10 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl10_c_3_6 : tbl10 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl10_c_4_0 : tbl10 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl10_c_4_1 : tbl10 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl10_c_4_2 : tbl10 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl10_c_4_3 : tbl10 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl10_c_4_4 : tbl10 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_4_5 : tbl10 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl10_c_4_6 : tbl10 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl10_c_5_0 : tbl10 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl10_c_5_1 : tbl10 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl10_c_5_2 : tbl10 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl10_c_5_3 : tbl10 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl10_c_5_4 : tbl10 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl10_c_5_5 : tbl10 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_5_6 : tbl10 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl10_c_6_0 : tbl10 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl10_c_6_1 : tbl10 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl10_c_6_2 : tbl10 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl10_c_6_3 : tbl10 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl10_c_6_4 : tbl10 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl10_c_6_5 : tbl10 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl10_c_6_6 : tbl10 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 11 (reach, depth 7, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 3375 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 225 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 77625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((2023 / 6750 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 450 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 30 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 155250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 115 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 230 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 7935 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl11_c_0_0 : tbl11 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_0_1 : tbl11 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl11_c_0_2 : tbl11 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl11_c_0_3 : tbl11 (0 : Fin 7) (3 : Fin 7) = some ((289 / 3375 : ℚ), true) := rfl
theorem tbl11_c_0_4 : tbl11 (0 : Fin 7) (4 : Fin 7) = some ((17 / 225 : ℚ), true) := rfl
theorem tbl11_c_0_5 : tbl11 (0 : Fin 7) (5 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl11_c_0_6 : tbl11 (0 : Fin 7) (6 : Fin 7) = some ((4913 / 77625 : ℚ), true) := rfl
theorem tbl11_c_1_0 : tbl11 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl11_c_1_1 : tbl11 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_1_2 : tbl11 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl11_c_1_3 : tbl11 (1 : Fin 7) (3 : Fin 7) = some ((2023 / 6750 : ℚ), true) := rfl
theorem tbl11_c_1_4 : tbl11 (1 : Fin 7) (4 : Fin 7) = some ((119 / 450 : ℚ), true) := rfl
theorem tbl11_c_1_5 : tbl11 (1 : Fin 7) (5 : Fin 7) = some ((7 / 30 : ℚ), true) := rfl
theorem tbl11_c_1_6 : tbl11 (1 : Fin 7) (6 : Fin 7) = some ((34391 / 155250 : ℚ), true) := rfl
theorem tbl11_c_2_0 : tbl11 (2 : Fin 7) (0 : Fin 7) = some ((459 / 46 : ℚ), true) := rfl
theorem tbl11_c_2_1 : tbl11 (2 : Fin 7) (1 : Fin 7) = some ((459 / 115 : ℚ), true) := rfl
theorem tbl11_c_2_2 : tbl11 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_2_3 : tbl11 (2 : Fin 7) (3 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl11_c_2_4 : tbl11 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl11_c_2_5 : tbl11 (2 : Fin 7) (5 : Fin 7) = some ((153 / 230 : ℚ), true) := rfl
theorem tbl11_c_2_6 : tbl11 (2 : Fin 7) (6 : Fin 7) = some ((4913 / 7935 : ℚ), true) := rfl
theorem tbl11_c_3_0 : tbl11 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_1 : tbl11 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl11_c_3_2 : tbl11 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl11_c_3_3 : tbl11 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_3_4 : tbl11 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl11_c_3_5 : tbl11 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl11_c_3_6 : tbl11 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl11_c_4_0 : tbl11 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl11_c_4_1 : tbl11 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl11_c_4_2 : tbl11 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl11_c_4_3 : tbl11 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl11_c_4_4 : tbl11 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_4_5 : tbl11 (4 : Fin 7) (5 : Fin 7) = some ((9 / 10 : ℚ), true) := rfl
theorem tbl11_c_4_6 : tbl11 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl11_c_5_0 : tbl11 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl11_c_5_1 : tbl11 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl11_c_5_2 : tbl11 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl11_c_5_3 : tbl11 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl11_c_5_4 : tbl11 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl11_c_5_5 : tbl11 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_5_6 : tbl11 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl11_c_6_0 : tbl11 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl11_c_6_1 : tbl11 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl11_c_6_2 : tbl11 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl11_c_6_3 : tbl11 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl11_c_6_4 : tbl11 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl11_c_6_5 : tbl11 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl11_c_6_6 : tbl11 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 12 (internal, depth 1, last reading row 6, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl12 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((21 / 25 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 29 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((31 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((31 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((31 / 19 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((31 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((31 / 25 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 25 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 29 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl12_c_0_0 : tbl12 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_0_1 : tbl12 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl12_c_0_2 : tbl12 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl12_c_0_3 : tbl12 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl12_c_0_4 : tbl12 (0 : Fin 7) (4 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl12_c_0_5 : tbl12 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl12_c_0_6 : tbl12 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl12_c_1_0 : tbl12 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl12_c_1_1 : tbl12 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_1_2 : tbl12 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl12_c_1_3 : tbl12 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl12_c_1_4 : tbl12 (1 : Fin 7) (4 : Fin 7) = some ((7 / 25 : ℚ), false) := rfl
theorem tbl12_c_1_5 : tbl12 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl12_c_1_6 : tbl12 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl12_c_2_0 : tbl12 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl12_c_2_1 : tbl12 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl12_c_2_2 : tbl12 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_2_3 : tbl12 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl12_c_2_4 : tbl12 (2 : Fin 7) (4 : Fin 7) = some ((21 / 25 : ℚ), false) := rfl
theorem tbl12_c_2_5 : tbl12 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl12_c_2_6 : tbl12 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl12_c_3_0 : tbl12 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl12_c_3_1 : tbl12 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl12_c_3_2 : tbl12 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl12_c_3_3 : tbl12 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_3_4 : tbl12 (3 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl12_c_3_5 : tbl12 (3 : Fin 7) (5 : Fin 7) = some ((25 / 29 : ℚ), false) := rfl
theorem tbl12_c_3_6 : tbl12 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl12_c_4_0 : tbl12 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl12_c_4_1 : tbl12 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl12_c_4_2 : tbl12 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl12_c_4_3 : tbl12 (4 : Fin 7) (3 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl12_c_4_4 : tbl12 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_4_5 : tbl12 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl12_c_4_6 : tbl12 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl12_c_5_0 : tbl12 (5 : Fin 7) (0 : Fin 7) = some ((31 / 2 : ℚ), false) := rfl
theorem tbl12_c_5_1 : tbl12 (5 : Fin 7) (1 : Fin 7) = some ((31 / 5 : ℚ), false) := rfl
theorem tbl12_c_5_2 : tbl12 (5 : Fin 7) (2 : Fin 7) = some ((31 / 19 : ℚ), false) := rfl
theorem tbl12_c_5_3 : tbl12 (5 : Fin 7) (3 : Fin 7) = some ((31 / 23 : ℚ), false) := rfl
theorem tbl12_c_5_4 : tbl12 (5 : Fin 7) (4 : Fin 7) = some ((31 / 25 : ℚ), false) := rfl
theorem tbl12_c_5_5 : tbl12 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_5_6 : tbl12 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl12_c_6_0 : tbl12 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl12_c_6_1 : tbl12 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl12_c_6_2 : tbl12 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl12_c_6_3 : tbl12 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl12_c_6_4 : tbl12 (6 : Fin 7) (4 : Fin 7) = some ((33 / 25 : ℚ), false) := rfl
theorem tbl12_c_6_5 : tbl12 (6 : Fin 7) (5 : Fin 7) = some ((33 / 29 : ℚ), false) := rfl
theorem tbl12_c_6_6 : tbl12 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 13 (internal, depth 2, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl13 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((21 / 25 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 29 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((31 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((31 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((31 / 19 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((31 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((31 / 25 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 25 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl13_c_0_0 : tbl13 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_0_1 : tbl13 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl13_c_0_2 : tbl13 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl13_c_0_3 : tbl13 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl13_c_0_4 : tbl13 (0 : Fin 7) (4 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl13_c_0_5 : tbl13 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl13_c_0_6 : tbl13 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl13_c_1_0 : tbl13 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl13_c_1_1 : tbl13 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_1_2 : tbl13 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl13_c_1_3 : tbl13 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl13_c_1_4 : tbl13 (1 : Fin 7) (4 : Fin 7) = some ((7 / 25 : ℚ), false) := rfl
theorem tbl13_c_1_5 : tbl13 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl13_c_1_6 : tbl13 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl13_c_2_0 : tbl13 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl13_c_2_1 : tbl13 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl13_c_2_2 : tbl13 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_2_3 : tbl13 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl13_c_2_4 : tbl13 (2 : Fin 7) (4 : Fin 7) = some ((21 / 25 : ℚ), false) := rfl
theorem tbl13_c_2_5 : tbl13 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl13_c_2_6 : tbl13 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl13_c_3_0 : tbl13 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl13_c_3_1 : tbl13 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl13_c_3_2 : tbl13 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl13_c_3_3 : tbl13 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_3_4 : tbl13 (3 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl13_c_3_5 : tbl13 (3 : Fin 7) (5 : Fin 7) = some ((25 / 29 : ℚ), false) := rfl
theorem tbl13_c_3_6 : tbl13 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl13_c_4_0 : tbl13 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl13_c_4_1 : tbl13 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl13_c_4_2 : tbl13 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl13_c_4_3 : tbl13 (4 : Fin 7) (3 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl13_c_4_4 : tbl13 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_4_5 : tbl13 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl13_c_4_6 : tbl13 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl13_c_5_0 : tbl13 (5 : Fin 7) (0 : Fin 7) = some ((31 / 2 : ℚ), false) := rfl
theorem tbl13_c_5_1 : tbl13 (5 : Fin 7) (1 : Fin 7) = some ((31 / 5 : ℚ), false) := rfl
theorem tbl13_c_5_2 : tbl13 (5 : Fin 7) (2 : Fin 7) = some ((31 / 19 : ℚ), false) := rfl
theorem tbl13_c_5_3 : tbl13 (5 : Fin 7) (3 : Fin 7) = some ((31 / 23 : ℚ), false) := rfl
theorem tbl13_c_5_4 : tbl13 (5 : Fin 7) (4 : Fin 7) = some ((31 / 25 : ℚ), false) := rfl
theorem tbl13_c_5_5 : tbl13 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_5_6 : tbl13 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl13_c_6_0 : tbl13 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl13_c_6_1 : tbl13 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl13_c_6_2 : tbl13 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl13_c_6_3 : tbl13 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl13_c_6_4 : tbl13 (6 : Fin 7) (4 : Fin 7) = some ((33 / 25 : ℚ), false) := rfl
theorem tbl13_c_6_5 : tbl13 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl13_c_6_6 : tbl13 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 14 (internal, depth 3, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl14 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 87 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 29 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 115 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 155 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl14_c_0_0 : tbl14 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_0_1 : tbl14 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl14_c_0_2 : tbl14 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl14_c_0_3 : tbl14 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl14_c_0_4 : tbl14 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl14_c_0_5 : tbl14 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl14_c_0_6 : tbl14 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl14_c_1_0 : tbl14 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl14_c_1_1 : tbl14 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_1_2 : tbl14 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl14_c_1_3 : tbl14 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl14_c_1_4 : tbl14 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl14_c_1_5 : tbl14 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl14_c_1_6 : tbl14 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl14_c_2_0 : tbl14 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl14_c_2_1 : tbl14 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl14_c_2_2 : tbl14 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_2_3 : tbl14 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl14_c_2_4 : tbl14 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl14_c_2_5 : tbl14 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl14_c_2_6 : tbl14 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl14_c_3_0 : tbl14 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl14_c_3_1 : tbl14 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl14_c_3_2 : tbl14 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl14_c_3_3 : tbl14 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_3_4 : tbl14 (3 : Fin 7) (4 : Fin 7) = some ((85 / 87 : ℚ), true) := rfl
theorem tbl14_c_3_5 : tbl14 (3 : Fin 7) (5 : Fin 7) = some ((25 / 29 : ℚ), false) := rfl
theorem tbl14_c_3_6 : tbl14 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl14_c_4_0 : tbl14 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl14_c_4_1 : tbl14 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl14_c_4_2 : tbl14 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl14_c_4_3 : tbl14 (4 : Fin 7) (3 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl14_c_4_4 : tbl14 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_4_5 : tbl14 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl14_c_4_6 : tbl14 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl14_c_5_0 : tbl14 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl14_c_5_1 : tbl14 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl14_c_5_2 : tbl14 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl14_c_5_3 : tbl14 (5 : Fin 7) (3 : Fin 7) = some ((153 / 115 : ℚ), true) := rfl
theorem tbl14_c_5_4 : tbl14 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl14_c_5_5 : tbl14 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_5_6 : tbl14 (5 : Fin 7) (6 : Fin 7) = some ((153 / 155 : ℚ), true) := rfl
theorem tbl14_c_6_0 : tbl14 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl14_c_6_1 : tbl14 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl14_c_6_2 : tbl14 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl14_c_6_3 : tbl14 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl14_c_6_4 : tbl14 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl14_c_6_5 : tbl14 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl14_c_6_6 : tbl14 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 15 (internal, depth 4, last reading row 3, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl15 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((5 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 19 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 87 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 29 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 31 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 155 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl15_c_0_0 : tbl15 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_0_1 : tbl15 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl15_c_0_2 : tbl15 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl15_c_0_3 : tbl15 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl15_c_0_4 : tbl15 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl15_c_0_5 : tbl15 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl15_c_0_6 : tbl15 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl15_c_1_0 : tbl15 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl15_c_1_1 : tbl15 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_1_2 : tbl15 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl15_c_1_3 : tbl15 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl15_c_1_4 : tbl15 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl15_c_1_5 : tbl15 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl15_c_1_6 : tbl15 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl15_c_2_0 : tbl15 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl15_c_2_1 : tbl15 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl15_c_2_2 : tbl15 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_2_3 : tbl15 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl15_c_2_4 : tbl15 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl15_c_2_5 : tbl15 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl15_c_2_6 : tbl15 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl15_c_3_0 : tbl15 (3 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl15_c_3_1 : tbl15 (3 : Fin 7) (1 : Fin 7) = some ((5 : ℚ), false) := rfl
theorem tbl15_c_3_2 : tbl15 (3 : Fin 7) (2 : Fin 7) = some ((25 / 19 : ℚ), false) := rfl
theorem tbl15_c_3_3 : tbl15 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_3_4 : tbl15 (3 : Fin 7) (4 : Fin 7) = some ((85 / 87 : ℚ), true) := rfl
theorem tbl15_c_3_5 : tbl15 (3 : Fin 7) (5 : Fin 7) = some ((25 / 29 : ℚ), false) := rfl
theorem tbl15_c_3_6 : tbl15 (3 : Fin 7) (6 : Fin 7) = some ((25 / 31 : ℚ), false) := rfl
theorem tbl15_c_4_0 : tbl15 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl15_c_4_1 : tbl15 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl15_c_4_2 : tbl15 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl15_c_4_3 : tbl15 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl15_c_4_4 : tbl15 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_4_5 : tbl15 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl15_c_4_6 : tbl15 (4 : Fin 7) (6 : Fin 7) = some ((27 / 31 : ℚ), false) := rfl
theorem tbl15_c_5_0 : tbl15 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl15_c_5_1 : tbl15 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl15_c_5_2 : tbl15 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl15_c_5_3 : tbl15 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl15_c_5_4 : tbl15 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl15_c_5_5 : tbl15 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_5_6 : tbl15 (5 : Fin 7) (6 : Fin 7) = some ((153 / 155 : ℚ), true) := rfl
theorem tbl15_c_6_0 : tbl15 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl15_c_6_1 : tbl15 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl15_c_6_2 : tbl15 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl15_c_6_3 : tbl15 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl15_c_6_4 : tbl15 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl15_c_6_5 : tbl15 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl15_c_6_6 : tbl15 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 16 (internal, depth 5, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl16 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 345 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((119 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((119 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((2023 / 2175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 155 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 150 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 375 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2023 / 2175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2325 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((34391 / 2250 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((34391 / 5625 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 34875 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl16_c_0_0 : tbl16 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_0_1 : tbl16 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl16_c_0_2 : tbl16 (0 : Fin 7) (2 : Fin 7) = some ((34 / 345 : ℚ), true) := rfl
theorem tbl16_c_0_3 : tbl16 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl16_c_0_4 : tbl16 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl16_c_0_5 : tbl16 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl16_c_0_6 : tbl16 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl16_c_1_0 : tbl16 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl16_c_1_1 : tbl16 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_1_2 : tbl16 (1 : Fin 7) (2 : Fin 7) = some ((119 / 345 : ℚ), true) := rfl
theorem tbl16_c_1_3 : tbl16 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl16_c_1_4 : tbl16 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl16_c_1_5 : tbl16 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl16_c_1_6 : tbl16 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl16_c_2_0 : tbl16 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl16_c_2_1 : tbl16 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl16_c_2_2 : tbl16 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_2_3 : tbl16 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl16_c_2_4 : tbl16 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl16_c_2_5 : tbl16 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl16_c_2_6 : tbl16 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl16_c_3_0 : tbl16 (3 : Fin 7) (0 : Fin 7) = some ((119 / 10 : ℚ), true) := rfl
theorem tbl16_c_3_1 : tbl16 (3 : Fin 7) (1 : Fin 7) = some ((119 / 25 : ℚ), true) := rfl
theorem tbl16_c_3_2 : tbl16 (3 : Fin 7) (2 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl16_c_3_3 : tbl16 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_3_4 : tbl16 (3 : Fin 7) (4 : Fin 7) = some ((2023 / 2175 : ℚ), true) := rfl
theorem tbl16_c_3_5 : tbl16 (3 : Fin 7) (5 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl16_c_3_6 : tbl16 (3 : Fin 7) (6 : Fin 7) = some ((119 / 155 : ℚ), true) := rfl
theorem tbl16_c_4_0 : tbl16 (4 : Fin 7) (0 : Fin 7) = some ((2023 / 150 : ℚ), true) := rfl
theorem tbl16_c_4_1 : tbl16 (4 : Fin 7) (1 : Fin 7) = some ((2023 / 375 : ℚ), true) := rfl
theorem tbl16_c_4_2 : tbl16 (4 : Fin 7) (2 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl16_c_4_3 : tbl16 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl16_c_4_4 : tbl16 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_4_5 : tbl16 (4 : Fin 7) (5 : Fin 7) = some ((2023 / 2175 : ℚ), true) := rfl
theorem tbl16_c_4_6 : tbl16 (4 : Fin 7) (6 : Fin 7) = some ((2023 / 2325 : ℚ), true) := rfl
theorem tbl16_c_5_0 : tbl16 (5 : Fin 7) (0 : Fin 7) = some ((34391 / 2250 : ℚ), true) := rfl
theorem tbl16_c_5_1 : tbl16 (5 : Fin 7) (1 : Fin 7) = some ((34391 / 5625 : ℚ), true) := rfl
theorem tbl16_c_5_2 : tbl16 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3375 : ℚ), true) := rfl
theorem tbl16_c_5_3 : tbl16 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl16_c_5_4 : tbl16 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl16_c_5_5 : tbl16 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_5_6 : tbl16 (5 : Fin 7) (6 : Fin 7) = some ((34391 / 34875 : ℚ), true) := rfl
theorem tbl16_c_6_0 : tbl16 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl16_c_6_1 : tbl16 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl16_c_6_2 : tbl16 (6 : Fin 7) (2 : Fin 7) = some ((187 / 115 : ℚ), true) := rfl
theorem tbl16_c_6_3 : tbl16 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl16_c_6_4 : tbl16 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl16_c_6_5 : tbl16 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl16_c_6_6 : tbl16 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 17 (internal, depth 6, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl17 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 345 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((119 / 345 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((119 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((2023 / 2175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 155 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 150 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 375 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2023 / 2175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2325 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((34391 / 2250 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((34391 / 5625 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((34391 / 34875 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl17_c_0_0 : tbl17 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_0_1 : tbl17 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl17_c_0_2 : tbl17 (0 : Fin 7) (2 : Fin 7) = some ((34 / 345 : ℚ), true) := rfl
theorem tbl17_c_0_3 : tbl17 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl17_c_0_4 : tbl17 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl17_c_0_5 : tbl17 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl17_c_0_6 : tbl17 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl17_c_1_0 : tbl17 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl17_c_1_1 : tbl17 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_1_2 : tbl17 (1 : Fin 7) (2 : Fin 7) = some ((119 / 345 : ℚ), true) := rfl
theorem tbl17_c_1_3 : tbl17 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl17_c_1_4 : tbl17 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl17_c_1_5 : tbl17 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl17_c_1_6 : tbl17 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl17_c_2_0 : tbl17 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl17_c_2_1 : tbl17 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl17_c_2_2 : tbl17 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_2_3 : tbl17 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl17_c_2_4 : tbl17 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl17_c_2_5 : tbl17 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl17_c_2_6 : tbl17 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl17_c_3_0 : tbl17 (3 : Fin 7) (0 : Fin 7) = some ((119 / 10 : ℚ), true) := rfl
theorem tbl17_c_3_1 : tbl17 (3 : Fin 7) (1 : Fin 7) = some ((119 / 25 : ℚ), true) := rfl
theorem tbl17_c_3_2 : tbl17 (3 : Fin 7) (2 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl17_c_3_3 : tbl17 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_3_4 : tbl17 (3 : Fin 7) (4 : Fin 7) = some ((2023 / 2175 : ℚ), true) := rfl
theorem tbl17_c_3_5 : tbl17 (3 : Fin 7) (5 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl17_c_3_6 : tbl17 (3 : Fin 7) (6 : Fin 7) = some ((119 / 155 : ℚ), true) := rfl
theorem tbl17_c_4_0 : tbl17 (4 : Fin 7) (0 : Fin 7) = some ((2023 / 150 : ℚ), true) := rfl
theorem tbl17_c_4_1 : tbl17 (4 : Fin 7) (1 : Fin 7) = some ((2023 / 375 : ℚ), true) := rfl
theorem tbl17_c_4_2 : tbl17 (4 : Fin 7) (2 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl17_c_4_3 : tbl17 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl17_c_4_4 : tbl17 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_4_5 : tbl17 (4 : Fin 7) (5 : Fin 7) = some ((2023 / 2175 : ℚ), true) := rfl
theorem tbl17_c_4_6 : tbl17 (4 : Fin 7) (6 : Fin 7) = some ((2023 / 2325 : ℚ), true) := rfl
theorem tbl17_c_5_0 : tbl17 (5 : Fin 7) (0 : Fin 7) = some ((34391 / 2250 : ℚ), true) := rfl
theorem tbl17_c_5_1 : tbl17 (5 : Fin 7) (1 : Fin 7) = some ((34391 / 5625 : ℚ), true) := rfl
theorem tbl17_c_5_2 : tbl17 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3375 : ℚ), true) := rfl
theorem tbl17_c_5_3 : tbl17 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl17_c_5_4 : tbl17 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl17_c_5_5 : tbl17 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_5_6 : tbl17 (5 : Fin 7) (6 : Fin 7) = some ((34391 / 34875 : ℚ), true) := rfl
theorem tbl17_c_6_0 : tbl17 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl17_c_6_1 : tbl17 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl17_c_6_2 : tbl17 (6 : Fin 7) (2 : Fin 7) = some ((187 / 115 : ℚ), true) := rfl
theorem tbl17_c_6_3 : tbl17 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl17_c_6_4 : tbl17 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl17_c_6_5 : tbl17 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl17_c_6_6 : tbl17 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 18 (reach, depth 7, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl18 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((578 / 6003 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((170 / 2001 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((50 / 667 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 31 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((2023 / 6003 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((595 / 2001 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((175 / 667 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 31 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((595 / 667 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((525 / 667 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((21 / 31 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((119 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((595 / 667 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 155 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 150 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 375 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((2023 / 2175 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2325 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((2023 / 138 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((2023 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((2023 / 2139 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl18_c_0_0 : tbl18 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_0_1 : tbl18 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl18_c_0_2 : tbl18 (0 : Fin 7) (2 : Fin 7) = some ((578 / 6003 : ℚ), true) := rfl
theorem tbl18_c_0_3 : tbl18 (0 : Fin 7) (3 : Fin 7) = some ((170 / 2001 : ℚ), true) := rfl
theorem tbl18_c_0_4 : tbl18 (0 : Fin 7) (4 : Fin 7) = some ((50 / 667 : ℚ), true) := rfl
theorem tbl18_c_0_5 : tbl18 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl18_c_0_6 : tbl18 (0 : Fin 7) (6 : Fin 7) = some ((2 / 31 : ℚ), false) := rfl
theorem tbl18_c_1_0 : tbl18 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl18_c_1_1 : tbl18 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_1_2 : tbl18 (1 : Fin 7) (2 : Fin 7) = some ((2023 / 6003 : ℚ), true) := rfl
theorem tbl18_c_1_3 : tbl18 (1 : Fin 7) (3 : Fin 7) = some ((595 / 2001 : ℚ), true) := rfl
theorem tbl18_c_1_4 : tbl18 (1 : Fin 7) (4 : Fin 7) = some ((175 / 667 : ℚ), true) := rfl
theorem tbl18_c_1_5 : tbl18 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl18_c_1_6 : tbl18 (1 : Fin 7) (6 : Fin 7) = some ((7 / 31 : ℚ), false) := rfl
theorem tbl18_c_2_0 : tbl18 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl18_c_2_1 : tbl18 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl18_c_2_2 : tbl18 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_2_3 : tbl18 (2 : Fin 7) (3 : Fin 7) = some ((595 / 667 : ℚ), true) := rfl
theorem tbl18_c_2_4 : tbl18 (2 : Fin 7) (4 : Fin 7) = some ((525 / 667 : ℚ), true) := rfl
theorem tbl18_c_2_5 : tbl18 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl18_c_2_6 : tbl18 (2 : Fin 7) (6 : Fin 7) = some ((21 / 31 : ℚ), false) := rfl
theorem tbl18_c_3_0 : tbl18 (3 : Fin 7) (0 : Fin 7) = some ((119 / 10 : ℚ), true) := rfl
theorem tbl18_c_3_1 : tbl18 (3 : Fin 7) (1 : Fin 7) = some ((119 / 25 : ℚ), true) := rfl
theorem tbl18_c_3_2 : tbl18 (3 : Fin 7) (2 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl18_c_3_3 : tbl18 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_3_4 : tbl18 (3 : Fin 7) (4 : Fin 7) = some ((595 / 667 : ℚ), true) := rfl
theorem tbl18_c_3_5 : tbl18 (3 : Fin 7) (5 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl18_c_3_6 : tbl18 (3 : Fin 7) (6 : Fin 7) = some ((119 / 155 : ℚ), true) := rfl
theorem tbl18_c_4_0 : tbl18 (4 : Fin 7) (0 : Fin 7) = some ((2023 / 150 : ℚ), true) := rfl
theorem tbl18_c_4_1 : tbl18 (4 : Fin 7) (1 : Fin 7) = some ((2023 / 375 : ℚ), true) := rfl
theorem tbl18_c_4_2 : tbl18 (4 : Fin 7) (2 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl18_c_4_3 : tbl18 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl18_c_4_4 : tbl18 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_4_5 : tbl18 (4 : Fin 7) (5 : Fin 7) = some ((2023 / 2175 : ℚ), true) := rfl
theorem tbl18_c_4_6 : tbl18 (4 : Fin 7) (6 : Fin 7) = some ((2023 / 2325 : ℚ), true) := rfl
theorem tbl18_c_5_0 : tbl18 (5 : Fin 7) (0 : Fin 7) = some ((2023 / 138 : ℚ), true) := rfl
theorem tbl18_c_5_1 : tbl18 (5 : Fin 7) (1 : Fin 7) = some ((2023 / 345 : ℚ), true) := rfl
theorem tbl18_c_5_2 : tbl18 (5 : Fin 7) (2 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl18_c_5_3 : tbl18 (5 : Fin 7) (3 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl18_c_5_4 : tbl18 (5 : Fin 7) (4 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl18_c_5_5 : tbl18 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_5_6 : tbl18 (5 : Fin 7) (6 : Fin 7) = some ((2023 / 2139 : ℚ), true) := rfl
theorem tbl18_c_6_0 : tbl18 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl18_c_6_1 : tbl18 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl18_c_6_2 : tbl18 (6 : Fin 7) (2 : Fin 7) = some ((4913 / 3105 : ℚ), true) := rfl
theorem tbl18_c_6_3 : tbl18 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl18_c_6_4 : tbl18 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl18_c_6_5 : tbl18 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl18_c_6_6 : tbl18 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 19 (internal, depth 5, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl19 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((357 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl19_c_0_0 : tbl19 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_0_1 : tbl19 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl19_c_0_2 : tbl19 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl19_c_0_3 : tbl19 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl19_c_0_4 : tbl19 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl19_c_0_5 : tbl19 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl19_c_0_6 : tbl19 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl19_c_1_0 : tbl19 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl19_c_1_1 : tbl19 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_1_2 : tbl19 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl19_c_1_3 : tbl19 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl19_c_1_4 : tbl19 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl19_c_1_5 : tbl19 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl19_c_1_6 : tbl19 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl19_c_2_0 : tbl19 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl19_c_2_1 : tbl19 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl19_c_2_2 : tbl19 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_2_3 : tbl19 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl19_c_2_4 : tbl19 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl19_c_2_5 : tbl19 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl19_c_2_6 : tbl19 (2 : Fin 7) (6 : Fin 7) = some ((357 / 529 : ℚ), true) := rfl
theorem tbl19_c_3_0 : tbl19 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl19_c_3_1 : tbl19 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl19_c_3_2 : tbl19 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl19_c_3_3 : tbl19 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_3_4 : tbl19 (3 : Fin 7) (4 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl19_c_3_5 : tbl19 (3 : Fin 7) (5 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl19_c_3_6 : tbl19 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl19_c_4_0 : tbl19 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl19_c_4_1 : tbl19 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl19_c_4_2 : tbl19 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl19_c_4_3 : tbl19 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl19_c_4_4 : tbl19 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_4_5 : tbl19 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl19_c_4_6 : tbl19 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl19_c_5_0 : tbl19 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl19_c_5_1 : tbl19 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl19_c_5_2 : tbl19 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl19_c_5_3 : tbl19 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl19_c_5_4 : tbl19 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl19_c_5_5 : tbl19 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_5_6 : tbl19 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl19_c_6_0 : tbl19 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl19_c_6_1 : tbl19 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl19_c_6_2 : tbl19 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl19_c_6_3 : tbl19 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl19_c_6_4 : tbl19 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl19_c_6_5 : tbl19 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl19_c_6_6 : tbl19 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 20 (internal, depth 6, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl20 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((357 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl20_c_0_0 : tbl20 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_0_1 : tbl20 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl20_c_0_2 : tbl20 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl20_c_0_3 : tbl20 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl20_c_0_4 : tbl20 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl20_c_0_5 : tbl20 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl20_c_0_6 : tbl20 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl20_c_1_0 : tbl20 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl20_c_1_1 : tbl20 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_1_2 : tbl20 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl20_c_1_3 : tbl20 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl20_c_1_4 : tbl20 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl20_c_1_5 : tbl20 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl20_c_1_6 : tbl20 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl20_c_2_0 : tbl20 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl20_c_2_1 : tbl20 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl20_c_2_2 : tbl20 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_2_3 : tbl20 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl20_c_2_4 : tbl20 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl20_c_2_5 : tbl20 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl20_c_2_6 : tbl20 (2 : Fin 7) (6 : Fin 7) = some ((357 / 529 : ℚ), true) := rfl
theorem tbl20_c_3_0 : tbl20 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl20_c_3_1 : tbl20 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl20_c_3_2 : tbl20 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl20_c_3_3 : tbl20 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_3_4 : tbl20 (3 : Fin 7) (4 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl20_c_3_5 : tbl20 (3 : Fin 7) (5 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl20_c_3_6 : tbl20 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl20_c_4_0 : tbl20 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl20_c_4_1 : tbl20 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl20_c_4_2 : tbl20 (4 : Fin 7) (2 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl20_c_4_3 : tbl20 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl20_c_4_4 : tbl20 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_4_5 : tbl20 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl20_c_4_6 : tbl20 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl20_c_5_0 : tbl20 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl20_c_5_1 : tbl20 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl20_c_5_2 : tbl20 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3105 : ℚ), true) := rfl
theorem tbl20_c_5_3 : tbl20 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl20_c_5_4 : tbl20 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl20_c_5_5 : tbl20 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_5_6 : tbl20 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl20_c_6_0 : tbl20 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl20_c_6_1 : tbl20 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl20_c_6_2 : tbl20 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl20_c_6_3 : tbl20 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl20_c_6_4 : tbl20 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl20_c_6_5 : tbl20 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl20_c_6_6 : tbl20 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 21 (deadend, depth 7, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl21 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 437 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 437 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 115 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 667 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 7935 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3105 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl21_c_0_0 : tbl21 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_0_1 : tbl21 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl21_c_0_2 : tbl21 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl21_c_0_3 : tbl21 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl21_c_0_4 : tbl21 (0 : Fin 7) (4 : Fin 7) = some ((34 / 437 : ℚ), true) := rfl
theorem tbl21_c_0_5 : tbl21 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl21_c_0_6 : tbl21 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl21_c_1_0 : tbl21 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl21_c_1_1 : tbl21 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_1_2 : tbl21 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl21_c_1_3 : tbl21 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl21_c_1_4 : tbl21 (1 : Fin 7) (4 : Fin 7) = some ((119 / 437 : ℚ), true) := rfl
theorem tbl21_c_1_5 : tbl21 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl21_c_1_6 : tbl21 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl21_c_2_0 : tbl21 (2 : Fin 7) (0 : Fin 7) = some ((459 / 46 : ℚ), true) := rfl
theorem tbl21_c_2_1 : tbl21 (2 : Fin 7) (1 : Fin 7) = some ((459 / 115 : ℚ), true) := rfl
theorem tbl21_c_2_2 : tbl21 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_2_3 : tbl21 (2 : Fin 7) (3 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl21_c_2_4 : tbl21 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl21_c_2_5 : tbl21 (2 : Fin 7) (5 : Fin 7) = some ((459 / 667 : ℚ), true) := rfl
theorem tbl21_c_2_6 : tbl21 (2 : Fin 7) (6 : Fin 7) = some ((4913 / 7935 : ℚ), true) := rfl
theorem tbl21_c_3_0 : tbl21 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl21_c_3_1 : tbl21 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl21_c_3_2 : tbl21 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl21_c_3_3 : tbl21 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_3_4 : tbl21 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl21_c_3_5 : tbl21 (3 : Fin 7) (5 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl21_c_3_6 : tbl21 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl21_c_4_0 : tbl21 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl21_c_4_1 : tbl21 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl21_c_4_2 : tbl21 (4 : Fin 7) (2 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl21_c_4_3 : tbl21 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl21_c_4_4 : tbl21 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_4_5 : tbl21 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl21_c_4_6 : tbl21 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl21_c_5_0 : tbl21 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl21_c_5_1 : tbl21 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl21_c_5_2 : tbl21 (5 : Fin 7) (2 : Fin 7) = some ((4913 / 3105 : ℚ), true) := rfl
theorem tbl21_c_5_3 : tbl21 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl21_c_5_4 : tbl21 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl21_c_5_5 : tbl21 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_5_6 : tbl21 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl21_c_6_0 : tbl21 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl21_c_6_1 : tbl21 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl21_c_6_2 : tbl21 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl21_c_6_3 : tbl21 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl21_c_6_4 : tbl21 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl21_c_6_5 : tbl21 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl21_c_6_6 : tbl21 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 22 (internal, depth 7, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl22 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((50 / 493 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((175 / 493 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((357 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((675 / 493 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 17 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl22_c_0_0 : tbl22 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_0_1 : tbl22 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl22_c_0_2 : tbl22 (0 : Fin 7) (2 : Fin 7) = some ((50 / 493 : ℚ), true) := rfl
theorem tbl22_c_0_3 : tbl22 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl22_c_0_4 : tbl22 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl22_c_0_5 : tbl22 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl22_c_0_6 : tbl22 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl22_c_1_0 : tbl22 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl22_c_1_1 : tbl22 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_1_2 : tbl22 (1 : Fin 7) (2 : Fin 7) = some ((175 / 493 : ℚ), true) := rfl
theorem tbl22_c_1_3 : tbl22 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl22_c_1_4 : tbl22 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl22_c_1_5 : tbl22 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl22_c_1_6 : tbl22 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl22_c_2_0 : tbl22 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl22_c_2_1 : tbl22 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl22_c_2_2 : tbl22 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_2_3 : tbl22 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl22_c_2_4 : tbl22 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl22_c_2_5 : tbl22 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl22_c_2_6 : tbl22 (2 : Fin 7) (6 : Fin 7) = some ((357 / 529 : ℚ), true) := rfl
theorem tbl22_c_3_0 : tbl22 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl22_c_3_1 : tbl22 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl22_c_3_2 : tbl22 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl22_c_3_3 : tbl22 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_3_4 : tbl22 (3 : Fin 7) (4 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl22_c_3_5 : tbl22 (3 : Fin 7) (5 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl22_c_3_6 : tbl22 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl22_c_4_0 : tbl22 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl22_c_4_1 : tbl22 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl22_c_4_2 : tbl22 (4 : Fin 7) (2 : Fin 7) = some ((675 / 493 : ℚ), true) := rfl
theorem tbl22_c_4_3 : tbl22 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl22_c_4_4 : tbl22 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_4_5 : tbl22 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl22_c_4_6 : tbl22 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl22_c_5_0 : tbl22 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl22_c_5_1 : tbl22 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl22_c_5_2 : tbl22 (5 : Fin 7) (2 : Fin 7) = some ((25 / 17 : ℚ), true) := rfl
theorem tbl22_c_5_3 : tbl22 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl22_c_5_4 : tbl22 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl22_c_5_5 : tbl22 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_5_6 : tbl22 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl22_c_6_0 : tbl22 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl22_c_6_1 : tbl22 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl22_c_6_2 : tbl22 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl22_c_6_3 : tbl22 (6 : Fin 7) (3 : Fin 7) = some ((33 / 23 : ℚ), false) := rfl
theorem tbl22_c_6_4 : tbl22 (6 : Fin 7) (4 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl22_c_6_5 : tbl22 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl22_c_6_6 : tbl22 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 23 (reach, depth 8, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl23 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((50 / 493 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((170 / 2001 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((50 / 667 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2890 / 46023 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((175 / 493 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((595 / 2001 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((175 / 667 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((10115 / 46023 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((595 / 667 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((525 / 667 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((10115 / 15341 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((675 / 493 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 29 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((675 / 46 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((135 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 17 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl23_c_0_0 : tbl23 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_0_1 : tbl23 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl23_c_0_2 : tbl23 (0 : Fin 7) (2 : Fin 7) = some ((50 / 493 : ℚ), true) := rfl
theorem tbl23_c_0_3 : tbl23 (0 : Fin 7) (3 : Fin 7) = some ((170 / 2001 : ℚ), true) := rfl
theorem tbl23_c_0_4 : tbl23 (0 : Fin 7) (4 : Fin 7) = some ((50 / 667 : ℚ), true) := rfl
theorem tbl23_c_0_5 : tbl23 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl23_c_0_6 : tbl23 (0 : Fin 7) (6 : Fin 7) = some ((2890 / 46023 : ℚ), true) := rfl
theorem tbl23_c_1_0 : tbl23 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl23_c_1_1 : tbl23 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_1_2 : tbl23 (1 : Fin 7) (2 : Fin 7) = some ((175 / 493 : ℚ), true) := rfl
theorem tbl23_c_1_3 : tbl23 (1 : Fin 7) (3 : Fin 7) = some ((595 / 2001 : ℚ), true) := rfl
theorem tbl23_c_1_4 : tbl23 (1 : Fin 7) (4 : Fin 7) = some ((175 / 667 : ℚ), true) := rfl
theorem tbl23_c_1_5 : tbl23 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl23_c_1_6 : tbl23 (1 : Fin 7) (6 : Fin 7) = some ((10115 / 46023 : ℚ), true) := rfl
theorem tbl23_c_2_0 : tbl23 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl23_c_2_1 : tbl23 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl23_c_2_2 : tbl23 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_2_3 : tbl23 (2 : Fin 7) (3 : Fin 7) = some ((595 / 667 : ℚ), true) := rfl
theorem tbl23_c_2_4 : tbl23 (2 : Fin 7) (4 : Fin 7) = some ((525 / 667 : ℚ), true) := rfl
theorem tbl23_c_2_5 : tbl23 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl23_c_2_6 : tbl23 (2 : Fin 7) (6 : Fin 7) = some ((10115 / 15341 : ℚ), true) := rfl
theorem tbl23_c_3_0 : tbl23 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl23_c_3_1 : tbl23 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl23_c_3_2 : tbl23 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl23_c_3_3 : tbl23 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_3_4 : tbl23 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl23_c_3_5 : tbl23 (3 : Fin 7) (5 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl23_c_3_6 : tbl23 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl23_c_4_0 : tbl23 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl23_c_4_1 : tbl23 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl23_c_4_2 : tbl23 (4 : Fin 7) (2 : Fin 7) = some ((675 / 493 : ℚ), true) := rfl
theorem tbl23_c_4_3 : tbl23 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl23_c_4_4 : tbl23 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_4_5 : tbl23 (4 : Fin 7) (5 : Fin 7) = some ((27 / 29 : ℚ), false) := rfl
theorem tbl23_c_4_6 : tbl23 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl23_c_5_0 : tbl23 (5 : Fin 7) (0 : Fin 7) = some ((675 / 46 : ℚ), true) := rfl
theorem tbl23_c_5_1 : tbl23 (5 : Fin 7) (1 : Fin 7) = some ((135 / 23 : ℚ), true) := rfl
theorem tbl23_c_5_2 : tbl23 (5 : Fin 7) (2 : Fin 7) = some ((25 / 17 : ℚ), true) := rfl
theorem tbl23_c_5_3 : tbl23 (5 : Fin 7) (3 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl23_c_5_4 : tbl23 (5 : Fin 7) (4 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl23_c_5_5 : tbl23 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_5_6 : tbl23 (5 : Fin 7) (6 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl23_c_6_0 : tbl23 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl23_c_6_1 : tbl23 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl23_c_6_2 : tbl23 (6 : Fin 7) (2 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl23_c_6_3 : tbl23 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl23_c_6_4 : tbl23 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl23_c_6_5 : tbl23 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl23_c_6_6 : tbl23 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 24 (internal, depth 6, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl24 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((21 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((21 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((21 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 145 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((21 / 29 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((357 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl24_c_0_0 : tbl24 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_0_1 : tbl24 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl24_c_0_2 : tbl24 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl24_c_0_3 : tbl24 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl24_c_0_4 : tbl24 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl24_c_0_5 : tbl24 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl24_c_0_6 : tbl24 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl24_c_1_0 : tbl24 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl24_c_1_1 : tbl24 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_1_2 : tbl24 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl24_c_1_3 : tbl24 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl24_c_1_4 : tbl24 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl24_c_1_5 : tbl24 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl24_c_1_6 : tbl24 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl24_c_2_0 : tbl24 (2 : Fin 7) (0 : Fin 7) = some ((21 / 2 : ℚ), false) := rfl
theorem tbl24_c_2_1 : tbl24 (2 : Fin 7) (1 : Fin 7) = some ((21 / 5 : ℚ), false) := rfl
theorem tbl24_c_2_2 : tbl24 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_2_3 : tbl24 (2 : Fin 7) (3 : Fin 7) = some ((21 / 23 : ℚ), false) := rfl
theorem tbl24_c_2_4 : tbl24 (2 : Fin 7) (4 : Fin 7) = some ((119 / 145 : ℚ), true) := rfl
theorem tbl24_c_2_5 : tbl24 (2 : Fin 7) (5 : Fin 7) = some ((21 / 29 : ℚ), false) := rfl
theorem tbl24_c_2_6 : tbl24 (2 : Fin 7) (6 : Fin 7) = some ((357 / 529 : ℚ), true) := rfl
theorem tbl24_c_3_0 : tbl24 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl24_c_3_1 : tbl24 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl24_c_3_2 : tbl24 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl24_c_3_3 : tbl24 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_3_4 : tbl24 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl24_c_3_5 : tbl24 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl24_c_3_6 : tbl24 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl24_c_4_0 : tbl24 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl24_c_4_1 : tbl24 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl24_c_4_2 : tbl24 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl24_c_4_3 : tbl24 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl24_c_4_4 : tbl24 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_4_5 : tbl24 (4 : Fin 7) (5 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl24_c_4_6 : tbl24 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl24_c_5_0 : tbl24 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl24_c_5_1 : tbl24 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl24_c_5_2 : tbl24 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl24_c_5_3 : tbl24 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl24_c_5_4 : tbl24 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl24_c_5_5 : tbl24 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_5_6 : tbl24 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl24_c_6_0 : tbl24 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl24_c_6_1 : tbl24 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl24_c_6_2 : tbl24 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl24_c_6_3 : tbl24 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl24_c_6_4 : tbl24 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl24_c_6_5 : tbl24 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl24_c_6_6 : tbl24 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 25 (internal, depth 7, last reading row 2, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl25 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 435 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 435 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 625 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((83521 / 129375 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl25_c_0_0 : tbl25 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_0_1 : tbl25 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl25_c_0_2 : tbl25 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl25_c_0_3 : tbl25 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl25_c_0_4 : tbl25 (0 : Fin 7) (4 : Fin 7) = some ((34 / 435 : ℚ), true) := rfl
theorem tbl25_c_0_5 : tbl25 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl25_c_0_6 : tbl25 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl25_c_1_0 : tbl25 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl25_c_1_1 : tbl25 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_1_2 : tbl25 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl25_c_1_3 : tbl25 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl25_c_1_4 : tbl25 (1 : Fin 7) (4 : Fin 7) = some ((119 / 435 : ℚ), true) := rfl
theorem tbl25_c_1_5 : tbl25 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl25_c_1_6 : tbl25 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl25_c_2_0 : tbl25 (2 : Fin 7) (0 : Fin 7) = some ((2601 / 250 : ℚ), true) := rfl
theorem tbl25_c_2_1 : tbl25 (2 : Fin 7) (1 : Fin 7) = some ((2601 / 625 : ℚ), true) := rfl
theorem tbl25_c_2_2 : tbl25 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_2_3 : tbl25 (2 : Fin 7) (3 : Fin 7) = some ((4913 / 5625 : ℚ), true) := rfl
theorem tbl25_c_2_4 : tbl25 (2 : Fin 7) (4 : Fin 7) = some ((289 / 375 : ℚ), true) := rfl
theorem tbl25_c_2_5 : tbl25 (2 : Fin 7) (5 : Fin 7) = some ((17 / 25 : ℚ), true) := rfl
theorem tbl25_c_2_6 : tbl25 (2 : Fin 7) (6 : Fin 7) = some ((83521 / 129375 : ℚ), true) := rfl
theorem tbl25_c_3_0 : tbl25 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl25_c_3_1 : tbl25 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl25_c_3_2 : tbl25 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl25_c_3_3 : tbl25 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_3_4 : tbl25 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl25_c_3_5 : tbl25 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl25_c_3_6 : tbl25 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl25_c_4_0 : tbl25 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl25_c_4_1 : tbl25 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl25_c_4_2 : tbl25 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl25_c_4_3 : tbl25 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl25_c_4_4 : tbl25 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_4_5 : tbl25 (4 : Fin 7) (5 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl25_c_4_6 : tbl25 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl25_c_5_0 : tbl25 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl25_c_5_1 : tbl25 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl25_c_5_2 : tbl25 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl25_c_5_3 : tbl25 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl25_c_5_4 : tbl25 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl25_c_5_5 : tbl25 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_5_6 : tbl25 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl25_c_6_0 : tbl25 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl25_c_6_1 : tbl25 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl25_c_6_2 : tbl25 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl25_c_6_3 : tbl25 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl25_c_6_4 : tbl25 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl25_c_6_5 : tbl25 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl25_c_6_6 : tbl25 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 26 (deadend, depth 8, last reading row 4, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl26 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((2 / 5 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 437 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 29 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((34 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 19 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((119 / 437 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((7 / 29 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((119 / 529 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 46 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 115 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((24565 / 36501 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 7935 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((561 / 437 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 5 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 19 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 1587 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 345 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((153 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 95 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 5 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 207 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl26_c_0_0 : tbl26 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_0_1 : tbl26 (0 : Fin 7) (1 : Fin 7) = some ((2 / 5 : ℚ), false) := rfl
theorem tbl26_c_0_2 : tbl26 (0 : Fin 7) (2 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tbl26_c_0_3 : tbl26 (0 : Fin 7) (3 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl26_c_0_4 : tbl26 (0 : Fin 7) (4 : Fin 7) = some ((34 / 437 : ℚ), true) := rfl
theorem tbl26_c_0_5 : tbl26 (0 : Fin 7) (5 : Fin 7) = some ((2 / 29 : ℚ), false) := rfl
theorem tbl26_c_0_6 : tbl26 (0 : Fin 7) (6 : Fin 7) = some ((34 / 529 : ℚ), true) := rfl
theorem tbl26_c_1_0 : tbl26 (1 : Fin 7) (0 : Fin 7) = some ((7 / 2 : ℚ), false) := rfl
theorem tbl26_c_1_1 : tbl26 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_1_2 : tbl26 (1 : Fin 7) (2 : Fin 7) = some ((7 / 19 : ℚ), false) := rfl
theorem tbl26_c_1_3 : tbl26 (1 : Fin 7) (3 : Fin 7) = some ((7 / 23 : ℚ), false) := rfl
theorem tbl26_c_1_4 : tbl26 (1 : Fin 7) (4 : Fin 7) = some ((119 / 437 : ℚ), true) := rfl
theorem tbl26_c_1_5 : tbl26 (1 : Fin 7) (5 : Fin 7) = some ((7 / 29 : ℚ), false) := rfl
theorem tbl26_c_1_6 : tbl26 (1 : Fin 7) (6 : Fin 7) = some ((119 / 529 : ℚ), true) := rfl
theorem tbl26_c_2_0 : tbl26 (2 : Fin 7) (0 : Fin 7) = some ((459 / 46 : ℚ), true) := rfl
theorem tbl26_c_2_1 : tbl26 (2 : Fin 7) (1 : Fin 7) = some ((459 / 115 : ℚ), true) := rfl
theorem tbl26_c_2_2 : tbl26 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_2_3 : tbl26 (2 : Fin 7) (3 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl26_c_2_4 : tbl26 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl26_c_2_5 : tbl26 (2 : Fin 7) (5 : Fin 7) = some ((24565 / 36501 : ℚ), true) := rfl
theorem tbl26_c_2_6 : tbl26 (2 : Fin 7) (6 : Fin 7) = some ((4913 / 7935 : ℚ), true) := rfl
theorem tbl26_c_3_0 : tbl26 (3 : Fin 7) (0 : Fin 7) = some ((561 / 46 : ℚ), true) := rfl
theorem tbl26_c_3_1 : tbl26 (3 : Fin 7) (1 : Fin 7) = some ((561 / 115 : ℚ), true) := rfl
theorem tbl26_c_3_2 : tbl26 (3 : Fin 7) (2 : Fin 7) = some ((561 / 437 : ℚ), true) := rfl
theorem tbl26_c_3_3 : tbl26 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_3_4 : tbl26 (3 : Fin 7) (4 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl26_c_3_5 : tbl26 (3 : Fin 7) (5 : Fin 7) = some ((425 / 529 : ℚ), true) := rfl
theorem tbl26_c_3_6 : tbl26 (3 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl26_c_4_0 : tbl26 (4 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl26_c_4_1 : tbl26 (4 : Fin 7) (1 : Fin 7) = some ((27 / 5 : ℚ), false) := rfl
theorem tbl26_c_4_2 : tbl26 (4 : Fin 7) (2 : Fin 7) = some ((27 / 19 : ℚ), false) := rfl
theorem tbl26_c_4_3 : tbl26 (4 : Fin 7) (3 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl26_c_4_4 : tbl26 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_4_5 : tbl26 (4 : Fin 7) (5 : Fin 7) = some ((1445 / 1587 : ℚ), true) := rfl
theorem tbl26_c_4_6 : tbl26 (4 : Fin 7) (6 : Fin 7) = some ((289 / 345 : ℚ), true) := rfl
theorem tbl26_c_5_0 : tbl26 (5 : Fin 7) (0 : Fin 7) = some ((153 / 10 : ℚ), true) := rfl
theorem tbl26_c_5_1 : tbl26 (5 : Fin 7) (1 : Fin 7) = some ((153 / 25 : ℚ), true) := rfl
theorem tbl26_c_5_2 : tbl26 (5 : Fin 7) (2 : Fin 7) = some ((153 / 95 : ℚ), true) := rfl
theorem tbl26_c_5_3 : tbl26 (5 : Fin 7) (3 : Fin 7) = some ((289 / 225 : ℚ), true) := rfl
theorem tbl26_c_5_4 : tbl26 (5 : Fin 7) (4 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl26_c_5_5 : tbl26 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_5_6 : tbl26 (5 : Fin 7) (6 : Fin 7) = some ((4913 / 5175 : ℚ), true) := rfl
theorem tbl26_c_6_0 : tbl26 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tbl26_c_6_1 : tbl26 (6 : Fin 7) (1 : Fin 7) = some ((33 / 5 : ℚ), false) := rfl
theorem tbl26_c_6_2 : tbl26 (6 : Fin 7) (2 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tbl26_c_6_3 : tbl26 (6 : Fin 7) (3 : Fin 7) = some ((289 / 207 : ℚ), true) := rfl
theorem tbl26_c_6_4 : tbl26 (6 : Fin 7) (4 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl26_c_6_5 : tbl26 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl26_c_6_6 : tbl26 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-! ## 1b. The node states and the certificate trees -/

/-- The start-zone root: DFS node 0 (depth 1, last reading row 5, exit numerator 17, frontier sup 17 / 15). -/
-- STANDING: DATA
def node0 : DfsNode := ⟨tbl0, (5 : Fin 7), (17 : ℚ), (17 / 15 : ℚ), {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 1 (internal, depth 2, last reading row 4, exit numerator 17): child of node 0 by the step (4, 15, 17). -/
-- STANDING: DATA
def node1 : DfsNode := ⟨tbl1, (4 : Fin 7), (17 : ℚ), (34 / 25 : ℚ), node0.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 2 (internal, depth 3, last reading row 3, exit numerator 17): child of node 1 by the step (3, 15, 17). -/
-- STANDING: DATA
def node2 : DfsNode := ⟨tbl2, (3 : Fin 7), (17 : ℚ), (34 / 23 : ℚ), node1.seen ∪ {((3 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 3 (internal, depth 4, last reading row 2, exit numerator 17): child of node 2 by the step (2, 15, 17). -/
-- STANDING: DATA
def node3 : DfsNode := ⟨tbl3, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node2.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 4 (reach, depth 5, last reading row 5, exit numerator 25): child of node 3 by the step (5, 23, 25). -/
-- STANDING: DATA
def node4 : DfsNode := ⟨tbl4, (5 : Fin 7), (25 : ℚ), (5 / 3 : ℚ), node3.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 5 (internal, depth 4, last reading row 6, exit numerator 25): child of node 2 by the step (6, 23, 25). -/
-- STANDING: DATA
def node5 : DfsNode := ⟨tbl5, (6 : Fin 7), (25 : ℚ), (50 / 31 : ℚ), node2.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 6 (internal, depth 5, last reading row 2, exit numerator 17): child of node 5 by the step (2, 15, 17). -/
-- STANDING: DATA
def node6 : DfsNode := ⟨tbl6, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node5.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 7 (reach, depth 6, last reading row 4, exit numerator 25): child of node 6 by the step (4, 23, 25). -/
-- STANDING: DATA
def node7 : DfsNode := ⟨tbl7, (4 : Fin 7), (25 : ℚ), (17 / 9 : ℚ), node6.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 8 (reach, depth 6, last reading row 5, exit numerator 25): child of node 6 by the step (5, 23, 25). -/
-- STANDING: DATA
def node8 : DfsNode := ⟨tbl8, (5 : Fin 7), (25 : ℚ), (5 / 3 : ℚ), node6.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 9 (internal, depth 5, last reading row 5, exit numerator 25): child of node 5 by the step (5, 23, 25). -/
-- STANDING: DATA
def node9 : DfsNode := ⟨tbl9, (5 : Fin 7), (25 : ℚ), (5 / 3 : ℚ), node5.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 10 (internal, depth 6, last reading row 2, exit numerator 17): child of node 9 by the step (2, 15, 17). -/
-- STANDING: DATA
def node10 : DfsNode := ⟨tbl10, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node9.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 11 (reach, depth 7, last reading row 4, exit numerator 25): child of node 10 by the step (4, 23, 25). -/
-- STANDING: DATA
def node11 : DfsNode := ⟨tbl11, (4 : Fin 7), (25 : ℚ), (17 / 9 : ℚ), node10.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- The start-zone root: DFS node 12 (depth 1, last reading row 6, exit numerator 17, frontier sup 34 / 31). -/
-- STANDING: DATA
def node12 : DfsNode := ⟨tbl12, (6 : Fin 7), (17 : ℚ), (34 / 31 : ℚ), {((6 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 13 (internal, depth 2, last reading row 5, exit numerator 17): child of node 12 by the step (5, 15, 17). -/
-- STANDING: DATA
def node13 : DfsNode := ⟨tbl13, (5 : Fin 7), (17 : ℚ), (34 / 29 : ℚ), node12.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 14 (internal, depth 3, last reading row 4, exit numerator 17): child of node 13 by the step (4, 15, 17). -/
-- STANDING: DATA
def node14 : DfsNode := ⟨tbl14, (4 : Fin 7), (17 : ℚ), (34 / 25 : ℚ), node13.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 15 (internal, depth 4, last reading row 3, exit numerator 17): child of node 14 by the step (3, 15, 17). -/
-- STANDING: DATA
def node15 : DfsNode := ⟨tbl15, (3 : Fin 7), (17 : ℚ), (34 / 23 : ℚ), node14.seen ∪ {((3 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 16 (internal, depth 5, last reading row 2, exit numerator 17): child of node 15 by the step (2, 15, 17). -/
-- STANDING: DATA
def node16 : DfsNode := ⟨tbl16, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node15.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 17 (internal, depth 6, last reading row 5, exit numerator 25): child of node 16 by the step (5, 23, 25). -/
-- STANDING: DATA
def node17 : DfsNode := ⟨tbl17, (5 : Fin 7), (25 : ℚ), (50 / 29 : ℚ), node16.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 18 (reach, depth 7, last reading row 4, exit numerator 25): child of node 17 by the step (4, 23, 25). -/
-- STANDING: DATA
def node18 : DfsNode := ⟨tbl18, (4 : Fin 7), (25 : ℚ), (170 / 87 : ℚ), node17.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 19 (internal, depth 5, last reading row 6, exit numerator 25): child of node 15 by the step (6, 23, 25). -/
-- STANDING: DATA
def node19 : DfsNode := ⟨tbl19, (6 : Fin 7), (25 : ℚ), (50 / 31 : ℚ), node15.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 20 (internal, depth 6, last reading row 2, exit numerator 17): child of node 19 by the step (2, 15, 17). -/
-- STANDING: DATA
def node20 : DfsNode := ⟨tbl20, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node19.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 21 (deadend, depth 7, last reading row 4, exit numerator 25): child of node 20 by the step (4, 23, 25). -/
-- STANDING: DATA
def node21 : DfsNode := ⟨tbl21, (4 : Fin 7), (25 : ℚ), (170 / 87 : ℚ), node20.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 22 (internal, depth 7, last reading row 5, exit numerator 25): child of node 20 by the step (5, 23, 25). -/
-- STANDING: DATA
def node22 : DfsNode := ⟨tbl22, (5 : Fin 7), (25 : ℚ), (50 / 29 : ℚ), node20.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 23 (reach, depth 8, last reading row 4, exit numerator 25): child of node 22 by the step (4, 23, 25). -/
-- STANDING: DATA
def node23 : DfsNode := ⟨tbl23, (4 : Fin 7), (25 : ℚ), (170 / 87 : ℚ), node22.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 24 (internal, depth 6, last reading row 5, exit numerator 25): child of node 19 by the step (5, 23, 25). -/
-- STANDING: DATA
def node24 : DfsNode := ⟨tbl24, (5 : Fin 7), (25 : ℚ), (50 / 29 : ℚ), node19.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 25 (internal, depth 7, last reading row 2, exit numerator 17): child of node 24 by the step (2, 15, 17). -/
-- STANDING: DATA
def node25 : DfsNode := ⟨tbl25, (2 : Fin 7), (17 : ℚ), (34 / 19 : ℚ), node24.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 26 (deadend, depth 8, last reading row 4, exit numerator 25): child of node 25 by the step (4, 23, 25). -/
-- STANDING: DATA
def node26 : DfsNode := ⟨tbl26, (4 : Fin 7), (25 : ℚ), (170 / 87 : ℚ), node25.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- The dead-end leaf, DFS node 26: no filter-passing step. -/
-- STANDING: DATA
def tree26 : DfsCert := DfsCert.deadend node26

def children25 : List DfsCert := [tree26]
/-- The subtree rooted at internal node 25: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree25 : DfsCert := DfsCert.node node25 children25

def children24 : List DfsCert := [tree25]
/-- The subtree rooted at internal node 24: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree24 : DfsCert := DfsCert.node node24 children24

/-- The reach-prune leaf, DFS node 23: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree23 : DfsCert := DfsCert.prune node23

def children22 : List DfsCert := [tree23]
/-- The subtree rooted at internal node 22: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree22 : DfsCert := DfsCert.node node22 children22

/-- The dead-end leaf, DFS node 21: no filter-passing step. -/
-- STANDING: DATA
def tree21 : DfsCert := DfsCert.deadend node21

def children20 : List DfsCert := [tree21, tree22]
/-- The subtree rooted at internal node 20: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree20 : DfsCert := DfsCert.node node20 children20

def children19 : List DfsCert := [tree20, tree24]
/-- The subtree rooted at internal node 19: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree19 : DfsCert := DfsCert.node node19 children19

/-- The reach-prune leaf, DFS node 18: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree18 : DfsCert := DfsCert.prune node18

def children17 : List DfsCert := [tree18]
/-- The subtree rooted at internal node 17: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree17 : DfsCert := DfsCert.node node17 children17

def children16 : List DfsCert := [tree17]
/-- The subtree rooted at internal node 16: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree16 : DfsCert := DfsCert.node node16 children16

def children15 : List DfsCert := [tree16, tree19]
/-- The subtree rooted at internal node 15: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree15 : DfsCert := DfsCert.node node15 children15

def children14 : List DfsCert := [tree15]
/-- The subtree rooted at internal node 14: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree14 : DfsCert := DfsCert.node node14 children14

def children13 : List DfsCert := [tree14]
/-- The subtree rooted at internal node 13: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree13 : DfsCert := DfsCert.node node13 children13

def children12 : List DfsCert := [tree13]
/-- The subtree rooted at internal node 12: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree12 : DfsCert := DfsCert.node node12 children12

/-- The reach-prune leaf, DFS node 11: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree11 : DfsCert := DfsCert.prune node11

def children10 : List DfsCert := [tree11]
/-- The subtree rooted at internal node 10: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree10 : DfsCert := DfsCert.node node10 children10

def children9 : List DfsCert := [tree10]
/-- The subtree rooted at internal node 9: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree9 : DfsCert := DfsCert.node node9 children9

/-- The reach-prune leaf, DFS node 8: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree8 : DfsCert := DfsCert.prune node8

/-- The reach-prune leaf, DFS node 7: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree7 : DfsCert := DfsCert.prune node7

def children6 : List DfsCert := [tree7, tree8]
/-- The subtree rooted at internal node 6: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree6 : DfsCert := DfsCert.node node6 children6

def children5 : List DfsCert := [tree6, tree9]
/-- The subtree rooted at internal node 5: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree5 : DfsCert := DfsCert.node node5 children5

/-- The reach-prune leaf, DFS node 4: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree4 : DfsCert := DfsCert.prune node4

def children3 : List DfsCert := [tree4]
/-- The subtree rooted at internal node 3: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree3 : DfsCert := DfsCert.node node3 children3

def children2 : List DfsCert := [tree3, tree5]
/-- The subtree rooted at internal node 2: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree2 : DfsCert := DfsCert.node node2 children2

def children1 : List DfsCert := [tree2]
/-- The subtree rooted at internal node 1: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree1 : DfsCert := DfsCert.node node1 children1

def children0 : List DfsCert := [tree1]
/-- The subtree rooted at internal node 0: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree0 : DfsCert := DfsCert.node node0 children0

/-- The box's WHOLE certificate forest (2 start-zone root(s), 27 nodes),
transcribed verbatim from the reconstruction. -/
-- STANDING: DATA
def forest : List DfsCert := [tree0, tree12]

/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/

theorem nodeOK_0 : DfsNodeOK node0 := by
  show uExitOK tbl0 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl0_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_0
theorem nodeOK_1 : DfsNodeOK node1 := by
  show uExitOK tbl1 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl1_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_1
theorem nodeOK_2 : DfsNodeOK node2 := by
  show uExitOK tbl2 (3 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl2_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_2
theorem nodeOK_3 : DfsNodeOK node3 := by
  show uExitOK tbl3 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl3_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_3
theorem nodeOK_4 : DfsNodeOK node4 := by
  show uExitOK tbl4 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl4_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl4_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_4
theorem nodeOK_5 : DfsNodeOK node5 := by
  show uExitOK tbl5 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl5_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_5
theorem nodeOK_6 : DfsNodeOK node6 := by
  show uExitOK tbl6 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl6_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl6_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_6
theorem nodeOK_7 : DfsNodeOK node7 := by
  show uExitOK tbl7 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl7_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_7
theorem nodeOK_8 : DfsNodeOK node8 := by
  show uExitOK tbl8 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl8_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_8
theorem nodeOK_9 : DfsNodeOK node9 := by
  show uExitOK tbl9 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl9_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl9_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_9
theorem nodeOK_10 : DfsNodeOK node10 := by
  show uExitOK tbl10 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl10_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl10_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_10
theorem nodeOK_11 : DfsNodeOK node11 := by
  show uExitOK tbl11 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl11_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl11_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_11
theorem nodeOK_12 : DfsNodeOK node12 := by
  show uExitOK tbl12 (6 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl12_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl12_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_12
theorem nodeOK_13 : DfsNodeOK node13 := by
  show uExitOK tbl13 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl13_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl13_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_13
theorem nodeOK_14 : DfsNodeOK node14 := by
  show uExitOK tbl14 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl14_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl14_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_14
theorem nodeOK_15 : DfsNodeOK node15 := by
  show uExitOK tbl15 (3 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl15_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl15_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_15
theorem nodeOK_16 : DfsNodeOK node16 := by
  show uExitOK tbl16 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl16_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl16_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_16
theorem nodeOK_17 : DfsNodeOK node17 := by
  show uExitOK tbl17 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl17_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl17_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_17
theorem nodeOK_18 : DfsNodeOK node18 := by
  show uExitOK tbl18 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl18_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl18_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_18
theorem nodeOK_19 : DfsNodeOK node19 := by
  show uExitOK tbl19 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl19_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_19
theorem nodeOK_20 : DfsNodeOK node20 := by
  show uExitOK tbl20 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl20_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_20
theorem nodeOK_21 : DfsNodeOK node21 := by
  show uExitOK tbl21 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl21_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl21_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_21
theorem nodeOK_22 : DfsNodeOK node22 := by
  show uExitOK tbl22 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl22_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl22_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_22
theorem nodeOK_23 : DfsNodeOK node23 := by
  show uExitOK tbl23 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl23_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl23_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_23
theorem nodeOK_24 : DfsNodeOK node24 := by
  show uExitOK tbl24 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl24_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl24_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_24
theorem nodeOK_25 : DfsNodeOK node25 := by
  show uExitOK tbl25 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl25_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl25_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_25
theorem nodeOK_26 : DfsNodeOK node26 := by
  show uExitOK tbl26 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl26_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl26_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_26

/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/

/-- Node 1's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_1_1 : uAdd tbl0 (5 : Fin 7) (4 : Fin 7) ((17 / 15 : ℚ)) true = some tbl1 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tbl1] <;> norm_num)

/-- Node 1's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_1_2 : uAdd tbl1 (4 : Fin 7) (5 : Fin 7) ((17 / 17 : ℚ)) true = some tbl1 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_5] <;> norm_num)

/-- Node 1's full step equation. -/
theorem stepEq_1 : uStep tbl0 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1 addEq_1_2

/-- Node 1's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_1 : childState (boxN m4res_1_3_10_12_13_15_16) node0 (4 : Fin 7) (17 : ℚ) tbl1 = DfsCert.root tree1 :=
  by
    simp only [childState, DfsCert.root, tree1, node1]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node0.U (4 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node0, tbl0_c_0_4]
    norm_num [hlo]

#print axioms addEq_1_1
#print axioms addEq_1_2
#print axioms stepEq_1
#print axioms childEq_1

/-- Node 2's step (3, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_2_1 : uAdd tbl1 (4 : Fin 7) (3 : Fin 7) ((17 / 15 : ℚ)) true = some tbl2 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl1_c_4_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_3_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl1, tbl2] <;> norm_num)

/-- Node 2's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_2_2 : uAdd tbl2 (3 : Fin 7) (4 : Fin 7) ((17 / 17 : ℚ)) true = some tbl2 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_4] <;> norm_num)

/-- Node 2's full step equation. -/
theorem stepEq_2 : uStep tbl1 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_2_1 addEq_2_2

/-- Node 2's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_2 : childState (boxN m4res_1_3_10_12_13_15_16) node1 (3 : Fin 7) (17 : ℚ) tbl2 = DfsCert.root tree2 :=
  by
    simp only [childState, DfsCert.root, tree2, node2]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node1.U (3 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node1, tbl1_c_0_3]
    norm_num [hlo]

#print axioms addEq_2_1
#print axioms addEq_2_2
#print axioms stepEq_2
#print axioms childEq_2

/-- Node 3's step (2, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_3_1 : uAdd tbl2 (3 : Fin 7) (2 : Fin 7) ((17 / 15 : ℚ)) true = some tbl3 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl2_c_3_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_2_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl2, tbl3] <;> norm_num)

/-- Node 3's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_3_2 : uAdd tbl3 (2 : Fin 7) (3 : Fin 7) ((17 / 17 : ℚ)) true = some tbl3 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_3] <;> norm_num)

/-- Node 3's full step equation. -/
theorem stepEq_3 : uStep tbl2 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl3 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1 addEq_3_2

/-- Node 3's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_3 : childState (boxN m4res_1_3_10_12_13_15_16) node2 (2 : Fin 7) (17 : ℚ) tbl3 = DfsCert.root tree3 :=
  by
    simp only [childState, DfsCert.root, tree3, node3]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node2.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node2, tbl2_c_0_2]
    norm_num [hlo]

#print axioms addEq_3_1
#print axioms addEq_3_2
#print axioms stepEq_3
#print axioms childEq_3

/-- Node 4's step (5, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_4_1 : uAdd tbl3 (2 : Fin 7) (5 : Fin 7) ((17 / 23 : ℚ)) true = some tbl3 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_5] <;> norm_num)

/-- Node 4's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_4_2 : uAdd tbl3 (5 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl3 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_5_2] <;> norm_num)

/-- Node 4's full step equation. -/
theorem stepEq_4 : uStep tbl3 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_4_1 addEq_4_2

/-- Node 4's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_4 : childState (boxN m4res_1_3_10_12_13_15_16) node3 (5 : Fin 7) (25 : ℚ) tbl4 = DfsCert.root tree4 :=
  by
    simp only [childState, DfsCert.root, tree4, node4]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node3.U (5 : Fin 7) = (15 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node3, tbl3_c_0_5]
    norm_num [hlo]

#print axioms addEq_4_1
#print axioms addEq_4_2
#print axioms stepEq_4
#print axioms childEq_4

/-- Node 5's step (6, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_5_1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((17 / 23 : ℚ)) true = some tbl5 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_6_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl2, tbl5] <;> norm_num)

/-- Node 5's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_5_2 : uAdd tbl5 (6 : Fin 7) (3 : Fin 7) ((25 / 17 : ℚ)) true = some tbl5 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_3] <;> norm_num)

/-- Node 5's full step equation. -/
theorem stepEq_5 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl5 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1 addEq_5_2

/-- Node 5's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_5 : childState (boxN m4res_1_3_10_12_13_15_16) node2 (6 : Fin 7) (25 : ℚ) tbl5 = DfsCert.root tree5 :=
  by
    simp only [childState, DfsCert.root, tree5, node5]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node2.U (6 : Fin 7) = (31 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node2, tbl2_c_0_6]
    norm_num [hlo]

#print axioms addEq_5_1
#print axioms addEq_5_2
#print axioms stepEq_5
#print axioms childEq_5

/-- Node 6's step (2, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_6_1 : uAdd tbl5 (6 : Fin 7) (2 : Fin 7) ((25 / 15 : ℚ)) true = some tbl6 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl5_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl5, tbl6] <;> norm_num)

/-- Node 6's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_6_2 : uAdd tbl6 (2 : Fin 7) (6 : Fin 7) ((17 / 25 : ℚ)) true = some tbl6 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_6] <;> norm_num)

/-- Node 6's full step equation. -/
theorem stepEq_6 : uStep tbl5 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_6_1 addEq_6_2

/-- Node 6's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_6 : childState (boxN m4res_1_3_10_12_13_15_16) node5 (2 : Fin 7) (17 : ℚ) tbl6 = DfsCert.root tree6 :=
  by
    simp only [childState, DfsCert.root, tree6, node6]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node5.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node5, tbl5_c_0_2]
    norm_num [hlo]

#print axioms addEq_6_1
#print axioms addEq_6_2
#print axioms stepEq_6
#print axioms childEq_6

/-- Node 7's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_7_1 : uAdd tbl6 (2 : Fin 7) (4 : Fin 7) ((17 / 23 : ℚ)) true = some tbl7 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl6_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl6_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl6, tbl7] <;> norm_num)

/-- Node 7's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_7_2 : uAdd tbl7 (4 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl7 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_4_2] <;> norm_num)

/-- Node 7's full step equation. -/
theorem stepEq_7 : uStep tbl6 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1 addEq_7_2

/-- Node 7's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_7 : childState (boxN m4res_1_3_10_12_13_15_16) node6 (4 : Fin 7) (25 : ℚ) tbl7 = DfsCert.root tree7 :=
  by
    simp only [childState, DfsCert.root, tree7, node7]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node6.U (4 : Fin 7) = (225 / 17 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node6, tbl6_c_0_4]
    norm_num [hlo]

#print axioms addEq_7_1
#print axioms addEq_7_2
#print axioms stepEq_7
#print axioms childEq_7

/-- Node 8's step (5, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_8_1 : uAdd tbl6 (2 : Fin 7) (5 : Fin 7) ((17 / 23 : ℚ)) true = some tbl6 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_5] <;> norm_num)

/-- Node 8's step: add 2 propagates to the child table. -/
theorem addEq_8_2 : uAdd tbl6 (5 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl8 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl6_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl6_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl6, tbl8] <;> norm_num)

/-- Node 8's full step equation. -/
theorem stepEq_8 : uStep tbl6 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_8_1 addEq_8_2

/-- Node 8's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_8 : childState (boxN m4res_1_3_10_12_13_15_16) node6 (5 : Fin 7) (25 : ℚ) tbl8 = DfsCert.root tree8 :=
  by
    simp only [childState, DfsCert.root, tree8, node8]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node6.U (5 : Fin 7) = (15 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node6, tbl6_c_0_5]
    norm_num [hlo]

#print axioms addEq_8_1
#print axioms addEq_8_2
#print axioms stepEq_8
#print axioms childEq_8

/-- Node 9's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_9_1 : uAdd tbl5 (6 : Fin 7) (5 : Fin 7) ((25 / 23 : ℚ)) true = some tbl9 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl5_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl5, tbl9] <;> norm_num)

/-- Node 9's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_9_2 : uAdd tbl9 (5 : Fin 7) (6 : Fin 7) ((25 / 25 : ℚ)) true = some tbl9 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_6] <;> norm_num)

/-- Node 9's full step equation. -/
theorem stepEq_9 : uStep tbl5 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1 addEq_9_2

/-- Node 9's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_9 : childState (boxN m4res_1_3_10_12_13_15_16) node5 (5 : Fin 7) (25 : ℚ) tbl9 = DfsCert.root tree9 :=
  by
    simp only [childState, DfsCert.root, tree9, node9]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node5.U (5 : Fin 7) = (15 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node5, tbl5_c_0_5]
    norm_num [hlo]

#print axioms addEq_9_1
#print axioms addEq_9_2
#print axioms stepEq_9
#print axioms childEq_9

/-- Node 10's step (2, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_10_1 : uAdd tbl9 (5 : Fin 7) (2 : Fin 7) ((25 / 15 : ℚ)) true = some tbl9 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_2] <;> norm_num)

/-- Node 10's step: add 2 propagates to the child table. -/
theorem addEq_10_2 : uAdd tbl9 (2 : Fin 7) (5 : Fin 7) ((17 / 25 : ℚ)) true = some tbl10 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl9_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl9_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl9, tbl10] <;> norm_num)

/-- Node 10's full step equation. -/
theorem stepEq_10 : uStep tbl9 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_10_1 addEq_10_2

/-- Node 10's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_10 : childState (boxN m4res_1_3_10_12_13_15_16) node9 (2 : Fin 7) (17 : ℚ) tbl10 = DfsCert.root tree10 :=
  by
    simp only [childState, DfsCert.root, tree10, node10]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node9.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node9, tbl9_c_0_2]
    norm_num [hlo]

#print axioms addEq_10_1
#print axioms addEq_10_2
#print axioms stepEq_10
#print axioms childEq_10

/-- Node 11's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_11_1 : uAdd tbl10 (2 : Fin 7) (4 : Fin 7) ((17 / 23 : ℚ)) true = some tbl11 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl10_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl10_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl10, tbl11] <;> norm_num)

/-- Node 11's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_11_2 : uAdd tbl11 (4 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl11 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_4_2] <;> norm_num)

/-- Node 11's full step equation. -/
theorem stepEq_11 : uStep tbl10 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1 addEq_11_2

/-- Node 11's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_11 : childState (boxN m4res_1_3_10_12_13_15_16) node10 (4 : Fin 7) (25 : ℚ) tbl11 = DfsCert.root tree11 :=
  by
    simp only [childState, DfsCert.root, tree11, node11]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node10.U (4 : Fin 7) = (225 / 17 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node10, tbl10_c_0_4]
    norm_num [hlo]

#print axioms addEq_11_1
#print axioms addEq_11_2
#print axioms stepEq_11
#print axioms childEq_11

/-- Node 13's step (5, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_13_1 : uAdd tbl12 (6 : Fin 7) (5 : Fin 7) ((17 / 15 : ℚ)) true = some tbl13 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl12_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl12_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl12, tbl13] <;> norm_num)

/-- Node 13's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_13_2 : uAdd tbl13 (5 : Fin 7) (6 : Fin 7) ((17 / 17 : ℚ)) true = some tbl13 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_6] <;> norm_num)

/-- Node 13's full step equation. -/
theorem stepEq_13 : uStep tbl12 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl13 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_13_1 addEq_13_2

/-- Node 13's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_13 : childState (boxN m4res_1_3_10_12_13_15_16) node12 (5 : Fin 7) (17 : ℚ) tbl13 = DfsCert.root tree13 :=
  by
    simp only [childState, DfsCert.root, tree13, node13]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node12.U (5 : Fin 7) = (29 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node12, tbl12_c_0_5]
    norm_num [hlo]

#print axioms addEq_13_1
#print axioms addEq_13_2
#print axioms stepEq_13
#print axioms childEq_13

/-- Node 14's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_14_1 : uAdd tbl13 (5 : Fin 7) (4 : Fin 7) ((17 / 15 : ℚ)) true = some tbl14 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl13_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl13_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl13, tbl14] <;> norm_num)

/-- Node 14's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_14_2 : uAdd tbl14 (4 : Fin 7) (5 : Fin 7) ((17 / 17 : ℚ)) true = some tbl14 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_5] <;> norm_num)

/-- Node 14's full step equation. -/
theorem stepEq_14 : uStep tbl13 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_14_1 addEq_14_2

/-- Node 14's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_14 : childState (boxN m4res_1_3_10_12_13_15_16) node13 (4 : Fin 7) (17 : ℚ) tbl14 = DfsCert.root tree14 :=
  by
    simp only [childState, DfsCert.root, tree14, node14]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node13.U (4 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node13, tbl13_c_0_4]
    norm_num [hlo]

#print axioms addEq_14_1
#print axioms addEq_14_2
#print axioms stepEq_14
#print axioms childEq_14

/-- Node 15's step (3, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_15_1 : uAdd tbl14 (4 : Fin 7) (3 : Fin 7) ((17 / 15 : ℚ)) true = some tbl15 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl14_c_4_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl14_c_3_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl14, tbl15] <;> norm_num)

/-- Node 15's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_15_2 : uAdd tbl15 (3 : Fin 7) (4 : Fin 7) ((17 / 17 : ℚ)) true = some tbl15 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_4] <;> norm_num)

/-- Node 15's full step equation. -/
theorem stepEq_15 : uStep tbl14 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_15_1 addEq_15_2

/-- Node 15's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_15 : childState (boxN m4res_1_3_10_12_13_15_16) node14 (3 : Fin 7) (17 : ℚ) tbl15 = DfsCert.root tree15 :=
  by
    simp only [childState, DfsCert.root, tree15, node15]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node14.U (3 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node14, tbl14_c_0_3]
    norm_num [hlo]

#print axioms addEq_15_1
#print axioms addEq_15_2
#print axioms stepEq_15
#print axioms childEq_15

/-- Node 16's step (2, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_16_1 : uAdd tbl15 (3 : Fin 7) (2 : Fin 7) ((17 / 15 : ℚ)) true = some tbl16 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl15_c_3_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl15_c_2_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl15, tbl16] <;> norm_num)

/-- Node 16's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_16_2 : uAdd tbl16 (2 : Fin 7) (3 : Fin 7) ((17 / 17 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_3] <;> norm_num)

/-- Node 16's full step equation. -/
theorem stepEq_16 : uStep tbl15 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl16 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_16_1 addEq_16_2

/-- Node 16's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_16 : childState (boxN m4res_1_3_10_12_13_15_16) node15 (2 : Fin 7) (17 : ℚ) tbl16 = DfsCert.root tree16 :=
  by
    simp only [childState, DfsCert.root, tree16, node16]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node15.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node15, tbl15_c_0_2]
    norm_num [hlo]

#print axioms addEq_16_1
#print axioms addEq_16_2
#print axioms stepEq_16
#print axioms childEq_16

/-- Node 17's step (5, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_17_1 : uAdd tbl16 (2 : Fin 7) (5 : Fin 7) ((17 / 23 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_5] <;> norm_num)

/-- Node 17's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_17_2 : uAdd tbl16 (5 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_5_2] <;> norm_num)

/-- Node 17's full step equation. -/
theorem stepEq_17 : uStep tbl16 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl17 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_17_1 addEq_17_2

/-- Node 17's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_17 : childState (boxN m4res_1_3_10_12_13_15_16) node16 (5 : Fin 7) (25 : ℚ) tbl17 = DfsCert.root tree17 :=
  by
    simp only [childState, DfsCert.root, tree17, node17]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node16.U (5 : Fin 7) = (29 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node16, tbl16_c_0_5]
    norm_num [hlo]

#print axioms addEq_17_1
#print axioms addEq_17_2
#print axioms stepEq_17
#print axioms childEq_17

/-- Node 18's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_18_1 : uAdd tbl17 (5 : Fin 7) (4 : Fin 7) ((25 / 23 : ℚ)) true = some tbl18 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl17_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl17_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl17, tbl18] <;> norm_num)

/-- Node 18's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_18_2 : uAdd tbl18 (4 : Fin 7) (5 : Fin 7) ((25 / 25 : ℚ)) true = some tbl18 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl18_c_4_5] <;> norm_num)

/-- Node 18's full step equation. -/
theorem stepEq_18 : uStep tbl17 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl18 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_18_1 addEq_18_2

/-- Node 18's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_18 : childState (boxN m4res_1_3_10_12_13_15_16) node17 (4 : Fin 7) (25 : ℚ) tbl18 = DfsCert.root tree18 :=
  by
    simp only [childState, DfsCert.root, tree18, node18]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node17.U (4 : Fin 7) = (435 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node17, tbl17_c_0_4]
    norm_num [hlo]

#print axioms addEq_18_1
#print axioms addEq_18_2
#print axioms stepEq_18
#print axioms childEq_18

/-- Node 19's step (6, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_19_1 : uAdd tbl15 (3 : Fin 7) (6 : Fin 7) ((17 / 23 : ℚ)) true = some tbl19 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl15_c_3_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl15_c_6_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl15, tbl19] <;> norm_num)

/-- Node 19's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_19_2 : uAdd tbl19 (6 : Fin 7) (3 : Fin 7) ((25 / 17 : ℚ)) true = some tbl19 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_3] <;> norm_num)

/-- Node 19's full step equation. -/
theorem stepEq_19 : uStep tbl15 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl19 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_19_1 addEq_19_2

/-- Node 19's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_19 : childState (boxN m4res_1_3_10_12_13_15_16) node15 (6 : Fin 7) (25 : ℚ) tbl19 = DfsCert.root tree19 :=
  by
    simp only [childState, DfsCert.root, tree19, node19]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node15.U (6 : Fin 7) = (31 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node15, tbl15_c_0_6]
    norm_num [hlo]

#print axioms addEq_19_1
#print axioms addEq_19_2
#print axioms stepEq_19
#print axioms childEq_19

/-- Node 20's step (2, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_20_1 : uAdd tbl19 (6 : Fin 7) (2 : Fin 7) ((25 / 15 : ℚ)) true = some tbl20 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl19_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl19, tbl20] <;> norm_num)

/-- Node 20's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_20_2 : uAdd tbl20 (2 : Fin 7) (6 : Fin 7) ((17 / 25 : ℚ)) true = some tbl20 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_6] <;> norm_num)

/-- Node 20's full step equation. -/
theorem stepEq_20 : uStep tbl19 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl20 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_20_1 addEq_20_2

/-- Node 20's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_20 : childState (boxN m4res_1_3_10_12_13_15_16) node19 (2 : Fin 7) (17 : ℚ) tbl20 = DfsCert.root tree20 :=
  by
    simp only [childState, DfsCert.root, tree20, node20]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node19.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node19, tbl19_c_0_2]
    norm_num [hlo]

#print axioms addEq_20_1
#print axioms addEq_20_2
#print axioms stepEq_20
#print axioms childEq_20

/-- Node 21's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_21_1 : uAdd tbl20 (2 : Fin 7) (4 : Fin 7) ((17 / 23 : ℚ)) true = some tbl21 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl20_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl20, tbl21] <;> norm_num)

/-- Node 21's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_21_2 : uAdd tbl21 (4 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl21 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_2] <;> norm_num)

/-- Node 21's full step equation. -/
theorem stepEq_21 : uStep tbl20 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl21 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_21_1 addEq_21_2

/-- Node 21's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_21 : childState (boxN m4res_1_3_10_12_13_15_16) node20 (4 : Fin 7) (25 : ℚ) tbl21 = DfsCert.root tree21 :=
  by
    simp only [childState, DfsCert.root, tree21, node21]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node20.U (4 : Fin 7) = (435 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node20, tbl20_c_0_4]
    norm_num [hlo]

#print axioms addEq_21_1
#print axioms addEq_21_2
#print axioms stepEq_21
#print axioms childEq_21

/-- Node 22's step (5, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_22_1 : uAdd tbl20 (2 : Fin 7) (5 : Fin 7) ((17 / 23 : ℚ)) true = some tbl20 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_5] <;> norm_num)

/-- Node 22's step: add 2 propagates to the child table. -/
theorem addEq_22_2 : uAdd tbl20 (5 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl22 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl20_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl20, tbl22] <;> norm_num)

/-- Node 22's full step equation. -/
theorem stepEq_22 : uStep tbl20 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl22 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_22_1 addEq_22_2

/-- Node 22's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_22 : childState (boxN m4res_1_3_10_12_13_15_16) node20 (5 : Fin 7) (25 : ℚ) tbl22 = DfsCert.root tree22 :=
  by
    simp only [childState, DfsCert.root, tree22, node22]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node20.U (5 : Fin 7) = (29 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node20, tbl20_c_0_5]
    norm_num [hlo]

#print axioms addEq_22_1
#print axioms addEq_22_2
#print axioms stepEq_22
#print axioms childEq_22

/-- Node 23's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_23_1 : uAdd tbl22 (5 : Fin 7) (4 : Fin 7) ((25 / 23 : ℚ)) true = some tbl23 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl22_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl22_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl22, tbl23] <;> norm_num)

/-- Node 23's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_23_2 : uAdd tbl23 (4 : Fin 7) (5 : Fin 7) ((25 / 25 : ℚ)) true = some tbl23 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl23_c_4_5] <;> norm_num)

/-- Node 23's full step equation. -/
theorem stepEq_23 : uStep tbl22 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl23 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_23_1 addEq_23_2

/-- Node 23's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_23 : childState (boxN m4res_1_3_10_12_13_15_16) node22 (4 : Fin 7) (25 : ℚ) tbl23 = DfsCert.root tree23 :=
  by
    simp only [childState, DfsCert.root, tree23, node23]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node22.U (4 : Fin 7) = (435 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node22, tbl22_c_0_4]
    norm_num [hlo]

#print axioms addEq_23_1
#print axioms addEq_23_2
#print axioms stepEq_23
#print axioms childEq_23

/-- Node 24's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_24_1 : uAdd tbl19 (6 : Fin 7) (5 : Fin 7) ((25 / 23 : ℚ)) true = some tbl24 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl19_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl19, tbl24] <;> norm_num)

/-- Node 24's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_24_2 : uAdd tbl24 (5 : Fin 7) (6 : Fin 7) ((25 / 25 : ℚ)) true = some tbl24 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_6] <;> norm_num)

/-- Node 24's full step equation. -/
theorem stepEq_24 : uStep tbl19 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl24 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_24_1 addEq_24_2

/-- Node 24's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_24 : childState (boxN m4res_1_3_10_12_13_15_16) node19 (5 : Fin 7) (25 : ℚ) tbl24 = DfsCert.root tree24 :=
  by
    simp only [childState, DfsCert.root, tree24, node24]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node19.U (5 : Fin 7) = (29 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node19, tbl19_c_0_5]
    norm_num [hlo]

#print axioms addEq_24_1
#print axioms addEq_24_2
#print axioms stepEq_24
#print axioms childEq_24

/-- Node 25's step (2, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_25_1 : uAdd tbl24 (5 : Fin 7) (2 : Fin 7) ((25 / 15 : ℚ)) true = some tbl24 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_2] <;> norm_num)

/-- Node 25's step: add 2 propagates to the child table. -/
theorem addEq_25_2 : uAdd tbl24 (2 : Fin 7) (5 : Fin 7) ((17 / 25 : ℚ)) true = some tbl25 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl24_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl24_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl24, tbl25] <;> norm_num)

/-- Node 25's full step equation. -/
theorem stepEq_25 : uStep tbl24 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl25 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_25_1 addEq_25_2

/-- Node 25's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_25 : childState (boxN m4res_1_3_10_12_13_15_16) node24 (2 : Fin 7) (17 : ℚ) tbl25 = DfsCert.root tree25 :=
  by
    simp only [childState, DfsCert.root, tree25, node25]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node24.U (2 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node24, tbl24_c_0_2]
    norm_num [hlo]

#print axioms addEq_25_1
#print axioms addEq_25_2
#print axioms stepEq_25
#print axioms childEq_25

/-- Node 26's step (4, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_26_1 : uAdd tbl25 (2 : Fin 7) (4 : Fin 7) ((17 / 23 : ℚ)) true = some tbl26 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl25_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl25_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl25, tbl26] <;> norm_num)

/-- Node 26's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_26_2 : uAdd tbl26 (4 : Fin 7) (2 : Fin 7) ((25 / 17 : ℚ)) true = some tbl26 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_2] <;> norm_num)

/-- Node 26's full step equation. -/
theorem stepEq_26 : uStep tbl25 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl26 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_26_1 addEq_26_2

/-- Node 26's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_26 : childState (boxN m4res_1_3_10_12_13_15_16) node25 (4 : Fin 7) (25 : ℚ) tbl26 = DfsCert.root tree26 :=
  by
    simp only [childState, DfsCert.root, tree26, node26]
    have hlo : dfsLo (boxN m4res_1_3_10_12_13_15_16) node25.U (4 : Fin 7) = (435 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_3_10_12_13_15_16, node25, tbl25_c_0_4]
    norm_num [hlo]

#print axioms addEq_26_1
#print axioms addEq_26_2
#print axioms stepEq_26
#print axioms childEq_26

/-! ## 3b. The seam kills -/

/-- Seam-failure kills at node 0 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk0_seam_2_1 : uStep tbl0 (5 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_2] <;> norm_num)

theorem sk0_seam_3_1 : uStep tbl0 (5 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_3] <;> norm_num)

theorem sk0_seam_4_1 : uStep tbl0 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_4] <;> norm_num)

theorem sk0_seam_5_1 : uStep tbl0 (5 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_5] <;> norm_num)

theorem sk0_seam_6_1 : uStep tbl0 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_6] <;> norm_num)

theorem sk0_seam_6_2 : uStep tbl0 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 1 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk1_seam_2_1 : uStep tbl1 (4 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_2_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_2] <;> norm_num)

theorem sk1_seam_3_1 : uStep tbl1 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_3_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_3] <;> norm_num)

theorem sk1_seam_4_1 : uStep tbl1 (4 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_4_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_4] <;> norm_num)

theorem sk1_seam_5_1 : uStep tbl1 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_5] <;> norm_num)

theorem sk1_seam_6_1 : uStep tbl1 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_6] <;> norm_num)

theorem sk1_seam_6_2 : uStep tbl1 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 2 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk2_seam_2_1 : uStep tbl2 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_2_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_2] <;> norm_num)

theorem sk2_seam_3_1 : uStep tbl2 (3 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_3_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_3] <;> norm_num)

theorem sk2_seam_4_1 : uStep tbl2 (3 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_4_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_4] <;> norm_num)

theorem sk2_seam_5_1 : uStep tbl2 (3 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_5] <;> norm_num)

theorem sk2_seam_6_1 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_6] <;> norm_num)

theorem sk2_seam_6_2 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_6] <;> norm_num)


/-- Seam-failure kills at node 3 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk3_seam_2_1 : uStep tbl3 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_2] <;> norm_num)

theorem sk3_seam_3_1 : uStep tbl3 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_3] <;> norm_num)

theorem sk3_seam_4_1 : uStep tbl3 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_4] <;> norm_num)

theorem sk3_seam_4_3 : uStep tbl3 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl3_c_2_4] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl3_c_4_2] <;> norm_num

theorem sk3_seam_5_1 : uStep tbl3 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_5] <;> norm_num)

theorem sk3_seam_6_1 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_6] <;> norm_num)

theorem sk3_seam_6_2 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_6] <;> norm_num)

theorem sk3_seam_6_3 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 5 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk5_seam_2_1 : uStep tbl5 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_2_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_2] <;> norm_num)

theorem sk5_seam_3_1 : uStep tbl5 (6 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_3_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_3] <;> norm_num)

theorem sk5_seam_4_1 : uStep tbl5 (6 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_4_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_4] <;> norm_num)

theorem sk5_seam_5_1 : uStep tbl5 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_5] <;> norm_num)

theorem sk5_seam_6_1 : uStep tbl5 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_6] <;> norm_num)

theorem sk5_seam_6_2 : uStep tbl5 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 6 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk6_seam_2_1 : uStep tbl6 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_2] <;> norm_num)

theorem sk6_seam_3_1 : uStep tbl6 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_3] <;> norm_num)

theorem sk6_seam_4_1 : uStep tbl6 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_4] <;> norm_num)

theorem sk6_seam_5_1 : uStep tbl6 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_5] <;> norm_num)

theorem sk6_seam_6_1 : uStep tbl6 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_6] <;> norm_num)

theorem sk6_seam_6_2 : uStep tbl6 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 9 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk9_seam_2_1 : uStep tbl9 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_2] <;> norm_num)

theorem sk9_seam_3_1 : uStep tbl9 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_3] <;> norm_num)

theorem sk9_seam_4_1 : uStep tbl9 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_4] <;> norm_num)

theorem sk9_seam_5_1 : uStep tbl9 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_5] <;> norm_num)

theorem sk9_seam_6_1 : uStep tbl9 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_6] <;> norm_num)

theorem sk9_seam_6_2 : uStep tbl9 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 10 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk10_seam_2_1 : uStep tbl10 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_2] <;> norm_num)

theorem sk10_seam_3_1 : uStep tbl10 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_3] <;> norm_num)

theorem sk10_seam_4_1 : uStep tbl10 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_4] <;> norm_num)

theorem sk10_seam_5_1 : uStep tbl10 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_5] <;> norm_num)

theorem sk10_seam_6_1 : uStep tbl10 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_6] <;> norm_num)

theorem sk10_seam_6_2 : uStep tbl10 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 12 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk12_seam_2_1 : uStep tbl12 (6 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (6 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_6_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_2_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_6_2] <;> norm_num)

theorem sk12_seam_3_1 : uStep tbl12 (6 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (6 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_6_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_3_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_6_3] <;> norm_num)

theorem sk12_seam_4_1 : uStep tbl12 (6 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (6 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_6_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_4_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_6_4] <;> norm_num)

theorem sk12_seam_5_1 : uStep tbl12 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (6 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_6_5] <;> norm_num)

theorem sk12_seam_6_1 : uStep tbl12 (6 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (6 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 13 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk13_seam_2_1 : uStep tbl13 (5 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_2] <;> norm_num)

theorem sk13_seam_3_1 : uStep tbl13 (5 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_3] <;> norm_num)

theorem sk13_seam_4_1 : uStep tbl13 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_4] <;> norm_num)

theorem sk13_seam_5_1 : uStep tbl13 (5 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_5] <;> norm_num)

theorem sk13_seam_6_1 : uStep tbl13 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 14 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk14_seam_2_1 : uStep tbl14 (4 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (4 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_2_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_4_2] <;> norm_num)

theorem sk14_seam_3_1 : uStep tbl14 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_3_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_4_3] <;> norm_num)

theorem sk14_seam_4_1 : uStep tbl14 (4 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (4 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_4_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_4_4] <;> norm_num)

theorem sk14_seam_5_1 : uStep tbl14 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_4_5] <;> norm_num)

theorem sk14_seam_6_1 : uStep tbl14 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 15 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk15_seam_2_1 : uStep tbl15 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_2_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_3_2] <;> norm_num)

theorem sk15_seam_3_1 : uStep tbl15 (3 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (3 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_3_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_3_3] <;> norm_num)

theorem sk15_seam_4_1 : uStep tbl15 (3 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_4_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_3_4] <;> norm_num)

theorem sk15_seam_5_1 : uStep tbl15 (3 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (3 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_3_5] <;> norm_num)

theorem sk15_seam_6_1 : uStep tbl15 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (3 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_3_6] <;> norm_num)


/-- Seam-failure kills at node 16 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk16_seam_2_1 : uStep tbl16 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_2] <;> norm_num)

theorem sk16_seam_3_1 : uStep tbl16 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_3] <;> norm_num)

theorem sk16_seam_4_1 : uStep tbl16 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_4] <;> norm_num)

theorem sk16_seam_4_3 : uStep tbl16 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl16_c_2_4] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl16_c_4_2] <;> norm_num

theorem sk16_seam_5_1 : uStep tbl16 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_5] <;> norm_num)

theorem sk16_seam_6_1 : uStep tbl16 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_6] <;> norm_num)

theorem sk16_seam_6_3 : uStep tbl16 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 17 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk17_seam_2_1 : uStep tbl17 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_2] <;> norm_num)

theorem sk17_seam_3_1 : uStep tbl17 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_3] <;> norm_num)

theorem sk17_seam_4_1 : uStep tbl17 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_4] <;> norm_num)

theorem sk17_seam_5_1 : uStep tbl17 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_5] <;> norm_num)

theorem sk17_seam_6_1 : uStep tbl17 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_6] <;> norm_num)

theorem sk17_seam_6_3 : uStep tbl17 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 19 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk19_seam_2_1 : uStep tbl19 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (6 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_2_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_6_2] <;> norm_num)

theorem sk19_seam_3_1 : uStep tbl19 (6 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (6 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_3_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_6_3] <;> norm_num)

theorem sk19_seam_4_1 : uStep tbl19 (6 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (6 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_4_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_6_4] <;> norm_num)

theorem sk19_seam_5_1 : uStep tbl19 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (6 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_6_5] <;> norm_num)

theorem sk19_seam_6_1 : uStep tbl19 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 20 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk20_seam_2_1 : uStep tbl20 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_2] <;> norm_num)

theorem sk20_seam_3_1 : uStep tbl20 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_3] <;> norm_num)

theorem sk20_seam_4_1 : uStep tbl20 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_4] <;> norm_num)

theorem sk20_seam_5_1 : uStep tbl20 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_5] <;> norm_num)

theorem sk20_seam_6_1 : uStep tbl20 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 21 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk21_seam_2_1 : uStep tbl21 (4 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_2_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_2] <;> norm_num)

theorem sk21_seam_3_1 : uStep tbl21 (4 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_3_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_3] <;> norm_num)

theorem sk21_seam_3_3 : uStep tbl21 (4 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl21_c_4_3] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl21_c_3_4] <;> norm_num

theorem sk21_seam_4_1 : uStep tbl21 (4 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_4_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_4] <;> norm_num)

theorem sk21_seam_5_1 : uStep tbl21 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_5] <;> norm_num)

theorem sk21_seam_5_3 : uStep tbl21 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_5] <;> norm_num)

theorem sk21_seam_6_1 : uStep tbl21 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_6] <;> norm_num)

theorem sk21_seam_6_4 : uStep tbl21 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl21_c_4_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl21_c_6_4] <;> norm_num


/-- Seam-failure kills at node 22 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk22_seam_2_1 : uStep tbl22 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_5_2] <;> norm_num)

theorem sk22_seam_3_1 : uStep tbl22 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (5 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_5_3] <;> norm_num)

theorem sk22_seam_4_1 : uStep tbl22 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (5 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_5_4] <;> norm_num)

theorem sk22_seam_5_1 : uStep tbl22 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_5_5] <;> norm_num)

theorem sk22_seam_6_1 : uStep tbl22 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 24 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk24_seam_2_1 : uStep tbl24 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl24 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl24 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl24_c_2_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl24_c_5_2] <;> norm_num)

theorem sk24_seam_3_1 : uStep tbl24 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl24 (5 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl24 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl24_c_3_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl24_c_5_3] <;> norm_num)

theorem sk24_seam_4_1 : uStep tbl24 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl24 (5 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl24 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl24_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl24_c_5_4] <;> norm_num)

theorem sk24_seam_4_3 : uStep tbl24 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl24_c_5_4] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl24_c_4_5] <;> norm_num

theorem sk24_seam_5_1 : uStep tbl24 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl24 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl24 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl24_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl24_c_5_5] <;> norm_num)

theorem sk24_seam_6_1 : uStep tbl24 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl24 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl24 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl24_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl24_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 25 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk25_seam_2_1 : uStep tbl25 (2 : Fin 7) (2 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl25 (2 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl25 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl25_c_2_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl25_c_2_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl25_c_2_2] <;> norm_num)

theorem sk25_seam_3_1 : uStep tbl25 (2 : Fin 7) (3 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl25 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl25 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl25_c_2_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl25_c_3_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl25_c_2_3] <;> norm_num)

theorem sk25_seam_4_1 : uStep tbl25 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl25 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl25 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl25_c_2_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl25_c_4_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl25_c_2_4] <;> norm_num)

theorem sk25_seam_5_1 : uStep tbl25 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl25 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl25 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl25_c_2_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl25_c_5_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl25_c_2_5] <;> norm_num)

theorem sk25_seam_6_1 : uStep tbl25 (2 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl25 (2 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl25 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl25_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl25_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl25_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 26 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk26_seam_2_1 : uStep tbl26 (4 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl26 (4 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl26 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_2] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl26_c_2_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl26_c_4_2] <;> norm_num)

theorem sk26_seam_3_1 : uStep tbl26 (4 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl26 (4 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl26 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_3] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl26_c_3_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl26_c_4_3] <;> norm_num)

theorem sk26_seam_3_3 : uStep tbl26 (4 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl26_c_4_3] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl26_c_3_4] <;> norm_num

theorem sk26_seam_4_1 : uStep tbl26 (4 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl26 (4 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl26 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl26_c_4_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl26_c_4_4] <;> norm_num)

theorem sk26_seam_5_1 : uStep tbl26 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl26 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl26 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl26_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl26_c_4_5] <;> norm_num)

theorem sk26_seam_6_1 : uStep tbl26 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl26 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl26 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl26_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl26_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl26_c_4_6] <;> norm_num)

theorem sk26_seam_6_4 : uStep tbl26 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl26_c_4_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl26_c_6_4] <;> norm_num


#print axioms sk0_seam_2_1
#print axioms sk0_seam_3_1
#print axioms sk0_seam_4_1
#print axioms sk0_seam_5_1
#print axioms sk0_seam_6_1
#print axioms sk0_seam_6_2
#print axioms sk1_seam_2_1
#print axioms sk1_seam_3_1
#print axioms sk1_seam_4_1
#print axioms sk1_seam_5_1
#print axioms sk1_seam_6_1
#print axioms sk1_seam_6_2
#print axioms sk2_seam_2_1
#print axioms sk2_seam_3_1
#print axioms sk2_seam_4_1
#print axioms sk2_seam_5_1
#print axioms sk2_seam_6_1
#print axioms sk2_seam_6_2
#print axioms sk3_seam_2_1
#print axioms sk3_seam_3_1
#print axioms sk3_seam_4_1
#print axioms sk3_seam_4_3
#print axioms sk3_seam_5_1
#print axioms sk3_seam_6_1
#print axioms sk3_seam_6_2
#print axioms sk3_seam_6_3
#print axioms sk5_seam_2_1
#print axioms sk5_seam_3_1
#print axioms sk5_seam_4_1
#print axioms sk5_seam_5_1
#print axioms sk5_seam_6_1
#print axioms sk5_seam_6_2
#print axioms sk6_seam_2_1
#print axioms sk6_seam_3_1
#print axioms sk6_seam_4_1
#print axioms sk6_seam_5_1
#print axioms sk6_seam_6_1
#print axioms sk6_seam_6_2
#print axioms sk9_seam_2_1
#print axioms sk9_seam_3_1
#print axioms sk9_seam_4_1
#print axioms sk9_seam_5_1
#print axioms sk9_seam_6_1
#print axioms sk9_seam_6_2
#print axioms sk10_seam_2_1
#print axioms sk10_seam_3_1
#print axioms sk10_seam_4_1
#print axioms sk10_seam_5_1
#print axioms sk10_seam_6_1
#print axioms sk10_seam_6_2
#print axioms sk12_seam_2_1
#print axioms sk12_seam_3_1
#print axioms sk12_seam_4_1
#print axioms sk12_seam_5_1
#print axioms sk12_seam_6_1
#print axioms sk13_seam_2_1
#print axioms sk13_seam_3_1
#print axioms sk13_seam_4_1
#print axioms sk13_seam_5_1
#print axioms sk13_seam_6_1
#print axioms sk14_seam_2_1
#print axioms sk14_seam_3_1
#print axioms sk14_seam_4_1
#print axioms sk14_seam_5_1
#print axioms sk14_seam_6_1
#print axioms sk15_seam_2_1
#print axioms sk15_seam_3_1
#print axioms sk15_seam_4_1
#print axioms sk15_seam_5_1
#print axioms sk15_seam_6_1
#print axioms sk16_seam_2_1
#print axioms sk16_seam_3_1
#print axioms sk16_seam_4_1
#print axioms sk16_seam_4_3
#print axioms sk16_seam_5_1
#print axioms sk16_seam_6_1
#print axioms sk16_seam_6_3
#print axioms sk17_seam_2_1
#print axioms sk17_seam_3_1
#print axioms sk17_seam_4_1
#print axioms sk17_seam_5_1
#print axioms sk17_seam_6_1
#print axioms sk17_seam_6_3
#print axioms sk19_seam_2_1
#print axioms sk19_seam_3_1
#print axioms sk19_seam_4_1
#print axioms sk19_seam_5_1
#print axioms sk19_seam_6_1
#print axioms sk20_seam_2_1
#print axioms sk20_seam_3_1
#print axioms sk20_seam_4_1
#print axioms sk20_seam_5_1
#print axioms sk20_seam_6_1
#print axioms sk21_seam_2_1
#print axioms sk21_seam_3_1
#print axioms sk21_seam_3_3
#print axioms sk21_seam_4_1
#print axioms sk21_seam_5_1
#print axioms sk21_seam_5_3
#print axioms sk21_seam_6_1
#print axioms sk21_seam_6_4
#print axioms sk22_seam_2_1
#print axioms sk22_seam_3_1
#print axioms sk22_seam_4_1
#print axioms sk22_seam_5_1
#print axioms sk22_seam_6_1
#print axioms sk24_seam_2_1
#print axioms sk24_seam_3_1
#print axioms sk24_seam_4_1
#print axioms sk24_seam_4_3
#print axioms sk24_seam_5_1
#print axioms sk24_seam_6_1
#print axioms sk25_seam_2_1
#print axioms sk25_seam_3_1
#print axioms sk25_seam_4_1
#print axioms sk25_seam_5_1
#print axioms sk25_seam_6_1
#print axioms sk26_seam_2_1
#print axioms sk26_seam_3_1
#print axioms sk26_seam_3_3
#print axioms sk26_seam_4_1
#print axioms sk26_seam_5_1
#print axioms sk26_seam_6_1
#print axioms sk26_seam_6_4

/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/

/-- The `match-completeness` at node 0: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_0 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node0 b A B) : ∃ c ∈ children0, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node0 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk0_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk0_seam_3_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk0_seam_4_1).elim
    · exact ⟨tree1, by simp [children0], tbl1, stepEq_1, childEq_1⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 109)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (5 : Fin 7) = (31 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨5, by norm_num⟩ : Fin 7) = (31 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((31 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 109 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((31 / 2 : ℚ)) ≤ (109 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk0_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl0_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl0 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk0_seam_6_1).elim
    · exact (hseam sk0_seam_6_2).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 1: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_1 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node1 b A B) : ∃ c ∈ children1, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node1 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk1_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk1_seam_3_1).elim
    · exact ⟨tree2, by simp [children1], tbl2, stepEq_2, childEq_2⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk1_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk1_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl1_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl1 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk1_seam_6_1).elim
    · exact (hseam sk1_seam_6_2).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 2: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_2 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node2 b A B) : ∃ c ∈ children2, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node2 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk2_seam_2_1).elim
    · exact ⟨tree3, by simp [children2], tbl3, stepEq_3, childEq_3⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk2_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk2_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk2_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl2_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl2 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk2_seam_6_1).elim
    · exact (hseam sk2_seam_6_2).elim
    · exact ⟨tree5, by simp [children2], tbl5, stepEq_5, childEq_5⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 3: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_3 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node3 b A B) : ∃ c ∈ children3, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node3 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk3_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (3 : Fin 7) = (119 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨3, by norm_num⟩ : Fin 7) = (119 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((119 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((119 / 10 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk3_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (4 : Fin 7) = (2023 / 150 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨4, by norm_num⟩ : Fin 7) = (2023 / 150 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2023 / 150 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2023 / 150 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk3_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk3_seam_4_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 107)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (5 : Fin 7) = (34391 / 2250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨5, by norm_num⟩ : Fin 7) = (34391 / 2250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((34391 / 2250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 107 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((34391 / 2250 : ℚ)) ≤ (107 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk3_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree4, by simp [children3], tbl4, stepEq_4, childEq_4⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl3_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl3 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk3_seam_6_1).elim
    · exact (hseam sk3_seam_6_2).elim
    · exact (hseam sk3_seam_6_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 5: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_5 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node5 b A B) : ∃ c ∈ children5, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node5 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk5_seam_2_1).elim
    · exact ⟨tree6, by simp [children5], tbl6, stepEq_6, childEq_6⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk5_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk5_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk5_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree9, by simp [children5], tbl9, stepEq_9, childEq_9⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl5_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl5 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk5_seam_6_1).elim
    · exact (hseam sk5_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 6: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_6 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node6 b A B) : ∃ c ∈ children6, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node6 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk6_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk6_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk6_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree7, by simp [children6], tbl7, stepEq_7, childEq_7⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk6_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree8, by simp [children6], tbl8, stepEq_8, childEq_8⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node6, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl6_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl6 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk6_seam_6_1).elim
    · exact (hseam sk6_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 9: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_9 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node9 b A B) : ∃ c ∈ children9, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node9 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk9_seam_2_1).elim
    · exact ⟨tree10, by simp [children9], tbl10, stepEq_10, childEq_10⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk9_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk9_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk9_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl9_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl9 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk9_seam_6_1).elim
    · exact (hseam sk9_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 10: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_10 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node10 b A B) : ∃ c ∈ children10, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node10 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 73)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (2 : Fin 7) = (2601 / 250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨2, by norm_num⟩ : Fin 7) = (2601 / 250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2601 / 250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 73 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2601 / 250 : ℚ)) ≤ (73 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk10_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk10_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk10_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree11, by simp [children10], tbl11, stepEq_11, childEq_11⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk10_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node10, node9, node5, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl10_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl10 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk10_seam_6_1).elim
    · exact (hseam sk10_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 12: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_12 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node12 b A B) : ∃ c ∈ children12, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node12 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk12_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk12_seam_3_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk12_seam_4_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 109)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (5 : Fin 7) = (31 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨5, by norm_num⟩ : Fin 7) = (31 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((31 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 109 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((31 / 2 : ℚ)) ≤ (109 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk12_seam_5_1).elim
    · exact ⟨tree13, by simp [children12], tbl13, stepEq_13, childEq_13⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl12_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl12 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk12_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 13: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_13 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node13 b A B) : ∃ c ∈ children13, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node13 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk13_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk13_seam_3_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk13_seam_4_1).elim
    · exact ⟨tree14, by simp [children13], tbl14, stepEq_14, childEq_14⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 109)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (5 : Fin 7) = (31 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨5, by norm_num⟩ : Fin 7) = (31 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((31 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 109 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((31 / 2 : ℚ)) ≤ (109 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk13_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl13_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl13 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk13_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 14: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_14 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node14 b A B) : ∃ c ∈ children14, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node14 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk14_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk14_seam_3_1).elim
    · exact ⟨tree15, by simp [children14], tbl15, stepEq_15, childEq_15⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk14_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk14_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl14_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl14 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk14_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 15: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_15 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node15 b A B) : ∃ c ∈ children15, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node15 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk15_seam_2_1).elim
    · exact ⟨tree16, by simp [children15], tbl16, stepEq_16, childEq_16⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (3 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨3, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk15_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk15_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk15_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl15_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl15 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk15_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree19, by simp [children15], tbl19, stepEq_19, childEq_19⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 16: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_16 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node16 b A B) : ∃ c ∈ children16, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node16 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk16_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (3 : Fin 7) = (119 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨3, by norm_num⟩ : Fin 7) = (119 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((119 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((119 / 10 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk16_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (4 : Fin 7) = (2023 / 150 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨4, by norm_num⟩ : Fin 7) = (2023 / 150 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2023 / 150 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2023 / 150 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk16_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk16_seam_4_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 107)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (5 : Fin 7) = (34391 / 2250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨5, by norm_num⟩ : Fin 7) = (34391 / 2250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((34391 / 2250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 107 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((34391 / 2250 : ℚ)) ≤ (107 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk16_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree17, by simp [children16], tbl17, stepEq_17, childEq_17⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl16_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl16 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk16_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk16_seam_6_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 17: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_17 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node17 b A B) : ∃ c ∈ children17, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node17 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk17_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (3 : Fin 7) = (119 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨3, by norm_num⟩ : Fin 7) = (119 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((119 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((119 / 10 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk17_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (4 : Fin 7) = (2023 / 150 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨4, by norm_num⟩ : Fin 7) = (2023 / 150 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2023 / 150 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2023 / 150 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk17_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree18, by simp [children17], tbl18, stepEq_18, childEq_18⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 107)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (5 : Fin 7) = (34391 / 2250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨5, by norm_num⟩ : Fin 7) = (34391 / 2250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((34391 / 2250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 107 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((34391 / 2250 : ℚ)) ≤ (107 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk17_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node17, node16, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl17_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl17 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk17_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk17_seam_6_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 19: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_19 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node19 b A B) : ∃ c ∈ children19, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node19 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk19_seam_2_1).elim
    · exact ⟨tree20, by simp [children19], tbl20, stepEq_20, childEq_20⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk19_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk19_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk19_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree24, by simp [children19], tbl24, stepEq_24, childEq_24⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl19_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl19 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk19_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 20: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_20 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node20 b A B) : ∃ c ∈ children20, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node20 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk20_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk20_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk20_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree21, by simp [children20], tbl21, stepEq_21, childEq_21⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk20_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree22, by simp [children20], tbl22, stepEq_22, childEq_22⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl20_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl20 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk20_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 21: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_21 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node21 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 8, M = ceil(7·hi) = 70)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (2 : Fin 7) = (459 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨2, by norm_num⟩ : Fin 7) = (459 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((459 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 70 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((459 / 46 : ℚ)) ≤ (70 : ℚ))
    have h8 : j ≤ 8 := by omega
    interval_cases j
    · exact hseam sk21_seam_2_1
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact hseam sk21_seam_3_1
    · exact hfresh (by decide)
    · exact hseam sk21_seam_3_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk21_seam_4_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact hseam sk21_seam_5_1
    · exact hfresh (by decide)
    · exact hseam sk21_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node21, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl21_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl21 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact hseam sk21_seam_6_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hseam sk21_seam_6_4
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 22: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_22 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node22 b A B) : ∃ c ∈ children22, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node22 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk22_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk22_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk22_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree23, by simp [children22], tbl23, stepEq_23, childEq_23⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk22_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node22, node20, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl22_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl22 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk22_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 24: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_24 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node24 b A B) : ∃ c ∈ children24, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node24 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (2 : Fin 7) = (21 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨2, by norm_num⟩ : Fin 7) = (21 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((21 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((21 / 2 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk24_seam_2_1).elim
    · exact ⟨tree25, by simp [children24], tbl25, stepEq_25, childEq_25⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk24_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk24_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk24_seam_4_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk24_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl24_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl24 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk24_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 25: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_25 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node25 b A B) : ∃ c ∈ children25, DfsMatch (boxN m4res_1_3_10_12_13_15_16) node25 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 9, M = ceil(7·hi) = 73)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (2 : Fin 7) = (2601 / 250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨2, by norm_num⟩ : Fin 7) = (2601 / 250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2601 / 250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 73 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2601 / 250 : ℚ)) ≤ (73 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam sk25_seam_2_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk25_seam_3_1).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk25_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree26, by simp [children25], tbl26, stepEq_26, childEq_26⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact (hseam sk25_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl25_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl25 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam sk25_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 26: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_26 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_3_10_12_13_15_16) node26 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 25)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (1 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_1_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨1, by norm_num⟩ : Fin 7) = (7 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((7 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 25 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((7 / 2 : ℚ)) ≤ (25 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 8, M = ceil(7·hi) = 70)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (2 : Fin 7) = (459 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_2_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨2, by norm_num⟩ : Fin 7) = (459 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((459 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 70 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((459 / 46 : ℚ)) ≤ (70 : ℚ))
    have h8 : j ≤ 8 := by omega
    interval_cases j
    · exact hseam sk26_seam_2_1
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (3 : Fin 7) = (561 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_3_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨3, by norm_num⟩ : Fin 7) = (561 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 46 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact hseam sk26_seam_3_1
    · exact hfresh (by decide)
    · exact hseam sk26_seam_3_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (4 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_4_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨4, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk26_seam_4_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 13, M = ceil(7·hi) = 108)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (5 : Fin 7) = (153 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_5_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨5, by norm_num⟩ : Fin 7) = (153 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((153 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 108 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((153 / 10 : ℚ)) ≤ (108 : ℚ))
    have h8 : j ≤ 13 := by omega
    interval_cases j
    · exact hseam sk26_seam_5_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [node26, node25, node24, node19, node15, node14, node13, node12] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_3_10_12_13_15_16, tbl26_c_6_0]
    have hval : dfsHi (boxN m4res_1_3_10_12_13_15_16) tbl26 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact hseam sk26_seam_6_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hseam sk26_seam_6_4
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


#print axioms enumMatch_0
#print axioms enumMatch_1
#print axioms enumMatch_2
#print axioms enumMatch_3
#print axioms enumMatch_5
#print axioms enumMatch_6
#print axioms enumMatch_9
#print axioms enumMatch_10
#print axioms enumMatch_12
#print axioms enumMatch_13
#print axioms enumMatch_14
#print axioms enumMatch_15
#print axioms enumMatch_16
#print axioms enumMatch_17
#print axioms enumMatch_19
#print axioms enumMatch_20
#print axioms enumDead_21
#print axioms enumMatch_22
#print axioms enumMatch_24
#print axioms enumMatch_25
#print axioms enumDead_26

/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/

theorem closed_26 : DfsClosed tree26 := by
  simp only [tree26, DfsClosed]
  exact nodeOK_26

#print axioms closed_26
theorem closed_25 : DfsClosed tree25 := by
  simp only [tree25, DfsClosed]
  refine ⟨nodeOK_25, ?_⟩
  intro t ht
  simp only [children25, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_26
  · exact absurd ht'1 (by simp)

#print axioms closed_25
theorem closed_24 : DfsClosed tree24 := by
  simp only [tree24, DfsClosed]
  refine ⟨nodeOK_24, ?_⟩
  intro t ht
  simp only [children24, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_25
  · exact absurd ht'1 (by simp)

#print axioms closed_24
theorem closed_23 : DfsClosed tree23 := by
  simp only [tree23, DfsClosed]
  exact nodeOK_23

#print axioms closed_23
theorem closed_22 : DfsClosed tree22 := by
  simp only [tree22, DfsClosed]
  refine ⟨nodeOK_22, ?_⟩
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_23
  · exact absurd ht'1 (by simp)

#print axioms closed_22
theorem closed_21 : DfsClosed tree21 := by
  simp only [tree21, DfsClosed]
  exact nodeOK_21

#print axioms closed_21
theorem closed_20 : DfsClosed tree20 := by
  simp only [tree20, DfsClosed]
  refine ⟨nodeOK_20, ?_⟩
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_21
  · rcases ht'1 with rfl | ht'2
    · exact closed_22
    · exact absurd ht'2 (by simp)

#print axioms closed_20
theorem closed_19 : DfsClosed tree19 := by
  simp only [tree19, DfsClosed]
  refine ⟨nodeOK_19, ?_⟩
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_20
  · rcases ht'1 with rfl | ht'2
    · exact closed_24
    · exact absurd ht'2 (by simp)

#print axioms closed_19
theorem closed_18 : DfsClosed tree18 := by
  simp only [tree18, DfsClosed]
  exact nodeOK_18

#print axioms closed_18
theorem closed_17 : DfsClosed tree17 := by
  simp only [tree17, DfsClosed]
  refine ⟨nodeOK_17, ?_⟩
  intro t ht
  simp only [children17, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_18
  · exact absurd ht'1 (by simp)

#print axioms closed_17
theorem closed_16 : DfsClosed tree16 := by
  simp only [tree16, DfsClosed]
  refine ⟨nodeOK_16, ?_⟩
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_17
  · exact absurd ht'1 (by simp)

#print axioms closed_16
theorem closed_15 : DfsClosed tree15 := by
  simp only [tree15, DfsClosed]
  refine ⟨nodeOK_15, ?_⟩
  intro t ht
  simp only [children15, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_16
  · rcases ht'1 with rfl | ht'2
    · exact closed_19
    · exact absurd ht'2 (by simp)

#print axioms closed_15
theorem closed_14 : DfsClosed tree14 := by
  simp only [tree14, DfsClosed]
  refine ⟨nodeOK_14, ?_⟩
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_15
  · exact absurd ht'1 (by simp)

#print axioms closed_14
theorem closed_13 : DfsClosed tree13 := by
  simp only [tree13, DfsClosed]
  refine ⟨nodeOK_13, ?_⟩
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_14
  · exact absurd ht'1 (by simp)

#print axioms closed_13
theorem closed_12 : DfsClosed tree12 := by
  simp only [tree12, DfsClosed]
  refine ⟨nodeOK_12, ?_⟩
  intro t ht
  simp only [children12, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_13
  · exact absurd ht'1 (by simp)

#print axioms closed_12
theorem closed_11 : DfsClosed tree11 := by
  simp only [tree11, DfsClosed]
  exact nodeOK_11

#print axioms closed_11
theorem closed_10 : DfsClosed tree10 := by
  simp only [tree10, DfsClosed]
  refine ⟨nodeOK_10, ?_⟩
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_11
  · exact absurd ht'1 (by simp)

#print axioms closed_10
theorem closed_9 : DfsClosed tree9 := by
  simp only [tree9, DfsClosed]
  refine ⟨nodeOK_9, ?_⟩
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_10
  · exact absurd ht'1 (by simp)

#print axioms closed_9
theorem closed_8 : DfsClosed tree8 := by
  simp only [tree8, DfsClosed]
  exact nodeOK_8

#print axioms closed_8
theorem closed_7 : DfsClosed tree7 := by
  simp only [tree7, DfsClosed]
  exact nodeOK_7

#print axioms closed_7
theorem closed_6 : DfsClosed tree6 := by
  simp only [tree6, DfsClosed]
  refine ⟨nodeOK_6, ?_⟩
  intro t ht
  simp only [children6, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_7
  · rcases ht'1 with rfl | ht'2
    · exact closed_8
    · exact absurd ht'2 (by simp)

#print axioms closed_6
theorem closed_5 : DfsClosed tree5 := by
  simp only [tree5, DfsClosed]
  refine ⟨nodeOK_5, ?_⟩
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_6
  · rcases ht'1 with rfl | ht'2
    · exact closed_9
    · exact absurd ht'2 (by simp)

#print axioms closed_5
theorem closed_4 : DfsClosed tree4 := by
  simp only [tree4, DfsClosed]
  exact nodeOK_4

#print axioms closed_4
theorem closed_3 : DfsClosed tree3 := by
  simp only [tree3, DfsClosed]
  refine ⟨nodeOK_3, ?_⟩
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_4
  · exact absurd ht'1 (by simp)

#print axioms closed_3
theorem closed_2 : DfsClosed tree2 := by
  simp only [tree2, DfsClosed]
  refine ⟨nodeOK_2, ?_⟩
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_3
  · rcases ht'1 with rfl | ht'2
    · exact closed_5
    · exact absurd ht'2 (by simp)

#print axioms closed_2
theorem closed_1 : DfsClosed tree1 := by
  simp only [tree1, DfsClosed]
  refine ⟨nodeOK_1, ?_⟩
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_2
  · exact absurd ht'1 (by simp)

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

theorem enum_26 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree26 := by
  simp only [tree26, DfsEnum]
  exact fun b A B hf => enumDead_26 b A B hf

#print axioms enum_26
theorem enum_25 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree25 := by
  simp only [tree25, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_25 b A B hf, ?_⟩
  intro t ht
  simp only [children25, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_26
  · exact absurd ht'1 (by simp)

#print axioms enum_25
theorem enum_24 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree24 := by
  simp only [tree24, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_24 b A B hf, ?_⟩
  intro t ht
  simp only [children24, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_25
  · exact absurd ht'1 (by simp)

#print axioms enum_24
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_23 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree23 := by
  simp only [tree23, DfsEnum]

#print axioms enum_23
theorem enum_22 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree22 := by
  simp only [tree22, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_22 b A B hf, ?_⟩
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_23
  · exact absurd ht'1 (by simp)

#print axioms enum_22
theorem enum_21 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree21 := by
  simp only [tree21, DfsEnum]
  exact fun b A B hf => enumDead_21 b A B hf

#print axioms enum_21
theorem enum_20 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree20 := by
  simp only [tree20, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_20 b A B hf, ?_⟩
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_21
  · rcases ht'1 with rfl | ht'2
    · exact enum_22
    · exact absurd ht'2 (by simp)

#print axioms enum_20
theorem enum_19 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree19 := by
  simp only [tree19, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_19 b A B hf, ?_⟩
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_20
  · rcases ht'1 with rfl | ht'2
    · exact enum_24
    · exact absurd ht'2 (by simp)

#print axioms enum_19
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_18 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree18 := by
  simp only [tree18, DfsEnum]

#print axioms enum_18
theorem enum_17 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree17 := by
  simp only [tree17, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_17 b A B hf, ?_⟩
  intro t ht
  simp only [children17, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_18
  · exact absurd ht'1 (by simp)

#print axioms enum_17
theorem enum_16 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree16 := by
  simp only [tree16, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_16 b A B hf, ?_⟩
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_17
  · exact absurd ht'1 (by simp)

#print axioms enum_16
theorem enum_15 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree15 := by
  simp only [tree15, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_15 b A B hf, ?_⟩
  intro t ht
  simp only [children15, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_16
  · rcases ht'1 with rfl | ht'2
    · exact enum_19
    · exact absurd ht'2 (by simp)

#print axioms enum_15
theorem enum_14 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree14 := by
  simp only [tree14, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_14 b A B hf, ?_⟩
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_15
  · exact absurd ht'1 (by simp)

#print axioms enum_14
theorem enum_13 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree13 := by
  simp only [tree13, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_13 b A B hf, ?_⟩
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_14
  · exact absurd ht'1 (by simp)

#print axioms enum_13
theorem enum_12 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree12 := by
  simp only [tree12, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_12 b A B hf, ?_⟩
  intro t ht
  simp only [children12, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_13
  · exact absurd ht'1 (by simp)

#print axioms enum_12
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_11 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree11 := by
  simp only [tree11, DfsEnum]

#print axioms enum_11
theorem enum_10 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree10 := by
  simp only [tree10, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_10 b A B hf, ?_⟩
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_11
  · exact absurd ht'1 (by simp)

#print axioms enum_10
theorem enum_9 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree9 := by
  simp only [tree9, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_9 b A B hf, ?_⟩
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_10
  · exact absurd ht'1 (by simp)

#print axioms enum_9
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_8 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree8 := by
  simp only [tree8, DfsEnum]

#print axioms enum_8
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_7 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree7 := by
  simp only [tree7, DfsEnum]

#print axioms enum_7
theorem enum_6 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree6 := by
  simp only [tree6, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_6 b A B hf, ?_⟩
  intro t ht
  simp only [children6, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_7
  · rcases ht'1 with rfl | ht'2
    · exact enum_8
    · exact absurd ht'2 (by simp)

#print axioms enum_6
theorem enum_5 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree5 := by
  simp only [tree5, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_5 b A B hf, ?_⟩
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_6
  · rcases ht'1 with rfl | ht'2
    · exact enum_9
    · exact absurd ht'2 (by simp)

#print axioms enum_5
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_4 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree4 := by
  simp only [tree4, DfsEnum]

#print axioms enum_4
theorem enum_3 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree3 := by
  simp only [tree3, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_3 b A B hf, ?_⟩
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_4
  · exact absurd ht'1 (by simp)

#print axioms enum_3
theorem enum_2 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree2 := by
  simp only [tree2, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_2 b A B hf, ?_⟩
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_3
  · rcases ht'1 with rfl | ht'2
    · exact enum_5
    · exact absurd ht'2 (by simp)

#print axioms enum_2
theorem enum_1 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree1 := by
  simp only [tree1, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_1 b A B hf, ?_⟩
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_2
  · exact absurd ht'1 (by simp)

#print axioms enum_1
theorem enum_0 : DfsEnum (boxN m4res_1_3_10_12_13_15_16) tree0 := by
  simp only [tree0, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_0 b A B hf, ?_⟩
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_1
  · exact absurd ht'1 (by simp)

#print axioms enum_0

/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_26 : DfsPruneDom tree26 := by
  simp only [tree26, DfsPruneDom]

#print axioms pd_26
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_25 : DfsPruneDom tree25 := by
  simp only [tree25, DfsPruneDom]
  intro t ht
  simp only [children25, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_26
  · exact absurd ht'1 (by simp)

#print axioms pd_25
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_24 : DfsPruneDom tree24 := by
  simp only [tree24, DfsPruneDom]
  intro t ht
  simp only [children24, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_25
  · exact absurd ht'1 (by simp)

#print axioms pd_24
theorem pd_23 (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree23 :=
  hprune_23

#print axioms pd_23
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_22 (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree22 := by
  simp only [tree22, DfsPruneDom]
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_23 hprune_23 
  · exact absurd ht'1 (by simp)

#print axioms pd_22
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_21 : DfsPruneDom tree21 := by
  simp only [tree21, DfsPruneDom]

#print axioms pd_21
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_20 (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree20 := by
  simp only [tree20, DfsPruneDom]
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_21
  · rcases ht'1 with rfl | ht'2
    · exact pd_22 hprune_23 
    · exact absurd ht'2 (by simp)

#print axioms pd_20
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_19 (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree19 := by
  simp only [tree19, DfsPruneDom]
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_20 hprune_23 
  · rcases ht'1 with rfl | ht'2
    · exact pd_24
    · exact absurd ht'2 (by simp)

#print axioms pd_19
theorem pd_18 (hprune_18 : DfsPruneDom tree18) : DfsPruneDom tree18 :=
  hprune_18

#print axioms pd_18
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_17 (hprune_18 : DfsPruneDom tree18) : DfsPruneDom tree17 := by
  simp only [tree17, DfsPruneDom]
  intro t ht
  simp only [children17, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_18 hprune_18 
  · exact absurd ht'1 (by simp)

#print axioms pd_17
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_16 (hprune_18 : DfsPruneDom tree18) : DfsPruneDom tree16 := by
  simp only [tree16, DfsPruneDom]
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_17 hprune_18 
  · exact absurd ht'1 (by simp)

#print axioms pd_16
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_15 (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree15 := by
  simp only [tree15, DfsPruneDom]
  intro t ht
  simp only [children15, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_16 hprune_18 
  · rcases ht'1 with rfl | ht'2
    · exact pd_19 hprune_23 
    · exact absurd ht'2 (by simp)

#print axioms pd_15
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_14 (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree14 := by
  simp only [tree14, DfsPruneDom]
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_15 hprune_18 hprune_23 
  · exact absurd ht'1 (by simp)

#print axioms pd_14
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_13 (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree13 := by
  simp only [tree13, DfsPruneDom]
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_14 hprune_18 hprune_23 
  · exact absurd ht'1 (by simp)

#print axioms pd_13
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_12 (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) : DfsPruneDom tree12 := by
  simp only [tree12, DfsPruneDom]
  intro t ht
  simp only [children12, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_13 hprune_18 hprune_23 
  · exact absurd ht'1 (by simp)

#print axioms pd_12
theorem pd_11 (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree11 :=
  hprune_11

#print axioms pd_11
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_10 (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree10 := by
  simp only [tree10, DfsPruneDom]
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_11 hprune_11 
  · exact absurd ht'1 (by simp)

#print axioms pd_10
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_9 (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree9 := by
  simp only [tree9, DfsPruneDom]
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_10 hprune_11 
  · exact absurd ht'1 (by simp)

#print axioms pd_9
theorem pd_8 (hprune_8 : DfsPruneDom tree8) : DfsPruneDom tree8 :=
  hprune_8

#print axioms pd_8
theorem pd_7 (hprune_7 : DfsPruneDom tree7) : DfsPruneDom tree7 :=
  hprune_7

#print axioms pd_7
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_6 (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) : DfsPruneDom tree6 := by
  simp only [tree6, DfsPruneDom]
  intro t ht
  simp only [children6, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_7 hprune_7 
  · rcases ht'1 with rfl | ht'2
    · exact pd_8 hprune_8 
    · exact absurd ht'2 (by simp)

#print axioms pd_6
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_5 (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree5 := by
  simp only [tree5, DfsPruneDom]
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_6 hprune_7 hprune_8 
  · rcases ht'1 with rfl | ht'2
    · exact pd_9 hprune_11 
    · exact absurd ht'2 (by simp)

#print axioms pd_5
theorem pd_4 (hprune_4 : DfsPruneDom tree4) : DfsPruneDom tree4 :=
  hprune_4

#print axioms pd_4
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_3 (hprune_4 : DfsPruneDom tree4) : DfsPruneDom tree3 := by
  simp only [tree3, DfsPruneDom]
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_4 hprune_4 
  · exact absurd ht'1 (by simp)

#print axioms pd_3
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_2 (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree2 := by
  simp only [tree2, DfsPruneDom]
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_3 hprune_4 
  · rcases ht'1 with rfl | ht'2
    · exact pd_5 hprune_7 hprune_8 hprune_11 
    · exact absurd ht'2 (by simp)

#print axioms pd_2
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_1 (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree1 := by
  simp only [tree1, DfsPruneDom]
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_2 hprune_4 hprune_7 hprune_8 hprune_11 
  · exact absurd ht'1 (by simp)

#print axioms pd_1
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_0 (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) : DfsPruneDom tree0 := by
  simp only [tree0, DfsPruneDom]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_1 hprune_4 hprune_7 hprune_8 hprune_11 
  · exact absurd ht'1 (by simp)

#print axioms pd_0

/-! ## 6. The forest assemblies -/

/-- The FOREST is closed (the form the data connection consumes). -/
theorem hforestClosed : ∀ t ∈ forest, DfsClosed t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_0
  · rcases ht'1 with rfl | ht'2
    · exact closed_12
    · exact absurd ht'2 (by simp)

/-- The FOREST enumerates. -/
theorem hforestEnum : ∀ t ∈ forest, DfsEnum (boxN m4res_1_3_10_12_13_15_16) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_0
  · rcases ht'1 with rfl | ht'2
    · exact enum_12
    · exact absurd ht'2 (by simp)

/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly
OWED (b)
so this proof needs no hypotheses; at dead ends and internal nodes the condition is
inherited/vacuous. -/
theorem hforestPruneDom (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) : ∀ t ∈ forest, DfsPruneDom t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_0 hprune_4 hprune_7 hprune_8 hprune_11 
  · rcases ht'1 with rfl | ht'2
    · exact pd_12 hprune_18 hprune_23 
    · exact absurd ht'2 (by simp)

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 4** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_4 (h : DfsPruneDom tree4) : DfsPruneDom tree4 :=
  h

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 7** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_7 (h : DfsPruneDom tree7) : DfsPruneDom tree7 :=
  h

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 8** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_8 (h : DfsPruneDom tree8) : DfsPruneDom tree8 :=
  h

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 11** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_11 (h : DfsPruneDom tree11) : DfsPruneDom tree11 :=
  h

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 18** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_18 (h : DfsPruneDom tree18) : DfsPruneDom tree18 :=
  h

/-- **OWED (b) -- the per-prune-leaf domination at reach leaf 23** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only; no per-leaf reach_utc
state-graph dump exists, so this datum cannot be transcribed.  Needed artifact:
per-prune-leaf reach_utc verdict records. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_pruneDom_23 (h : DfsPruneDom tree23) : DfsPruneDom tree23 :=
  h

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;
the artifacts give only the reconstructed root states, no opening-match record.
Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade
statement of E810's strict-monotone reading for this box. -/
-- STANDING: OWED
theorem m4rung2_1_3_10_12_13_15_16_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_3_10_12_13_15_16) forest) :
    DfsRootAdm (boxN m4res_1_3_10_12_13_15_16) forest := hcadm

/-! ## 7. The census envelope and the composed theorems (generic data connection) -/

/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the
record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists
only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise
exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /
`m4boxClear_of_data` directly). -/
theorem hn17_1_3_10_12_13_15_16 : ∀ i : Fin 7, boxN m4res_1_3_10_12_13_15_16 i ≤ 17 := by
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

#print axioms hn17_1_3_10_12_13_15_16

/-- **The composed certificate theorem**: the banked record (`m4resData_1_3_10_12_13_15_16`,
[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the
90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim. -/
theorem m4rung2_1_3_10_12_13_15_16_cert (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) (hcadm : DfsRootAdm (boxN m4res_1_3_10_12_13_15_16) forest) :
    M4CertSound (boxN m4res_1_3_10_12_13_15_16) ∧
      ∀ k ∈ m4res_1_3_10_12_13_15_16.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  m4CertSound_of_data m4res_1_3_10_12_13_15_16 m4resData_1_3_10_12_13_15_16 forest hforestClosed hforestEnum
    (hforestPruneDom hprune_4 hprune_7 hprune_8 hprune_11 hprune_18 hprune_23 ) hcadm

/-- **The composed clear-point theorem (the scaling target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --
the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest
instead of a crown. -/
theorem m4rung2_1_3_10_12_13_15_16_boxClear (hprune_4 : DfsPruneDom tree4) (hprune_7 : DfsPruneDom tree7) (hprune_8 : DfsPruneDom tree8) (hprune_11 : DfsPruneDom tree11) (hprune_18 : DfsPruneDom tree18) (hprune_23 : DfsPruneDom tree23) (hcadm : DfsRootAdm (boxN m4res_1_3_10_12_13_15_16) forest)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_3_10_12_13_15_16) hn17_1_3_10_12_13_15_16)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_3_10_12_13_15_16) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_3_10_12_13_15_16) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_data m4res_1_3_10_12_13_15_16 hn17_1_3_10_12_13_15_16 hcc forest
    hforestClosed hforestEnum (hforestPruneDom hprune_4 hprune_7 hprune_8 hprune_11 hprune_18 hprune_23 ) hcadm g hface

#print axioms m4rung2_1_3_10_12_13_15_16_cert
#print axioms m4rung2_1_3_10_12_13_15_16_boxClear

end Fresh.M4CertRung2_1_3_10_12_13_15_16

