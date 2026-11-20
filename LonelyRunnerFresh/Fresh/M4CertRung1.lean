import Fresh.M4CertSound

/-!
# M4CertRung1: rung 1 of the per-box M4 certificate transcription (box (1,4,6,7,10,16,16))

Written 2026-11-20 by `m4rung1_gen_v1.py` from the reconstruction
(`experiments/n8/m4rung1_recon_v1.py`, [T 31/31] against both checkpoint artifacts and the
banked record `Fresh.MechDataBatch.m4res_1_4_6_7_10_16_16`).  No existing file is edited.

This file works ONE concrete rung of the transcription pattern that
`Fresh.M4CertSound.m4cert_1_4_6_7_10_16_16` carries as the named OWED
`DfsCert_1_4_6_7_10_16_16`: the box's closed, enumerating, prune-dominated DFS certificate
forest (51,748 nodes) consumed as literal `DfsCert` data.  The full forest is far beyond a
single kernel rung; this file transcribes the CROWN: DFS node 1293 of the reconstructed
tree (depth 6, last reading row 5, exit numerator 41, frontier sup 82/31), whose two leaf
children are one reach-prune leaf (node 1294, step (2,15,17)) and one dead-end leaf
(node 1295, step (4,23,25)) -- the smallest subtree containing BOTH leaf kinds, i.e. every
component of the pattern at literal scale.  Proven here, kernel-checked on the literals:
DfsClosed at all 3 nodes (`uExitOK = false`), DfsEnum at the internal node (all 53
Lean-spec candidates (b, A, B) with A = 8j-1, B = 8j+1, entry/hi < 7: each either killed
by the entry/frontier comparison, the seen-freshness set, or a seam failure
(`uStep = none`), or matched against the transcribed child; DfsEnum at the dead-end leaf
(all 52 candidates killed).  The reconstruction verified data-side over the WHOLE tree that
at every internal node the filter-passing candidates equal the actual children and at
every dead-end none pass (0 mismatches), and that the Lean-spec extra rows (rank 0, the
same reading row) never pass the full filters (0 holes) -- so the per-node pattern proven
here is the pattern for all 36,126 internal + 13,485 dead-end nodes of this box and the
2,328 boxes that follow.

OWED (named, not discharged by any existing artifact):
* `hprune_c0` (DfsPruneDom at the reach-prune leaf) -- OWED (b) of `Fresh.M4CertSound`'s
  header: the per-leaf `reach_utc` domination.  The artifacts record only aggregates
  (2,137 reach leaves; the leaf state sups 82/31 .. 2618/403); no per-leaf reach_utc
  state-graph dump exists.  Needed artifact: per-prune-leaf `reach_utc` verdict records.
* `hcadm` (DfsRootAdm) -- OWED (a): the E810 strict-monotone opening side.  The artifacts
  give only `nstart = 3` (plus the reconstructed root states in
  `m4rung1_roots_v1.json`); no opening-match record exists.  Needed artifact: per-root
  opening-match / soft-admissible-path records (or a proof-grade E810 monotone statement).
* the full-forest transcription itself -- the checkpoints store summary counts only
  (leaves/nodes/maxdepth/nstart/leaf kinds/leaf keys/pinches); the per-node tree had to be
  reconstructed by the verbatim re-run.  Needed artifact: a machine-readable full-tree
  dump per box (the reconstruction provides one for this box).
-/
namespace Fresh.M4CertRung1

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

/-! ## 1. The crown tables, node states and certificate literals (verbatim data) -/

/-- Crown table `tblRoot`: the DFS node's bound table, transcribed cell-verbatim
from the reconstruction of the box's certificate tree (exact rationals, strict
flags; `none` = unbounded). -/
def tblRoot : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 133 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 130 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 1235 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((28611 / 4550 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 2275 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 2275 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 26 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1729 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 247 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9537 / 910 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 455 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 133 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 19 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 133 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 182 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblRoot_c_0_0 : tblRoot (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_0_1 : tblRoot (0 : Fin 7) (1 : Fin 7) = some ((34 / 133 : ℚ), true) := rfl
theorem tblRoot_c_0_2 : tblRoot (0 : Fin 7) (2 : Fin 7) = some ((2 / 11 : ℚ), false) := rfl
theorem tblRoot_c_0_3 : tblRoot (0 : Fin 7) (3 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tblRoot_c_0_4 : tblRoot (0 : Fin 7) (4 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tblRoot_c_0_5 : tblRoot (0 : Fin 7) (5 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblRoot_c_0_6 : tblRoot (0 : Fin 7) (6 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblRoot_c_1_0 : tblRoot (1 : Fin 7) (0 : Fin 7) = some ((561 / 130 : ℚ), true) := rfl
theorem tblRoot_c_1_1 : tblRoot (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_1_2 : tblRoot (1 : Fin 7) (2 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tblRoot_c_1_3 : tblRoot (1 : Fin 7) (3 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblRoot_c_1_4 : tblRoot (1 : Fin 7) (4 : Fin 7) = some ((561 / 1235 : ℚ), true) := rfl
theorem tblRoot_c_1_5 : tblRoot (1 : Fin 7) (5 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblRoot_c_1_6 : tblRoot (1 : Fin 7) (6 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblRoot_c_2_0 : tblRoot (2 : Fin 7) (0 : Fin 7) = some ((28611 / 4550 : ℚ), true) := rfl
theorem tblRoot_c_2_1 : tblRoot (2 : Fin 7) (1 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblRoot_c_2_2 : tblRoot (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_2_3 : tblRoot (2 : Fin 7) (3 : Fin 7) = some ((153 / 175 : ℚ), true) := rfl
theorem tblRoot_c_2_4 : tblRoot (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblRoot_c_2_5 : tblRoot (2 : Fin 7) (5 : Fin 7) = some ((867 / 2275 : ℚ), true) := rfl
theorem tblRoot_c_2_6 : tblRoot (2 : Fin 7) (6 : Fin 7) = some ((867 / 2275 : ℚ), true) := rfl
theorem tblRoot_c_3_0 : tblRoot (3 : Fin 7) (0 : Fin 7) = some ((187 / 26 : ℚ), true) := rfl
theorem tblRoot_c_3_1 : tblRoot (3 : Fin 7) (1 : Fin 7) = some ((3179 / 1729 : ℚ), true) := rfl
theorem tblRoot_c_3_2 : tblRoot (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblRoot_c_3_3 : tblRoot (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_3_4 : tblRoot (3 : Fin 7) (4 : Fin 7) = some ((187 / 247 : ℚ), true) := rfl
theorem tblRoot_c_3_5 : tblRoot (3 : Fin 7) (5 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblRoot_c_3_6 : tblRoot (3 : Fin 7) (6 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblRoot_c_4_0 : tblRoot (4 : Fin 7) (0 : Fin 7) = some ((9537 / 910 : ℚ), true) := rfl
theorem tblRoot_c_4_1 : tblRoot (4 : Fin 7) (1 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblRoot_c_4_2 : tblRoot (4 : Fin 7) (2 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tblRoot_c_4_3 : tblRoot (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblRoot_c_4_4 : tblRoot (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_4_5 : tblRoot (4 : Fin 7) (5 : Fin 7) = some ((289 / 455 : ℚ), true) := rfl
theorem tblRoot_c_4_6 : tblRoot (4 : Fin 7) (6 : Fin 7) = some ((289 / 455 : ℚ), true) := rfl
theorem tblRoot_c_5_0 : tblRoot (5 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), true) := rfl
theorem tblRoot_c_5_1 : tblRoot (5 : Fin 7) (1 : Fin 7) = some ((561 / 133 : ℚ), true) := rfl
theorem tblRoot_c_5_2 : tblRoot (5 : Fin 7) (2 : Fin 7) = some ((3 : ℚ), true) := rfl
theorem tblRoot_c_5_3 : tblRoot (5 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblRoot_c_5_4 : tblRoot (5 : Fin 7) (4 : Fin 7) = some ((33 / 19 : ℚ), true) := rfl
theorem tblRoot_c_5_5 : tblRoot (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblRoot_c_5_6 : tblRoot (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblRoot_c_6_0 : tblRoot (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tblRoot_c_6_1 : tblRoot (6 : Fin 7) (1 : Fin 7) = some ((561 / 133 : ℚ), true) := rfl
theorem tblRoot_c_6_2 : tblRoot (6 : Fin 7) (2 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tblRoot_c_6_3 : tblRoot (6 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblRoot_c_6_4 : tblRoot (6 : Fin 7) (4 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tblRoot_c_6_5 : tblRoot (6 : Fin 7) (5 : Fin 7) = some ((187 / 182 : ℚ), true) := rfl
theorem tblRoot_c_6_6 : tblRoot (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Crown table `tblC0`: the DFS node's bound table, transcribed cell-verbatim
from the reconstruction of the box's certificate tree (exact rationals, strict
flags; `none` = unbounded). -/
def tblC0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 47775 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((697 / 4095 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((697 / 6825 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 130 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((697 / 975 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((697 / 1625 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((28611 / 4550 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 2275 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 2275 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 26 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11849 / 6825 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((697 / 585 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((697 / 975 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9537 / 910 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((11849 / 6825 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 455 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((697 / 175 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((41 / 15 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((41 / 25 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((130339 / 31850 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((7667 / 2730 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((7667 / 4550 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 182 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblC0_c_0_0 : tblC0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_0_1 : tblC0 (0 : Fin 7) (1 : Fin 7) = some ((11849 / 47775 : ℚ), true) := rfl
theorem tblC0_c_0_2 : tblC0 (0 : Fin 7) (2 : Fin 7) = some ((697 / 4095 : ℚ), true) := rfl
theorem tblC0_c_0_3 : tblC0 (0 : Fin 7) (3 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tblC0_c_0_4 : tblC0 (0 : Fin 7) (4 : Fin 7) = some ((697 / 6825 : ℚ), true) := rfl
theorem tblC0_c_0_5 : tblC0 (0 : Fin 7) (5 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblC0_c_0_6 : tblC0 (0 : Fin 7) (6 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblC0_c_1_0 : tblC0 (1 : Fin 7) (0 : Fin 7) = some ((561 / 130 : ℚ), true) := rfl
theorem tblC0_c_1_1 : tblC0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_1_2 : tblC0 (1 : Fin 7) (2 : Fin 7) = some ((697 / 975 : ℚ), true) := rfl
theorem tblC0_c_1_3 : tblC0 (1 : Fin 7) (3 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblC0_c_1_4 : tblC0 (1 : Fin 7) (4 : Fin 7) = some ((697 / 1625 : ℚ), true) := rfl
theorem tblC0_c_1_5 : tblC0 (1 : Fin 7) (5 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblC0_c_1_6 : tblC0 (1 : Fin 7) (6 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblC0_c_2_0 : tblC0 (2 : Fin 7) (0 : Fin 7) = some ((28611 / 4550 : ℚ), true) := rfl
theorem tblC0_c_2_1 : tblC0 (2 : Fin 7) (1 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblC0_c_2_2 : tblC0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_2_3 : tblC0 (2 : Fin 7) (3 : Fin 7) = some ((153 / 175 : ℚ), true) := rfl
theorem tblC0_c_2_4 : tblC0 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblC0_c_2_5 : tblC0 (2 : Fin 7) (5 : Fin 7) = some ((867 / 2275 : ℚ), true) := rfl
theorem tblC0_c_2_6 : tblC0 (2 : Fin 7) (6 : Fin 7) = some ((867 / 2275 : ℚ), true) := rfl
theorem tblC0_c_3_0 : tblC0 (3 : Fin 7) (0 : Fin 7) = some ((187 / 26 : ℚ), true) := rfl
theorem tblC0_c_3_1 : tblC0 (3 : Fin 7) (1 : Fin 7) = some ((11849 / 6825 : ℚ), true) := rfl
theorem tblC0_c_3_2 : tblC0 (3 : Fin 7) (2 : Fin 7) = some ((697 / 585 : ℚ), true) := rfl
theorem tblC0_c_3_3 : tblC0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_3_4 : tblC0 (3 : Fin 7) (4 : Fin 7) = some ((697 / 975 : ℚ), true) := rfl
theorem tblC0_c_3_5 : tblC0 (3 : Fin 7) (5 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblC0_c_3_6 : tblC0 (3 : Fin 7) (6 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblC0_c_4_0 : tblC0 (4 : Fin 7) (0 : Fin 7) = some ((9537 / 910 : ℚ), true) := rfl
theorem tblC0_c_4_1 : tblC0 (4 : Fin 7) (1 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblC0_c_4_2 : tblC0 (4 : Fin 7) (2 : Fin 7) = some ((11849 / 6825 : ℚ), true) := rfl
theorem tblC0_c_4_3 : tblC0 (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblC0_c_4_4 : tblC0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_4_5 : tblC0 (4 : Fin 7) (5 : Fin 7) = some ((289 / 455 : ℚ), true) := rfl
theorem tblC0_c_4_6 : tblC0 (4 : Fin 7) (6 : Fin 7) = some ((289 / 455 : ℚ), true) := rfl
theorem tblC0_c_5_0 : tblC0 (5 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), true) := rfl
theorem tblC0_c_5_1 : tblC0 (5 : Fin 7) (1 : Fin 7) = some ((697 / 175 : ℚ), true) := rfl
theorem tblC0_c_5_2 : tblC0 (5 : Fin 7) (2 : Fin 7) = some ((41 / 15 : ℚ), true) := rfl
theorem tblC0_c_5_3 : tblC0 (5 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblC0_c_5_4 : tblC0 (5 : Fin 7) (4 : Fin 7) = some ((41 / 25 : ℚ), true) := rfl
theorem tblC0_c_5_5 : tblC0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC0_c_5_6 : tblC0 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblC0_c_6_0 : tblC0 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tblC0_c_6_1 : tblC0 (6 : Fin 7) (1 : Fin 7) = some ((130339 / 31850 : ℚ), true) := rfl
theorem tblC0_c_6_2 : tblC0 (6 : Fin 7) (2 : Fin 7) = some ((7667 / 2730 : ℚ), true) := rfl
theorem tblC0_c_6_3 : tblC0 (6 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblC0_c_6_4 : tblC0 (6 : Fin 7) (4 : Fin 7) = some ((7667 / 4550 : ℚ), true) := rfl
theorem tblC0_c_6_5 : tblC0 (6 : Fin 7) (5 : Fin 7) = some ((187 / 182 : ℚ), true) := rfl
theorem tblC0_c_6_6 : tblC0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Crown table `tblC1`: the DFS node's bound table, transcribed cell-verbatim
from the reconstruction of the box's certificate tree (exact rationals, strict
flags; `none` = unbounded). -/
def tblC1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((34 / 133 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 19 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 273 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((561 / 130 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((561 / 1235 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 65 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((495 / 82 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((495 / 574 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 41 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 41 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 26 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1729 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 247 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((825 / 82 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((75 / 41 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((825 / 574 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 41 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 41 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 133 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 19 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((33 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((561 / 133 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 19 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 182 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblC1_c_0_0 : tblC1 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_0_1 : tblC1 (0 : Fin 7) (1 : Fin 7) = some ((34 / 133 : ℚ), true) := rfl
theorem tblC1_c_0_2 : tblC1 (0 : Fin 7) (2 : Fin 7) = some ((2 / 11 : ℚ), false) := rfl
theorem tblC1_c_0_3 : tblC1 (0 : Fin 7) (3 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tblC1_c_0_4 : tblC1 (0 : Fin 7) (4 : Fin 7) = some ((2 / 19 : ℚ), false) := rfl
theorem tblC1_c_0_5 : tblC1 (0 : Fin 7) (5 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblC1_c_0_6 : tblC1 (0 : Fin 7) (6 : Fin 7) = some ((17 / 273 : ℚ), true) := rfl
theorem tblC1_c_1_0 : tblC1 (1 : Fin 7) (0 : Fin 7) = some ((561 / 130 : ℚ), true) := rfl
theorem tblC1_c_1_1 : tblC1 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_1_2 : tblC1 (1 : Fin 7) (2 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tblC1_c_1_3 : tblC1 (1 : Fin 7) (3 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblC1_c_1_4 : tblC1 (1 : Fin 7) (4 : Fin 7) = some ((561 / 1235 : ℚ), true) := rfl
theorem tblC1_c_1_5 : tblC1 (1 : Fin 7) (5 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblC1_c_1_6 : tblC1 (1 : Fin 7) (6 : Fin 7) = some ((17 / 65 : ℚ), true) := rfl
theorem tblC1_c_2_0 : tblC1 (2 : Fin 7) (0 : Fin 7) = some ((495 / 82 : ℚ), true) := rfl
theorem tblC1_c_2_1 : tblC1 (2 : Fin 7) (1 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblC1_c_2_2 : tblC1 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_2_3 : tblC1 (2 : Fin 7) (3 : Fin 7) = some ((495 / 574 : ℚ), true) := rfl
theorem tblC1_c_2_4 : tblC1 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblC1_c_2_5 : tblC1 (2 : Fin 7) (5 : Fin 7) = some ((15 / 41 : ℚ), true) := rfl
theorem tblC1_c_2_6 : tblC1 (2 : Fin 7) (6 : Fin 7) = some ((15 / 41 : ℚ), true) := rfl
theorem tblC1_c_3_0 : tblC1 (3 : Fin 7) (0 : Fin 7) = some ((187 / 26 : ℚ), true) := rfl
theorem tblC1_c_3_1 : tblC1 (3 : Fin 7) (1 : Fin 7) = some ((3179 / 1729 : ℚ), true) := rfl
theorem tblC1_c_3_2 : tblC1 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblC1_c_3_3 : tblC1 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_3_4 : tblC1 (3 : Fin 7) (4 : Fin 7) = some ((187 / 247 : ℚ), true) := rfl
theorem tblC1_c_3_5 : tblC1 (3 : Fin 7) (5 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblC1_c_3_6 : tblC1 (3 : Fin 7) (6 : Fin 7) = some ((17 / 39 : ℚ), true) := rfl
theorem tblC1_c_4_0 : tblC1 (4 : Fin 7) (0 : Fin 7) = some ((825 / 82 : ℚ), true) := rfl
theorem tblC1_c_4_1 : tblC1 (4 : Fin 7) (1 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblC1_c_4_2 : tblC1 (4 : Fin 7) (2 : Fin 7) = some ((75 / 41 : ℚ), true) := rfl
theorem tblC1_c_4_3 : tblC1 (4 : Fin 7) (3 : Fin 7) = some ((825 / 574 : ℚ), true) := rfl
theorem tblC1_c_4_4 : tblC1 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_4_5 : tblC1 (4 : Fin 7) (5 : Fin 7) = some ((25 / 41 : ℚ), true) := rfl
theorem tblC1_c_4_6 : tblC1 (4 : Fin 7) (6 : Fin 7) = some ((25 / 41 : ℚ), true) := rfl
theorem tblC1_c_5_0 : tblC1 (5 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), true) := rfl
theorem tblC1_c_5_1 : tblC1 (5 : Fin 7) (1 : Fin 7) = some ((561 / 133 : ℚ), true) := rfl
theorem tblC1_c_5_2 : tblC1 (5 : Fin 7) (2 : Fin 7) = some ((3 : ℚ), true) := rfl
theorem tblC1_c_5_3 : tblC1 (5 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblC1_c_5_4 : tblC1 (5 : Fin 7) (4 : Fin 7) = some ((33 / 19 : ℚ), true) := rfl
theorem tblC1_c_5_5 : tblC1 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblC1_c_5_6 : tblC1 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblC1_c_6_0 : tblC1 (6 : Fin 7) (0 : Fin 7) = some ((33 / 2 : ℚ), false) := rfl
theorem tblC1_c_6_1 : tblC1 (6 : Fin 7) (1 : Fin 7) = some ((561 / 133 : ℚ), true) := rfl
theorem tblC1_c_6_2 : tblC1 (6 : Fin 7) (2 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tblC1_c_6_3 : tblC1 (6 : Fin 7) (3 : Fin 7) = some ((33 / 14 : ℚ), true) := rfl
theorem tblC1_c_6_4 : tblC1 (6 : Fin 7) (4 : Fin 7) = some ((33 / 19 : ℚ), false) := rfl
theorem tblC1_c_6_5 : tblC1 (6 : Fin 7) (5 : Fin 7) = some ((187 / 182 : ℚ), true) := rfl
theorem tblC1_c_6_6 : tblC1 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- The crown root: DFS node 1293 (depth 6, last reading row 5, exit numerator 41,
frontier sup 82/31, seen-set = its 6 ancestor zone pairs). -/
-- STANDING: DATA (transcribed verbatim from the box's reconstructed certificate tree)
def nodeRoot : DfsNode := ⟨tblRoot, (5 : Fin 7), (41 : ℚ), (82 / 31 : ℚ), {((1 : Fin 7), (9 : ℚ)), ((2 : Fin 7), (9 : ℚ)), ((3 : Fin 7), (17 : ℚ)), ((3 : Fin 7), (9 : ℚ)), ((4 : Fin 7), (17 : ℚ)), ((5 : Fin 7), (41 : ℚ))}⟩

/-- The reach-prune leaf: DFS node 1294 (step (2, 15, 17) from the root; the `reach_utc`
abstraction found no completing state -- kind `reach` of the checkpoint). -/
-- STANDING: DATA (transcribed verbatim; seen = the root's set plus the step pair)
def nodeC0 : DfsNode := ⟨tblC0, (2 : Fin 7), (17 : ℚ), (34 / 11 : ℚ), nodeRoot.seen ∪ {((2 : Fin 7), (17 : ℚ))}⟩

/-- The dead-end leaf: DFS node 1295 (step (4, 23, 25) from the root; no filter-passing
step -- kind `deadend` of the checkpoint). -/
-- STANDING: DATA (transcribed verbatim; seen = the root's set plus the step pair)
def nodeC1 : DfsNode := ⟨tblC1, (4 : Fin 7), (25 : ℚ), (50 / 19 : ℚ), nodeRoot.seen ∪ {((4 : Fin 7), (25 : ℚ))}⟩

/-- The two leaf certificates and the crown forest (a genuine subtree of the box's
closed certificate tree: every child of every retained internal node is retained). -/
-- STANDING: DATA
def cert_c0 : DfsCert := DfsCert.prune nodeC0
def cert_c1 : DfsCert := DfsCert.deadend nodeC1
def crown_children : List DfsCert := [cert_c0, cert_c1]
def crown_1 : DfsCert := DfsCert.node nodeRoot crown_children

/-! ## 2. The node completion checks fail at all three nodes (`DfsClosed`) -/

theorem nodeOK_root : DfsNodeOK (nodeRoot) := by
  show uExitOK tblRoot (5 : Fin 7) (41 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tblRoot_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tblRoot_c_0_5] <;> norm_num)]
  rfl

theorem nodeOK_c0 : DfsNodeOK (nodeC0) := by
  show uExitOK tblC0 (2 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tblC0_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tblC0_c_0_2] <;> norm_num)]
  rfl

theorem nodeOK_c1 : DfsNodeOK (nodeC1) := by
  show uExitOK tblC1 (4 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tblC1_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tblC1_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_root
#print axioms nodeOK_c0
#print axioms nodeOK_c1

/-! ## 3. The child steps (`DfsMatch`) and the seam kills -/

/-- Child c0's step (2, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is ground-false on the exact cells). -/
theorem addEq_c0_1 : uAdd tblRoot (5 : Fin 7) (2 : Fin 7) ((41 / 15 : ℚ)) true = some tblC0 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblRoot_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tblRoot_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblRoot, tblC0] <;> norm_num)

/-- Child c0's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_c0_2 : uAdd tblC0 (2 : Fin 7) (5 : Fin 7) ((17 / 41 : ℚ)) true = some tblC0 :=
  uAdd_eq_some_self (by simp [uKeepCur, tblC0_c_2_5] <;> norm_num)

/-- Child c0's full step equation. -/
theorem stepEq_c0 : uStep tblRoot (5 : Fin 7) (2 : Fin 7) (41 : ℚ) (15 : ℚ) (17 : ℚ) = some tblC0 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_c0_1 addEq_c0_2

/-- Child c0's `childState` equation: the child node is exactly the DFS expansion rule's
state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent set plus
the step pair). -/
theorem childEq_c0 : childState (boxN m4res_1_4_6_7_10_16_16) nodeRoot (2 : Fin 7) (17 : ℚ) tblC0 = DfsCert.root cert_c0 :=
  by
    simp only [childState, DfsCert.root, cert_c0, nodeC0]
    have hlo : dfsLo (boxN m4res_1_4_6_7_10_16_16) nodeRoot.U (2 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_4_6_7_10_16_16, nodeRoot, tblRoot_c_0_2]
    norm_num [hlo]

/-- Child c1's step (4, 23, 25): add 1 is keep-current (the stored bound is already tighter, table unchanged). -/
theorem addEq_c1_1 : uAdd tblRoot (5 : Fin 7) (4 : Fin 7) ((41 / 23 : ℚ)) true = some tblRoot :=
  uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_4] <;> norm_num)

/-- Child c1's step: add 2 propagates to the child table. -/
theorem addEq_c1_2 : uAdd tblRoot (4 : Fin 7) (5 : Fin 7) ((25 / 41 : ℚ)) true = some tblC1 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblRoot_c_4_5] <;> norm_num)
    (by simp [uBack, uBackCond, tblRoot_c_5_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblRoot, tblC1] <;> norm_num)

/-- Child c1's full step equation. -/
theorem stepEq_c1 : uStep tblRoot (5 : Fin 7) (4 : Fin 7) (41 : ℚ) (23 : ℚ) (25 : ℚ) = some tblC1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_c1_1 addEq_c1_2

/-- Child c1's `childState` equation: the child node is exactly the DFS expansion rule's
state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent set plus
the step pair). -/
theorem childEq_c1 : childState (boxN m4res_1_4_6_7_10_16_16) nodeRoot (4 : Fin 7) (25 : ℚ) tblC1 = DfsCert.root cert_c1 :=
  by
    simp only [childState, DfsCert.root, cert_c1, nodeC1]
    have hlo : dfsLo (boxN m4res_1_4_6_7_10_16_16) nodeRoot.U (4 : Fin 7) = (19 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_4_6_7_10_16_16, nodeRoot, tblRoot_c_0_4]
    norm_num [hlo]

#print axioms addEq_c0_1
#print axioms addEq_c0_2
#print axioms stepEq_c0
#print axioms childEq_c0
#print axioms addEq_c1_1
#print axioms addEq_c1_2
#print axioms stepEq_c1
#print axioms childEq_c1

/-- Seam-failure kills at the crown root: for the candidates that pass the entry and
freshness filters but fail a seam bound, `uStep = none` (kernel-evaluated on the
literal cells; each kill is the first `uAdd` rejected by the back-check, or the second
rejected after a keep-current first `uAdd`). -/
theorem skR_seam_0_1 : uStep tblRoot (5 : Fin 7) (0 : Fin 7) (41 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tblRoot_c_5_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tblRoot_c_0_5] <;> norm_num

theorem skR_seam_4_1 : uStep tblRoot (5 : Fin 7) (4 : Fin 7) (41 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (4 : Fin 7) ((41 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_4_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_4] <;> norm_num)

theorem skR_seam_5_1 : uStep tblRoot (5 : Fin 7) (5 : Fin 7) (41 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_5] <;> norm_num)

theorem skR_seam_5_2 : uStep tblRoot (5 : Fin 7) (5 : Fin 7) (41 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_5] <;> norm_num)

theorem skR_seam_5_3 : uStep tblRoot (5 : Fin 7) (5 : Fin 7) (41 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_5] <;> norm_num)

theorem skR_seam_5_4 : uStep tblRoot (5 : Fin 7) (5 : Fin 7) (41 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_5] <;> norm_num)

theorem skR_seam_6_1 : uStep tblRoot (5 : Fin 7) (6 : Fin 7) (41 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_6] <;> norm_num)

theorem skR_seam_6_2 : uStep tblRoot (5 : Fin 7) (6 : Fin 7) (41 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_6] <;> norm_num)

theorem skR_seam_6_3 : uStep tblRoot (5 : Fin 7) (6 : Fin 7) (41 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_6] <;> norm_num)

theorem skR_seam_6_4 : uStep tblRoot (5 : Fin 7) (6 : Fin 7) (41 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_6] <;> norm_num)

theorem skR_seam_6_5 : uStep tblRoot (5 : Fin 7) (6 : Fin 7) (41 : ℚ) (((8 * 5 - 1 : ℕ) : ℚ)) (((8 * 5 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblRoot (5 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (((8 * 5 - 1 : ℕ) : ℚ))) true = some tblRoot :=
    uAdd_eq_some_self (by simp [uKeepCur, tblRoot_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblRoot_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tblRoot_c_5_6] <;> norm_num)


/-- Seam-failure kills at the dead-end leaf: for the candidates that pass the entry and
freshness filters but fail a seam bound, `uStep = none` (kernel-evaluated on the
literal cells; each kill is the first `uAdd` rejected by the back-check, or the second
rejected after a keep-current first `uAdd`). -/
theorem skC1_seam_0_1 : uStep tblC1 (4 : Fin 7) (0 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tblC1_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tblC1_c_0_4] <;> norm_num

theorem skC1_seam_2_2 : uStep tblC1 (4 : Fin 7) (2 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tblC1_c_4_2] <;> norm_num) ?_
  simp [uBack, uBackCond, tblC1_c_2_4] <;> norm_num

theorem skC1_seam_4_1 : uStep tblC1 (4 : Fin 7) (4 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_4] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_4_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_4] <;> norm_num)

theorem skC1_seam_5_1 : uStep tblC1 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_5] <;> norm_num)

theorem skC1_seam_5_2 : uStep tblC1 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_5] <;> norm_num)

theorem skC1_seam_5_3 : uStep tblC1 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_5] <;> norm_num)

theorem skC1_seam_5_4 : uStep tblC1 (4 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_5] <;> norm_num)

theorem skC1_seam_6_1 : uStep tblC1 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_6] <;> norm_num)

theorem skC1_seam_6_2 : uStep tblC1 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_6] <;> norm_num)

theorem skC1_seam_6_3 : uStep tblC1 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_6] <;> norm_num)

theorem skC1_seam_6_4 : uStep tblC1 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_6] <;> norm_num)

theorem skC1_seam_6_5 : uStep tblC1 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 5 - 1 : ℕ) : ℚ)) (((8 * 5 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tblC1 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 5 - 1 : ℕ) : ℚ))) true = some tblC1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tblC1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tblC1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tblC1_c_4_6] <;> norm_num)


#print axioms skR_seam_0_1
#print axioms skR_seam_4_1
#print axioms skR_seam_5_1
#print axioms skR_seam_5_2
#print axioms skR_seam_5_3
#print axioms skR_seam_5_4
#print axioms skR_seam_6_1
#print axioms skR_seam_6_2
#print axioms skR_seam_6_3
#print axioms skR_seam_6_4
#print axioms skR_seam_6_5
#print axioms skC1_seam_0_1
#print axioms skC1_seam_2_2
#print axioms skC1_seam_4_1
#print axioms skC1_seam_5_1
#print axioms skC1_seam_5_2
#print axioms skC1_seam_5_3
#print axioms skC1_seam_5_4
#print axioms skC1_seam_6_1
#print axioms skC1_seam_6_2
#print axioms skC1_seam_6_3
#print axioms skC1_seam_6_4
#print axioms skC1_seam_6_5

/-! ## 4. The enumeration proofs (`DfsEnum` at the internal node and the dead-end leaf) -/

/-- The `match-completeness` at nodeRoot: for EVERY Lean-spec candidate step `(b, A, B)` -- b ranging
over all 7 rows (including rank 0, which the run never expands, and the same reading
row, which the run skips -- the reconstruction audited 0 holes there over the whole
tree), A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by
the entry/frontier comparison, the seen-freshness set, or a seam failure, or (internal
node) matched against the transcribed child. -/
theorem enumMatch_root (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_4_6_7_10_16_16) nodeRoot b A B) : ∃ c ∈ crown_children, DfsMatch (boxN m4res_1_4_6_7_10_16_16) nodeRoot b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam skR_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 31)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (1 : Fin 7) = (561 / 130 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_1_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨1, by norm_num⟩ : Fin 7) = (561 / 130 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 130 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 31 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 130 : ℚ)) ≤ (31 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (2 : Fin 7) = (28611 / 4550 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_2_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨2, by norm_num⟩ : Fin 7) = (28611 / 4550 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((28611 / 4550 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((28611 / 4550 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨cert_c0, by simp [crown_children], tblC0, stepEq_c0, childEq_c0⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 6, M = ceil(7·hi) = 51)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (3 : Fin 7) = (187 / 26 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_3_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨3, by norm_num⟩ : Fin 7) = (187 / 26 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((187 / 26 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 51 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((187 / 26 : ℚ)) ≤ (51 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 9, M = ceil(7·hi) = 74)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (4 : Fin 7) = (9537 / 910 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_4_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨4, by norm_num⟩ : Fin 7) = (9537 / 910 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9537 / 910 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 74 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9537 / 910 : ℚ)) ≤ (74 : ℚ))
    have h8 : j ≤ 9 := by omega
    interval_cases j
    · exact (hseam skR_seam_4_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨cert_c1, by simp [crown_children], tblC1, stepEq_c1, childEq_c1⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (5 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_5_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨5, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam skR_seam_5_1).elim
    · exact (hseam skR_seam_5_2).elim
    · exact (hseam skR_seam_5_3).elim
    · exact (hseam skR_seam_5_4).elim
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

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_6_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact (hseam skR_seam_6_1).elim
    · exact (hseam skR_seam_6_2).elim
    · exact (hseam skR_seam_6_3).elim
    · exact (hseam skR_seam_6_4).elim
    · exact (hseam skR_seam_6_5).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at nodeC1: for EVERY Lean-spec candidate step `(b, A, B)` -- b ranging
over all 7 rows (including rank 0, which the run never expands, and the same reading
row, which the run skips -- the reconstruction audited 0 holes there over the whole
tree), A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by
the entry/frontier comparison, the seen-freshness set, or a seam failure, or (internal
node) matched against the transcribed child. -/
theorem enumDead_c1 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_4_6_7_10_16_16) nodeC1 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam skC1_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 3, M = ceil(7·hi) = 31)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (1 : Fin 7) = (561 / 130 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_1_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨1, by norm_num⟩ : Fin 7) = (561 / 130 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((561 / 130 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 31 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((561 / 130 : ℚ)) ≤ (31 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 2 (jmax = 5, M = ceil(7·hi) = 43)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (2 : Fin 7) = (495 / 82 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_2_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨2, by norm_num⟩ : Fin 7) = (495 / 82 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((495 / 82 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 43 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((495 / 82 : ℚ)) ≤ (43 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hseam skC1_seam_2_2
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 6, M = ceil(7·hi) = 51)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (3 : Fin 7) = (187 / 26 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_3_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨3, by norm_num⟩ : Fin 7) = (187 / 26 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((187 / 26 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 51 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((187 / 26 : ℚ)) ≤ (51 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 8, M = ceil(7·hi) = 71)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (4 : Fin 7) = (825 / 82 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_4_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨4, by norm_num⟩ : Fin 7) = (825 / 82 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((825 / 82 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 71 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((825 / 82 : ℚ)) ≤ (71 : ℚ))
    have h8 : j ≤ 8 := by omega
    interval_cases j
    · exact hseam skC1_seam_4_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (5 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_5_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨5, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact hseam skC1_seam_5_1
    · exact hseam skC1_seam_5_2
    · exact hseam skC1_seam_5_3
    · exact hseam skC1_seam_5_4
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

  · -- b = row 6 (jmax = 14, M = ceil(7·hi) = 116)
    simp only [nodeC1, nodeRoot] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (6 : Fin 7) = (33 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblC1_c_6_0]
    have hval : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblC1 (⟨6, by norm_num⟩ : Fin 7) = (33 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((33 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 116 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((33 / 2 : ℚ)) ≤ (116 : ℚ))
    have h8 : j ≤ 14 := by omega
    interval_cases j
    · exact hseam skC1_seam_6_1
    · exact hseam skC1_seam_6_2
    · exact hseam skC1_seam_6_3
    · exact hseam skC1_seam_6_4
    · exact hseam skC1_seam_6_5
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


#print axioms enumMatch_root
#print axioms enumDead_c1

/-! ## 5. The assembly and the composed theorems -/

/-- The crown FOREST is closed (the form `DfsCert_1_4_6_7_10_16_16` consumes): both
leaves fail the completion check. -/
theorem hcrownClosed : ∀ t ∈ crown_children, DfsClosed t := by
  intro t ht
  simp only [crown_children, List.mem_cons] at ht
  rcases ht with rfl | ht'
  · simp only [cert_c0, DfsClosed]; exact nodeOK_c0
  · rcases ht' with rfl | ht''
    · simp only [cert_c1, DfsClosed]; exact nodeOK_c1
    · exact absurd ht'' (by simp)

/-- The crown FOREST enumerates: the prune leaf is vacuous, the dead end kills every
filter-passing step. -/
theorem hcrownEnum : ∀ t ∈ crown_children, DfsEnum (boxN m4res_1_4_6_7_10_16_16) t := by
  intro t ht
  simp only [crown_children, List.mem_cons] at ht
  rcases ht with rfl | ht'
  · simp only [cert_c0, DfsEnum]
  · rcases ht' with rfl | ht''
    · simp only [cert_c1, DfsEnum]; exact fun b A B hf => enumDead_c1 b A B hf
    · exact absurd ht'' (by simp)

/-- The per-prune-leaf domination over the crown forest: trivial at the dead-end leaf,
and at the reach-prune leaf exactly OWED (b). -/
theorem hcrownPruneDom (hprune_c0 : DfsPruneDom cert_c0) :
    ∀ t ∈ crown_children, DfsPruneDom t := by
  intro t ht
  simp only [crown_children, List.mem_cons] at ht
  rcases ht with rfl | ht'
  · exact hprune_c0
  · rcases ht' with rfl | ht''
    · simp only [cert_c1, DfsPruneDom]
    · exact absurd ht'' (by simp)

/-- The crown TREE (the root with its two children) is closed and enumerating -- the
root's own verdicts ride on the forest forms above (the pattern-match predicates are
unfolded by their simp equations, then the conjunction is assembled). -/
theorem hcrownTreeClosed : DfsClosed crown_1 := by
  simp only [crown_1, DfsClosed]
  exact ⟨nodeOK_root, hcrownClosed⟩

theorem hcrownTreeEnum : DfsEnum (boxN m4res_1_4_6_7_10_16_16) crown_1 := by
  simp only [crown_1, DfsEnum]
  exact ⟨fun b A B hf => enumMatch_root b A B hf, hcrownEnum⟩

#print axioms hcrownClosed
#print axioms hcrownEnum
#print axioms hcrownPruneDom
#print axioms hcrownTreeClosed
#print axioms hcrownTreeEnum

/-- **OWED (b) -- the per-prune-leaf domination at the reach leaf** (the reach_utc
abstraction's [P] conclusion: no completing real chain passes through the leaf).  The
checkpoint artifacts record the AGGREGATE verdict only (2,137 reach leaves and the state
sup pinches); no per-leaf reach_utc state-graph dump exists, so this datum cannot be
transcribed.  Needed artifact: per-prune-leaf reach_utc verdict records (the completing-
state absence per leaf state). -/
-- STANDING: OWED
theorem m4rung1_pruneDom_c0 (hprune_c0 : DfsPruneDom cert_c0) : DfsPruneDom cert_c0 :=
  hprune_c0

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  The artifacts give only `nstart = 3` and
the reconstructed root states (`m4rung1_roots_v1.json`); the opening-match argument is not
recorded.  Needed artifact: per-root opening-match / soft-admissible-path records, or a
proof-grade statement of E810's strict-monotone reading for this box.  Note this is
stated for the CROWN forest; for the full 3-root forest the same hypothesis shape is
what `Fresh.M4Cert.DfsCert_1_4_6_7_10_16_16` carries. -/
-- STANDING: OWED
theorem m4rung1_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) crown_children) :
    DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) crown_children := hcadm

/-- **The banked-instance bridge**: the crown's proven pieces + the two OWEDs assemble
into exactly the hypothesis `Fresh.M4Cert.DfsCert_1_4_6_7_10_16_16` demands of `T` -- the
shape the remaining 2,328 boxes must fill by the same generator run. -/
theorem m4rung1_bankedInstance (hprune_c0 : DfsPruneDom cert_c0)
    (hcadm : DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) crown_children) :
    DfsCert_1_4_6_7_10_16_16 crown_children :=
  ⟨hcrownClosed, hcrownEnum, hcrownPruneDom hprune_c0, hcadm⟩

/-- **The composed certificate theorem**: the banked record (`m4resData_1_4_6_7_10_16_16`,
[T 2329/2329]) + the crown certificate deliver the box kill AND the 90-type leaf-key
embedding, through `Fresh.M4Cert.m4cert_1_4_6_7_10_16_16` verbatim. -/
theorem m4rung1_cert (hprune_c0 : DfsPruneDom cert_c0)
    (hcadm : DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) crown_children) :
    M4CertSound (boxN m4res_1_4_6_7_10_16_16) ∧
      ∀ k ∈ m4res_1_4_6_7_10_16_16.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  m4cert_1_4_6_7_10_16_16 crown_children (m4rung1_bankedInstance hprune_c0 hcadm)

/-- **The composed clear-point theorem (the rung's target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the crown pieces -- the
hypothesis shape is exactly the banked instance's (`m4boxClear_1_4_6_7_10_16_16`), with
`T` now a transcribed literal forest instead of a variable. -/
theorem m4rung1_boxClear (hprune_c0 : DfsPruneDom cert_c0)
    (hcadm : DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) crown_children)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_4_6_7_10_16_16) hn17_1_4_6_7_10_16_16)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_4_6_7_10_16_16) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_4_6_7_10_16_16) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_data m4res_1_4_6_7_10_16_16 hn17_1_4_6_7_10_16_16 hcc crown_children
    hcrownClosed hcrownEnum (hcrownPruneDom hprune_c0) hcadm g hface

#print axioms m4rung1_bankedInstance
#print axioms m4rung1_cert
#print axioms m4rung1_boxClear

end Fresh.M4CertRung1
