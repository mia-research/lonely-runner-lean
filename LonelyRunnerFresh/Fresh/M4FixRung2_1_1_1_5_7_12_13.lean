import Fresh.M4CertSound
import Fresh.M4FixResBank_v1
import Fresh.ReachUtcProof

/-!
# M4FixRung2_1_1_1_5_7_12_13: per-box M4 certificate transcription, box (1, 1, 1, 5, 7, 12, 13)

Written 2026-11-20 by `m4fix_gen_v1.py` from the per-box reconstruction
(`experiments/n8/m4fix_recon_v1.py`, [T]-verified against both checkpoint artifacts
(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the
CONSTRUCTED record `Fresh.M4FixResBank_v1.m4res_1_1_1_5_7_12_13`).  No existing file is edited.

This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a
WHOLE certificate FOREST: all 12 nodes of the box's reconstructed DFS certificate
tree(s) -- 8 internal, 1 reach-prune leaves,
3 dead-end leaves, 1 start-zone root(s) -- transcribed as literal `DfsCert` data: tables as
49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,
seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,
and the composed theorems through the GENERIC data connection
(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).

OWED (named, not discharged by any existing artifact):
* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`'s header: the E810 strict-monotone
  opening side (hypothesis-identity stub here, as in rung 1).
* OWED (b) -- now SPLIT by the per-leaf verdict transcription (section 5b): the
  verdict side of every reach-prune leaf's `reach_utc` domination is transcribed
  from `experiments/n8/reachutc_1_1_1_5_7_12_13.json` and DISCHARGED here
  (`verdictNoCompl_*`); what remains OWED per leaf is the `[P]` state-graph
  PROJECTION instance `reachutcProj_*` (realized chain → completing state
  reachable), being proved in parallel in `Fresh/ReachUtcProof.lean`.
-/

namespace Fresh.M4FixRung2_1_1_1_5_7_12_13

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

/-- Table of DFS node 0 (internal, depth 1, last reading row 4, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl0_c_0_0 : tbl0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_0_1 : tbl0 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_2 : tbl0 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_3 : tbl0 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl0_c_0_4 : tbl0 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl0_c_0_5 : tbl0 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl0_c_0_6 : tbl0 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl0_c_1_0 : tbl0 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_1_1 : tbl0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_1_2 : tbl0 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_1_3 : tbl0 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), true) := rfl
theorem tbl0_c_1_4 : tbl0 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl0_c_1_5 : tbl0 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl0_c_1_6 : tbl0 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl0_c_2_0 : tbl0 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl0_c_2_1 : tbl0 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_2_2 : tbl0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_2_3 : tbl0 (2 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl0_c_2_4 : tbl0 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl0_c_2_5 : tbl0 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl0_c_2_6 : tbl0 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl0_c_3_0 : tbl0 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl0_c_3_1 : tbl0 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_2 : tbl0 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_3 : tbl0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_3_4 : tbl0 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl0_c_3_5 : tbl0 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl0_c_3_6 : tbl0 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl0_c_4_0 : tbl0 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl0_c_4_1 : tbl0 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_2 : tbl0 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_3 : tbl0 (4 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl0_c_4_4 : tbl0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_4_5 : tbl0 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl0_c_4_6 : tbl0 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl0_c_5_0 : tbl0 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl0_c_5_1 : tbl0 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_2 : tbl0 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_3 : tbl0 (5 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl0_c_5_4 : tbl0 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl0_c_5_5 : tbl0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_5_6 : tbl0 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_6_0 : tbl0 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl0_c_6_1 : tbl0 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_2 : tbl0 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_3 : tbl0 (6 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl0_c_6_4 : tbl0 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tbl0_c_6_5 : tbl0 (6 : Fin 7) (5 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl0_c_6_6 : tbl0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 1 (deadend, depth 2, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 49 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 98 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 98 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((99 / 14 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((99 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((99 / 175 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((225 / 98 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 98 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl1_c_0_0 : tbl1 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_0_1 : tbl1 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_0_2 : tbl1 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_0_3 : tbl1 (0 : Fin 7) (3 : Fin 7) = some ((9 / 49 : ℚ), true) := rfl
theorem tbl1_c_0_4 : tbl1 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl1_c_0_5 : tbl1 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl1_c_0_6 : tbl1 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl1_c_1_0 : tbl1 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl1_c_1_1 : tbl1 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_1_2 : tbl1 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_1_3 : tbl1 (1 : Fin 7) (3 : Fin 7) = some ((27 / 98 : ℚ), true) := rfl
theorem tbl1_c_1_4 : tbl1 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl1_c_1_5 : tbl1 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl1_c_1_6 : tbl1 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl1_c_2_0 : tbl1 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl1_c_2_1 : tbl1 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl1_c_2_2 : tbl1 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_2_3 : tbl1 (2 : Fin 7) (3 : Fin 7) = some ((27 / 98 : ℚ), true) := rfl
theorem tbl1_c_2_4 : tbl1 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl1_c_2_5 : tbl1 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl1_c_2_6 : tbl1 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl1_c_3_0 : tbl1 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl1_c_3_1 : tbl1 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl1_c_3_2 : tbl1 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl1_c_3_3 : tbl1 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_3_4 : tbl1 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl1_c_3_5 : tbl1 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl1_c_3_6 : tbl1 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl1_c_4_0 : tbl1 (4 : Fin 7) (0 : Fin 7) = some ((99 / 14 : ℚ), true) := rfl
theorem tbl1_c_4_1 : tbl1 (4 : Fin 7) (1 : Fin 7) = some ((99 / 14 : ℚ), true) := rfl
theorem tbl1_c_4_2 : tbl1 (4 : Fin 7) (2 : Fin 7) = some ((99 / 14 : ℚ), true) := rfl
theorem tbl1_c_4_3 : tbl1 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl1_c_4_4 : tbl1 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_4_5 : tbl1 (4 : Fin 7) (5 : Fin 7) = some ((99 / 161 : ℚ), true) := rfl
theorem tbl1_c_4_6 : tbl1 (4 : Fin 7) (6 : Fin 7) = some ((99 / 175 : ℚ), true) := rfl
theorem tbl1_c_5_0 : tbl1 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl1_c_5_1 : tbl1 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl1_c_5_2 : tbl1 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl1_c_5_3 : tbl1 (5 : Fin 7) (3 : Fin 7) = some ((225 / 98 : ℚ), true) := rfl
theorem tbl1_c_5_4 : tbl1 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl1_c_5_5 : tbl1 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_5_6 : tbl1 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_6_0 : tbl1 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl1_c_6_1 : tbl1 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl1_c_6_2 : tbl1 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl1_c_6_3 : tbl1 (6 : Fin 7) (3 : Fin 7) = some ((243 / 98 : ℚ), true) := rfl
theorem tbl1_c_6_4 : tbl1 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tbl1_c_6_5 : tbl1 (6 : Fin 7) (5 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl1_c_6_6 : tbl1 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 2 (internal, depth 2, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl2_c_0_0 : tbl2 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_0_1 : tbl2 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl2_c_0_2 : tbl2 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl2_c_0_3 : tbl2 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl2_c_0_4 : tbl2 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl2_c_0_5 : tbl2 (0 : Fin 7) (5 : Fin 7) = some ((3 / 35 : ℚ), true) := rfl
theorem tbl2_c_0_6 : tbl2 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl2_c_1_0 : tbl2 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl2_c_1_1 : tbl2 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_1_2 : tbl2 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl2_c_1_3 : tbl2 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), true) := rfl
theorem tbl2_c_1_4 : tbl2 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl2_c_1_5 : tbl2 (1 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl2_c_1_6 : tbl2 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl2_c_2_0 : tbl2 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl2_c_2_1 : tbl2 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl2_c_2_2 : tbl2 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_2_3 : tbl2 (2 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl2_c_2_4 : tbl2 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl2_c_2_5 : tbl2 (2 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl2_c_2_6 : tbl2 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl2_c_3_0 : tbl2 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl2_c_3_1 : tbl2 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl2_c_3_2 : tbl2 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl2_c_3_3 : tbl2 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_3_4 : tbl2 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl2_c_3_5 : tbl2 (3 : Fin 7) (5 : Fin 7) = some ((33 / 70 : ℚ), true) := rfl
theorem tbl2_c_3_6 : tbl2 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl2_c_4_0 : tbl2 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl2_c_4_1 : tbl2 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl2_c_4_2 : tbl2 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl2_c_4_3 : tbl2 (4 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl2_c_4_4 : tbl2 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_4_5 : tbl2 (4 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl2_c_4_6 : tbl2 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl2_c_5_0 : tbl2 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl2_c_5_1 : tbl2 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl2_c_5_2 : tbl2 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl2_c_5_3 : tbl2 (5 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl2_c_5_4 : tbl2 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl2_c_5_5 : tbl2 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_5_6 : tbl2 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl2_c_6_0 : tbl2 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl2_c_6_1 : tbl2 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl2_c_6_2 : tbl2 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl2_c_6_3 : tbl2 (6 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl2_c_6_4 : tbl2 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tbl2_c_6_5 : tbl2 (6 : Fin 7) (5 : Fin 7) = some ((81 / 70 : ℚ), true) := rfl
theorem tbl2_c_6_6 : tbl2 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 3 (internal, depth 3, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((1377 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl3_c_0_0 : tbl3 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_0_1 : tbl3 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl3_c_0_2 : tbl3 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl3_c_0_3 : tbl3 (0 : Fin 7) (3 : Fin 7) = some ((51 / 245 : ℚ), true) := rfl
theorem tbl3_c_0_4 : tbl3 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl3_c_0_5 : tbl3 (0 : Fin 7) (5 : Fin 7) = some ((3 / 35 : ℚ), true) := rfl
theorem tbl3_c_0_6 : tbl3 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl3_c_1_0 : tbl3 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl3_c_1_1 : tbl3 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_1_2 : tbl3 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl3_c_1_3 : tbl3 (1 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tbl3_c_1_4 : tbl3 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl3_c_1_5 : tbl3 (1 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl3_c_1_6 : tbl3 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl3_c_2_0 : tbl3 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl3_c_2_1 : tbl3 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl3_c_2_2 : tbl3 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_2_3 : tbl3 (2 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tbl3_c_2_4 : tbl3 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl3_c_2_5 : tbl3 (2 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl3_c_2_6 : tbl3 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl3_c_3_0 : tbl3 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl3_c_3_1 : tbl3 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl3_c_3_2 : tbl3 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl3_c_3_3 : tbl3 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_3_4 : tbl3 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl3_c_3_5 : tbl3 (3 : Fin 7) (5 : Fin 7) = some ((33 / 70 : ℚ), true) := rfl
theorem tbl3_c_3_6 : tbl3 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl3_c_4_0 : tbl3 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl3_c_4_1 : tbl3 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl3_c_4_2 : tbl3 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl3_c_4_3 : tbl3 (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl3_c_4_4 : tbl3 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_4_5 : tbl3 (4 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl3_c_4_6 : tbl3 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl3_c_5_0 : tbl3 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl3_c_5_1 : tbl3 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl3_c_5_2 : tbl3 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl3_c_5_3 : tbl3 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl3_c_5_4 : tbl3 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl3_c_5_5 : tbl3 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_5_6 : tbl3 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl3_c_6_0 : tbl3 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl3_c_6_1 : tbl3 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl3_c_6_2 : tbl3 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl3_c_6_3 : tbl3 (6 : Fin 7) (3 : Fin 7) = some ((1377 / 490 : ℚ), true) := rfl
theorem tbl3_c_6_4 : tbl3 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tbl3_c_6_5 : tbl3 (6 : Fin 7) (5 : Fin 7) = some ((81 / 70 : ℚ), true) := rfl
theorem tbl3_c_6_6 : tbl3 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 4 (reach, depth 4, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((729 / 1610 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 805 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl4_c_0_0 : tbl4 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_0_1 : tbl4 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl4_c_0_2 : tbl4 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl4_c_0_3 : tbl4 (0 : Fin 7) (3 : Fin 7) = some ((51 / 245 : ℚ), true) := rfl
theorem tbl4_c_0_4 : tbl4 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl4_c_0_5 : tbl4 (0 : Fin 7) (5 : Fin 7) = some ((3 / 35 : ℚ), true) := rfl
theorem tbl4_c_0_6 : tbl4 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl4_c_1_0 : tbl4 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl4_c_1_1 : tbl4 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_1_2 : tbl4 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl4_c_1_3 : tbl4 (1 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tbl4_c_1_4 : tbl4 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl4_c_1_5 : tbl4 (1 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl4_c_1_6 : tbl4 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl4_c_2_0 : tbl4 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl4_c_2_1 : tbl4 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl4_c_2_2 : tbl4 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_2_3 : tbl4 (2 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tbl4_c_2_4 : tbl4 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl4_c_2_5 : tbl4 (2 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tbl4_c_2_6 : tbl4 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl4_c_3_0 : tbl4 (3 : Fin 7) (0 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl4_c_3_1 : tbl4 (3 : Fin 7) (1 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl4_c_3_2 : tbl4 (3 : Fin 7) (2 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl4_c_3_3 : tbl4 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_3_4 : tbl4 (3 : Fin 7) (4 : Fin 7) = some ((243 / 322 : ℚ), true) := rfl
theorem tbl4_c_3_5 : tbl4 (3 : Fin 7) (5 : Fin 7) = some ((729 / 1610 : ℚ), true) := rfl
theorem tbl4_c_3_6 : tbl4 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl4_c_4_0 : tbl4 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl4_c_4_1 : tbl4 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl4_c_4_2 : tbl4 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl4_c_4_3 : tbl4 (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl4_c_4_4 : tbl4 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_4_5 : tbl4 (4 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl4_c_4_6 : tbl4 (4 : Fin 7) (6 : Fin 7) = some ((459 / 805 : ℚ), true) := rfl
theorem tbl4_c_5_0 : tbl4 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl4_c_5_1 : tbl4 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl4_c_5_2 : tbl4 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl4_c_5_3 : tbl4 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl4_c_5_4 : tbl4 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl4_c_5_5 : tbl4 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_5_6 : tbl4 (5 : Fin 7) (6 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl4_c_6_0 : tbl4 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl4_c_6_1 : tbl4 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl4_c_6_2 : tbl4 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl4_c_6_3 : tbl4 (6 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), true) := rfl
theorem tbl4_c_6_4 : tbl4 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tbl4_c_6_5 : tbl4 (6 : Fin 7) (5 : Fin 7) = some ((81 / 70 : ℚ), true) := rfl
theorem tbl4_c_6_6 : tbl4 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 5 (internal, depth 2, last reading row 6, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl5_c_0_0 : tbl5 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_0_1 : tbl5 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl5_c_0_2 : tbl5 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl5_c_0_3 : tbl5 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl5_c_0_4 : tbl5 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl5_c_0_5 : tbl5 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl5_c_0_6 : tbl5 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl5_c_1_0 : tbl5 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl5_c_1_1 : tbl5 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_1_2 : tbl5 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl5_c_1_3 : tbl5 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), true) := rfl
theorem tbl5_c_1_4 : tbl5 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl5_c_1_5 : tbl5 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl5_c_1_6 : tbl5 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl5_c_2_0 : tbl5 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl5_c_2_1 : tbl5 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl5_c_2_2 : tbl5 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_2_3 : tbl5 (2 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl5_c_2_4 : tbl5 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl5_c_2_5 : tbl5 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl5_c_2_6 : tbl5 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl5_c_3_0 : tbl5 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl5_c_3_1 : tbl5 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl5_c_3_2 : tbl5 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl5_c_3_3 : tbl5 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_3_4 : tbl5 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl5_c_3_5 : tbl5 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl5_c_3_6 : tbl5 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl5_c_4_0 : tbl5 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl5_c_4_1 : tbl5 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl5_c_4_2 : tbl5 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl5_c_4_3 : tbl5 (4 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl5_c_4_4 : tbl5 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_4_5 : tbl5 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl5_c_4_6 : tbl5 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl5_c_5_0 : tbl5 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl5_c_5_1 : tbl5 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl5_c_5_2 : tbl5 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl5_c_5_3 : tbl5 (5 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl5_c_5_4 : tbl5 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl5_c_5_5 : tbl5 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_5_6 : tbl5 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl5_c_6_0 : tbl5 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl5_c_6_1 : tbl5 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl5_c_6_2 : tbl5 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl5_c_6_3 : tbl5 (6 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl5_c_6_4 : tbl5 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl5_c_6_5 : tbl5 (6 : Fin 7) (5 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tbl5_c_6_6 : tbl5 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 6 (deadend, depth 3, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 175 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 175 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((187 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl6_c_0_0 : tbl6 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_0_1 : tbl6 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl6_c_0_2 : tbl6 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl6_c_0_3 : tbl6 (0 : Fin 7) (3 : Fin 7) = some ((34 / 175 : ℚ), true) := rfl
theorem tbl6_c_0_4 : tbl6 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl6_c_0_5 : tbl6 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl6_c_0_6 : tbl6 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl6_c_1_0 : tbl6 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl6_c_1_1 : tbl6 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_1_2 : tbl6 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl6_c_1_3 : tbl6 (1 : Fin 7) (3 : Fin 7) = some ((51 / 175 : ℚ), true) := rfl
theorem tbl6_c_1_4 : tbl6 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl6_c_1_5 : tbl6 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl6_c_1_6 : tbl6 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl6_c_2_0 : tbl6 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl6_c_2_1 : tbl6 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl6_c_2_2 : tbl6 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_2_3 : tbl6 (2 : Fin 7) (3 : Fin 7) = some ((51 / 175 : ℚ), true) := rfl
theorem tbl6_c_2_4 : tbl6 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl6_c_2_5 : tbl6 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl6_c_2_6 : tbl6 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl6_c_3_0 : tbl6 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl6_c_3_1 : tbl6 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl6_c_3_2 : tbl6 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl6_c_3_3 : tbl6 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_3_4 : tbl6 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl6_c_3_5 : tbl6 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl6_c_3_6 : tbl6 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl6_c_4_0 : tbl6 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl6_c_4_1 : tbl6 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl6_c_4_2 : tbl6 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl6_c_4_3 : tbl6 (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl6_c_4_4 : tbl6 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_4_5 : tbl6 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl6_c_4_6 : tbl6 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl6_c_5_0 : tbl6 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl6_c_5_1 : tbl6 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl6_c_5_2 : tbl6 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl6_c_5_3 : tbl6 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl6_c_5_4 : tbl6 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl6_c_5_5 : tbl6 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_5_6 : tbl6 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl6_c_6_0 : tbl6 (6 : Fin 7) (0 : Fin 7) = some ((187 / 14 : ℚ), true) := rfl
theorem tbl6_c_6_1 : tbl6 (6 : Fin 7) (1 : Fin 7) = some ((187 / 14 : ℚ), true) := rfl
theorem tbl6_c_6_2 : tbl6 (6 : Fin 7) (2 : Fin 7) = some ((187 / 14 : ℚ), true) := rfl
theorem tbl6_c_6_3 : tbl6 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl6_c_6_4 : tbl6 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl6_c_6_5 : tbl6 (6 : Fin 7) (5 : Fin 7) = some ((187 / 161 : ℚ), true) := rfl
theorem tbl6_c_6_6 : tbl6 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 7 (internal, depth 3, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl7_c_0_0 : tbl7 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_0_1 : tbl7 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl7_c_0_2 : tbl7 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl7_c_0_3 : tbl7 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl7_c_0_4 : tbl7 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl7_c_0_5 : tbl7 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl7_c_0_6 : tbl7 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl7_c_1_0 : tbl7 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl7_c_1_1 : tbl7 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_1_2 : tbl7 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl7_c_1_3 : tbl7 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), true) := rfl
theorem tbl7_c_1_4 : tbl7 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl7_c_1_5 : tbl7 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl7_c_1_6 : tbl7 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl7_c_2_0 : tbl7 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl7_c_2_1 : tbl7 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl7_c_2_2 : tbl7 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_2_3 : tbl7 (2 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl7_c_2_4 : tbl7 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl7_c_2_5 : tbl7 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl7_c_2_6 : tbl7 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl7_c_3_0 : tbl7 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl7_c_3_1 : tbl7 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl7_c_3_2 : tbl7 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl7_c_3_3 : tbl7 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_3_4 : tbl7 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl7_c_3_5 : tbl7 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl7_c_3_6 : tbl7 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl7_c_4_0 : tbl7 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl7_c_4_1 : tbl7 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl7_c_4_2 : tbl7 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl7_c_4_3 : tbl7 (4 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl7_c_4_4 : tbl7 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_4_5 : tbl7 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl7_c_4_6 : tbl7 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl7_c_5_0 : tbl7 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl7_c_5_1 : tbl7 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl7_c_5_2 : tbl7 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl7_c_5_3 : tbl7 (5 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl7_c_5_4 : tbl7 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl7_c_5_5 : tbl7 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_5_6 : tbl7 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl7_c_6_0 : tbl7 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl7_c_6_1 : tbl7 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl7_c_6_2 : tbl7 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl7_c_6_3 : tbl7 (6 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tbl7_c_6_4 : tbl7 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl7_c_6_5 : tbl7 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl7_c_6_6 : tbl7 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 8 (internal, depth 4, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((255 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl8_c_0_0 : tbl8 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_0_1 : tbl8 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl8_c_0_2 : tbl8 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl8_c_0_3 : tbl8 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl8_c_0_4 : tbl8 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl8_c_0_5 : tbl8 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl8_c_0_6 : tbl8 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl8_c_1_0 : tbl8 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl8_c_1_1 : tbl8 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_1_2 : tbl8 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl8_c_1_3 : tbl8 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl8_c_1_4 : tbl8 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl8_c_1_5 : tbl8 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl8_c_1_6 : tbl8 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl8_c_2_0 : tbl8 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl8_c_2_1 : tbl8 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl8_c_2_2 : tbl8 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_2_3 : tbl8 (2 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl8_c_2_4 : tbl8 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl8_c_2_5 : tbl8 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl8_c_2_6 : tbl8 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl8_c_3_0 : tbl8 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl8_c_3_1 : tbl8 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl8_c_3_2 : tbl8 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl8_c_3_3 : tbl8 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_3_4 : tbl8 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tbl8_c_3_5 : tbl8 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl8_c_3_6 : tbl8 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tbl8_c_4_0 : tbl8 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl8_c_4_1 : tbl8 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl8_c_4_2 : tbl8 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl8_c_4_3 : tbl8 (4 : Fin 7) (3 : Fin 7) = some ((255 / 161 : ℚ), true) := rfl
theorem tbl8_c_4_4 : tbl8 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_4_5 : tbl8 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl8_c_4_6 : tbl8 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl8_c_5_0 : tbl8 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl8_c_5_1 : tbl8 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl8_c_5_2 : tbl8 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl8_c_5_3 : tbl8 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl8_c_5_4 : tbl8 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl8_c_5_5 : tbl8 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_5_6 : tbl8 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl8_c_6_0 : tbl8 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl8_c_6_1 : tbl8 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl8_c_6_2 : tbl8 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl8_c_6_3 : tbl8 (6 : Fin 7) (3 : Fin 7) = some ((289 / 105 : ℚ), true) := rfl
theorem tbl8_c_6_4 : tbl8 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl8_c_6_5 : tbl8 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl8_c_6_6 : tbl8 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 9 (internal, depth 5, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((255 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 105 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl9_c_0_0 : tbl9 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_0_1 : tbl9 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl9_c_0_2 : tbl9 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl9_c_0_3 : tbl9 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl9_c_0_4 : tbl9 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl9_c_0_5 : tbl9 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl9_c_0_6 : tbl9 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl9_c_1_0 : tbl9 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl9_c_1_1 : tbl9 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_1_2 : tbl9 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl9_c_1_3 : tbl9 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl9_c_1_4 : tbl9 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl9_c_1_5 : tbl9 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl9_c_1_6 : tbl9 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl9_c_2_0 : tbl9 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl9_c_2_1 : tbl9 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl9_c_2_2 : tbl9 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_2_3 : tbl9 (2 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl9_c_2_4 : tbl9 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl9_c_2_5 : tbl9 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl9_c_2_6 : tbl9 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl9_c_3_0 : tbl9 (3 : Fin 7) (0 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_1 : tbl9 (3 : Fin 7) (1 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_2 : tbl9 (3 : Fin 7) (2 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_3 : tbl9 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_3_4 : tbl9 (3 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl9_c_3_5 : tbl9 (3 : Fin 7) (5 : Fin 7) = some ((51 / 115 : ℚ), true) := rfl
theorem tbl9_c_3_6 : tbl9 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl9_c_4_0 : tbl9 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl9_c_4_1 : tbl9 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl9_c_4_2 : tbl9 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl9_c_4_3 : tbl9 (4 : Fin 7) (3 : Fin 7) = some ((255 / 161 : ℚ), true) := rfl
theorem tbl9_c_4_4 : tbl9 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_4_5 : tbl9 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tbl9_c_4_6 : tbl9 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl9_c_5_0 : tbl9 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl9_c_5_1 : tbl9 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl9_c_5_2 : tbl9 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl9_c_5_3 : tbl9 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl9_c_5_4 : tbl9 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl9_c_5_5 : tbl9 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_5_6 : tbl9 (5 : Fin 7) (6 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl9_c_6_0 : tbl9 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl9_c_6_1 : tbl9 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl9_c_6_2 : tbl9 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl9_c_6_3 : tbl9 (6 : Fin 7) (3 : Fin 7) = some ((289 / 105 : ℚ), true) := rfl
theorem tbl9_c_6_4 : tbl9 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl9_c_6_5 : tbl9 (6 : Fin 7) (5 : Fin 7) = some ((17 / 15 : ℚ), true) := rfl
theorem tbl9_c_6_6 : tbl9 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 10 (internal, depth 6, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((225 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((255 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((425 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl10_c_0_0 : tbl10 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_0_1 : tbl10 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl10_c_0_2 : tbl10 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl10_c_0_3 : tbl10 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl10_c_0_4 : tbl10 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl10_c_0_5 : tbl10 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), true) := rfl
theorem tbl10_c_0_6 : tbl10 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl10_c_1_0 : tbl10 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl10_c_1_1 : tbl10 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_1_2 : tbl10 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl10_c_1_3 : tbl10 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl10_c_1_4 : tbl10 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl10_c_1_5 : tbl10 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl10_c_1_6 : tbl10 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl10_c_2_0 : tbl10 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl10_c_2_1 : tbl10 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl10_c_2_2 : tbl10 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_2_3 : tbl10 (2 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl10_c_2_4 : tbl10 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl10_c_2_5 : tbl10 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl10_c_2_6 : tbl10 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl10_c_3_0 : tbl10 (3 : Fin 7) (0 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_1 : tbl10 (3 : Fin 7) (1 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_2 : tbl10 (3 : Fin 7) (2 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_3 : tbl10 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_3_4 : tbl10 (3 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl10_c_3_5 : tbl10 (3 : Fin 7) (5 : Fin 7) = some ((225 / 529 : ℚ), true) := rfl
theorem tbl10_c_3_6 : tbl10 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl10_c_4_0 : tbl10 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl10_c_4_1 : tbl10 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl10_c_4_2 : tbl10 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl10_c_4_3 : tbl10 (4 : Fin 7) (3 : Fin 7) = some ((255 / 161 : ℚ), true) := rfl
theorem tbl10_c_4_4 : tbl10 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_4_5 : tbl10 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl10_c_4_6 : tbl10 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl10_c_5_0 : tbl10 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl10_c_5_1 : tbl10 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl10_c_5_2 : tbl10 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl10_c_5_3 : tbl10 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl10_c_5_4 : tbl10 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tbl10_c_5_5 : tbl10 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_5_6 : tbl10 (5 : Fin 7) (6 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl10_c_6_0 : tbl10 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl10_c_6_1 : tbl10 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl10_c_6_2 : tbl10 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl10_c_6_3 : tbl10 (6 : Fin 7) (3 : Fin 7) = some ((425 / 161 : ℚ), true) := rfl
theorem tbl10_c_6_4 : tbl10 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl10_c_6_5 : tbl10 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl10_c_6_6 : tbl10 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 11 (deadend, depth 7, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((375 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((225 / 529 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((255 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((425 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((125 / 69 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl11_c_0_0 : tbl11 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_0_1 : tbl11 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl11_c_0_2 : tbl11 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl11_c_0_3 : tbl11 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl11_c_0_4 : tbl11 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tbl11_c_0_5 : tbl11 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), true) := rfl
theorem tbl11_c_0_6 : tbl11 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tbl11_c_1_0 : tbl11 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl11_c_1_1 : tbl11 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_1_2 : tbl11 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl11_c_1_3 : tbl11 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl11_c_1_4 : tbl11 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl11_c_1_5 : tbl11 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl11_c_1_6 : tbl11 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tbl11_c_2_0 : tbl11 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl11_c_2_1 : tbl11 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl11_c_2_2 : tbl11 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_2_3 : tbl11 (2 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl11_c_2_4 : tbl11 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tbl11_c_2_5 : tbl11 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tbl11_c_2_6 : tbl11 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tbl11_c_3_0 : tbl11 (3 : Fin 7) (0 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_1 : tbl11 (3 : Fin 7) (1 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_2 : tbl11 (3 : Fin 7) (2 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_3 : tbl11 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_3_4 : tbl11 (3 : Fin 7) (4 : Fin 7) = some ((375 / 529 : ℚ), true) := rfl
theorem tbl11_c_3_5 : tbl11 (3 : Fin 7) (5 : Fin 7) = some ((225 / 529 : ℚ), true) := rfl
theorem tbl11_c_3_6 : tbl11 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl11_c_4_0 : tbl11 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tbl11_c_4_1 : tbl11 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl11_c_4_2 : tbl11 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tbl11_c_4_3 : tbl11 (4 : Fin 7) (3 : Fin 7) = some ((255 / 161 : ℚ), true) := rfl
theorem tbl11_c_4_4 : tbl11 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_4_5 : tbl11 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl11_c_4_6 : tbl11 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl11_c_5_0 : tbl11 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl11_c_5_1 : tbl11 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl11_c_5_2 : tbl11 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl11_c_5_3 : tbl11 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl11_c_5_4 : tbl11 (5 : Fin 7) (4 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl11_c_5_5 : tbl11 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_5_6 : tbl11 (5 : Fin 7) (6 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl11_c_6_0 : tbl11 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tbl11_c_6_1 : tbl11 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl11_c_6_2 : tbl11 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tbl11_c_6_3 : tbl11 (6 : Fin 7) (3 : Fin 7) = some ((425 / 161 : ℚ), true) := rfl
theorem tbl11_c_6_4 : tbl11 (6 : Fin 7) (4 : Fin 7) = some ((125 / 69 : ℚ), true) := rfl
theorem tbl11_c_6_5 : tbl11 (6 : Fin 7) (5 : Fin 7) = some ((25 / 23 : ℚ), true) := rfl
theorem tbl11_c_6_6 : tbl11 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 4's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 490 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 70 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 322 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((729 / 1610 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 805 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((1377 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 70 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS4_c_0_0 : tblS4 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_0_1 : tblS4 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS4_c_0_2 : tblS4 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS4_c_0_3 : tblS4 (0 : Fin 7) (3 : Fin 7) = some ((51 / 245 : ℚ), true) := rfl
theorem tblS4_c_0_4 : tblS4 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tblS4_c_0_5 : tblS4 (0 : Fin 7) (5 : Fin 7) = some ((3 / 35 : ℚ), true) := rfl
theorem tblS4_c_0_6 : tblS4 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tblS4_c_1_0 : tblS4 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tblS4_c_1_1 : tblS4 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_1_2 : tblS4 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS4_c_1_3 : tblS4 (1 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tblS4_c_1_4 : tblS4 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tblS4_c_1_5 : tblS4 (1 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tblS4_c_1_6 : tblS4 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tblS4_c_2_0 : tblS4 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS4_c_2_1 : tblS4 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tblS4_c_2_2 : tblS4 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_2_3 : tblS4 (2 : Fin 7) (3 : Fin 7) = some ((153 / 490 : ℚ), true) := rfl
theorem tblS4_c_2_4 : tblS4 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tblS4_c_2_5 : tblS4 (2 : Fin 7) (5 : Fin 7) = some ((9 / 70 : ℚ), true) := rfl
theorem tblS4_c_2_6 : tblS4 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tblS4_c_3_0 : tblS4 (3 : Fin 7) (0 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tblS4_c_3_1 : tblS4 (3 : Fin 7) (1 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tblS4_c_3_2 : tblS4 (3 : Fin 7) (2 : Fin 7) = some ((243 / 46 : ℚ), true) := rfl
theorem tblS4_c_3_3 : tblS4 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_3_4 : tblS4 (3 : Fin 7) (4 : Fin 7) = some ((243 / 322 : ℚ), true) := rfl
theorem tblS4_c_3_5 : tblS4 (3 : Fin 7) (5 : Fin 7) = some ((729 / 1610 : ℚ), true) := rfl
theorem tblS4_c_3_6 : tblS4 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tblS4_c_4_0 : tblS4 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tblS4_c_4_1 : tblS4 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tblS4_c_4_2 : tblS4 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tblS4_c_4_3 : tblS4 (4 : Fin 7) (3 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tblS4_c_4_4 : tblS4 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_4_5 : tblS4 (4 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblS4_c_4_6 : tblS4 (4 : Fin 7) (6 : Fin 7) = some ((459 / 805 : ℚ), true) := rfl
theorem tblS4_c_5_0 : tblS4 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tblS4_c_5_1 : tblS4 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS4_c_5_2 : tblS4 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS4_c_5_3 : tblS4 (5 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblS4_c_5_4 : tblS4 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tblS4_c_5_5 : tblS4 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_5_6 : tblS4 (5 : Fin 7) (6 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tblS4_c_6_0 : tblS4 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tblS4_c_6_1 : tblS4 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tblS4_c_6_2 : tblS4 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tblS4_c_6_3 : tblS4 (6 : Fin 7) (3 : Fin 7) = some ((1377 / 490 : ℚ), true) := rfl
theorem tblS4_c_6_4 : tblS4 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tblS4_c_6_5 : tblS4 (6 : Fin 7) (5 : Fin 7) = some ((81 / 70 : ℚ), true) := rfl
theorem tblS4_c_6_6 : tblS4 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 5's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 25 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 14 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 25 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((11 / 14 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 25 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((15 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 14 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS5_c_0_0 : tblS5 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_0_1 : tblS5 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS5_c_0_2 : tblS5 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS5_c_0_3 : tblS5 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tblS5_c_0_4 : tblS5 (0 : Fin 7) (4 : Fin 7) = some ((1 / 7 : ℚ), true) := rfl
theorem tblS5_c_0_5 : tblS5 (0 : Fin 7) (5 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tblS5_c_0_6 : tblS5 (0 : Fin 7) (6 : Fin 7) = some ((2 / 25 : ℚ), false) := rfl
theorem tblS5_c_1_0 : tblS5 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tblS5_c_1_1 : tblS5 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_1_2 : tblS5 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS5_c_1_3 : tblS5 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), true) := rfl
theorem tblS5_c_1_4 : tblS5 (1 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tblS5_c_1_5 : tblS5 (1 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), true) := rfl
theorem tblS5_c_1_6 : tblS5 (1 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), true) := rfl
theorem tblS5_c_2_0 : tblS5 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS5_c_2_1 : tblS5 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tblS5_c_2_2 : tblS5 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_2_3 : tblS5 (2 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tblS5_c_2_4 : tblS5 (2 : Fin 7) (4 : Fin 7) = some ((3 / 14 : ℚ), true) := rfl
theorem tblS5_c_2_5 : tblS5 (2 : Fin 7) (5 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tblS5_c_2_6 : tblS5 (2 : Fin 7) (6 : Fin 7) = some ((3 / 25 : ℚ), false) := rfl
theorem tblS5_c_3_0 : tblS5 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tblS5_c_3_1 : tblS5 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS5_c_3_2 : tblS5 (3 : Fin 7) (2 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS5_c_3_3 : tblS5 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_3_4 : tblS5 (3 : Fin 7) (4 : Fin 7) = some ((11 / 14 : ℚ), true) := rfl
theorem tblS5_c_3_5 : tblS5 (3 : Fin 7) (5 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tblS5_c_3_6 : tblS5 (3 : Fin 7) (6 : Fin 7) = some ((11 / 25 : ℚ), false) := rfl
theorem tblS5_c_4_0 : tblS5 (4 : Fin 7) (0 : Fin 7) = some ((15 / 2 : ℚ), false) := rfl
theorem tblS5_c_4_1 : tblS5 (4 : Fin 7) (1 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tblS5_c_4_2 : tblS5 (4 : Fin 7) (2 : Fin 7) = some ((15 / 2 : ℚ), true) := rfl
theorem tblS5_c_4_3 : tblS5 (4 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tblS5_c_4_4 : tblS5 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_4_5 : tblS5 (4 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), false) := rfl
theorem tblS5_c_4_6 : tblS5 (4 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblS5_c_5_0 : tblS5 (5 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tblS5_c_5_1 : tblS5 (5 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS5_c_5_2 : tblS5 (5 : Fin 7) (2 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS5_c_5_3 : tblS5 (5 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tblS5_c_5_4 : tblS5 (5 : Fin 7) (4 : Fin 7) = some ((25 / 14 : ℚ), true) := rfl
theorem tblS5_c_5_5 : tblS5 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_5_6 : tblS5 (5 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS5_c_6_0 : tblS5 (6 : Fin 7) (0 : Fin 7) = some ((27 / 2 : ℚ), false) := rfl
theorem tblS5_c_6_1 : tblS5 (6 : Fin 7) (1 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tblS5_c_6_2 : tblS5 (6 : Fin 7) (2 : Fin 7) = some ((27 / 2 : ℚ), true) := rfl
theorem tblS5_c_6_3 : tblS5 (6 : Fin 7) (3 : Fin 7) = some ((3 : ℚ), false) := rfl
theorem tblS5_c_6_4 : tblS5 (6 : Fin 7) (4 : Fin 7) = some ((27 / 14 : ℚ), true) := rfl
theorem tblS5_c_6_5 : tblS5 (6 : Fin 7) (5 : Fin 7) = some ((27 / 23 : ℚ), false) := rfl
theorem tblS5_c_6_6 : tblS5 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-! ## 1b. The node states and the certificate trees -/

/-- The start-zone root: DFS node 0 (depth 1, last reading row 4, exit numerator 9, frontier sup 9 / 7). -/
-- STANDING: DATA
def node0 : DfsNode := ⟨tbl0, (4 : Fin 7), (9 : ℚ), (9 / 7 : ℚ), {((4 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 1 (deadend, depth 2, last reading row 3, exit numerator 9): child of node 0 by the step (3, 7, 9). -/
-- STANDING: DATA
def node1 : DfsNode := ⟨tbl1, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node0.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 2 (internal, depth 2, last reading row 5, exit numerator 17): child of node 0 by the step (5, 15, 17). -/
-- STANDING: DATA
def node2 : DfsNode := ⟨tbl2, (5 : Fin 7), (17 : ℚ), (34 / 23 : ℚ), node0.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 3 (internal, depth 3, last reading row 3, exit numerator 9): child of node 2 by the step (3, 7, 9). -/
-- STANDING: DATA
def node3 : DfsNode := ⟨tbl3, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node2.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 4 (reach, depth 4, last reading row 6, exit numerator 25): child of node 3 by the step (6, 23, 25). -/
-- STANDING: DATA
def node4 : DfsNode := ⟨tbl4, (6 : Fin 7), (25 : ℚ), (2 : ℚ), node3.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 5 (internal, depth 2, last reading row 6, exit numerator 17): child of node 0 by the step (6, 15, 17). -/
-- STANDING: DATA
def node5 : DfsNode := ⟨tbl5, (6 : Fin 7), (17 : ℚ), (34 / 25 : ℚ), node0.seen ∪ {((6 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 6 (deadend, depth 3, last reading row 3, exit numerator 9): child of node 5 by the step (3, 7, 9). -/
-- STANDING: DATA
def node6 : DfsNode := ⟨tbl6, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node5.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 7 (internal, depth 3, last reading row 5, exit numerator 17): child of node 5 by the step (5, 15, 17). -/
-- STANDING: DATA
def node7 : DfsNode := ⟨tbl7, (5 : Fin 7), (17 : ℚ), (34 / 23 : ℚ), node5.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 8 (internal, depth 4, last reading row 3, exit numerator 9): child of node 7 by the step (3, 7, 9). -/
-- STANDING: DATA
def node8 : DfsNode := ⟨tbl8, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node7.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 9 (internal, depth 5, last reading row 6, exit numerator 25): child of node 8 by the step (6, 23, 25). -/
-- STANDING: DATA
def node9 : DfsNode := ⟨tbl9, (6 : Fin 7), (25 : ℚ), (2 : ℚ), node8.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 10 (internal, depth 6, last reading row 5, exit numerator 25): child of node 9 by the step (5, 23, 25). -/
-- STANDING: DATA
def node10 : DfsNode := ⟨tbl10, (5 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node9.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 11 (deadend, depth 7, last reading row 4, exit numerator 17): child of node 10 by the step (4, 15, 17). -/
-- STANDING: DATA
def node11 : DfsNode := ⟨tbl11, (4 : Fin 7), (17 : ℚ), (17 / 7 : ℚ), node10.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- The dead-end leaf, DFS node 11: no filter-passing step. -/
-- STANDING: DATA
def tree11 : DfsCert := DfsCert.deadend node11

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

def children8 : List DfsCert := [tree9]
/-- The subtree rooted at internal node 8: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree8 : DfsCert := DfsCert.node node8 children8

def children7 : List DfsCert := [tree8]
/-- The subtree rooted at internal node 7: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree7 : DfsCert := DfsCert.node node7 children7

/-- The dead-end leaf, DFS node 6: no filter-passing step. -/
-- STANDING: DATA
def tree6 : DfsCert := DfsCert.deadend node6

def children5 : List DfsCert := [tree6, tree7]
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

def children2 : List DfsCert := [tree3]
/-- The subtree rooted at internal node 2: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree2 : DfsCert := DfsCert.node node2 children2

/-- The dead-end leaf, DFS node 1: no filter-passing step. -/
-- STANDING: DATA
def tree1 : DfsCert := DfsCert.deadend node1

def children0 : List DfsCert := [tree1, tree2, tree5]
/-- The subtree rooted at internal node 0: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree0 : DfsCert := DfsCert.node node0 children0

/-- The box's WHOLE certificate forest (1 start-zone root(s), 12 nodes),
transcribed verbatim from the reconstruction. -/
-- STANDING: DATA
def forest : List DfsCert := [tree0]

/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/

theorem nodeOK_0 : DfsNodeOK node0 := by
  show uExitOK tbl0 (4 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl0_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_0
theorem nodeOK_1 : DfsNodeOK node1 := by
  show uExitOK tbl1 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl1_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_1
theorem nodeOK_2 : DfsNodeOK node2 := by
  show uExitOK tbl2 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl2_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_2
theorem nodeOK_3 : DfsNodeOK node3 := by
  show uExitOK tbl3 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl3_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_3
theorem nodeOK_4 : DfsNodeOK node4 := by
  show uExitOK tbl4 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl4_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl4_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_4
theorem nodeOK_5 : DfsNodeOK node5 := by
  show uExitOK tbl5 (6 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl5_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_5
theorem nodeOK_6 : DfsNodeOK node6 := by
  show uExitOK tbl6 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl6_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl6_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_6
theorem nodeOK_7 : DfsNodeOK node7 := by
  show uExitOK tbl7 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl7_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_7
theorem nodeOK_8 : DfsNodeOK node8 := by
  show uExitOK tbl8 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl8_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_8
theorem nodeOK_9 : DfsNodeOK node9 := by
  show uExitOK tbl9 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl9_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl9_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_9
theorem nodeOK_10 : DfsNodeOK node10 := by
  show uExitOK tbl10 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl10_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl10_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_10
theorem nodeOK_11 : DfsNodeOK node11 := by
  show uExitOK tbl11 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl11_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl11_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_11

/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/

/-- Node 1's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_1_1 : uAdd tbl0 (4 : Fin 7) (3 : Fin 7) ((9 / 7 : ℚ)) true = some tbl1 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_4_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_3_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tbl1] <;> norm_num)

/-- Node 1's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_1_2 : uAdd tbl1 (3 : Fin 7) (4 : Fin 7) ((9 / 9 : ℚ)) true = some tbl1 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_3_4] <;> norm_num)

/-- Node 1's full step equation. -/
theorem stepEq_1 : uStep tbl0 (4 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1 addEq_1_2

/-- Node 1's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_1 : childState (boxN m4res_1_1_1_5_7_12_13) node0 (3 : Fin 7) (9 : ℚ) tbl1 = DfsCert.root tree1 :=
  by
    simp only [childState, DfsCert.root, tree1, node1]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node0.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node0, tbl0_c_0_3]
    norm_num [hlo]

#print axioms addEq_1_1
#print axioms addEq_1_2
#print axioms stepEq_1
#print axioms childEq_1

/-- Node 2's step (5, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_2_1 : uAdd tbl0 (4 : Fin 7) (5 : Fin 7) ((9 / 15 : ℚ)) true = some tbl2 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_4_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_5_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tbl2] <;> norm_num)

/-- Node 2's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_2_2 : uAdd tbl2 (5 : Fin 7) (4 : Fin 7) ((17 / 9 : ℚ)) true = some tbl2 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_5_4] <;> norm_num)

/-- Node 2's full step equation. -/
theorem stepEq_2 : uStep tbl0 (4 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_2_1 addEq_2_2

/-- Node 2's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_2 : childState (boxN m4res_1_1_1_5_7_12_13) node0 (5 : Fin 7) (17 : ℚ) tbl2 = DfsCert.root tree2 :=
  by
    simp only [childState, DfsCert.root, tree2, node2]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node0.U (5 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node0, tbl0_c_0_5]
    norm_num [hlo]

#print axioms addEq_2_1
#print axioms addEq_2_2
#print axioms stepEq_2
#print axioms childEq_2

/-- Node 3's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_3_1 : uAdd tbl2 (5 : Fin 7) (3 : Fin 7) ((17 / 7 : ℚ)) true = some tbl3 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl2_c_5_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_3_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl2, tbl3] <;> norm_num)

/-- Node 3's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_3_2 : uAdd tbl3 (3 : Fin 7) (5 : Fin 7) ((9 / 17 : ℚ)) true = some tbl3 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_3_5] <;> norm_num)

/-- Node 3's full step equation. -/
theorem stepEq_3 : uStep tbl2 (5 : Fin 7) (3 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl3 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1 addEq_3_2

/-- Node 3's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_3 : childState (boxN m4res_1_1_1_5_7_12_13) node2 (3 : Fin 7) (9 : ℚ) tbl3 = DfsCert.root tree3 :=
  by
    simp only [childState, DfsCert.root, tree3, node3]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node2.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node2, tbl2_c_0_3]
    norm_num [hlo]

#print axioms addEq_3_1
#print axioms addEq_3_2
#print axioms stepEq_3
#print axioms childEq_3

/-- Node 4's step (6, 23, 25): add 1 propagates to the intermediate table tblS4 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_4_1 : uAdd tbl3 (3 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tblS4 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl3_c_3_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_6_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl3, tblS4] <;> norm_num)

/-- Node 4's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_4_2 : uAdd tblS4 (6 : Fin 7) (3 : Fin 7) ((25 / 9 : ℚ)) true = some tbl4 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS4_c_6_3] <;> norm_num)
    (by simp [uBack, uBackCond, tblS4_c_3_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS4, tbl4] <;> norm_num)

/-- Node 4's full step equation. -/
theorem stepEq_4 : uStep tbl3 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_4_1 addEq_4_2

/-- Node 4's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_4 : childState (boxN m4res_1_1_1_5_7_12_13) node3 (6 : Fin 7) (25 : ℚ) tbl4 = DfsCert.root tree4 :=
  by
    simp only [childState, DfsCert.root, tree4, node4]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node3.U (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node3, tbl3_c_0_6]
    norm_num [hlo]

#print axioms addEq_4_1
#print axioms addEq_4_2
#print axioms stepEq_4
#print axioms childEq_4

/-- Node 5's step (6, 15, 17): add 1 propagates to the intermediate table tblS5 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_5_1 : uAdd tbl0 (4 : Fin 7) (6 : Fin 7) ((9 / 15 : ℚ)) true = some tblS5 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_4_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_6_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tblS5] <;> norm_num)

/-- Node 5's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_5_2 : uAdd tblS5 (6 : Fin 7) (4 : Fin 7) ((17 / 9 : ℚ)) true = some tbl5 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS5_c_6_4] <;> norm_num)
    (by simp [uBack, uBackCond, tblS5_c_4_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS5, tbl5] <;> norm_num)

/-- Node 5's full step equation. -/
theorem stepEq_5 : uStep tbl0 (4 : Fin 7) (6 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl5 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1 addEq_5_2

/-- Node 5's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_5 : childState (boxN m4res_1_1_1_5_7_12_13) node0 (6 : Fin 7) (17 : ℚ) tbl5 = DfsCert.root tree5 :=
  by
    simp only [childState, DfsCert.root, tree5, node5]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node0.U (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node0, tbl0_c_0_6]
    norm_num [hlo]

#print axioms addEq_5_1
#print axioms addEq_5_2
#print axioms stepEq_5
#print axioms childEq_5

/-- Node 6's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_6_1 : uAdd tbl5 (6 : Fin 7) (3 : Fin 7) ((17 / 7 : ℚ)) true = some tbl6 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl5_c_6_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_3_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl5, tbl6] <;> norm_num)

/-- Node 6's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_6_2 : uAdd tbl6 (3 : Fin 7) (6 : Fin 7) ((9 / 17 : ℚ)) true = some tbl6 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_3_6] <;> norm_num)

/-- Node 6's full step equation. -/
theorem stepEq_6 : uStep tbl5 (6 : Fin 7) (3 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_6_1 addEq_6_2

/-- Node 6's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_6 : childState (boxN m4res_1_1_1_5_7_12_13) node5 (3 : Fin 7) (9 : ℚ) tbl6 = DfsCert.root tree6 :=
  by
    simp only [childState, DfsCert.root, tree6, node6]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node5.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node5, tbl5_c_0_3]
    norm_num [hlo]

#print axioms addEq_6_1
#print axioms addEq_6_2
#print axioms stepEq_6
#print axioms childEq_6

/-- Node 7's step (5, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_7_1 : uAdd tbl5 (6 : Fin 7) (5 : Fin 7) ((17 / 15 : ℚ)) true = some tbl7 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl5_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl5_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl5, tbl7] <;> norm_num)

/-- Node 7's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_7_2 : uAdd tbl7 (5 : Fin 7) (6 : Fin 7) ((17 / 17 : ℚ)) true = some tbl7 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_5_6] <;> norm_num)

/-- Node 7's full step equation. -/
theorem stepEq_7 : uStep tbl5 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1 addEq_7_2

/-- Node 7's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_7 : childState (boxN m4res_1_1_1_5_7_12_13) node5 (5 : Fin 7) (17 : ℚ) tbl7 = DfsCert.root tree7 :=
  by
    simp only [childState, DfsCert.root, tree7, node7]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node5.U (5 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node5, tbl5_c_0_5]
    norm_num [hlo]

#print axioms addEq_7_1
#print axioms addEq_7_2
#print axioms stepEq_7
#print axioms childEq_7

/-- Node 8's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_8_1 : uAdd tbl7 (5 : Fin 7) (3 : Fin 7) ((17 / 7 : ℚ)) true = some tbl8 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl7_c_5_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_3_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl7, tbl8] <;> norm_num)

/-- Node 8's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_8_2 : uAdd tbl8 (3 : Fin 7) (5 : Fin 7) ((9 / 17 : ℚ)) true = some tbl8 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_3_5] <;> norm_num)

/-- Node 8's full step equation. -/
theorem stepEq_8 : uStep tbl7 (5 : Fin 7) (3 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_8_1 addEq_8_2

/-- Node 8's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_8 : childState (boxN m4res_1_1_1_5_7_12_13) node7 (3 : Fin 7) (9 : ℚ) tbl8 = DfsCert.root tree8 :=
  by
    simp only [childState, DfsCert.root, tree8, node8]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node7.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node7, tbl7_c_0_3]
    norm_num [hlo]

#print axioms addEq_8_1
#print axioms addEq_8_2
#print axioms stepEq_8
#print axioms childEq_8

/-- Node 9's step (6, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_9_1 : uAdd tbl8 (3 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tbl9 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl8_c_3_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_6_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl8, tbl9] <;> norm_num)

/-- Node 9's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_9_2 : uAdd tbl9 (6 : Fin 7) (3 : Fin 7) ((25 / 9 : ℚ)) true = some tbl9 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_6_3] <;> norm_num)

/-- Node 9's full step equation. -/
theorem stepEq_9 : uStep tbl8 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1 addEq_9_2

/-- Node 9's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_9 : childState (boxN m4res_1_1_1_5_7_12_13) node8 (6 : Fin 7) (25 : ℚ) tbl9 = DfsCert.root tree9 :=
  by
    simp only [childState, DfsCert.root, tree9, node9]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node8.U (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node8, tbl8_c_0_6]
    norm_num [hlo]

#print axioms addEq_9_1
#print axioms addEq_9_2
#print axioms stepEq_9
#print axioms childEq_9

/-- Node 10's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_10_1 : uAdd tbl9 (6 : Fin 7) (5 : Fin 7) ((25 / 23 : ℚ)) true = some tbl10 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl9_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl9_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl9, tbl10] <;> norm_num)

/-- Node 10's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_10_2 : uAdd tbl10 (5 : Fin 7) (6 : Fin 7) ((25 / 25 : ℚ)) true = some tbl10 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_5_6] <;> norm_num)

/-- Node 10's full step equation. -/
theorem stepEq_10 : uStep tbl9 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_10_1 addEq_10_2

/-- Node 10's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_10 : childState (boxN m4res_1_1_1_5_7_12_13) node9 (5 : Fin 7) (25 : ℚ) tbl10 = DfsCert.root tree10 :=
  by
    simp only [childState, DfsCert.root, tree10, node10]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node9.U (5 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node9, tbl9_c_0_5]
    norm_num [hlo]

#print axioms addEq_10_1
#print axioms addEq_10_2
#print axioms stepEq_10
#print axioms childEq_10

/-- Node 11's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_11_1 : uAdd tbl10 (5 : Fin 7) (4 : Fin 7) ((25 / 15 : ℚ)) true = some tbl11 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl10_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl10_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl10, tbl11] <;> norm_num)

/-- Node 11's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_11_2 : uAdd tbl11 (4 : Fin 7) (5 : Fin 7) ((17 / 25 : ℚ)) true = some tbl11 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_4_5] <;> norm_num)

/-- Node 11's full step equation. -/
theorem stepEq_11 : uStep tbl10 (5 : Fin 7) (4 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1 addEq_11_2

/-- Node 11's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_11 : childState (boxN m4res_1_1_1_5_7_12_13) node10 (4 : Fin 7) (17 : ℚ) tbl11 = DfsCert.root tree11 :=
  by
    simp only [childState, DfsCert.root, tree11, node11]
    have hlo : dfsLo (boxN m4res_1_1_1_5_7_12_13) node10.U (4 : Fin 7) = (7 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_1_5_7_12_13, node10, tbl10_c_0_4]
    norm_num [hlo]

#print axioms addEq_11_1
#print axioms addEq_11_2
#print axioms stepEq_11
#print axioms childEq_11

/-! ## 3b. The seam kills -/

/-- Seam-failure kills at node 0 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk0_seam_5_1 : uStep tbl0 (4 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (4 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_4_5] <;> norm_num)

theorem sk0_seam_6_1 : uStep tbl0 (4 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (4 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 1 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk1_seam_5_1 : uStep tbl1 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_3_5] <;> norm_num)

theorem sk1_seam_5_2 : uStep tbl1 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_3_5] <;> norm_num)

theorem sk1_seam_5_3 : uStep tbl1 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl1_c_3_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl1_c_5_3] <;> norm_num

theorem sk1_seam_6_1 : uStep tbl1 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_3_6] <;> norm_num)

theorem sk1_seam_6_2 : uStep tbl1 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_3_6] <;> norm_num)

theorem sk1_seam_6_3 : uStep tbl1 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl1_c_3_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl1_c_6_3] <;> norm_num


/-- Seam-failure kills at node 2 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk2_seam_5_1 : uStep tbl2 (5 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (5 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_5_5] <;> norm_num)

theorem sk2_seam_6_1 : uStep tbl2 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_5_6] <;> norm_num)

theorem sk2_seam_6_2 : uStep tbl2 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 3 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk3_seam_5_1 : uStep tbl3 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_3_5] <;> norm_num)

theorem sk3_seam_5_3 : uStep tbl3 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl3_c_3_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl3_c_5_3] <;> norm_num

theorem sk3_seam_6_1 : uStep tbl3 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_3_6] <;> norm_num)

theorem sk3_seam_6_2 : uStep tbl3 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_3_6] <;> norm_num)


/-- Seam-failure kills at node 5 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk5_seam_5_1 : uStep tbl5 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_5] <;> norm_num)

theorem sk5_seam_6_1 : uStep tbl5 (6 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl5 (6 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl5 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl5_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl5_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 6 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk6_seam_5_1 : uStep tbl6 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_3_5] <;> norm_num)

theorem sk6_seam_5_2 : uStep tbl6 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_3_5] <;> norm_num)

theorem sk6_seam_5_3 : uStep tbl6 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl6_c_3_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl6_c_5_3] <;> norm_num

theorem sk6_seam_6_1 : uStep tbl6 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl6 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl6 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl6_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl6_c_3_6] <;> norm_num)

theorem sk6_seam_6_3 : uStep tbl6 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl6_c_3_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl6_c_6_3] <;> norm_num


/-- Seam-failure kills at node 7 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk7_seam_5_1 : uStep tbl7 (5 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl7 (5 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl7 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl7_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl7_c_5_5] <;> norm_num)

theorem sk7_seam_6_1 : uStep tbl7 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl7 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl7 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl7_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl7_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 8 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk8_seam_5_1 : uStep tbl8 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl8 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl8 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_3_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl8_c_5_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl8_c_3_5] <;> norm_num)

theorem sk8_seam_5_3 : uStep tbl8 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl8_c_3_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl8_c_5_3] <;> norm_num

theorem sk8_seam_6_1 : uStep tbl8 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl8 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl8 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl8_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl8_c_3_6] <;> norm_num)


/-- Seam-failure kills at node 9 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk9_seam_5_1 : uStep tbl9 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (6 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_6_5] <;> norm_num)

theorem sk9_seam_6_1 : uStep tbl9 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 10 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk10_seam_5_1 : uStep tbl10 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_5_5] <;> norm_num)

theorem sk10_seam_6_1 : uStep tbl10 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl10 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl10 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl10_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl10_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl10_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 11 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk11_seam_0_1 : uStep tbl11 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl11_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl11_c_0_4] <;> norm_num

theorem sk11_seam_5_1 : uStep tbl11 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl11 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl11 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl11_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl11_c_4_5] <;> norm_num)

theorem sk11_seam_6_1 : uStep tbl11 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl11 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl11 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl11_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl11_c_4_6] <;> norm_num)

theorem sk11_seam_6_4 : uStep tbl11 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl11_c_4_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl11_c_6_4] <;> norm_num


#print axioms sk0_seam_5_1
#print axioms sk0_seam_6_1
#print axioms sk1_seam_5_1
#print axioms sk1_seam_5_2
#print axioms sk1_seam_5_3
#print axioms sk1_seam_6_1
#print axioms sk1_seam_6_2
#print axioms sk1_seam_6_3
#print axioms sk2_seam_5_1
#print axioms sk2_seam_6_1
#print axioms sk2_seam_6_2
#print axioms sk3_seam_5_1
#print axioms sk3_seam_5_3
#print axioms sk3_seam_6_1
#print axioms sk3_seam_6_2
#print axioms sk5_seam_5_1
#print axioms sk5_seam_6_1
#print axioms sk6_seam_5_1
#print axioms sk6_seam_5_2
#print axioms sk6_seam_5_3
#print axioms sk6_seam_6_1
#print axioms sk6_seam_6_3
#print axioms sk7_seam_5_1
#print axioms sk7_seam_6_1
#print axioms sk8_seam_5_1
#print axioms sk8_seam_5_3
#print axioms sk8_seam_6_1
#print axioms sk9_seam_5_1
#print axioms sk9_seam_6_1
#print axioms sk10_seam_5_1
#print axioms sk10_seam_6_1
#print axioms sk11_seam_0_1
#print axioms sk11_seam_5_1
#print axioms sk11_seam_6_1
#print axioms sk11_seam_6_4

/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/

/-- The `match-completeness` at node 0: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_0 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node0 b A B) : ∃ c ∈ children0, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node0 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree1, by simp [children0], tbl1, stepEq_1, childEq_1⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk0_seam_5_1).elim
    · exact ⟨tree2, by simp [children0], tbl2, stepEq_2, childEq_2⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl0_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl0 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk0_seam_6_1).elim
    · exact ⟨tree5, by simp [children0], tbl5, stepEq_5, childEq_5⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
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
theorem enumDead_1 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node1 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 50)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (4 : Fin 7) = (99 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨4, by norm_num⟩ : Fin 7) = (99 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((99 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 50 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((99 / 14 : ℚ)) ≤ (50 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk1_seam_5_1
    · exact hseam sk1_seam_5_2
    · exact hseam sk1_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl1_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl1 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk1_seam_6_1
    · exact hseam sk1_seam_6_2
    · exact hseam sk1_seam_6_3
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
theorem enumMatch_2 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node2 b A B) : ∃ c ∈ children2, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node2 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree3, by simp [children2], tbl3, stepEq_3, childEq_3⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
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

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl2_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl2 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk2_seam_6_1).elim
    · exact (hseam sk2_seam_6_2).elim
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
theorem enumMatch_3 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node3 b A B) : ∃ c ∈ children3, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node3 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk3_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk3_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node3, node2, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl3_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl3 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk3_seam_6_1).elim
    · exact (hseam sk3_seam_6_2).elim
    · exact ⟨tree4, by simp [children3], tbl4, stepEq_4, childEq_4⟩
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
theorem enumMatch_5 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node5 b A B) : ∃ c ∈ children5, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node5 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree6, by simp [children5], tbl6, stepEq_6, childEq_6⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk5_seam_5_1).elim
    · exact ⟨tree7, by simp [children5], tbl7, stepEq_7, childEq_7⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl5_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl5 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk5_seam_6_1).elim
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


/-- The `dead-end verdict` at node 6: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_6 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node6 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk6_seam_5_1
    · exact hseam sk6_seam_5_2
    · exact hseam sk6_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 94)
    simp only [node6, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (6 : Fin 7) = (187 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl6_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl6 (⟨6, by norm_num⟩ : Fin 7) = (187 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((187 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 94 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((187 / 14 : ℚ)) ≤ (94 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk6_seam_6_1
    · exact hfresh (by decide)
    · exact hseam sk6_seam_6_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 7: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_7 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node7 b A B) : ∃ c ∈ children7, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node7 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree8, by simp [children7], tbl8, stepEq_8, childEq_8⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk7_seam_5_1).elim
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

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl7_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl7 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk7_seam_6_1).elim
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


/-- The `match-completeness` at node 8: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_8 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node8 b A B) : ∃ c ∈ children8, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node8 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk8_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk8_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl8_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl8 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk8_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree9, by simp [children8], tbl9, stepEq_9, childEq_9⟩
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
theorem enumMatch_9 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node9 b A B) : ∃ c ∈ children9, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node9 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 37)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (3 : Fin 7) = (243 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨3, by norm_num⟩ : Fin 7) = (243 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((243 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 37 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((243 / 46 : ℚ)) ≤ (37 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk9_seam_5_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree10, by simp [children9], tbl10, stepEq_10, childEq_10⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl9_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl9 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk9_seam_6_1).elim
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


/-- The `match-completeness` at node 10: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_10 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node10 b A B) : ∃ c ∈ children10, DfsMatch (boxN m4res_1_1_1_5_7_12_13) node10 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 37)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (3 : Fin 7) = (243 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨3, by norm_num⟩ : Fin 7) = (243 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((243 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 37 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((243 / 46 : ℚ)) ≤ (37 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree11, by simp [children10], tbl11, stepEq_11, childEq_11⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
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

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl10_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl10 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk10_seam_6_1).elim
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


/-- The `dead-end verdict` at node 11: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_11 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_1_5_7_12_13) node11 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk11_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (2 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨2, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 37)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (3 : Fin 7) = (243 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨3, by norm_num⟩ : Fin 7) = (243 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((243 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 37 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((243 / 46 : ℚ)) ≤ (37 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 6, M = ceil(7·hi) = 53)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (4 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨4, by norm_num⟩ : Fin 7) = (15 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((15 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 53 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((15 / 2 : ℚ)) ≤ (53 : ℚ))
    have h8 : j ≤ 6 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (5 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨5, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk11_seam_5_1
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

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 95)
    simp only [node11, node10, node9, node8, node7, node5, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (6 : Fin 7) = (27 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl11_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl11 (⟨6, by norm_num⟩ : Fin 7) = (27 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((27 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 95 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((27 / 2 : ℚ)) ≤ (95 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk11_seam_6_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hseam sk11_seam_6_4
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


#print axioms enumMatch_0
#print axioms enumDead_1
#print axioms enumMatch_2
#print axioms enumMatch_3
#print axioms enumMatch_5
#print axioms enumDead_6
#print axioms enumMatch_7
#print axioms enumMatch_8
#print axioms enumMatch_9
#print axioms enumMatch_10
#print axioms enumDead_11

/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/

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
  refine ⟨nodeOK_8, ?_⟩
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_9
  · exact absurd ht'1 (by simp)

#print axioms closed_8
theorem closed_7 : DfsClosed tree7 := by
  simp only [tree7, DfsClosed]
  refine ⟨nodeOK_7, ?_⟩
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_8
  · exact absurd ht'1 (by simp)

#print axioms closed_7
theorem closed_6 : DfsClosed tree6 := by
  simp only [tree6, DfsClosed]
  exact nodeOK_6

#print axioms closed_6
theorem closed_5 : DfsClosed tree5 := by
  simp only [tree5, DfsClosed]
  refine ⟨nodeOK_5, ?_⟩
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_6
  · rcases ht'1 with rfl | ht'2
    · exact closed_7
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
  · exact absurd ht'1 (by simp)

#print axioms closed_2
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
  · rcases ht'1 with rfl | ht'2
    · exact closed_2
    · rcases ht'2 with rfl | ht'3
      · exact closed_5
      · exact absurd ht'3 (by simp)

#print axioms closed_0

theorem enum_11 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree11 := by
  simp only [tree11, DfsEnum]
  exact fun b A B hf => enumDead_11 b A B hf

#print axioms enum_11
theorem enum_10 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree10 := by
  simp only [tree10, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_10 b A B hf, ?_⟩
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_11
  · exact absurd ht'1 (by simp)

#print axioms enum_10
theorem enum_9 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree9 := by
  simp only [tree9, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_9 b A B hf, ?_⟩
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_10
  · exact absurd ht'1 (by simp)

#print axioms enum_9
theorem enum_8 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree8 := by
  simp only [tree8, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_8 b A B hf, ?_⟩
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_9
  · exact absurd ht'1 (by simp)

#print axioms enum_8
theorem enum_7 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree7 := by
  simp only [tree7, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_7 b A B hf, ?_⟩
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_8
  · exact absurd ht'1 (by simp)

#print axioms enum_7
theorem enum_6 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree6 := by
  simp only [tree6, DfsEnum]
  exact fun b A B hf => enumDead_6 b A B hf

#print axioms enum_6
theorem enum_5 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree5 := by
  simp only [tree5, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_5 b A B hf, ?_⟩
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_6
  · rcases ht'1 with rfl | ht'2
    · exact enum_7
    · exact absurd ht'2 (by simp)

#print axioms enum_5
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_4 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree4 := by
  simp only [tree4, DfsEnum]

#print axioms enum_4
theorem enum_3 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree3 := by
  simp only [tree3, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_3 b A B hf, ?_⟩
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_4
  · exact absurd ht'1 (by simp)

#print axioms enum_3
theorem enum_2 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree2 := by
  simp only [tree2, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_2 b A B hf, ?_⟩
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_3
  · exact absurd ht'1 (by simp)

#print axioms enum_2
theorem enum_1 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree1 := by
  simp only [tree1, DfsEnum]
  exact fun b A B hf => enumDead_1 b A B hf

#print axioms enum_1
theorem enum_0 : DfsEnum (boxN m4res_1_1_1_5_7_12_13) tree0 := by
  simp only [tree0, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_0 b A B hf, ?_⟩
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_1
  · rcases ht'1 with rfl | ht'2
    · exact enum_2
    · rcases ht'2 with rfl | ht'3
      · exact enum_5
      · exact absurd ht'3 (by simp)

#print axioms enum_0

/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_11 : DfsPruneDom tree11 := by
  simp only [tree11, DfsPruneDom]

#print axioms pd_11
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_10 : DfsPruneDom tree10 := by
  simp only [tree10, DfsPruneDom]
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_11
  · exact absurd ht'1 (by simp)

#print axioms pd_10
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_9 : DfsPruneDom tree9 := by
  simp only [tree9, DfsPruneDom]
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_10
  · exact absurd ht'1 (by simp)

#print axioms pd_9
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_8 : DfsPruneDom tree8 := by
  simp only [tree8, DfsPruneDom]
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_9
  · exact absurd ht'1 (by simp)

#print axioms pd_8
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_7 : DfsPruneDom tree7 := by
  simp only [tree7, DfsPruneDom]
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_8
  · exact absurd ht'1 (by simp)

#print axioms pd_7
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_6 : DfsPruneDom tree6 := by
  simp only [tree6, DfsPruneDom]

#print axioms pd_6
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_5 : DfsPruneDom tree5 := by
  simp only [tree5, DfsPruneDom]
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_6
  · rcases ht'1 with rfl | ht'2
    · exact pd_7
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
theorem pd_2 (hprune_4 : DfsPruneDom tree4) : DfsPruneDom tree2 := by
  simp only [tree2, DfsPruneDom]
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_3 hprune_4 
  · exact absurd ht'1 (by simp)

#print axioms pd_2
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_1 : DfsPruneDom tree1 := by
  simp only [tree1, DfsPruneDom]

#print axioms pd_1
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_0 (hprune_4 : DfsPruneDom tree4) : DfsPruneDom tree0 := by
  simp only [tree0, DfsPruneDom]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_1
  · rcases ht'1 with rfl | ht'2
    · exact pd_2 hprune_4 
    · rcases ht'2 with rfl | ht'3
      · exact pd_5
      · exact absurd ht'3 (by simp)

#print axioms pd_0

/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions (`reachutc_1_1_1_5_7_12_13.json`)

The per-prune-leaf verdict layer: the explored (frontier-sup, dump-rank) state sets
and pmax as literal data, the `no_completing_state_reachable` verdicts (discharged
HERE by literal per-case proofs over the census windows), the OWED `[P]` projection
instances (`reachutcProj_*`, discharged by the parallel `Fresh/ReachUtcProof.lean`),
and the verdict-carrying `DfsPruneDom` instances `m4fix_%s_pruneDom_*` (replacing
the identity stubs). -/

theorem hiPos_4 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_1_5_7_12_13) tbl4 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_5_7_12_13, tbl4_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_4 : List (ℚ × ℕ) := [((2 : ℚ), 7), ((15 / 7 : ℚ), 6), ((17 / 7 : ℚ), 5), ((66 / 25 : ℚ), 7), ((99 / 35 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 4
(dump state P = 2, a = 6, Aex = 25, verdict `no_completing_state_reachable`,
nst = 5, pmax = 99 / 35, transcribed from `experiments/n8/reachutc_1_1_1_5_7_12_13.json`).  FINDING
(machine-checked, `Fresh.ReachUtcProof.unrestricted_false`): the UNRESTRICTED
`DfsPruneDom` leaf condition is FALSE -- realized chains may use non-teeth zone
edges, which the state-graph verdict does not model.  The sound instance is the
ZONE form (`Fresh.ReachUtcProof.DfsPruneDomZone`, discharged by
`Fresh.ReachUtcProof.no_zone_chain_of_reach_utc`): it consumes the leaf's RELAXED
`reach_utc` closure (relaxed-closed, every sup ≤ 7, completing-free -- the strict
set transcribed below is NOT relaxed-closed), the envelope dominations `domHi`/`domLo`
from `UFine` plus the table cells, `hiPos`, `IsZoneExit Aex` and `Aex/dfsLo a ≤ P`.
Worked pattern: `Fresh.ReachUtcProof.verdict2`/`S2`/`domHi2`/`domLo2`/`no_zone_chain_leaf2`.
This stub carries the zone-form OWED until the per-leaf relaxed closures are
transcribed and the instance is discharged. -/
-- STANDING: OWED
theorem m4fix_1_1_1_5_7_12_13_pruneDom_4 (h : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) :
    DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4 := h

#print axioms m4fix_1_1_1_5_7_12_13_pruneDom_4

theorem pdZone_11 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree11 := by
  simp only [tree11, DfsPruneDomZone]

#print axioms pdZone_11
theorem pdZone_10 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree10 := by
  simp only [tree10, DfsPruneDomZone]
  intro t ht
  simp only [children10, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_11
  · exact absurd ht'1 (by simp)

#print axioms pdZone_10
theorem pdZone_9 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree9 := by
  simp only [tree9, DfsPruneDomZone]
  intro t ht
  simp only [children9, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_10
  · exact absurd ht'1 (by simp)

#print axioms pdZone_9
theorem pdZone_8 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree8 := by
  simp only [tree8, DfsPruneDomZone]
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_9
  · exact absurd ht'1 (by simp)

#print axioms pdZone_8
theorem pdZone_7 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree7 := by
  simp only [tree7, DfsPruneDomZone]
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_8
  · exact absurd ht'1 (by simp)

#print axioms pdZone_7
theorem pdZone_6 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree6 := by
  simp only [tree6, DfsPruneDomZone]

#print axioms pdZone_6
theorem pdZone_5 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree5 := by
  simp only [tree5, DfsPruneDomZone]
  intro t ht
  simp only [children5, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_6
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_7
    · exact absurd ht'2 (by simp)

#print axioms pdZone_5
theorem pdZone_4 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) :
    DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4 := hpruneZone_4

#print axioms pdZone_4
theorem pdZone_3 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree3 := by
  simp only [tree3, DfsPruneDomZone]
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_4 hpruneZone_4 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_3
theorem pdZone_2 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree2 := by
  simp only [tree2, DfsPruneDomZone]
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_3 hpruneZone_4 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_2
theorem pdZone_1 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree1 := by
  simp only [tree1, DfsPruneDomZone]

#print axioms pdZone_1
theorem pdZone_0 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree0 := by
  simp only [tree0, DfsPruneDomZone]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_1
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_2 hpruneZone_4 
    · rcases ht'2 with rfl | ht'3
      · exact pdZone_5
      · exact absurd ht'3 (by simp)

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
theorem hforestEnum : ∀ t ∈ forest, DfsEnum (boxN m4res_1_1_1_5_7_12_13) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_0
  · exact absurd ht'1 (by simp)

/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly
OWED (b)
so this proof needs no hypotheses; at dead ends and internal nodes the condition is
inherited/vacuous. -/
theorem hforestPruneDom (hprune_4 : DfsPruneDom tree4) : ∀ t ∈ forest, DfsPruneDom t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_0 hprune_4 
  · exact absurd ht'1 (by simp)

/-- The zone-form per-prune-leaf domination over the FOREST: at the reach-prune
leaves exactly OWED (b)'s zone-form remainder (the per-leaf zone-form stubs of
section 5b; the UNRESTRICTED form is false --
`Fresh.ReachUtcProof.unrestricted_false`). -/
theorem hforestPruneDomZone (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) : ∀ t ∈ forest, DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_0 hpruneZone_4 
  · exact absurd ht'1 (by simp)

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;
the artifacts give only the reconstructed root states, no opening-match record.
Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade
statement of E810's strict-monotone reading for this box. -/
-- STANDING: OWED
theorem m4fix_1_1_1_5_7_12_13_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_1_1_5_7_12_13) forest) :
    DfsRootAdm (boxN m4res_1_1_1_5_7_12_13) forest := hcadm

/-! ## 7. The census envelope and the composed theorems (generic data connection) -/

/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the
record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists
only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise
exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /
`m4boxClear_of_data` directly). -/
theorem hn17_1_1_1_5_7_12_13 : ∀ i : Fin 7, boxN m4res_1_1_1_5_7_12_13 i ≤ 17 := by
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

#print axioms hn17_1_1_1_5_7_12_13

/-- **The composed certificate theorem**: the banked record (`m4resData_1_1_1_5_7_12_13`,
[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the
90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim.  The
per-prune-leaf domination hypotheses are the reach_utc projection instances
(`hproj_<l> : reachutcProj_1_1_1_5_7_12_13_<l>`, OWED (b)'s per-leaf remainder); the verdict side
of each leaf is discharged inside `m4fix_1_1_1_5_7_12_13_pruneDom_<l>` from the transcribed
`reachutc_1_1_1_5_7_12_13.json` verdicts. -/
theorem m4fix_1_1_1_5_7_12_13_cert (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) (hcadm : DfsRootAdm (boxN m4res_1_1_1_5_7_12_13) forest) :
    M4CertSound (boxN m4res_1_1_1_5_7_12_13) ∧
      ∀ k ∈ m4res_1_1_1_5_7_12_13.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  ⟨m4CertSound_of_forest_zone (boxN m4res_1_1_1_5_7_12_13) forest hforestClosed hforestEnum
    (hforestPruneDomZone hpruneZone_4 ) hcadm, leafKeys_env90 m4res_1_1_1_5_7_12_13 m4resData_1_1_1_5_7_12_13⟩

/-- **The composed clear-point theorem (the scaling target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --
the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest
instead of a crown. -/
theorem m4fix_1_1_1_5_7_12_13_boxClear (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_1_5_7_12_13) tree4) (hcadm : DfsRootAdm (boxN m4res_1_1_1_5_7_12_13) forest)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_1_1_5_7_12_13) hn17_1_1_1_5_7_12_13)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_1_1_5_7_12_13) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_1_1_5_7_12_13) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_cert hn17_1_1_1_5_7_12_13 hcc
    (m4CertSound_of_forest_zone (boxN m4res_1_1_1_5_7_12_13) forest hforestClosed hforestEnum (hforestPruneDomZone hpruneZone_4 ) hcadm)
    g hface

#print axioms m4fix_1_1_1_5_7_12_13_cert
#print axioms m4fix_1_1_1_5_7_12_13_boxClear

end Fresh.M4FixRung2_1_1_1_5_7_12_13

