import Fresh.M4CertSound
import Fresh.M4FixResBank_v1
import Fresh.ReachUtcProof

/-!
# M4FixRung2_1_1_4_5_6_8_12: per-box M4 certificate transcription, box (1, 1, 4, 5, 6, 8, 12)

Written 2026-11-20 by `m4fix_gen_v1.py` from the per-box reconstruction
(`experiments/n8/m4fix_recon_v1.py`, [T]-verified against both checkpoint artifacts
(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the
CONSTRUCTED record `Fresh.M4FixResBank_v1.m4res_1_1_4_5_6_8_12`).  No existing file is edited.

This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a
WHOLE certificate FOREST: all 40 nodes of the box's reconstructed DFS certificate
tree(s) -- 24 internal, 10 reach-prune leaves,
6 dead-end leaves, 1 start-zone root(s) -- transcribed as literal `DfsCert` data: tables as
49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,
seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,
and the composed theorems through the GENERIC data connection
(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).

OWED (named, not discharged by any existing artifact):
* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`'s header: the E810 strict-monotone
  opening side (hypothesis-identity stub here, as in rung 1).
* OWED (b) -- now SPLIT by the per-leaf verdict transcription (section 5b): the
  verdict side of every reach-prune leaf's `reach_utc` domination is transcribed
  from `experiments/n8/reachutc_1_1_4_5_6_8_12.json` and DISCHARGED here
  (`verdictNoCompl_*`); what remains OWED per leaf is the `[P]` state-graph
  PROJECTION instance `reachutcProj_*` (realized chain → completing state
  reachable), being proved in parallel in `Fresh/ReachUtcProof.lean`.
-/

namespace Fresh.M4FixRung2_1_1_4_5_6_8_12

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

/-- Table of DFS node 0 (internal, depth 1, last reading row 5, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 11 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 11 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((17 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 9 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 11 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl0_c_0_0 : tbl0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_0_1 : tbl0 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_2 : tbl0 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl0_c_0_3 : tbl0 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl0_c_0_4 : tbl0 (0 : Fin 7) (4 : Fin 7) = some ((2 / 11 : ℚ), false) := rfl
theorem tbl0_c_0_5 : tbl0 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl0_c_0_6 : tbl0 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl0_c_1_0 : tbl0 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl0_c_1_1 : tbl0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_1_2 : tbl0 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl0_c_1_3 : tbl0 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl0_c_1_4 : tbl0 (1 : Fin 7) (4 : Fin 7) = some ((3 / 11 : ℚ), false) := rfl
theorem tbl0_c_1_5 : tbl0 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl0_c_1_6 : tbl0 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl0_c_2_0 : tbl0 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl0_c_2_1 : tbl0 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_2_2 : tbl0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_2_3 : tbl0 (2 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_2_4 : tbl0 (2 : Fin 7) (4 : Fin 7) = some ((9 / 11 : ℚ), false) := rfl
theorem tbl0_c_2_5 : tbl0 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl0_c_2_6 : tbl0 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl0_c_3_0 : tbl0 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl0_c_3_1 : tbl0 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_2 : tbl0 (3 : Fin 7) (2 : Fin 7) = some ((11 / 7 : ℚ), false) := rfl
theorem tbl0_c_3_3 : tbl0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_3_4 : tbl0 (3 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_3_5 : tbl0 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl0_c_3_6 : tbl0 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl0_c_4_0 : tbl0 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl0_c_4_1 : tbl0 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_2 : tbl0 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl0_c_4_3 : tbl0 (4 : Fin 7) (3 : Fin 7) = some ((13 / 9 : ℚ), false) := rfl
theorem tbl0_c_4_4 : tbl0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_4_5 : tbl0 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl0_c_4_6 : tbl0 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl0_c_5_0 : tbl0 (5 : Fin 7) (0 : Fin 7) = some ((17 / 2 : ℚ), false) := rfl
theorem tbl0_c_5_1 : tbl0 (5 : Fin 7) (1 : Fin 7) = some ((17 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_2 : tbl0 (5 : Fin 7) (2 : Fin 7) = some ((17 / 7 : ℚ), false) := rfl
theorem tbl0_c_5_3 : tbl0 (5 : Fin 7) (3 : Fin 7) = some ((17 / 9 : ℚ), false) := rfl
theorem tbl0_c_5_4 : tbl0 (5 : Fin 7) (4 : Fin 7) = some ((17 / 11 : ℚ), false) := rfl
theorem tbl0_c_5_5 : tbl0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_5_6 : tbl0 (5 : Fin 7) (6 : Fin 7) = some ((17 / 23 : ℚ), false) := rfl
theorem tbl0_c_6_0 : tbl0 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl0_c_6_1 : tbl0 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_2 : tbl0 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl0_c_6_3 : tbl0 (6 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl0_c_6_4 : tbl0 (6 : Fin 7) (4 : Fin 7) = some ((25 / 11 : ℚ), false) := rfl
theorem tbl0_c_6_5 : tbl0 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl0_c_6_6 : tbl0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 1 (internal, depth 2, last reading row 4, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl1 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 9 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl1_c_0_0 : tbl1 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_0_1 : tbl1 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_0_2 : tbl1 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl1_c_0_3 : tbl1 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl1_c_0_4 : tbl1 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl1_c_0_5 : tbl1 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl1_c_0_6 : tbl1 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl1_c_1_0 : tbl1 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl1_c_1_1 : tbl1 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_1_2 : tbl1 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl1_c_1_3 : tbl1 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl1_c_1_4 : tbl1 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl1_c_1_5 : tbl1 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl1_c_1_6 : tbl1 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl1_c_2_0 : tbl1 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl1_c_2_1 : tbl1 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl1_c_2_2 : tbl1 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_2_3 : tbl1 (2 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl1_c_2_4 : tbl1 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl1_c_2_5 : tbl1 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl1_c_2_6 : tbl1 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl1_c_3_0 : tbl1 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl1_c_3_1 : tbl1 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl1_c_3_2 : tbl1 (3 : Fin 7) (2 : Fin 7) = some ((11 / 7 : ℚ), false) := rfl
theorem tbl1_c_3_3 : tbl1 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_3_4 : tbl1 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tbl1_c_3_5 : tbl1 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl1_c_3_6 : tbl1 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl1_c_4_0 : tbl1 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl1_c_4_1 : tbl1 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl1_c_4_2 : tbl1 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl1_c_4_3 : tbl1 (4 : Fin 7) (3 : Fin 7) = some ((13 / 9 : ℚ), false) := rfl
theorem tbl1_c_4_4 : tbl1 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_4_5 : tbl1 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl1_c_4_6 : tbl1 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl1_c_5_0 : tbl1 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl1_c_5_1 : tbl1 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl1_c_5_2 : tbl1 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl1_c_5_3 : tbl1 (5 : Fin 7) (3 : Fin 7) = some ((13 / 7 : ℚ), true) := rfl
theorem tbl1_c_5_4 : tbl1 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl1_c_5_5 : tbl1 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl1_c_5_6 : tbl1 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl1_c_6_0 : tbl1 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl1_c_6_1 : tbl1 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl1_c_6_2 : tbl1 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl1_c_6_3 : tbl1 (6 : Fin 7) (3 : Fin 7) = some ((25 / 9 : ℚ), false) := rfl
theorem tbl1_c_6_4 : tbl1 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl1_c_6_5 : tbl1 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl1_c_6_6 : tbl1 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 2 (internal, depth 3, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl2 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl2_c_0_0 : tbl2 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_0_1 : tbl2 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl2_c_0_2 : tbl2 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl2_c_0_3 : tbl2 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl2_c_0_4 : tbl2 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl2_c_0_5 : tbl2 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl2_c_0_6 : tbl2 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl2_c_1_0 : tbl2 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl2_c_1_1 : tbl2 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_1_2 : tbl2 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl2_c_1_3 : tbl2 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl2_c_1_4 : tbl2 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl2_c_1_5 : tbl2 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl2_c_1_6 : tbl2 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl2_c_2_0 : tbl2 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl2_c_2_1 : tbl2 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl2_c_2_2 : tbl2 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_2_3 : tbl2 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl2_c_2_4 : tbl2 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl2_c_2_5 : tbl2 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl2_c_2_6 : tbl2 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl2_c_3_0 : tbl2 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl2_c_3_1 : tbl2 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl2_c_3_2 : tbl2 (3 : Fin 7) (2 : Fin 7) = some ((11 / 7 : ℚ), false) := rfl
theorem tbl2_c_3_3 : tbl2 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_3_4 : tbl2 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tbl2_c_3_5 : tbl2 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl2_c_3_6 : tbl2 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl2_c_4_0 : tbl2 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl2_c_4_1 : tbl2 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl2_c_4_2 : tbl2 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl2_c_4_3 : tbl2 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl2_c_4_4 : tbl2 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_4_5 : tbl2 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl2_c_4_6 : tbl2 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl2_c_5_0 : tbl2 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl2_c_5_1 : tbl2 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl2_c_5_2 : tbl2 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl2_c_5_3 : tbl2 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl2_c_5_4 : tbl2 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl2_c_5_5 : tbl2 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl2_c_5_6 : tbl2 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl2_c_6_0 : tbl2 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl2_c_6_1 : tbl2 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl2_c_6_2 : tbl2 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl2_c_6_3 : tbl2 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl2_c_6_4 : tbl2 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl2_c_6_5 : tbl2 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl2_c_6_6 : tbl2 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 3 (internal, depth 4, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl3 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((486 / 1715 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 1715 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl3_c_0_0 : tbl3 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_0_1 : tbl3 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl3_c_0_2 : tbl3 (0 : Fin 7) (2 : Fin 7) = some ((486 / 1715 : ℚ), true) := rfl
theorem tbl3_c_0_3 : tbl3 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl3_c_0_4 : tbl3 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl3_c_0_5 : tbl3 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl3_c_0_6 : tbl3 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl3_c_1_0 : tbl3 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl3_c_1_1 : tbl3 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_1_2 : tbl3 (1 : Fin 7) (2 : Fin 7) = some ((729 / 1715 : ℚ), true) := rfl
theorem tbl3_c_1_3 : tbl3 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl3_c_1_4 : tbl3 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl3_c_1_5 : tbl3 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl3_c_1_6 : tbl3 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl3_c_2_0 : tbl3 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl3_c_2_1 : tbl3 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl3_c_2_2 : tbl3 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_2_3 : tbl3 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl3_c_2_4 : tbl3 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl3_c_2_5 : tbl3 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl3_c_2_6 : tbl3 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl3_c_3_0 : tbl3 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl3_c_3_1 : tbl3 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl3_c_3_2 : tbl3 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl3_c_3_3 : tbl3 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_3_4 : tbl3 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tbl3_c_3_5 : tbl3 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl3_c_3_6 : tbl3 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl3_c_4_0 : tbl3 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl3_c_4_1 : tbl3 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl3_c_4_2 : tbl3 (4 : Fin 7) (2 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl3_c_4_3 : tbl3 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl3_c_4_4 : tbl3 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_4_5 : tbl3 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl3_c_4_6 : tbl3 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl3_c_5_0 : tbl3 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl3_c_5_1 : tbl3 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl3_c_5_2 : tbl3 (5 : Fin 7) (2 : Fin 7) = some ((729 / 343 : ℚ), true) := rfl
theorem tbl3_c_5_3 : tbl3 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl3_c_5_4 : tbl3 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl3_c_5_5 : tbl3 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl3_c_5_6 : tbl3 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl3_c_6_0 : tbl3 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl3_c_6_1 : tbl3 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl3_c_6_2 : tbl3 (6 : Fin 7) (2 : Fin 7) = some ((1215 / 343 : ℚ), true) := rfl
theorem tbl3_c_6_3 : tbl3 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl3_c_6_4 : tbl3 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl3_c_6_5 : tbl3 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl3_c_6_6 : tbl3 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 4 (reach, depth 5, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 45 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 27 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl4_c_0_0 : tbl4 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_0_1 : tbl4 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl4_c_0_2 : tbl4 (0 : Fin 7) (2 : Fin 7) = some ((34 / 135 : ℚ), true) := rfl
theorem tbl4_c_0_3 : tbl4 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl4_c_0_4 : tbl4 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl4_c_0_5 : tbl4 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl4_c_0_6 : tbl4 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl4_c_1_0 : tbl4 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl4_c_1_1 : tbl4 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_1_2 : tbl4 (1 : Fin 7) (2 : Fin 7) = some ((17 / 45 : ℚ), true) := rfl
theorem tbl4_c_1_3 : tbl4 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl4_c_1_4 : tbl4 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl4_c_1_5 : tbl4 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl4_c_1_6 : tbl4 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl4_c_2_0 : tbl4 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl4_c_2_1 : tbl4 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl4_c_2_2 : tbl4 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_2_3 : tbl4 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl4_c_2_4 : tbl4 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl4_c_2_5 : tbl4 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl4_c_2_6 : tbl4 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl4_c_3_0 : tbl4 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl4_c_3_1 : tbl4 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl4_c_3_2 : tbl4 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl4_c_3_3 : tbl4 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_3_4 : tbl4 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tbl4_c_3_5 : tbl4 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl4_c_3_6 : tbl4 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl4_c_4_0 : tbl4 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl4_c_4_1 : tbl4 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl4_c_4_2 : tbl4 (4 : Fin 7) (2 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl4_c_4_3 : tbl4 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl4_c_4_4 : tbl4 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_4_5 : tbl4 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl4_c_4_6 : tbl4 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl4_c_5_0 : tbl4 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl4_c_5_1 : tbl4 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl4_c_5_2 : tbl4 (5 : Fin 7) (2 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl4_c_5_3 : tbl4 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl4_c_5_4 : tbl4 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl4_c_5_5 : tbl4 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl4_c_5_6 : tbl4 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl4_c_6_0 : tbl4 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl4_c_6_1 : tbl4 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl4_c_6_2 : tbl4 (6 : Fin 7) (2 : Fin 7) = some ((85 / 27 : ℚ), true) := rfl
theorem tbl4_c_6_3 : tbl4 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl4_c_6_4 : tbl4 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl4_c_6_5 : tbl4 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl4_c_6_6 : tbl4 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 5 (reach, depth 5, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((50 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl5_c_0_0 : tbl5 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_0_1 : tbl5 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl5_c_0_2 : tbl5 (0 : Fin 7) (2 : Fin 7) = some ((50 / 207 : ℚ), true) := rfl
theorem tbl5_c_0_3 : tbl5 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl5_c_0_4 : tbl5 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl5_c_0_5 : tbl5 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl5_c_0_6 : tbl5 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl5_c_1_0 : tbl5 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl5_c_1_1 : tbl5 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_1_2 : tbl5 (1 : Fin 7) (2 : Fin 7) = some ((25 / 69 : ℚ), true) := rfl
theorem tbl5_c_1_3 : tbl5 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl5_c_1_4 : tbl5 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl5_c_1_5 : tbl5 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl5_c_1_6 : tbl5 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl5_c_2_0 : tbl5 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl5_c_2_1 : tbl5 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl5_c_2_2 : tbl5 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_2_3 : tbl5 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl5_c_2_4 : tbl5 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl5_c_2_5 : tbl5 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl5_c_2_6 : tbl5 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl5_c_3_0 : tbl5 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl5_c_3_1 : tbl5 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl5_c_3_2 : tbl5 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl5_c_3_3 : tbl5 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_3_4 : tbl5 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tbl5_c_3_5 : tbl5 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl5_c_3_6 : tbl5 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl5_c_4_0 : tbl5 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl5_c_4_1 : tbl5 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl5_c_4_2 : tbl5 (4 : Fin 7) (2 : Fin 7) = some ((325 / 207 : ℚ), true) := rfl
theorem tbl5_c_4_3 : tbl5 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl5_c_4_4 : tbl5 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_4_5 : tbl5 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl5_c_4_6 : tbl5 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl5_c_5_0 : tbl5 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl5_c_5_1 : tbl5 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl5_c_5_2 : tbl5 (5 : Fin 7) (2 : Fin 7) = some ((325 / 161 : ℚ), true) := rfl
theorem tbl5_c_5_3 : tbl5 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl5_c_5_4 : tbl5 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl5_c_5_5 : tbl5 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl5_c_5_6 : tbl5 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl5_c_6_0 : tbl5 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl5_c_6_1 : tbl5 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl5_c_6_2 : tbl5 (6 : Fin 7) (2 : Fin 7) = some ((25 / 9 : ℚ), true) := rfl
theorem tbl5_c_6_3 : tbl5 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl5_c_6_4 : tbl5 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl5_c_6_5 : tbl5 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl5_c_6_6 : tbl5 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 6 (reach, depth 5, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl6 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((486 / 1715 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((4374 / 53165 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 1715 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((6561 / 53165 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 434 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 3038 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((164025 / 21266 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((164025 / 21266 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((6561 / 10633 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl6_c_0_0 : tbl6 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_0_1 : tbl6 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl6_c_0_2 : tbl6 (0 : Fin 7) (2 : Fin 7) = some ((486 / 1715 : ℚ), true) := rfl
theorem tbl6_c_0_3 : tbl6 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl6_c_0_4 : tbl6 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl6_c_0_5 : tbl6 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl6_c_0_6 : tbl6 (0 : Fin 7) (6 : Fin 7) = some ((4374 / 53165 : ℚ), true) := rfl
theorem tbl6_c_1_0 : tbl6 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl6_c_1_1 : tbl6 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_1_2 : tbl6 (1 : Fin 7) (2 : Fin 7) = some ((729 / 1715 : ℚ), true) := rfl
theorem tbl6_c_1_3 : tbl6 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl6_c_1_4 : tbl6 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl6_c_1_5 : tbl6 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl6_c_1_6 : tbl6 (1 : Fin 7) (6 : Fin 7) = some ((6561 / 53165 : ℚ), true) := rfl
theorem tbl6_c_2_0 : tbl6 (2 : Fin 7) (0 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl6_c_2_1 : tbl6 (2 : Fin 7) (1 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl6_c_2_2 : tbl6 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_2_3 : tbl6 (2 : Fin 7) (3 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl6_c_2_4 : tbl6 (2 : Fin 7) (4 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl6_c_2_5 : tbl6 (2 : Fin 7) (5 : Fin 7) = some ((15 / 31 : ℚ), true) := rfl
theorem tbl6_c_2_6 : tbl6 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl6_c_3_0 : tbl6 (3 : Fin 7) (0 : Fin 7) = some ((2025 / 434 : ℚ), true) := rfl
theorem tbl6_c_3_1 : tbl6 (3 : Fin 7) (1 : Fin 7) = some ((2025 / 434 : ℚ), true) := rfl
theorem tbl6_c_3_2 : tbl6 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl6_c_3_3 : tbl6 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_3_4 : tbl6 (3 : Fin 7) (4 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl6_c_3_5 : tbl6 (3 : Fin 7) (5 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl6_c_3_6 : tbl6 (3 : Fin 7) (6 : Fin 7) = some ((81 / 217 : ℚ), true) := rfl
theorem tbl6_c_4_0 : tbl6 (4 : Fin 7) (0 : Fin 7) = some ((18225 / 3038 : ℚ), true) := rfl
theorem tbl6_c_4_1 : tbl6 (4 : Fin 7) (1 : Fin 7) = some ((18225 / 3038 : ℚ), true) := rfl
theorem tbl6_c_4_2 : tbl6 (4 : Fin 7) (2 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl6_c_4_3 : tbl6 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl6_c_4_4 : tbl6 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_4_5 : tbl6 (4 : Fin 7) (5 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl6_c_4_6 : tbl6 (4 : Fin 7) (6 : Fin 7) = some ((729 / 1519 : ℚ), true) := rfl
theorem tbl6_c_5_0 : tbl6 (5 : Fin 7) (0 : Fin 7) = some ((164025 / 21266 : ℚ), true) := rfl
theorem tbl6_c_5_1 : tbl6 (5 : Fin 7) (1 : Fin 7) = some ((164025 / 21266 : ℚ), true) := rfl
theorem tbl6_c_5_2 : tbl6 (5 : Fin 7) (2 : Fin 7) = some ((729 / 343 : ℚ), true) := rfl
theorem tbl6_c_5_3 : tbl6 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl6_c_5_4 : tbl6 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl6_c_5_5 : tbl6 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl6_c_5_6 : tbl6 (5 : Fin 7) (6 : Fin 7) = some ((6561 / 10633 : ℚ), true) := rfl
theorem tbl6_c_6_0 : tbl6 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl6_c_6_1 : tbl6 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl6_c_6_2 : tbl6 (6 : Fin 7) (2 : Fin 7) = some ((1215 / 343 : ℚ), true) := rfl
theorem tbl6_c_6_3 : tbl6 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl6_c_6_4 : tbl6 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl6_c_6_5 : tbl6 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl6_c_6_6 : tbl6 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 7 (internal, depth 4, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl7 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2187 / 5635 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl7_c_0_0 : tbl7 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_0_1 : tbl7 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl7_c_0_2 : tbl7 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl7_c_0_3 : tbl7 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl7_c_0_4 : tbl7 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl7_c_0_5 : tbl7 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl7_c_0_6 : tbl7 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl7_c_1_0 : tbl7 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl7_c_1_1 : tbl7 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_1_2 : tbl7 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl7_c_1_3 : tbl7 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl7_c_1_4 : tbl7 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl7_c_1_5 : tbl7 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl7_c_1_6 : tbl7 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl7_c_2_0 : tbl7 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl7_c_2_1 : tbl7 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl7_c_2_2 : tbl7 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_2_3 : tbl7 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl7_c_2_4 : tbl7 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl7_c_2_5 : tbl7 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl7_c_2_6 : tbl7 (2 : Fin 7) (6 : Fin 7) = some ((2187 / 5635 : ℚ), true) := rfl
theorem tbl7_c_3_0 : tbl7 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl7_c_3_1 : tbl7 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl7_c_3_2 : tbl7 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl7_c_3_3 : tbl7 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_3_4 : tbl7 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl7_c_3_5 : tbl7 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl7_c_3_6 : tbl7 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl7_c_4_0 : tbl7 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl7_c_4_1 : tbl7 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl7_c_4_2 : tbl7 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl7_c_4_3 : tbl7 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl7_c_4_4 : tbl7 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_4_5 : tbl7 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl7_c_4_6 : tbl7 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl7_c_5_0 : tbl7 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl7_c_5_1 : tbl7 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl7_c_5_2 : tbl7 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl7_c_5_3 : tbl7 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl7_c_5_4 : tbl7 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl7_c_5_5 : tbl7 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl7_c_5_6 : tbl7 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl7_c_6_0 : tbl7 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl7_c_6_1 : tbl7 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl7_c_6_2 : tbl7 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl7_c_6_3 : tbl7 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl7_c_6_4 : tbl7 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl7_c_6_5 : tbl7 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl7_c_6_6 : tbl7 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 8 (internal, depth 5, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl8_c_0_0 : tbl8 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_0_1 : tbl8 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl8_c_0_2 : tbl8 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl8_c_0_3 : tbl8 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl8_c_0_4 : tbl8 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl8_c_0_5 : tbl8 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl8_c_0_6 : tbl8 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl8_c_1_0 : tbl8 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl8_c_1_1 : tbl8 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_1_2 : tbl8 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl8_c_1_3 : tbl8 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl8_c_1_4 : tbl8 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl8_c_1_5 : tbl8 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl8_c_1_6 : tbl8 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl8_c_2_0 : tbl8 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl8_c_2_1 : tbl8 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl8_c_2_2 : tbl8 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_2_3 : tbl8 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl8_c_2_4 : tbl8 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl8_c_2_5 : tbl8 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl8_c_2_6 : tbl8 (2 : Fin 7) (6 : Fin 7) = some ((9 / 25 : ℚ), true) := rfl
theorem tbl8_c_3_0 : tbl8 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl8_c_3_1 : tbl8 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl8_c_3_2 : tbl8 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl8_c_3_3 : tbl8 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_3_4 : tbl8 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl8_c_3_5 : tbl8 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl8_c_3_6 : tbl8 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl8_c_4_0 : tbl8 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl8_c_4_1 : tbl8 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl8_c_4_2 : tbl8 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl8_c_4_3 : tbl8 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl8_c_4_4 : tbl8 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_4_5 : tbl8 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl8_c_4_6 : tbl8 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl8_c_5_0 : tbl8 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl8_c_5_1 : tbl8 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl8_c_5_2 : tbl8 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl8_c_5_3 : tbl8 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl8_c_5_4 : tbl8 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl8_c_5_5 : tbl8 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl8_c_5_6 : tbl8 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl8_c_6_0 : tbl8 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl8_c_6_1 : tbl8 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl8_c_6_2 : tbl8 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), true) := rfl
theorem tbl8_c_6_3 : tbl8 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl8_c_6_4 : tbl8 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl8_c_6_5 : tbl8 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl8_c_6_6 : tbl8 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 9 (deadend, depth 6, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl9 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((1215 / 322 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((1215 / 322 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 805 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl9_c_0_0 : tbl9 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_0_1 : tbl9 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl9_c_0_2 : tbl9 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl9_c_0_3 : tbl9 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl9_c_0_4 : tbl9 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl9_c_0_5 : tbl9 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl9_c_0_6 : tbl9 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl9_c_1_0 : tbl9 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl9_c_1_1 : tbl9 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_1_2 : tbl9 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl9_c_1_3 : tbl9 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl9_c_1_4 : tbl9 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl9_c_1_5 : tbl9 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl9_c_1_6 : tbl9 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl9_c_2_0 : tbl9 (2 : Fin 7) (0 : Fin 7) = some ((1215 / 322 : ℚ), true) := rfl
theorem tbl9_c_2_1 : tbl9 (2 : Fin 7) (1 : Fin 7) = some ((1215 / 322 : ℚ), true) := rfl
theorem tbl9_c_2_2 : tbl9 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_2_3 : tbl9 (2 : Fin 7) (3 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl9_c_2_4 : tbl9 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl9_c_2_5 : tbl9 (2 : Fin 7) (5 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl9_c_2_6 : tbl9 (2 : Fin 7) (6 : Fin 7) = some ((243 / 805 : ℚ), true) := rfl
theorem tbl9_c_3_0 : tbl9 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_1 : tbl9 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl9_c_3_2 : tbl9 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl9_c_3_3 : tbl9 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_3_4 : tbl9 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl9_c_3_5 : tbl9 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl9_c_3_6 : tbl9 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl9_c_4_0 : tbl9 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl9_c_4_1 : tbl9 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl9_c_4_2 : tbl9 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl9_c_4_3 : tbl9 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl9_c_4_4 : tbl9 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_4_5 : tbl9 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl9_c_4_6 : tbl9 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl9_c_5_0 : tbl9 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl9_c_5_1 : tbl9 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl9_c_5_2 : tbl9 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl9_c_5_3 : tbl9 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl9_c_5_4 : tbl9 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl9_c_5_5 : tbl9 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl9_c_5_6 : tbl9 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl9_c_6_0 : tbl9 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl9_c_6_1 : tbl9 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl9_c_6_2 : tbl9 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), true) := rfl
theorem tbl9_c_6_3 : tbl9 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl9_c_6_4 : tbl9 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl9_c_6_5 : tbl9 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl9_c_6_6 : tbl9 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 10 (reach, depth 6, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl10 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 45 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 69 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((255 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 27 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl10_c_0_0 : tbl10 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_0_1 : tbl10 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl10_c_0_2 : tbl10 (0 : Fin 7) (2 : Fin 7) = some ((34 / 135 : ℚ), true) := rfl
theorem tbl10_c_0_3 : tbl10 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl10_c_0_4 : tbl10 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl10_c_0_5 : tbl10 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl10_c_0_6 : tbl10 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl10_c_1_0 : tbl10 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl10_c_1_1 : tbl10 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_1_2 : tbl10 (1 : Fin 7) (2 : Fin 7) = some ((17 / 45 : ℚ), true) := rfl
theorem tbl10_c_1_3 : tbl10 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl10_c_1_4 : tbl10 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl10_c_1_5 : tbl10 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl10_c_1_6 : tbl10 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl10_c_2_0 : tbl10 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl10_c_2_1 : tbl10 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl10_c_2_2 : tbl10 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_2_3 : tbl10 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl10_c_2_4 : tbl10 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl10_c_2_5 : tbl10 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl10_c_2_6 : tbl10 (2 : Fin 7) (6 : Fin 7) = some ((9 / 25 : ℚ), true) := rfl
theorem tbl10_c_3_0 : tbl10 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_1 : tbl10 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl10_c_3_2 : tbl10 (3 : Fin 7) (2 : Fin 7) = some ((85 / 69 : ℚ), true) := rfl
theorem tbl10_c_3_3 : tbl10 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_3_4 : tbl10 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl10_c_3_5 : tbl10 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl10_c_3_6 : tbl10 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl10_c_4_0 : tbl10 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl10_c_4_1 : tbl10 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl10_c_4_2 : tbl10 (4 : Fin 7) (2 : Fin 7) = some ((255 / 161 : ℚ), true) := rfl
theorem tbl10_c_4_3 : tbl10 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl10_c_4_4 : tbl10 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_4_5 : tbl10 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl10_c_4_6 : tbl10 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl10_c_5_0 : tbl10 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl10_c_5_1 : tbl10 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl10_c_5_2 : tbl10 (5 : Fin 7) (2 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl10_c_5_3 : tbl10 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl10_c_5_4 : tbl10 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl10_c_5_5 : tbl10 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl10_c_5_6 : tbl10 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl10_c_6_0 : tbl10 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl10_c_6_1 : tbl10 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl10_c_6_2 : tbl10 (6 : Fin 7) (2 : Fin 7) = some ((85 / 27 : ℚ), true) := rfl
theorem tbl10_c_6_3 : tbl10 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl10_c_6_4 : tbl10 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl10_c_6_5 : tbl10 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl10_c_6_6 : tbl10 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 11 (internal, depth 6, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl11 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl11_c_0_0 : tbl11 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_0_1 : tbl11 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl11_c_0_2 : tbl11 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl11_c_0_3 : tbl11 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl11_c_0_4 : tbl11 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl11_c_0_5 : tbl11 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl11_c_0_6 : tbl11 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl11_c_1_0 : tbl11 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl11_c_1_1 : tbl11 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_1_2 : tbl11 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl11_c_1_3 : tbl11 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl11_c_1_4 : tbl11 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl11_c_1_5 : tbl11 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl11_c_1_6 : tbl11 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl11_c_2_0 : tbl11 (2 : Fin 7) (0 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl11_c_2_1 : tbl11 (2 : Fin 7) (1 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl11_c_2_2 : tbl11 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_2_3 : tbl11 (2 : Fin 7) (3 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl11_c_2_4 : tbl11 (2 : Fin 7) (4 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl11_c_2_5 : tbl11 (2 : Fin 7) (5 : Fin 7) = some ((15 / 31 : ℚ), true) := rfl
theorem tbl11_c_2_6 : tbl11 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl11_c_3_0 : tbl11 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_1 : tbl11 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl11_c_3_2 : tbl11 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl11_c_3_3 : tbl11 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_3_4 : tbl11 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl11_c_3_5 : tbl11 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl11_c_3_6 : tbl11 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl11_c_4_0 : tbl11 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl11_c_4_1 : tbl11 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl11_c_4_2 : tbl11 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl11_c_4_3 : tbl11 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl11_c_4_4 : tbl11 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_4_5 : tbl11 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl11_c_4_6 : tbl11 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl11_c_5_0 : tbl11 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl11_c_5_1 : tbl11 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl11_c_5_2 : tbl11 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl11_c_5_3 : tbl11 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl11_c_5_4 : tbl11 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl11_c_5_5 : tbl11 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl11_c_5_6 : tbl11 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl11_c_6_0 : tbl11 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl11_c_6_1 : tbl11 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl11_c_6_2 : tbl11 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), true) := rfl
theorem tbl11_c_6_3 : tbl11 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl11_c_6_4 : tbl11 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl11_c_6_5 : tbl11 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl11_c_6_6 : tbl11 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 12 (deadend, depth 7, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl12 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl12_c_0_0 : tbl12 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_0_1 : tbl12 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl12_c_0_2 : tbl12 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl12_c_0_3 : tbl12 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl12_c_0_4 : tbl12 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl12_c_0_5 : tbl12 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl12_c_0_6 : tbl12 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl12_c_1_0 : tbl12 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl12_c_1_1 : tbl12 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_1_2 : tbl12 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl12_c_1_3 : tbl12 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl12_c_1_4 : tbl12 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl12_c_1_5 : tbl12 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl12_c_1_6 : tbl12 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl12_c_2_0 : tbl12 (2 : Fin 7) (0 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl12_c_2_1 : tbl12 (2 : Fin 7) (1 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl12_c_2_2 : tbl12 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_2_3 : tbl12 (2 : Fin 7) (3 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl12_c_2_4 : tbl12 (2 : Fin 7) (4 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl12_c_2_5 : tbl12 (2 : Fin 7) (5 : Fin 7) = some ((15 / 31 : ℚ), true) := rfl
theorem tbl12_c_2_6 : tbl12 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl12_c_3_0 : tbl12 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl12_c_3_1 : tbl12 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl12_c_3_2 : tbl12 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl12_c_3_3 : tbl12 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_3_4 : tbl12 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl12_c_3_5 : tbl12 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl12_c_3_6 : tbl12 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl12_c_4_0 : tbl12 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl12_c_4_1 : tbl12 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl12_c_4_2 : tbl12 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl12_c_4_3 : tbl12 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl12_c_4_4 : tbl12 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_4_5 : tbl12 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl12_c_4_6 : tbl12 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl12_c_5_0 : tbl12 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl12_c_5_1 : tbl12 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl12_c_5_2 : tbl12 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl12_c_5_3 : tbl12 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl12_c_5_4 : tbl12 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl12_c_5_5 : tbl12 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl12_c_5_6 : tbl12 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl12_c_6_0 : tbl12 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl12_c_6_1 : tbl12 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl12_c_6_2 : tbl12 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), true) := rfl
theorem tbl12_c_6_3 : tbl12 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl12_c_6_4 : tbl12 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl12_c_6_5 : tbl12 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tbl12_c_6_6 : tbl12 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 13 (internal, depth 5, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl13 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2187 / 5635 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl13_c_0_0 : tbl13 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_0_1 : tbl13 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl13_c_0_2 : tbl13 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl13_c_0_3 : tbl13 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl13_c_0_4 : tbl13 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl13_c_0_5 : tbl13 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl13_c_0_6 : tbl13 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl13_c_1_0 : tbl13 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl13_c_1_1 : tbl13 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_1_2 : tbl13 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl13_c_1_3 : tbl13 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl13_c_1_4 : tbl13 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl13_c_1_5 : tbl13 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl13_c_1_6 : tbl13 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl13_c_2_0 : tbl13 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl13_c_2_1 : tbl13 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl13_c_2_2 : tbl13 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_2_3 : tbl13 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tbl13_c_2_4 : tbl13 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl13_c_2_5 : tbl13 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl13_c_2_6 : tbl13 (2 : Fin 7) (6 : Fin 7) = some ((2187 / 5635 : ℚ), true) := rfl
theorem tbl13_c_3_0 : tbl13 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl13_c_3_1 : tbl13 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl13_c_3_2 : tbl13 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl13_c_3_3 : tbl13 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_3_4 : tbl13 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl13_c_3_5 : tbl13 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl13_c_3_6 : tbl13 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl13_c_4_0 : tbl13 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl13_c_4_1 : tbl13 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl13_c_4_2 : tbl13 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl13_c_4_3 : tbl13 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl13_c_4_4 : tbl13 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_4_5 : tbl13 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl13_c_4_6 : tbl13 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl13_c_5_0 : tbl13 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl13_c_5_1 : tbl13 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl13_c_5_2 : tbl13 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl13_c_5_3 : tbl13 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl13_c_5_4 : tbl13 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl13_c_5_5 : tbl13 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl13_c_5_6 : tbl13 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl13_c_6_0 : tbl13 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl13_c_6_1 : tbl13 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl13_c_6_2 : tbl13 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl13_c_6_3 : tbl13 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl13_c_6_4 : tbl13 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl13_c_6_5 : tbl13 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl13_c_6_6 : tbl13 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 14 (internal, depth 6, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl14 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((164025 / 38318 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((164025 / 38318 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 833 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 119 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((6561 / 19159 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl14_c_0_0 : tbl14 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_0_1 : tbl14 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl14_c_0_2 : tbl14 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl14_c_0_3 : tbl14 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl14_c_0_4 : tbl14 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl14_c_0_5 : tbl14 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl14_c_0_6 : tbl14 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl14_c_1_0 : tbl14 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl14_c_1_1 : tbl14 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_1_2 : tbl14 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl14_c_1_3 : tbl14 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl14_c_1_4 : tbl14 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl14_c_1_5 : tbl14 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl14_c_1_6 : tbl14 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl14_c_2_0 : tbl14 (2 : Fin 7) (0 : Fin 7) = some ((164025 / 38318 : ℚ), true) := rfl
theorem tbl14_c_2_1 : tbl14 (2 : Fin 7) (1 : Fin 7) = some ((164025 / 38318 : ℚ), true) := rfl
theorem tbl14_c_2_2 : tbl14 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_2_3 : tbl14 (2 : Fin 7) (3 : Fin 7) = some ((729 / 833 : ℚ), true) := rfl
theorem tbl14_c_2_4 : tbl14 (2 : Fin 7) (4 : Fin 7) = some ((81 / 119 : ℚ), true) := rfl
theorem tbl14_c_2_5 : tbl14 (2 : Fin 7) (5 : Fin 7) = some ((9 / 17 : ℚ), true) := rfl
theorem tbl14_c_2_6 : tbl14 (2 : Fin 7) (6 : Fin 7) = some ((6561 / 19159 : ℚ), true) := rfl
theorem tbl14_c_3_0 : tbl14 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl14_c_3_1 : tbl14 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl14_c_3_2 : tbl14 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl14_c_3_3 : tbl14 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_3_4 : tbl14 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl14_c_3_5 : tbl14 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl14_c_3_6 : tbl14 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl14_c_4_0 : tbl14 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl14_c_4_1 : tbl14 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl14_c_4_2 : tbl14 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl14_c_4_3 : tbl14 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl14_c_4_4 : tbl14 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_4_5 : tbl14 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl14_c_4_6 : tbl14 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl14_c_5_0 : tbl14 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl14_c_5_1 : tbl14 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl14_c_5_2 : tbl14 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl14_c_5_3 : tbl14 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl14_c_5_4 : tbl14 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl14_c_5_5 : tbl14 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl14_c_5_6 : tbl14 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl14_c_6_0 : tbl14 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl14_c_6_1 : tbl14 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl14_c_6_2 : tbl14 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl14_c_6_3 : tbl14 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl14_c_6_4 : tbl14 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl14_c_6_5 : tbl14 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl14_c_6_6 : tbl14 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 15 (deadend, depth 7, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl15 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((1215 / 322 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((1215 / 322 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 805 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl15_c_0_0 : tbl15 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_0_1 : tbl15 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl15_c_0_2 : tbl15 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl15_c_0_3 : tbl15 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl15_c_0_4 : tbl15 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl15_c_0_5 : tbl15 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl15_c_0_6 : tbl15 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tbl15_c_1_0 : tbl15 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl15_c_1_1 : tbl15 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_1_2 : tbl15 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl15_c_1_3 : tbl15 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl15_c_1_4 : tbl15 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl15_c_1_5 : tbl15 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl15_c_1_6 : tbl15 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tbl15_c_2_0 : tbl15 (2 : Fin 7) (0 : Fin 7) = some ((1215 / 322 : ℚ), true) := rfl
theorem tbl15_c_2_1 : tbl15 (2 : Fin 7) (1 : Fin 7) = some ((1215 / 322 : ℚ), true) := rfl
theorem tbl15_c_2_2 : tbl15 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_2_3 : tbl15 (2 : Fin 7) (3 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl15_c_2_4 : tbl15 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl15_c_2_5 : tbl15 (2 : Fin 7) (5 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl15_c_2_6 : tbl15 (2 : Fin 7) (6 : Fin 7) = some ((243 / 805 : ℚ), true) := rfl
theorem tbl15_c_3_0 : tbl15 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl15_c_3_1 : tbl15 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl15_c_3_2 : tbl15 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl15_c_3_3 : tbl15 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_3_4 : tbl15 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl15_c_3_5 : tbl15 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl15_c_3_6 : tbl15 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl15_c_4_0 : tbl15 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl15_c_4_1 : tbl15 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl15_c_4_2 : tbl15 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl15_c_4_3 : tbl15 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl15_c_4_4 : tbl15 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_4_5 : tbl15 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl15_c_4_6 : tbl15 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl15_c_5_0 : tbl15 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl15_c_5_1 : tbl15 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl15_c_5_2 : tbl15 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl15_c_5_3 : tbl15 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl15_c_5_4 : tbl15 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl15_c_5_5 : tbl15 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl15_c_5_6 : tbl15 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl15_c_6_0 : tbl15 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl15_c_6_1 : tbl15 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl15_c_6_2 : tbl15 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl15_c_6_3 : tbl15 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl15_c_6_4 : tbl15 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl15_c_6_5 : tbl15 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl15_c_6_6 : tbl15 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 16 (internal, depth 7, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl16 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl16_c_0_0 : tbl16 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_0_1 : tbl16 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl16_c_0_2 : tbl16 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl16_c_0_3 : tbl16 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl16_c_0_4 : tbl16 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl16_c_0_5 : tbl16 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl16_c_0_6 : tbl16 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl16_c_1_0 : tbl16 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl16_c_1_1 : tbl16 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_1_2 : tbl16 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl16_c_1_3 : tbl16 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl16_c_1_4 : tbl16 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl16_c_1_5 : tbl16 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl16_c_1_6 : tbl16 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl16_c_2_0 : tbl16 (2 : Fin 7) (0 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl16_c_2_1 : tbl16 (2 : Fin 7) (1 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl16_c_2_2 : tbl16 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_2_3 : tbl16 (2 : Fin 7) (3 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl16_c_2_4 : tbl16 (2 : Fin 7) (4 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl16_c_2_5 : tbl16 (2 : Fin 7) (5 : Fin 7) = some ((15 / 31 : ℚ), true) := rfl
theorem tbl16_c_2_6 : tbl16 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl16_c_3_0 : tbl16 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl16_c_3_1 : tbl16 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl16_c_3_2 : tbl16 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl16_c_3_3 : tbl16 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_3_4 : tbl16 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl16_c_3_5 : tbl16 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl16_c_3_6 : tbl16 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl16_c_4_0 : tbl16 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl16_c_4_1 : tbl16 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl16_c_4_2 : tbl16 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl16_c_4_3 : tbl16 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl16_c_4_4 : tbl16 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_4_5 : tbl16 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl16_c_4_6 : tbl16 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl16_c_5_0 : tbl16 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl16_c_5_1 : tbl16 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl16_c_5_2 : tbl16 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl16_c_5_3 : tbl16 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl16_c_5_4 : tbl16 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl16_c_5_5 : tbl16 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl16_c_5_6 : tbl16 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl16_c_6_0 : tbl16 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl16_c_6_1 : tbl16 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl16_c_6_2 : tbl16 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl16_c_6_3 : tbl16 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl16_c_6_4 : tbl16 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl16_c_6_5 : tbl16 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl16_c_6_6 : tbl16 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 17 (deadend, depth 8, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl17 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 62 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1215 / 1519 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 31 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl17_c_0_0 : tbl17 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_0_1 : tbl17 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl17_c_0_2 : tbl17 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl17_c_0_3 : tbl17 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tbl17_c_0_4 : tbl17 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tbl17_c_0_5 : tbl17 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl17_c_0_6 : tbl17 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl17_c_1_0 : tbl17 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl17_c_1_1 : tbl17 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_1_2 : tbl17 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl17_c_1_3 : tbl17 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tbl17_c_1_4 : tbl17 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tbl17_c_1_5 : tbl17 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl17_c_1_6 : tbl17 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl17_c_2_0 : tbl17 (2 : Fin 7) (0 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl17_c_2_1 : tbl17 (2 : Fin 7) (1 : Fin 7) = some ((225 / 62 : ℚ), true) := rfl
theorem tbl17_c_2_2 : tbl17 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_2_3 : tbl17 (2 : Fin 7) (3 : Fin 7) = some ((1215 / 1519 : ℚ), true) := rfl
theorem tbl17_c_2_4 : tbl17 (2 : Fin 7) (4 : Fin 7) = some ((135 / 217 : ℚ), true) := rfl
theorem tbl17_c_2_5 : tbl17 (2 : Fin 7) (5 : Fin 7) = some ((15 / 31 : ℚ), true) := rfl
theorem tbl17_c_2_6 : tbl17 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl17_c_3_0 : tbl17 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl17_c_3_1 : tbl17 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tbl17_c_3_2 : tbl17 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tbl17_c_3_3 : tbl17 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_3_4 : tbl17 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl17_c_3_5 : tbl17 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tbl17_c_3_6 : tbl17 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl17_c_4_0 : tbl17 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl17_c_4_1 : tbl17 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tbl17_c_4_2 : tbl17 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tbl17_c_4_3 : tbl17 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl17_c_4_4 : tbl17 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_4_5 : tbl17 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tbl17_c_4_6 : tbl17 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tbl17_c_5_0 : tbl17 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl17_c_5_1 : tbl17 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tbl17_c_5_2 : tbl17 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tbl17_c_5_3 : tbl17 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tbl17_c_5_4 : tbl17 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl17_c_5_5 : tbl17 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl17_c_5_6 : tbl17 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tbl17_c_6_0 : tbl17 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tbl17_c_6_1 : tbl17 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tbl17_c_6_2 : tbl17 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), false) := rfl
theorem tbl17_c_6_3 : tbl17 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tbl17_c_6_4 : tbl17 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl17_c_6_5 : tbl17 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl17_c_6_6 : tbl17 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 18 (internal, depth 3, last reading row 6, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl18 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 9 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 / 3 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 9 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((221 / 63 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 81 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl18_c_0_0 : tbl18 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_0_1 : tbl18 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl18_c_0_2 : tbl18 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl18_c_0_3 : tbl18 (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), false) := rfl
theorem tbl18_c_0_4 : tbl18 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tbl18_c_0_5 : tbl18 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl18_c_0_6 : tbl18 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl18_c_1_0 : tbl18 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl18_c_1_1 : tbl18 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_1_2 : tbl18 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl18_c_1_3 : tbl18 (1 : Fin 7) (3 : Fin 7) = some ((1 / 3 : ℚ), false) := rfl
theorem tbl18_c_1_4 : tbl18 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tbl18_c_1_5 : tbl18 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl18_c_1_6 : tbl18 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl18_c_2_0 : tbl18 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl18_c_2_1 : tbl18 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl18_c_2_2 : tbl18 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_2_3 : tbl18 (2 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl18_c_2_4 : tbl18 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl18_c_2_5 : tbl18 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl18_c_2_6 : tbl18 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl18_c_3_0 : tbl18 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl18_c_3_1 : tbl18 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl18_c_3_2 : tbl18 (3 : Fin 7) (2 : Fin 7) = some ((11 / 7 : ℚ), false) := rfl
theorem tbl18_c_3_3 : tbl18 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_3_4 : tbl18 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tbl18_c_3_5 : tbl18 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl18_c_3_6 : tbl18 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl18_c_4_0 : tbl18 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl18_c_4_1 : tbl18 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl18_c_4_2 : tbl18 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl18_c_4_3 : tbl18 (4 : Fin 7) (3 : Fin 7) = some ((13 / 9 : ℚ), false) := rfl
theorem tbl18_c_4_4 : tbl18 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_4_5 : tbl18 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl18_c_4_6 : tbl18 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl18_c_5_0 : tbl18 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl18_c_5_1 : tbl18 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl18_c_5_2 : tbl18 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl18_c_5_3 : tbl18 (5 : Fin 7) (3 : Fin 7) = some ((13 / 7 : ℚ), true) := rfl
theorem tbl18_c_5_4 : tbl18 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl18_c_5_5 : tbl18 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl18_c_5_6 : tbl18 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl18_c_6_0 : tbl18 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl18_c_6_1 : tbl18 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl18_c_6_2 : tbl18 (6 : Fin 7) (2 : Fin 7) = some ((221 / 63 : ℚ), true) := rfl
theorem tbl18_c_6_3 : tbl18 (6 : Fin 7) (3 : Fin 7) = some ((221 / 81 : ℚ), true) := rfl
theorem tbl18_c_6_4 : tbl18 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl18_c_6_5 : tbl18 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl18_c_6_6 : tbl18 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 19 (internal, depth 4, last reading row 3, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl19 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((11 / 7 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((221 / 63 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl19_c_0_0 : tbl19 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_0_1 : tbl19 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl19_c_0_2 : tbl19 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl19_c_0_3 : tbl19 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl19_c_0_4 : tbl19 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tbl19_c_0_5 : tbl19 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl19_c_0_6 : tbl19 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl19_c_1_0 : tbl19 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl19_c_1_1 : tbl19 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_1_2 : tbl19 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl19_c_1_3 : tbl19 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl19_c_1_4 : tbl19 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tbl19_c_1_5 : tbl19 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl19_c_1_6 : tbl19 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl19_c_2_0 : tbl19 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl19_c_2_1 : tbl19 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl19_c_2_2 : tbl19 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_2_3 : tbl19 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl19_c_2_4 : tbl19 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl19_c_2_5 : tbl19 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl19_c_2_6 : tbl19 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl19_c_3_0 : tbl19 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl19_c_3_1 : tbl19 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl19_c_3_2 : tbl19 (3 : Fin 7) (2 : Fin 7) = some ((11 / 7 : ℚ), false) := rfl
theorem tbl19_c_3_3 : tbl19 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_3_4 : tbl19 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tbl19_c_3_5 : tbl19 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl19_c_3_6 : tbl19 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl19_c_4_0 : tbl19 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl19_c_4_1 : tbl19 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl19_c_4_2 : tbl19 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl19_c_4_3 : tbl19 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl19_c_4_4 : tbl19 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_4_5 : tbl19 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl19_c_4_6 : tbl19 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl19_c_5_0 : tbl19 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl19_c_5_1 : tbl19 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl19_c_5_2 : tbl19 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl19_c_5_3 : tbl19 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl19_c_5_4 : tbl19 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl19_c_5_5 : tbl19 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl19_c_5_6 : tbl19 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl19_c_6_0 : tbl19 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl19_c_6_1 : tbl19 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl19_c_6_2 : tbl19 (6 : Fin 7) (2 : Fin 7) = some ((221 / 63 : ℚ), true) := rfl
theorem tbl19_c_6_3 : tbl19 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl19_c_6_4 : tbl19 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl19_c_6_5 : tbl19 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl19_c_6_6 : tbl19 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 20 (internal, depth 5, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl20 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17901 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl20_c_0_0 : tbl20 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_0_1 : tbl20 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl20_c_0_2 : tbl20 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tbl20_c_0_3 : tbl20 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl20_c_0_4 : tbl20 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tbl20_c_0_5 : tbl20 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl20_c_0_6 : tbl20 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl20_c_1_0 : tbl20 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl20_c_1_1 : tbl20 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_1_2 : tbl20 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tbl20_c_1_3 : tbl20 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl20_c_1_4 : tbl20 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tbl20_c_1_5 : tbl20 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl20_c_1_6 : tbl20 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl20_c_2_0 : tbl20 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl20_c_2_1 : tbl20 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl20_c_2_2 : tbl20 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_2_3 : tbl20 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl20_c_2_4 : tbl20 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl20_c_2_5 : tbl20 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl20_c_2_6 : tbl20 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl20_c_3_0 : tbl20 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl20_c_3_1 : tbl20 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl20_c_3_2 : tbl20 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl20_c_3_3 : tbl20 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_3_4 : tbl20 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tbl20_c_3_5 : tbl20 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl20_c_3_6 : tbl20 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl20_c_4_0 : tbl20 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl20_c_4_1 : tbl20 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl20_c_4_2 : tbl20 (4 : Fin 7) (2 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl20_c_4_3 : tbl20 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl20_c_4_4 : tbl20 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_4_5 : tbl20 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl20_c_4_6 : tbl20 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl20_c_5_0 : tbl20 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl20_c_5_1 : tbl20 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl20_c_5_2 : tbl20 (5 : Fin 7) (2 : Fin 7) = some ((17901 / 7889 : ℚ), true) := rfl
theorem tbl20_c_5_3 : tbl20 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl20_c_5_4 : tbl20 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl20_c_5_5 : tbl20 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl20_c_5_6 : tbl20 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl20_c_6_0 : tbl20 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl20_c_6_1 : tbl20 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl20_c_6_2 : tbl20 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tbl20_c_6_3 : tbl20 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl20_c_6_4 : tbl20 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl20_c_6_5 : tbl20 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl20_c_6_6 : tbl20 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 21 (internal, depth 6, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl21 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((39 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((117 / 175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17901 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((1989 / 1225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl21_c_0_0 : tbl21 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_0_1 : tbl21 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl21_c_0_2 : tbl21 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tbl21_c_0_3 : tbl21 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl21_c_0_4 : tbl21 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl21_c_0_5 : tbl21 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl21_c_0_6 : tbl21 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl21_c_1_0 : tbl21 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl21_c_1_1 : tbl21 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_1_2 : tbl21 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tbl21_c_1_3 : tbl21 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl21_c_1_4 : tbl21 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl21_c_1_5 : tbl21 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl21_c_1_6 : tbl21 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl21_c_2_0 : tbl21 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl21_c_2_1 : tbl21 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl21_c_2_2 : tbl21 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_2_3 : tbl21 (2 : Fin 7) (3 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl21_c_2_4 : tbl21 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl21_c_2_5 : tbl21 (2 : Fin 7) (5 : Fin 7) = some ((13 / 25 : ℚ), true) := rfl
theorem tbl21_c_2_6 : tbl21 (2 : Fin 7) (6 : Fin 7) = some ((39 / 115 : ℚ), true) := rfl
theorem tbl21_c_3_0 : tbl21 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl21_c_3_1 : tbl21 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl21_c_3_2 : tbl21 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl21_c_3_3 : tbl21 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_3_4 : tbl21 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl21_c_3_5 : tbl21 (3 : Fin 7) (5 : Fin 7) = some ((117 / 175 : ℚ), true) := rfl
theorem tbl21_c_3_6 : tbl21 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl21_c_4_0 : tbl21 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl21_c_4_1 : tbl21 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl21_c_4_2 : tbl21 (4 : Fin 7) (2 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl21_c_4_3 : tbl21 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl21_c_4_4 : tbl21 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_4_5 : tbl21 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl21_c_4_6 : tbl21 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl21_c_5_0 : tbl21 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl21_c_5_1 : tbl21 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl21_c_5_2 : tbl21 (5 : Fin 7) (2 : Fin 7) = some ((17901 / 7889 : ℚ), true) := rfl
theorem tbl21_c_5_3 : tbl21 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl21_c_5_4 : tbl21 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl21_c_5_5 : tbl21 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl21_c_5_6 : tbl21 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl21_c_6_0 : tbl21 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl21_c_6_1 : tbl21 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl21_c_6_2 : tbl21 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tbl21_c_6_3 : tbl21 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl21_c_6_4 : tbl21 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl21_c_6_5 : tbl21 (6 : Fin 7) (5 : Fin 7) = some ((1989 / 1225 : ℚ), true) := rfl
theorem tbl21_c_6_6 : tbl21 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 22 (internal, depth 7, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl22 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 25 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((117 / 175 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((23409 / 10633 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((1989 / 1225 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl22_c_0_0 : tbl22 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_0_1 : tbl22 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl22_c_0_2 : tbl22 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tbl22_c_0_3 : tbl22 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl22_c_0_4 : tbl22 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl22_c_0_5 : tbl22 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl22_c_0_6 : tbl22 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl22_c_1_0 : tbl22 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl22_c_1_1 : tbl22 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_1_2 : tbl22 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tbl22_c_1_3 : tbl22 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl22_c_1_4 : tbl22 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl22_c_1_5 : tbl22 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl22_c_1_6 : tbl22 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl22_c_2_0 : tbl22 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl22_c_2_1 : tbl22 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl22_c_2_2 : tbl22 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_2_3 : tbl22 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl22_c_2_4 : tbl22 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl22_c_2_5 : tbl22 (2 : Fin 7) (5 : Fin 7) = some ((13 / 25 : ℚ), true) := rfl
theorem tbl22_c_2_6 : tbl22 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl22_c_3_0 : tbl22 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl22_c_3_1 : tbl22 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl22_c_3_2 : tbl22 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl22_c_3_3 : tbl22 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_3_4 : tbl22 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl22_c_3_5 : tbl22 (3 : Fin 7) (5 : Fin 7) = some ((117 / 175 : ℚ), true) := rfl
theorem tbl22_c_3_6 : tbl22 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl22_c_4_0 : tbl22 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl22_c_4_1 : tbl22 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl22_c_4_2 : tbl22 (4 : Fin 7) (2 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl22_c_4_3 : tbl22 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl22_c_4_4 : tbl22 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_4_5 : tbl22 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl22_c_4_6 : tbl22 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl22_c_5_0 : tbl22 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl22_c_5_1 : tbl22 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl22_c_5_2 : tbl22 (5 : Fin 7) (2 : Fin 7) = some ((23409 / 10633 : ℚ), true) := rfl
theorem tbl22_c_5_3 : tbl22 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl22_c_5_4 : tbl22 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl22_c_5_5 : tbl22 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl22_c_5_6 : tbl22 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl22_c_6_0 : tbl22 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl22_c_6_1 : tbl22 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl22_c_6_2 : tbl22 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tbl22_c_6_3 : tbl22 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl22_c_6_4 : tbl22 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl22_c_6_5 : tbl22 (6 : Fin 7) (5 : Fin 7) = some ((1989 / 1225 : ℚ), true) := rfl
theorem tbl22_c_6_6 : tbl22 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 23 (internal, depth 8, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl23 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((594 / 3703 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((66 / 529 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((891 / 3703 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((99 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15147 / 24955 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((23409 / 10633 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl23_c_0_0 : tbl23 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_0_1 : tbl23 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl23_c_0_2 : tbl23 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tbl23_c_0_3 : tbl23 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl23_c_0_4 : tbl23 (0 : Fin 7) (4 : Fin 7) = some ((594 / 3703 : ℚ), true) := rfl
theorem tbl23_c_0_5 : tbl23 (0 : Fin 7) (5 : Fin 7) = some ((66 / 529 : ℚ), true) := rfl
theorem tbl23_c_0_6 : tbl23 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl23_c_1_0 : tbl23 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl23_c_1_1 : tbl23 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_1_2 : tbl23 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tbl23_c_1_3 : tbl23 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl23_c_1_4 : tbl23 (1 : Fin 7) (4 : Fin 7) = some ((891 / 3703 : ℚ), true) := rfl
theorem tbl23_c_1_5 : tbl23 (1 : Fin 7) (5 : Fin 7) = some ((99 / 529 : ℚ), true) := rfl
theorem tbl23_c_1_6 : tbl23 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl23_c_2_0 : tbl23 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl23_c_2_1 : tbl23 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl23_c_2_2 : tbl23 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_2_3 : tbl23 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl23_c_2_4 : tbl23 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl23_c_2_5 : tbl23 (2 : Fin 7) (5 : Fin 7) = some ((1683 / 3565 : ℚ), true) := rfl
theorem tbl23_c_2_6 : tbl23 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl23_c_3_0 : tbl23 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl23_c_3_1 : tbl23 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl23_c_3_2 : tbl23 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl23_c_3_3 : tbl23 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_3_4 : tbl23 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl23_c_3_5 : tbl23 (3 : Fin 7) (5 : Fin 7) = some ((15147 / 24955 : ℚ), true) := rfl
theorem tbl23_c_3_6 : tbl23 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl23_c_4_0 : tbl23 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl23_c_4_1 : tbl23 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl23_c_4_2 : tbl23 (4 : Fin 7) (2 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl23_c_4_3 : tbl23 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl23_c_4_4 : tbl23 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_4_5 : tbl23 (4 : Fin 7) (5 : Fin 7) = some ((561 / 713 : ℚ), true) := rfl
theorem tbl23_c_4_6 : tbl23 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl23_c_5_0 : tbl23 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl23_c_5_1 : tbl23 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl23_c_5_2 : tbl23 (5 : Fin 7) (2 : Fin 7) = some ((23409 / 10633 : ℚ), true) := rfl
theorem tbl23_c_5_3 : tbl23 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl23_c_5_4 : tbl23 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl23_c_5_5 : tbl23 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl23_c_5_6 : tbl23 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl23_c_6_0 : tbl23 (6 : Fin 7) (0 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl23_c_6_1 : tbl23 (6 : Fin 7) (1 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl23_c_6_2 : tbl23 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tbl23_c_6_3 : tbl23 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl23_c_6_4 : tbl23 (6 : Fin 7) (4 : Fin 7) = some ((297 / 161 : ℚ), true) := rfl
theorem tbl23_c_6_5 : tbl23 (6 : Fin 7) (5 : Fin 7) = some ((33 / 23 : ℚ), true) := rfl
theorem tbl23_c_6_6 : tbl23 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 24 (reach, depth 9, last reading row 3, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl24 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((990 / 3703 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((110 / 529 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((594 / 3703 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((66 / 529 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1485 / 3703 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((165 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((891 / 3703 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((99 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15147 / 24955 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((8415 / 4991 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((935 / 713 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((5 / 3 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((495 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((55 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl24_c_0_0 : tbl24 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_0_1 : tbl24 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl24_c_0_2 : tbl24 (0 : Fin 7) (2 : Fin 7) = some ((990 / 3703 : ℚ), true) := rfl
theorem tbl24_c_0_3 : tbl24 (0 : Fin 7) (3 : Fin 7) = some ((110 / 529 : ℚ), true) := rfl
theorem tbl24_c_0_4 : tbl24 (0 : Fin 7) (4 : Fin 7) = some ((594 / 3703 : ℚ), true) := rfl
theorem tbl24_c_0_5 : tbl24 (0 : Fin 7) (5 : Fin 7) = some ((66 / 529 : ℚ), true) := rfl
theorem tbl24_c_0_6 : tbl24 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl24_c_1_0 : tbl24 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl24_c_1_1 : tbl24 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_1_2 : tbl24 (1 : Fin 7) (2 : Fin 7) = some ((1485 / 3703 : ℚ), true) := rfl
theorem tbl24_c_1_3 : tbl24 (1 : Fin 7) (3 : Fin 7) = some ((165 / 529 : ℚ), true) := rfl
theorem tbl24_c_1_4 : tbl24 (1 : Fin 7) (4 : Fin 7) = some ((891 / 3703 : ℚ), true) := rfl
theorem tbl24_c_1_5 : tbl24 (1 : Fin 7) (5 : Fin 7) = some ((99 / 529 : ℚ), true) := rfl
theorem tbl24_c_1_6 : tbl24 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl24_c_2_0 : tbl24 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl24_c_2_1 : tbl24 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl24_c_2_2 : tbl24 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_2_3 : tbl24 (2 : Fin 7) (3 : Fin 7) = some ((561 / 713 : ℚ), true) := rfl
theorem tbl24_c_2_4 : tbl24 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl24_c_2_5 : tbl24 (2 : Fin 7) (5 : Fin 7) = some ((1683 / 3565 : ℚ), true) := rfl
theorem tbl24_c_2_6 : tbl24 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl24_c_3_0 : tbl24 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl24_c_3_1 : tbl24 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl24_c_3_2 : tbl24 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl24_c_3_3 : tbl24 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_3_4 : tbl24 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl24_c_3_5 : tbl24 (3 : Fin 7) (5 : Fin 7) = some ((15147 / 24955 : ℚ), true) := rfl
theorem tbl24_c_3_6 : tbl24 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl24_c_4_0 : tbl24 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl24_c_4_1 : tbl24 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl24_c_4_2 : tbl24 (4 : Fin 7) (2 : Fin 7) = some ((8415 / 4991 : ℚ), true) := rfl
theorem tbl24_c_4_3 : tbl24 (4 : Fin 7) (3 : Fin 7) = some ((935 / 713 : ℚ), true) := rfl
theorem tbl24_c_4_4 : tbl24 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_4_5 : tbl24 (4 : Fin 7) (5 : Fin 7) = some ((561 / 713 : ℚ), true) := rfl
theorem tbl24_c_4_6 : tbl24 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl24_c_5_0 : tbl24 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl24_c_5_1 : tbl24 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl24_c_5_2 : tbl24 (5 : Fin 7) (2 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tbl24_c_5_3 : tbl24 (5 : Fin 7) (3 : Fin 7) = some ((5 / 3 : ℚ), true) := rfl
theorem tbl24_c_5_4 : tbl24 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl24_c_5_5 : tbl24 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl24_c_5_6 : tbl24 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl24_c_6_0 : tbl24 (6 : Fin 7) (0 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl24_c_6_1 : tbl24 (6 : Fin 7) (1 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl24_c_6_2 : tbl24 (6 : Fin 7) (2 : Fin 7) = some ((495 / 161 : ℚ), true) := rfl
theorem tbl24_c_6_3 : tbl24 (6 : Fin 7) (3 : Fin 7) = some ((55 / 23 : ℚ), true) := rfl
theorem tbl24_c_6_4 : tbl24 (6 : Fin 7) (4 : Fin 7) = some ((297 / 161 : ℚ), true) := rfl
theorem tbl24_c_6_5 : tbl24 (6 : Fin 7) (5 : Fin 7) = some ((33 / 23 : ℚ), true) := rfl
theorem tbl24_c_6_6 : tbl24 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 25 (reach, depth 6, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl25 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((34 / 135 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 45 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3757 / 1215 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl25_c_0_0 : tbl25 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_0_1 : tbl25 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl25_c_0_2 : tbl25 (0 : Fin 7) (2 : Fin 7) = some ((34 / 135 : ℚ), true) := rfl
theorem tbl25_c_0_3 : tbl25 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl25_c_0_4 : tbl25 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tbl25_c_0_5 : tbl25 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl25_c_0_6 : tbl25 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl25_c_1_0 : tbl25 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl25_c_1_1 : tbl25 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_1_2 : tbl25 (1 : Fin 7) (2 : Fin 7) = some ((17 / 45 : ℚ), true) := rfl
theorem tbl25_c_1_3 : tbl25 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl25_c_1_4 : tbl25 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tbl25_c_1_5 : tbl25 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl25_c_1_6 : tbl25 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl25_c_2_0 : tbl25 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl25_c_2_1 : tbl25 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl25_c_2_2 : tbl25 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_2_3 : tbl25 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl25_c_2_4 : tbl25 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl25_c_2_5 : tbl25 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl25_c_2_6 : tbl25 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl25_c_3_0 : tbl25 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl25_c_3_1 : tbl25 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl25_c_3_2 : tbl25 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl25_c_3_3 : tbl25 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_3_4 : tbl25 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tbl25_c_3_5 : tbl25 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl25_c_3_6 : tbl25 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl25_c_4_0 : tbl25 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl25_c_4_1 : tbl25 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl25_c_4_2 : tbl25 (4 : Fin 7) (2 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl25_c_4_3 : tbl25 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl25_c_4_4 : tbl25 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_4_5 : tbl25 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl25_c_4_6 : tbl25 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl25_c_5_0 : tbl25 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl25_c_5_1 : tbl25 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl25_c_5_2 : tbl25 (5 : Fin 7) (2 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl25_c_5_3 : tbl25 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl25_c_5_4 : tbl25 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl25_c_5_5 : tbl25 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl25_c_5_6 : tbl25 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl25_c_6_0 : tbl25 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl25_c_6_1 : tbl25 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl25_c_6_2 : tbl25 (6 : Fin 7) (2 : Fin 7) = some ((3757 / 1215 : ℚ), true) := rfl
theorem tbl25_c_6_3 : tbl25 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl25_c_6_4 : tbl25 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl25_c_6_5 : tbl25 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl25_c_6_6 : tbl25 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 26 (reach, depth 6, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl26 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((50 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl26_c_0_0 : tbl26 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_0_1 : tbl26 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl26_c_0_2 : tbl26 (0 : Fin 7) (2 : Fin 7) = some ((50 / 207 : ℚ), true) := rfl
theorem tbl26_c_0_3 : tbl26 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl26_c_0_4 : tbl26 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tbl26_c_0_5 : tbl26 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tbl26_c_0_6 : tbl26 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl26_c_1_0 : tbl26 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl26_c_1_1 : tbl26 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_1_2 : tbl26 (1 : Fin 7) (2 : Fin 7) = some ((25 / 69 : ℚ), true) := rfl
theorem tbl26_c_1_3 : tbl26 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl26_c_1_4 : tbl26 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tbl26_c_1_5 : tbl26 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tbl26_c_1_6 : tbl26 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl26_c_2_0 : tbl26 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl26_c_2_1 : tbl26 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl26_c_2_2 : tbl26 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_2_3 : tbl26 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl26_c_2_4 : tbl26 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tbl26_c_2_5 : tbl26 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tbl26_c_2_6 : tbl26 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tbl26_c_3_0 : tbl26 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tbl26_c_3_1 : tbl26 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tbl26_c_3_2 : tbl26 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl26_c_3_3 : tbl26 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_3_4 : tbl26 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tbl26_c_3_5 : tbl26 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tbl26_c_3_6 : tbl26 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tbl26_c_4_0 : tbl26 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl26_c_4_1 : tbl26 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl26_c_4_2 : tbl26 (4 : Fin 7) (2 : Fin 7) = some ((325 / 207 : ℚ), true) := rfl
theorem tbl26_c_4_3 : tbl26 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl26_c_4_4 : tbl26 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_4_5 : tbl26 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tbl26_c_4_6 : tbl26 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl26_c_5_0 : tbl26 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl26_c_5_1 : tbl26 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl26_c_5_2 : tbl26 (5 : Fin 7) (2 : Fin 7) = some ((325 / 161 : ℚ), true) := rfl
theorem tbl26_c_5_3 : tbl26 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl26_c_5_4 : tbl26 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl26_c_5_5 : tbl26 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl26_c_5_6 : tbl26 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl26_c_6_0 : tbl26 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl26_c_6_1 : tbl26 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tbl26_c_6_2 : tbl26 (6 : Fin 7) (2 : Fin 7) = some ((25 / 9 : ℚ), true) := rfl
theorem tbl26_c_6_3 : tbl26 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl26_c_6_4 : tbl26 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tbl26_c_6_5 : tbl26 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tbl26_c_6_6 : tbl26 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 27 (internal, depth 5, last reading row 5, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl27 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4131 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 805 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl27_c_0_0 : tbl27 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_0_1 : tbl27 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl27_c_0_2 : tbl27 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl27_c_0_3 : tbl27 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl27_c_0_4 : tbl27 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl27_c_0_5 : tbl27 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl27_c_0_6 : tbl27 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl27_c_1_0 : tbl27 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl27_c_1_1 : tbl27 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_1_2 : tbl27 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl27_c_1_3 : tbl27 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl27_c_1_4 : tbl27 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl27_c_1_5 : tbl27 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl27_c_1_6 : tbl27 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl27_c_2_0 : tbl27 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl27_c_2_1 : tbl27 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl27_c_2_2 : tbl27 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_2_3 : tbl27 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl27_c_2_4 : tbl27 (2 : Fin 7) (4 : Fin 7) = some ((4131 / 5635 : ℚ), true) := rfl
theorem tbl27_c_2_5 : tbl27 (2 : Fin 7) (5 : Fin 7) = some ((459 / 805 : ℚ), true) := rfl
theorem tbl27_c_2_6 : tbl27 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl27_c_3_0 : tbl27 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl27_c_3_1 : tbl27 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl27_c_3_2 : tbl27 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl27_c_3_3 : tbl27 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_3_4 : tbl27 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl27_c_3_5 : tbl27 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl27_c_3_6 : tbl27 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl27_c_4_0 : tbl27 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl27_c_4_1 : tbl27 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl27_c_4_2 : tbl27 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl27_c_4_3 : tbl27 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl27_c_4_4 : tbl27 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_4_5 : tbl27 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl27_c_4_6 : tbl27 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl27_c_5_0 : tbl27 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl27_c_5_1 : tbl27 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl27_c_5_2 : tbl27 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl27_c_5_3 : tbl27 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl27_c_5_4 : tbl27 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl27_c_5_5 : tbl27 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl27_c_5_6 : tbl27 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl27_c_6_0 : tbl27 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl27_c_6_1 : tbl27 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl27_c_6_2 : tbl27 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl27_c_6_3 : tbl27 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl27_c_6_4 : tbl27 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl27_c_6_5 : tbl27 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl27_c_6_6 : tbl27 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 28 (internal, depth 6, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl28 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((1053 / 238 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((1053 / 238 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1053 / 1127 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 119 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1053 / 2737 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl28_c_0_0 : tbl28 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_0_1 : tbl28 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl28_c_0_2 : tbl28 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl28_c_0_3 : tbl28 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl28_c_0_4 : tbl28 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl28_c_0_5 : tbl28 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl28_c_0_6 : tbl28 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl28_c_1_0 : tbl28 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl28_c_1_1 : tbl28 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_1_2 : tbl28 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl28_c_1_3 : tbl28 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl28_c_1_4 : tbl28 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl28_c_1_5 : tbl28 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl28_c_1_6 : tbl28 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl28_c_2_0 : tbl28 (2 : Fin 7) (0 : Fin 7) = some ((1053 / 238 : ℚ), true) := rfl
theorem tbl28_c_2_1 : tbl28 (2 : Fin 7) (1 : Fin 7) = some ((1053 / 238 : ℚ), true) := rfl
theorem tbl28_c_2_2 : tbl28 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_2_3 : tbl28 (2 : Fin 7) (3 : Fin 7) = some ((1053 / 1127 : ℚ), true) := rfl
theorem tbl28_c_2_4 : tbl28 (2 : Fin 7) (4 : Fin 7) = some ((81 / 119 : ℚ), true) := rfl
theorem tbl28_c_2_5 : tbl28 (2 : Fin 7) (5 : Fin 7) = some ((9 / 17 : ℚ), true) := rfl
theorem tbl28_c_2_6 : tbl28 (2 : Fin 7) (6 : Fin 7) = some ((1053 / 2737 : ℚ), true) := rfl
theorem tbl28_c_3_0 : tbl28 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl28_c_3_1 : tbl28 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl28_c_3_2 : tbl28 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl28_c_3_3 : tbl28 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_3_4 : tbl28 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl28_c_3_5 : tbl28 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl28_c_3_6 : tbl28 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl28_c_4_0 : tbl28 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl28_c_4_1 : tbl28 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl28_c_4_2 : tbl28 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl28_c_4_3 : tbl28 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl28_c_4_4 : tbl28 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_4_5 : tbl28 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl28_c_4_6 : tbl28 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl28_c_5_0 : tbl28 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl28_c_5_1 : tbl28 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl28_c_5_2 : tbl28 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl28_c_5_3 : tbl28 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl28_c_5_4 : tbl28 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl28_c_5_5 : tbl28 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl28_c_5_6 : tbl28 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl28_c_6_0 : tbl28 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl28_c_6_1 : tbl28 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl28_c_6_2 : tbl28 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl28_c_6_3 : tbl28 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl28_c_6_4 : tbl28 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl28_c_6_5 : tbl28 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl28_c_6_6 : tbl28 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 29 (internal, depth 7, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl29 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1989 / 4025 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((39 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl29_c_0_0 : tbl29 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_0_1 : tbl29 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl29_c_0_2 : tbl29 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl29_c_0_3 : tbl29 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl29_c_0_4 : tbl29 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl29_c_0_5 : tbl29 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl29_c_0_6 : tbl29 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl29_c_1_0 : tbl29 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl29_c_1_1 : tbl29 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_1_2 : tbl29 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl29_c_1_3 : tbl29 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl29_c_1_4 : tbl29 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl29_c_1_5 : tbl29 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl29_c_1_6 : tbl29 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl29_c_2_0 : tbl29 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl29_c_2_1 : tbl29 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl29_c_2_2 : tbl29 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_2_3 : tbl29 (2 : Fin 7) (3 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl29_c_2_4 : tbl29 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl29_c_2_5 : tbl29 (2 : Fin 7) (5 : Fin 7) = some ((1989 / 4025 : ℚ), true) := rfl
theorem tbl29_c_2_6 : tbl29 (2 : Fin 7) (6 : Fin 7) = some ((39 / 115 : ℚ), true) := rfl
theorem tbl29_c_3_0 : tbl29 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl29_c_3_1 : tbl29 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl29_c_3_2 : tbl29 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl29_c_3_3 : tbl29 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_3_4 : tbl29 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl29_c_3_5 : tbl29 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl29_c_3_6 : tbl29 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl29_c_4_0 : tbl29 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl29_c_4_1 : tbl29 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl29_c_4_2 : tbl29 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl29_c_4_3 : tbl29 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl29_c_4_4 : tbl29 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_4_5 : tbl29 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl29_c_4_6 : tbl29 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl29_c_5_0 : tbl29 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl29_c_5_1 : tbl29 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl29_c_5_2 : tbl29 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl29_c_5_3 : tbl29 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl29_c_5_4 : tbl29 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl29_c_5_5 : tbl29 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl29_c_5_6 : tbl29 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl29_c_6_0 : tbl29 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl29_c_6_1 : tbl29 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl29_c_6_2 : tbl29 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl29_c_6_3 : tbl29 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl29_c_6_4 : tbl29 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl29_c_6_5 : tbl29 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl29_c_6_6 : tbl29 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 30 (internal, depth 8, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl30 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 5425 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl30_c_0_0 : tbl30 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_0_1 : tbl30 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl30_c_0_2 : tbl30 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl30_c_0_3 : tbl30 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl30_c_0_4 : tbl30 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl30_c_0_5 : tbl30 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl30_c_0_6 : tbl30 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl30_c_1_0 : tbl30 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl30_c_1_1 : tbl30 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_1_2 : tbl30 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl30_c_1_3 : tbl30 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl30_c_1_4 : tbl30 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl30_c_1_5 : tbl30 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl30_c_1_6 : tbl30 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl30_c_2_0 : tbl30 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl30_c_2_1 : tbl30 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl30_c_2_2 : tbl30 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_2_3 : tbl30 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl30_c_2_4 : tbl30 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl30_c_2_5 : tbl30 (2 : Fin 7) (5 : Fin 7) = some ((2601 / 5425 : ℚ), true) := rfl
theorem tbl30_c_2_6 : tbl30 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl30_c_3_0 : tbl30 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl30_c_3_1 : tbl30 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl30_c_3_2 : tbl30 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl30_c_3_3 : tbl30 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_3_4 : tbl30 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl30_c_3_5 : tbl30 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl30_c_3_6 : tbl30 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl30_c_4_0 : tbl30 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl30_c_4_1 : tbl30 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl30_c_4_2 : tbl30 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl30_c_4_3 : tbl30 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl30_c_4_4 : tbl30 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_4_5 : tbl30 (4 : Fin 7) (5 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl30_c_4_6 : tbl30 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl30_c_5_0 : tbl30 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl30_c_5_1 : tbl30 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl30_c_5_2 : tbl30 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl30_c_5_3 : tbl30 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl30_c_5_4 : tbl30 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl30_c_5_5 : tbl30 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl30_c_5_6 : tbl30 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl30_c_6_0 : tbl30 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl30_c_6_1 : tbl30 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl30_c_6_2 : tbl30 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl30_c_6_3 : tbl30 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl30_c_6_4 : tbl30 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl30_c_6_5 : tbl30 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl30_c_6_6 : tbl30 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 31 (deadend, depth 9, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl31 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((594 / 3703 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((66 / 529 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((891 / 3703 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((99 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3861 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl31_c_0_0 : tbl31 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_0_1 : tbl31 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl31_c_0_2 : tbl31 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl31_c_0_3 : tbl31 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl31_c_0_4 : tbl31 (0 : Fin 7) (4 : Fin 7) = some ((594 / 3703 : ℚ), true) := rfl
theorem tbl31_c_0_5 : tbl31 (0 : Fin 7) (5 : Fin 7) = some ((66 / 529 : ℚ), true) := rfl
theorem tbl31_c_0_6 : tbl31 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl31_c_1_0 : tbl31 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl31_c_1_1 : tbl31 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_1_2 : tbl31 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl31_c_1_3 : tbl31 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl31_c_1_4 : tbl31 (1 : Fin 7) (4 : Fin 7) = some ((891 / 3703 : ℚ), true) := rfl
theorem tbl31_c_1_5 : tbl31 (1 : Fin 7) (5 : Fin 7) = some ((99 / 529 : ℚ), true) := rfl
theorem tbl31_c_1_6 : tbl31 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl31_c_2_0 : tbl31 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl31_c_2_1 : tbl31 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl31_c_2_2 : tbl31 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_2_3 : tbl31 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl31_c_2_4 : tbl31 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl31_c_2_5 : tbl31 (2 : Fin 7) (5 : Fin 7) = some ((1683 / 3565 : ℚ), true) := rfl
theorem tbl31_c_2_6 : tbl31 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl31_c_3_0 : tbl31 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl31_c_3_1 : tbl31 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl31_c_3_2 : tbl31 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl31_c_3_3 : tbl31 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_3_4 : tbl31 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl31_c_3_5 : tbl31 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl31_c_3_6 : tbl31 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl31_c_4_0 : tbl31 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl31_c_4_1 : tbl31 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl31_c_4_2 : tbl31 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl31_c_4_3 : tbl31 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl31_c_4_4 : tbl31 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_4_5 : tbl31 (4 : Fin 7) (5 : Fin 7) = some ((561 / 713 : ℚ), true) := rfl
theorem tbl31_c_4_6 : tbl31 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl31_c_5_0 : tbl31 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl31_c_5_1 : tbl31 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl31_c_5_2 : tbl31 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl31_c_5_3 : tbl31 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl31_c_5_4 : tbl31 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl31_c_5_5 : tbl31 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl31_c_5_6 : tbl31 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl31_c_6_0 : tbl31 (6 : Fin 7) (0 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl31_c_6_1 : tbl31 (6 : Fin 7) (1 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl31_c_6_2 : tbl31 (6 : Fin 7) (2 : Fin 7) = some ((3861 / 1127 : ℚ), true) := rfl
theorem tbl31_c_6_3 : tbl31 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl31_c_6_4 : tbl31 (6 : Fin 7) (4 : Fin 7) = some ((297 / 161 : ℚ), true) := rfl
theorem tbl31_c_6_5 : tbl31 (6 : Fin 7) (5 : Fin 7) = some ((33 / 23 : ℚ), true) := rfl
theorem tbl31_c_6_6 : tbl31 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 32 (reach, depth 7, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl32 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((50 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((1053 / 238 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((1053 / 238 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1053 / 1127 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 119 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 17 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1053 / 2737 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((195 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 207 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((325 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl32_c_0_0 : tbl32 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_0_1 : tbl32 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl32_c_0_2 : tbl32 (0 : Fin 7) (2 : Fin 7) = some ((50 / 207 : ℚ), true) := rfl
theorem tbl32_c_0_3 : tbl32 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl32_c_0_4 : tbl32 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl32_c_0_5 : tbl32 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl32_c_0_6 : tbl32 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl32_c_1_0 : tbl32 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl32_c_1_1 : tbl32 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_1_2 : tbl32 (1 : Fin 7) (2 : Fin 7) = some ((25 / 69 : ℚ), true) := rfl
theorem tbl32_c_1_3 : tbl32 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl32_c_1_4 : tbl32 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl32_c_1_5 : tbl32 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl32_c_1_6 : tbl32 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl32_c_2_0 : tbl32 (2 : Fin 7) (0 : Fin 7) = some ((1053 / 238 : ℚ), true) := rfl
theorem tbl32_c_2_1 : tbl32 (2 : Fin 7) (1 : Fin 7) = some ((1053 / 238 : ℚ), true) := rfl
theorem tbl32_c_2_2 : tbl32 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_2_3 : tbl32 (2 : Fin 7) (3 : Fin 7) = some ((1053 / 1127 : ℚ), true) := rfl
theorem tbl32_c_2_4 : tbl32 (2 : Fin 7) (4 : Fin 7) = some ((81 / 119 : ℚ), true) := rfl
theorem tbl32_c_2_5 : tbl32 (2 : Fin 7) (5 : Fin 7) = some ((9 / 17 : ℚ), true) := rfl
theorem tbl32_c_2_6 : tbl32 (2 : Fin 7) (6 : Fin 7) = some ((1053 / 2737 : ℚ), true) := rfl
theorem tbl32_c_3_0 : tbl32 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl32_c_3_1 : tbl32 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl32_c_3_2 : tbl32 (3 : Fin 7) (2 : Fin 7) = some ((195 / 161 : ℚ), true) := rfl
theorem tbl32_c_3_3 : tbl32 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_3_4 : tbl32 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl32_c_3_5 : tbl32 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl32_c_3_6 : tbl32 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl32_c_4_0 : tbl32 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl32_c_4_1 : tbl32 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl32_c_4_2 : tbl32 (4 : Fin 7) (2 : Fin 7) = some ((325 / 207 : ℚ), true) := rfl
theorem tbl32_c_4_3 : tbl32 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl32_c_4_4 : tbl32 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_4_5 : tbl32 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl32_c_4_6 : tbl32 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl32_c_5_0 : tbl32 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl32_c_5_1 : tbl32 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl32_c_5_2 : tbl32 (5 : Fin 7) (2 : Fin 7) = some ((325 / 161 : ℚ), true) := rfl
theorem tbl32_c_5_3 : tbl32 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl32_c_5_4 : tbl32 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl32_c_5_5 : tbl32 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl32_c_5_6 : tbl32 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl32_c_6_0 : tbl32 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl32_c_6_1 : tbl32 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl32_c_6_2 : tbl32 (6 : Fin 7) (2 : Fin 7) = some ((25 / 9 : ℚ), true) := rfl
theorem tbl32_c_6_3 : tbl32 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl32_c_6_4 : tbl32 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl32_c_6_5 : tbl32 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl32_c_6_6 : tbl32 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 33 (reach, depth 7, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl33 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((306 / 1519 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((8262 / 53165 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((918 / 7595 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((459 / 1519 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((12393 / 53165 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1377 / 7595 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((53703 / 15190 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((53703 / 15190 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4131 / 7595 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((3159 / 7595 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1519 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((5967 / 7595 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17901 / 10633 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1053 / 1519 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl33_c_0_0 : tbl33 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_0_1 : tbl33 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl33_c_0_2 : tbl33 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl33_c_0_3 : tbl33 (0 : Fin 7) (3 : Fin 7) = some ((306 / 1519 : ℚ), true) := rfl
theorem tbl33_c_0_4 : tbl33 (0 : Fin 7) (4 : Fin 7) = some ((8262 / 53165 : ℚ), true) := rfl
theorem tbl33_c_0_5 : tbl33 (0 : Fin 7) (5 : Fin 7) = some ((918 / 7595 : ℚ), true) := rfl
theorem tbl33_c_0_6 : tbl33 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl33_c_1_0 : tbl33 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl33_c_1_1 : tbl33 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_1_2 : tbl33 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl33_c_1_3 : tbl33 (1 : Fin 7) (3 : Fin 7) = some ((459 / 1519 : ℚ), true) := rfl
theorem tbl33_c_1_4 : tbl33 (1 : Fin 7) (4 : Fin 7) = some ((12393 / 53165 : ℚ), true) := rfl
theorem tbl33_c_1_5 : tbl33 (1 : Fin 7) (5 : Fin 7) = some ((1377 / 7595 : ℚ), true) := rfl
theorem tbl33_c_1_6 : tbl33 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl33_c_2_0 : tbl33 (2 : Fin 7) (0 : Fin 7) = some ((53703 / 15190 : ℚ), true) := rfl
theorem tbl33_c_2_1 : tbl33 (2 : Fin 7) (1 : Fin 7) = some ((53703 / 15190 : ℚ), true) := rfl
theorem tbl33_c_2_2 : tbl33 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_2_3 : tbl33 (2 : Fin 7) (3 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl33_c_2_4 : tbl33 (2 : Fin 7) (4 : Fin 7) = some ((4131 / 7595 : ℚ), true) := rfl
theorem tbl33_c_2_5 : tbl33 (2 : Fin 7) (5 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl33_c_2_6 : tbl33 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl33_c_3_0 : tbl33 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl33_c_3_1 : tbl33 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl33_c_3_2 : tbl33 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl33_c_3_3 : tbl33 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_3_4 : tbl33 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl33_c_3_5 : tbl33 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl33_c_3_6 : tbl33 (3 : Fin 7) (6 : Fin 7) = some ((3159 / 7595 : ℚ), true) := rfl
theorem tbl33_c_4_0 : tbl33 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl33_c_4_1 : tbl33 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl33_c_4_2 : tbl33 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl33_c_4_3 : tbl33 (4 : Fin 7) (3 : Fin 7) = some ((1989 / 1519 : ℚ), true) := rfl
theorem tbl33_c_4_4 : tbl33 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_4_5 : tbl33 (4 : Fin 7) (5 : Fin 7) = some ((5967 / 7595 : ℚ), true) := rfl
theorem tbl33_c_4_6 : tbl33 (4 : Fin 7) (6 : Fin 7) = some ((117 / 217 : ℚ), true) := rfl
theorem tbl33_c_5_0 : tbl33 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl33_c_5_1 : tbl33 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl33_c_5_2 : tbl33 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl33_c_5_3 : tbl33 (5 : Fin 7) (3 : Fin 7) = some ((17901 / 10633 : ℚ), true) := rfl
theorem tbl33_c_5_4 : tbl33 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl33_c_5_5 : tbl33 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl33_c_5_6 : tbl33 (5 : Fin 7) (6 : Fin 7) = some ((1053 / 1519 : ℚ), true) := rfl
theorem tbl33_c_6_0 : tbl33 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl33_c_6_1 : tbl33 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl33_c_6_2 : tbl33 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl33_c_6_3 : tbl33 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl33_c_6_4 : tbl33 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl33_c_6_5 : tbl33 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl33_c_6_6 : tbl33 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 34 (internal, depth 6, last reading row 6, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl34 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4131 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 805 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl34_c_0_0 : tbl34 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_0_1 : tbl34 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl34_c_0_2 : tbl34 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl34_c_0_3 : tbl34 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl34_c_0_4 : tbl34 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl34_c_0_5 : tbl34 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl34_c_0_6 : tbl34 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl34_c_1_0 : tbl34 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl34_c_1_1 : tbl34 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_1_2 : tbl34 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl34_c_1_3 : tbl34 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl34_c_1_4 : tbl34 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl34_c_1_5 : tbl34 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl34_c_1_6 : tbl34 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl34_c_2_0 : tbl34 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl34_c_2_1 : tbl34 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl34_c_2_2 : tbl34 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_2_3 : tbl34 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tbl34_c_2_4 : tbl34 (2 : Fin 7) (4 : Fin 7) = some ((4131 / 5635 : ℚ), true) := rfl
theorem tbl34_c_2_5 : tbl34 (2 : Fin 7) (5 : Fin 7) = some ((459 / 805 : ℚ), true) := rfl
theorem tbl34_c_2_6 : tbl34 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tbl34_c_3_0 : tbl34 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl34_c_3_1 : tbl34 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl34_c_3_2 : tbl34 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl34_c_3_3 : tbl34 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_3_4 : tbl34 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl34_c_3_5 : tbl34 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl34_c_3_6 : tbl34 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl34_c_4_0 : tbl34 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl34_c_4_1 : tbl34 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl34_c_4_2 : tbl34 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl34_c_4_3 : tbl34 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl34_c_4_4 : tbl34 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_4_5 : tbl34 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl34_c_4_6 : tbl34 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl34_c_5_0 : tbl34 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl34_c_5_1 : tbl34 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl34_c_5_2 : tbl34 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl34_c_5_3 : tbl34 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl34_c_5_4 : tbl34 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl34_c_5_5 : tbl34 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl34_c_5_6 : tbl34 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl34_c_6_0 : tbl34 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl34_c_6_1 : tbl34 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl34_c_6_2 : tbl34 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl34_c_6_3 : tbl34 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl34_c_6_4 : tbl34 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl34_c_6_5 : tbl34 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl34_c_6_6 : tbl34 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 35 (internal, depth 7, last reading row 2, exit numerator 9).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl35 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((53703 / 12250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((53703 / 12250 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4131 / 6125 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 875 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 25 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl35_c_0_0 : tbl35 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_0_1 : tbl35 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl35_c_0_2 : tbl35 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl35_c_0_3 : tbl35 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl35_c_0_4 : tbl35 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl35_c_0_5 : tbl35 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl35_c_0_6 : tbl35 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl35_c_1_0 : tbl35 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl35_c_1_1 : tbl35 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_1_2 : tbl35 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl35_c_1_3 : tbl35 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl35_c_1_4 : tbl35 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl35_c_1_5 : tbl35 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl35_c_1_6 : tbl35 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl35_c_2_0 : tbl35 (2 : Fin 7) (0 : Fin 7) = some ((53703 / 12250 : ℚ), true) := rfl
theorem tbl35_c_2_1 : tbl35 (2 : Fin 7) (1 : Fin 7) = some ((53703 / 12250 : ℚ), true) := rfl
theorem tbl35_c_2_2 : tbl35 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_2_3 : tbl35 (2 : Fin 7) (3 : Fin 7) = some ((153 / 175 : ℚ), true) := rfl
theorem tbl35_c_2_4 : tbl35 (2 : Fin 7) (4 : Fin 7) = some ((4131 / 6125 : ℚ), true) := rfl
theorem tbl35_c_2_5 : tbl35 (2 : Fin 7) (5 : Fin 7) = some ((459 / 875 : ℚ), true) := rfl
theorem tbl35_c_2_6 : tbl35 (2 : Fin 7) (6 : Fin 7) = some ((9 / 25 : ℚ), true) := rfl
theorem tbl35_c_3_0 : tbl35 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl35_c_3_1 : tbl35 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl35_c_3_2 : tbl35 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl35_c_3_3 : tbl35 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_3_4 : tbl35 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl35_c_3_5 : tbl35 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl35_c_3_6 : tbl35 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl35_c_4_0 : tbl35 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl35_c_4_1 : tbl35 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl35_c_4_2 : tbl35 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl35_c_4_3 : tbl35 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl35_c_4_4 : tbl35 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_4_5 : tbl35 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl35_c_4_6 : tbl35 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl35_c_5_0 : tbl35 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl35_c_5_1 : tbl35 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl35_c_5_2 : tbl35 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl35_c_5_3 : tbl35 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl35_c_5_4 : tbl35 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl35_c_5_5 : tbl35 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl35_c_5_6 : tbl35 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl35_c_6_0 : tbl35 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl35_c_6_1 : tbl35 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl35_c_6_2 : tbl35 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl35_c_6_3 : tbl35 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl35_c_6_4 : tbl35 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl35_c_6_5 : tbl35 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl35_c_6_6 : tbl35 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 36 (internal, depth 8, last reading row 4, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl36 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1989 / 4025 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((39 / 115 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((351 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((663 / 805 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl36_c_0_0 : tbl36 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_0_1 : tbl36 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl36_c_0_2 : tbl36 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl36_c_0_3 : tbl36 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl36_c_0_4 : tbl36 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl36_c_0_5 : tbl36 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl36_c_0_6 : tbl36 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl36_c_1_0 : tbl36 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl36_c_1_1 : tbl36 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_1_2 : tbl36 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl36_c_1_3 : tbl36 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl36_c_1_4 : tbl36 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl36_c_1_5 : tbl36 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl36_c_1_6 : tbl36 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl36_c_2_0 : tbl36 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl36_c_2_1 : tbl36 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl36_c_2_2 : tbl36 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_2_3 : tbl36 (2 : Fin 7) (3 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl36_c_2_4 : tbl36 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl36_c_2_5 : tbl36 (2 : Fin 7) (5 : Fin 7) = some ((1989 / 4025 : ℚ), true) := rfl
theorem tbl36_c_2_6 : tbl36 (2 : Fin 7) (6 : Fin 7) = some ((39 / 115 : ℚ), true) := rfl
theorem tbl36_c_3_0 : tbl36 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl36_c_3_1 : tbl36 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl36_c_3_2 : tbl36 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl36_c_3_3 : tbl36 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_3_4 : tbl36 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl36_c_3_5 : tbl36 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl36_c_3_6 : tbl36 (3 : Fin 7) (6 : Fin 7) = some ((351 / 805 : ℚ), true) := rfl
theorem tbl36_c_4_0 : tbl36 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl36_c_4_1 : tbl36 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl36_c_4_2 : tbl36 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl36_c_4_3 : tbl36 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tbl36_c_4_4 : tbl36 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_4_5 : tbl36 (4 : Fin 7) (5 : Fin 7) = some ((663 / 805 : ℚ), true) := rfl
theorem tbl36_c_4_6 : tbl36 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tbl36_c_5_0 : tbl36 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl36_c_5_1 : tbl36 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl36_c_5_2 : tbl36 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl36_c_5_3 : tbl36 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tbl36_c_5_4 : tbl36 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl36_c_5_5 : tbl36 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl36_c_5_6 : tbl36 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tbl36_c_6_0 : tbl36 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl36_c_6_1 : tbl36 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl36_c_6_2 : tbl36 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl36_c_6_3 : tbl36 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl36_c_6_4 : tbl36 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl36_c_6_5 : tbl36 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl36_c_6_6 : tbl36 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 37 (internal, depth 9, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl37 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((918 / 5635 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((102 / 805 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 805 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 5425 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl37_c_0_0 : tbl37 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_0_1 : tbl37 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl37_c_0_2 : tbl37 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl37_c_0_3 : tbl37 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl37_c_0_4 : tbl37 (0 : Fin 7) (4 : Fin 7) = some ((918 / 5635 : ℚ), true) := rfl
theorem tbl37_c_0_5 : tbl37 (0 : Fin 7) (5 : Fin 7) = some ((102 / 805 : ℚ), true) := rfl
theorem tbl37_c_0_6 : tbl37 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl37_c_1_0 : tbl37 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl37_c_1_1 : tbl37 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_1_2 : tbl37 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl37_c_1_3 : tbl37 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl37_c_1_4 : tbl37 (1 : Fin 7) (4 : Fin 7) = some ((1377 / 5635 : ℚ), true) := rfl
theorem tbl37_c_1_5 : tbl37 (1 : Fin 7) (5 : Fin 7) = some ((153 / 805 : ℚ), true) := rfl
theorem tbl37_c_1_6 : tbl37 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl37_c_2_0 : tbl37 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl37_c_2_1 : tbl37 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl37_c_2_2 : tbl37 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_2_3 : tbl37 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl37_c_2_4 : tbl37 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl37_c_2_5 : tbl37 (2 : Fin 7) (5 : Fin 7) = some ((2601 / 5425 : ℚ), true) := rfl
theorem tbl37_c_2_6 : tbl37 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl37_c_3_0 : tbl37 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl37_c_3_1 : tbl37 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl37_c_3_2 : tbl37 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl37_c_3_3 : tbl37 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_3_4 : tbl37 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl37_c_3_5 : tbl37 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl37_c_3_6 : tbl37 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl37_c_4_0 : tbl37 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl37_c_4_1 : tbl37 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl37_c_4_2 : tbl37 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl37_c_4_3 : tbl37 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl37_c_4_4 : tbl37 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_4_5 : tbl37 (4 : Fin 7) (5 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl37_c_4_6 : tbl37 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl37_c_5_0 : tbl37 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl37_c_5_1 : tbl37 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl37_c_5_2 : tbl37 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl37_c_5_3 : tbl37 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl37_c_5_4 : tbl37 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl37_c_5_5 : tbl37 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl37_c_5_6 : tbl37 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl37_c_6_0 : tbl37 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl37_c_6_1 : tbl37 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl37_c_6_2 : tbl37 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl37_c_6_3 : tbl37 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl37_c_6_4 : tbl37 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl37_c_6_5 : tbl37 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl37_c_6_6 : tbl37 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 38 (deadend, depth 10, last reading row 5, exit numerator 25).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl38 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((594 / 3703 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((66 / 529 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((891 / 3703 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((99 / 529 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((39 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((1683 / 3565 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 155 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 217 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((561 / 713 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 31 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((2601 / 1519 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3861 / 322 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3861 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((297 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((33 / 23 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl38_c_0_0 : tbl38 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_0_1 : tbl38 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl38_c_0_2 : tbl38 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl38_c_0_3 : tbl38 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tbl38_c_0_4 : tbl38 (0 : Fin 7) (4 : Fin 7) = some ((594 / 3703 : ℚ), true) := rfl
theorem tbl38_c_0_5 : tbl38 (0 : Fin 7) (5 : Fin 7) = some ((66 / 529 : ℚ), true) := rfl
theorem tbl38_c_0_6 : tbl38 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tbl38_c_1_0 : tbl38 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl38_c_1_1 : tbl38 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_1_2 : tbl38 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl38_c_1_3 : tbl38 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tbl38_c_1_4 : tbl38 (1 : Fin 7) (4 : Fin 7) = some ((891 / 3703 : ℚ), true) := rfl
theorem tbl38_c_1_5 : tbl38 (1 : Fin 7) (5 : Fin 7) = some ((99 / 529 : ℚ), true) := rfl
theorem tbl38_c_1_6 : tbl38 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tbl38_c_2_0 : tbl38 (2 : Fin 7) (0 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl38_c_2_1 : tbl38 (2 : Fin 7) (1 : Fin 7) = some ((39 / 10 : ℚ), true) := rfl
theorem tbl38_c_2_2 : tbl38 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_2_3 : tbl38 (2 : Fin 7) (3 : Fin 7) = some ((867 / 1085 : ℚ), true) := rfl
theorem tbl38_c_2_4 : tbl38 (2 : Fin 7) (4 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl38_c_2_5 : tbl38 (2 : Fin 7) (5 : Fin 7) = some ((1683 / 3565 : ℚ), true) := rfl
theorem tbl38_c_2_6 : tbl38 (2 : Fin 7) (6 : Fin 7) = some ((51 / 155 : ℚ), true) := rfl
theorem tbl38_c_3_0 : tbl38 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl38_c_3_1 : tbl38 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl38_c_3_2 : tbl38 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl38_c_3_3 : tbl38 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_3_4 : tbl38 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl38_c_3_5 : tbl38 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl38_c_3_6 : tbl38 (3 : Fin 7) (6 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl38_c_4_0 : tbl38 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl38_c_4_1 : tbl38 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl38_c_4_2 : tbl38 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl38_c_4_3 : tbl38 (4 : Fin 7) (3 : Fin 7) = some ((289 / 217 : ℚ), true) := rfl
theorem tbl38_c_4_4 : tbl38 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_4_5 : tbl38 (4 : Fin 7) (5 : Fin 7) = some ((561 / 713 : ℚ), true) := rfl
theorem tbl38_c_4_6 : tbl38 (4 : Fin 7) (6 : Fin 7) = some ((17 / 31 : ℚ), true) := rfl
theorem tbl38_c_5_0 : tbl38 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl38_c_5_1 : tbl38 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl38_c_5_2 : tbl38 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl38_c_5_3 : tbl38 (5 : Fin 7) (3 : Fin 7) = some ((2601 / 1519 : ℚ), true) := rfl
theorem tbl38_c_5_4 : tbl38 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl38_c_5_5 : tbl38 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl38_c_5_6 : tbl38 (5 : Fin 7) (6 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl38_c_6_0 : tbl38 (6 : Fin 7) (0 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl38_c_6_1 : tbl38 (6 : Fin 7) (1 : Fin 7) = some ((3861 / 322 : ℚ), true) := rfl
theorem tbl38_c_6_2 : tbl38 (6 : Fin 7) (2 : Fin 7) = some ((3861 / 1127 : ℚ), true) := rfl
theorem tbl38_c_6_3 : tbl38 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl38_c_6_4 : tbl38 (6 : Fin 7) (4 : Fin 7) = some ((297 / 161 : ℚ), true) := rfl
theorem tbl38_c_6_5 : tbl38 (6 : Fin 7) (5 : Fin 7) = some ((33 / 23 : ℚ), true) := rfl
theorem tbl38_c_6_6 : tbl38 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Table of DFS node 39 (reach, depth 8, last reading row 6, exit numerator 33).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl39 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((306 / 1519 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((8262 / 53165 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((918 / 7595 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((18 / 217 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((459 / 1519 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((12393 / 53165 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1377 / 7595 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((53703 / 15190 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((53703 / 15190 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 217 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4131 / 7595 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 1085 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 31 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((351 / 70 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((351 / 245 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((3159 / 7595 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1519 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((5967 / 7595 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 217 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((117 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((17901 / 10633 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1053 / 1519 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((5967 / 490 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((5967 / 1715 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 245 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 35 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl39_c_0_0 : tbl39 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_0_1 : tbl39 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl39_c_0_2 : tbl39 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl39_c_0_3 : tbl39 (0 : Fin 7) (3 : Fin 7) = some ((306 / 1519 : ℚ), true) := rfl
theorem tbl39_c_0_4 : tbl39 (0 : Fin 7) (4 : Fin 7) = some ((8262 / 53165 : ℚ), true) := rfl
theorem tbl39_c_0_5 : tbl39 (0 : Fin 7) (5 : Fin 7) = some ((918 / 7595 : ℚ), true) := rfl
theorem tbl39_c_0_6 : tbl39 (0 : Fin 7) (6 : Fin 7) = some ((18 / 217 : ℚ), true) := rfl
theorem tbl39_c_1_0 : tbl39 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl39_c_1_1 : tbl39 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_1_2 : tbl39 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl39_c_1_3 : tbl39 (1 : Fin 7) (3 : Fin 7) = some ((459 / 1519 : ℚ), true) := rfl
theorem tbl39_c_1_4 : tbl39 (1 : Fin 7) (4 : Fin 7) = some ((12393 / 53165 : ℚ), true) := rfl
theorem tbl39_c_1_5 : tbl39 (1 : Fin 7) (5 : Fin 7) = some ((1377 / 7595 : ℚ), true) := rfl
theorem tbl39_c_1_6 : tbl39 (1 : Fin 7) (6 : Fin 7) = some ((27 / 217 : ℚ), true) := rfl
theorem tbl39_c_2_0 : tbl39 (2 : Fin 7) (0 : Fin 7) = some ((53703 / 15190 : ℚ), true) := rfl
theorem tbl39_c_2_1 : tbl39 (2 : Fin 7) (1 : Fin 7) = some ((53703 / 15190 : ℚ), true) := rfl
theorem tbl39_c_2_2 : tbl39 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_2_3 : tbl39 (2 : Fin 7) (3 : Fin 7) = some ((153 / 217 : ℚ), true) := rfl
theorem tbl39_c_2_4 : tbl39 (2 : Fin 7) (4 : Fin 7) = some ((4131 / 7595 : ℚ), true) := rfl
theorem tbl39_c_2_5 : tbl39 (2 : Fin 7) (5 : Fin 7) = some ((459 / 1085 : ℚ), true) := rfl
theorem tbl39_c_2_6 : tbl39 (2 : Fin 7) (6 : Fin 7) = some ((9 / 31 : ℚ), true) := rfl
theorem tbl39_c_3_0 : tbl39 (3 : Fin 7) (0 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl39_c_3_1 : tbl39 (3 : Fin 7) (1 : Fin 7) = some ((351 / 70 : ℚ), true) := rfl
theorem tbl39_c_3_2 : tbl39 (3 : Fin 7) (2 : Fin 7) = some ((351 / 245 : ℚ), true) := rfl
theorem tbl39_c_3_3 : tbl39 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_3_4 : tbl39 (3 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tbl39_c_3_5 : tbl39 (3 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tbl39_c_3_6 : tbl39 (3 : Fin 7) (6 : Fin 7) = some ((3159 / 7595 : ℚ), true) := rfl
theorem tbl39_c_4_0 : tbl39 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl39_c_4_1 : tbl39 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl39_c_4_2 : tbl39 (4 : Fin 7) (2 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl39_c_4_3 : tbl39 (4 : Fin 7) (3 : Fin 7) = some ((1989 / 1519 : ℚ), true) := rfl
theorem tbl39_c_4_4 : tbl39 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_4_5 : tbl39 (4 : Fin 7) (5 : Fin 7) = some ((5967 / 7595 : ℚ), true) := rfl
theorem tbl39_c_4_6 : tbl39 (4 : Fin 7) (6 : Fin 7) = some ((117 / 217 : ℚ), true) := rfl
theorem tbl39_c_5_0 : tbl39 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl39_c_5_1 : tbl39 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tbl39_c_5_2 : tbl39 (5 : Fin 7) (2 : Fin 7) = some ((117 / 49 : ℚ), true) := rfl
theorem tbl39_c_5_3 : tbl39 (5 : Fin 7) (3 : Fin 7) = some ((17901 / 10633 : ℚ), true) := rfl
theorem tbl39_c_5_4 : tbl39 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tbl39_c_5_5 : tbl39 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl39_c_5_6 : tbl39 (5 : Fin 7) (6 : Fin 7) = some ((1053 / 1519 : ℚ), true) := rfl
theorem tbl39_c_6_0 : tbl39 (6 : Fin 7) (0 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl39_c_6_1 : tbl39 (6 : Fin 7) (1 : Fin 7) = some ((5967 / 490 : ℚ), true) := rfl
theorem tbl39_c_6_2 : tbl39 (6 : Fin 7) (2 : Fin 7) = some ((5967 / 1715 : ℚ), true) := rfl
theorem tbl39_c_6_3 : tbl39 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tbl39_c_6_4 : tbl39 (6 : Fin 7) (4 : Fin 7) = some ((459 / 245 : ℚ), true) := rfl
theorem tbl39_c_6_5 : tbl39 (6 : Fin 7) (5 : Fin 7) = some ((51 / 35 : ℚ), true) := rfl
theorem tbl39_c_6_6 : tbl39 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 4's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS4 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((486 / 1715 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 1715 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS4_c_0_0 : tblS4 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_0_1 : tblS4 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS4_c_0_2 : tblS4 (0 : Fin 7) (2 : Fin 7) = some ((486 / 1715 : ℚ), true) := rfl
theorem tblS4_c_0_3 : tblS4 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tblS4_c_0_4 : tblS4 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tblS4_c_0_5 : tblS4 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tblS4_c_0_6 : tblS4 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tblS4_c_1_0 : tblS4 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS4_c_1_1 : tblS4 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_1_2 : tblS4 (1 : Fin 7) (2 : Fin 7) = some ((729 / 1715 : ℚ), true) := rfl
theorem tblS4_c_1_3 : tblS4 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tblS4_c_1_4 : tblS4 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tblS4_c_1_5 : tblS4 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tblS4_c_1_6 : tblS4 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tblS4_c_2_0 : tblS4 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tblS4_c_2_1 : tblS4 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tblS4_c_2_2 : tblS4 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_2_3 : tblS4 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tblS4_c_2_4 : tblS4 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tblS4_c_2_5 : tblS4 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblS4_c_2_6 : tblS4 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tblS4_c_3_0 : tblS4 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tblS4_c_3_1 : tblS4 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS4_c_3_2 : tblS4 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS4_c_3_3 : tblS4 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_3_4 : tblS4 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tblS4_c_3_5 : tblS4 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tblS4_c_3_6 : tblS4 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tblS4_c_4_0 : tblS4 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tblS4_c_4_1 : tblS4 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tblS4_c_4_2 : tblS4 (4 : Fin 7) (2 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tblS4_c_4_3 : tblS4 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS4_c_4_4 : tblS4 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_4_5 : tblS4 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tblS4_c_4_6 : tblS4 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tblS4_c_5_0 : tblS4 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS4_c_5_1 : tblS4 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS4_c_5_2 : tblS4 (5 : Fin 7) (2 : Fin 7) = some ((729 / 343 : ℚ), true) := rfl
theorem tblS4_c_5_3 : tblS4 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tblS4_c_5_4 : tblS4 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS4_c_5_5 : tblS4 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS4_c_5_6 : tblS4 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tblS4_c_6_0 : tblS4 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tblS4_c_6_1 : tblS4 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS4_c_6_2 : tblS4 (6 : Fin 7) (2 : Fin 7) = some ((1215 / 343 : ℚ), true) := rfl
theorem tblS4_c_6_3 : tblS4 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tblS4_c_6_4 : tblS4 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tblS4_c_6_5 : tblS4 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tblS4_c_6_6 : tblS4 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 5's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS5 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((486 / 1715 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 1715 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 35 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((1215 / 343 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS5_c_0_0 : tblS5 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_0_1 : tblS5 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS5_c_0_2 : tblS5 (0 : Fin 7) (2 : Fin 7) = some ((486 / 1715 : ℚ), true) := rfl
theorem tblS5_c_0_3 : tblS5 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tblS5_c_0_4 : tblS5 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tblS5_c_0_5 : tblS5 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tblS5_c_0_6 : tblS5 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tblS5_c_1_0 : tblS5 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS5_c_1_1 : tblS5 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_1_2 : tblS5 (1 : Fin 7) (2 : Fin 7) = some ((729 / 1715 : ℚ), true) := rfl
theorem tblS5_c_1_3 : tblS5 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tblS5_c_1_4 : tblS5 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tblS5_c_1_5 : tblS5 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tblS5_c_1_6 : tblS5 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tblS5_c_2_0 : tblS5 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tblS5_c_2_1 : tblS5 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tblS5_c_2_2 : tblS5 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_2_3 : tblS5 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tblS5_c_2_4 : tblS5 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tblS5_c_2_5 : tblS5 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tblS5_c_2_6 : tblS5 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tblS5_c_3_0 : tblS5 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tblS5_c_3_1 : tblS5 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS5_c_3_2 : tblS5 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS5_c_3_3 : tblS5 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_3_4 : tblS5 (3 : Fin 7) (4 : Fin 7) = some ((33 / 35 : ℚ), true) := rfl
theorem tblS5_c_3_5 : tblS5 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tblS5_c_3_6 : tblS5 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tblS5_c_4_0 : tblS5 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tblS5_c_4_1 : tblS5 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tblS5_c_4_2 : tblS5 (4 : Fin 7) (2 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tblS5_c_4_3 : tblS5 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS5_c_4_4 : tblS5 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_4_5 : tblS5 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tblS5_c_4_6 : tblS5 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tblS5_c_5_0 : tblS5 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS5_c_5_1 : tblS5 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS5_c_5_2 : tblS5 (5 : Fin 7) (2 : Fin 7) = some ((729 / 343 : ℚ), true) := rfl
theorem tblS5_c_5_3 : tblS5 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tblS5_c_5_4 : tblS5 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS5_c_5_5 : tblS5 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS5_c_5_6 : tblS5 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tblS5_c_6_0 : tblS5 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tblS5_c_6_1 : tblS5 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS5_c_6_2 : tblS5 (6 : Fin 7) (2 : Fin 7) = some ((1215 / 343 : ℚ), true) := rfl
theorem tblS5_c_6_3 : tblS5 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tblS5_c_6_4 : tblS5 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tblS5_c_6_5 : tblS5 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tblS5_c_6_6 : tblS5 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 8's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS8 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((54 / 245 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((6 / 35 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((486 / 5635 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 245 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 35 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 5635 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((2187 / 5635 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((225 / 46 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((225 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2025 / 322 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((2025 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((135 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 161 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((18225 / 2254 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((18225 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((729 / 1127 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((25 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((25 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((135 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((15 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((5 / 3 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS8_c_0_0 : tblS8 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_0_1 : tblS8 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS8_c_0_2 : tblS8 (0 : Fin 7) (2 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tblS8_c_0_3 : tblS8 (0 : Fin 7) (3 : Fin 7) = some ((54 / 245 : ℚ), true) := rfl
theorem tblS8_c_0_4 : tblS8 (0 : Fin 7) (4 : Fin 7) = some ((6 / 35 : ℚ), true) := rfl
theorem tblS8_c_0_5 : tblS8 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tblS8_c_0_6 : tblS8 (0 : Fin 7) (6 : Fin 7) = some ((486 / 5635 : ℚ), true) := rfl
theorem tblS8_c_1_0 : tblS8 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS8_c_1_1 : tblS8 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_1_2 : tblS8 (1 : Fin 7) (2 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tblS8_c_1_3 : tblS8 (1 : Fin 7) (3 : Fin 7) = some ((81 / 245 : ℚ), true) := rfl
theorem tblS8_c_1_4 : tblS8 (1 : Fin 7) (4 : Fin 7) = some ((9 / 35 : ℚ), true) := rfl
theorem tblS8_c_1_5 : tblS8 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tblS8_c_1_6 : tblS8 (1 : Fin 7) (6 : Fin 7) = some ((729 / 5635 : ℚ), true) := rfl
theorem tblS8_c_2_0 : tblS8 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tblS8_c_2_1 : tblS8 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tblS8_c_2_2 : tblS8 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_2_3 : tblS8 (2 : Fin 7) (3 : Fin 7) = some ((243 / 245 : ℚ), true) := rfl
theorem tblS8_c_2_4 : tblS8 (2 : Fin 7) (4 : Fin 7) = some ((27 / 35 : ℚ), true) := rfl
theorem tblS8_c_2_5 : tblS8 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tblS8_c_2_6 : tblS8 (2 : Fin 7) (6 : Fin 7) = some ((2187 / 5635 : ℚ), true) := rfl
theorem tblS8_c_3_0 : tblS8 (3 : Fin 7) (0 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tblS8_c_3_1 : tblS8 (3 : Fin 7) (1 : Fin 7) = some ((225 / 46 : ℚ), true) := rfl
theorem tblS8_c_3_2 : tblS8 (3 : Fin 7) (2 : Fin 7) = some ((225 / 161 : ℚ), true) := rfl
theorem tblS8_c_3_3 : tblS8 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_3_4 : tblS8 (3 : Fin 7) (4 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tblS8_c_3_5 : tblS8 (3 : Fin 7) (5 : Fin 7) = some ((15 / 23 : ℚ), true) := rfl
theorem tblS8_c_3_6 : tblS8 (3 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tblS8_c_4_0 : tblS8 (4 : Fin 7) (0 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tblS8_c_4_1 : tblS8 (4 : Fin 7) (1 : Fin 7) = some ((2025 / 322 : ℚ), true) := rfl
theorem tblS8_c_4_2 : tblS8 (4 : Fin 7) (2 : Fin 7) = some ((2025 / 1127 : ℚ), true) := rfl
theorem tblS8_c_4_3 : tblS8 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS8_c_4_4 : tblS8 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_4_5 : tblS8 (4 : Fin 7) (5 : Fin 7) = some ((135 / 161 : ℚ), true) := rfl
theorem tblS8_c_4_6 : tblS8 (4 : Fin 7) (6 : Fin 7) = some ((81 / 161 : ℚ), true) := rfl
theorem tblS8_c_5_0 : tblS8 (5 : Fin 7) (0 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tblS8_c_5_1 : tblS8 (5 : Fin 7) (1 : Fin 7) = some ((18225 / 2254 : ℚ), true) := rfl
theorem tblS8_c_5_2 : tblS8 (5 : Fin 7) (2 : Fin 7) = some ((18225 / 7889 : ℚ), true) := rfl
theorem tblS8_c_5_3 : tblS8 (5 : Fin 7) (3 : Fin 7) = some ((81 / 49 : ℚ), true) := rfl
theorem tblS8_c_5_4 : tblS8 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS8_c_5_5 : tblS8 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS8_c_5_6 : tblS8 (5 : Fin 7) (6 : Fin 7) = some ((729 / 1127 : ℚ), true) := rfl
theorem tblS8_c_6_0 : tblS8 (6 : Fin 7) (0 : Fin 7) = some ((25 / 2 : ℚ), false) := rfl
theorem tblS8_c_6_1 : tblS8 (6 : Fin 7) (1 : Fin 7) = some ((25 / 2 : ℚ), true) := rfl
theorem tblS8_c_6_2 : tblS8 (6 : Fin 7) (2 : Fin 7) = some ((25 / 7 : ℚ), true) := rfl
theorem tblS8_c_6_3 : tblS8 (6 : Fin 7) (3 : Fin 7) = some ((135 / 49 : ℚ), true) := rfl
theorem tblS8_c_6_4 : tblS8 (6 : Fin 7) (4 : Fin 7) = some ((15 / 7 : ℚ), true) := rfl
theorem tblS8_c_6_5 : tblS8 (6 : Fin 7) (5 : Fin 7) = some ((5 / 3 : ℚ), false) := rfl
theorem tblS8_c_6_6 : tblS8 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 25's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS25 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17901 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS25_c_0_0 : tblS25 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_0_1 : tblS25 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS25_c_0_2 : tblS25 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tblS25_c_0_3 : tblS25 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tblS25_c_0_4 : tblS25 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tblS25_c_0_5 : tblS25 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tblS25_c_0_6 : tblS25 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tblS25_c_1_0 : tblS25 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS25_c_1_1 : tblS25 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_1_2 : tblS25 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tblS25_c_1_3 : tblS25 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tblS25_c_1_4 : tblS25 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tblS25_c_1_5 : tblS25 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tblS25_c_1_6 : tblS25 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tblS25_c_2_0 : tblS25 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tblS25_c_2_1 : tblS25 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tblS25_c_2_2 : tblS25 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_2_3 : tblS25 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tblS25_c_2_4 : tblS25 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tblS25_c_2_5 : tblS25 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), true) := rfl
theorem tblS25_c_2_6 : tblS25 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), false) := rfl
theorem tblS25_c_3_0 : tblS25 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tblS25_c_3_1 : tblS25 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS25_c_3_2 : tblS25 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS25_c_3_3 : tblS25 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_3_4 : tblS25 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tblS25_c_3_5 : tblS25 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tblS25_c_3_6 : tblS25 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tblS25_c_4_0 : tblS25 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tblS25_c_4_1 : tblS25 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tblS25_c_4_2 : tblS25 (4 : Fin 7) (2 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tblS25_c_4_3 : tblS25 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tblS25_c_4_4 : tblS25 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_4_5 : tblS25 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tblS25_c_4_6 : tblS25 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tblS25_c_5_0 : tblS25 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS25_c_5_1 : tblS25 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS25_c_5_2 : tblS25 (5 : Fin 7) (2 : Fin 7) = some ((17901 / 7889 : ℚ), true) := rfl
theorem tblS25_c_5_3 : tblS25 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tblS25_c_5_4 : tblS25 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS25_c_5_5 : tblS25 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS25_c_5_6 : tblS25 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tblS25_c_6_0 : tblS25 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tblS25_c_6_1 : tblS25 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tblS25_c_6_2 : tblS25 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tblS25_c_6_3 : tblS25 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblS25_c_6_4 : tblS25 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tblS25_c_6_5 : tblS25 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tblS25_c_6_6 : tblS25 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-- Intermediate surviving table of node 26's in-step: the propagation result of the FIRST `uAdd` of the step (the second `uAdd` lands on the child table).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tblS26 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((306 / 1127 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((34 / 161 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((34 / 207 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 15 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((2 / 23 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1127 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 161 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 69 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 / 5 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 23 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 161 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 23 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((11 / 2 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 207 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((11 / 15 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((11 / 23 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((221 / 161 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((13 / 15 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 23 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((117 / 14 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((17901 / 7889 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((1989 / 1127 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((117 / 161 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((221 / 18 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((153 / 49 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 9 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((221 / 135 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tblS26_c_0_0 : tblS26 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_0_1 : tblS26 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tblS26_c_0_2 : tblS26 (0 : Fin 7) (2 : Fin 7) = some ((306 / 1127 : ℚ), true) := rfl
theorem tblS26_c_0_3 : tblS26 (0 : Fin 7) (3 : Fin 7) = some ((34 / 161 : ℚ), true) := rfl
theorem tblS26_c_0_4 : tblS26 (0 : Fin 7) (4 : Fin 7) = some ((34 / 207 : ℚ), true) := rfl
theorem tblS26_c_0_5 : tblS26 (0 : Fin 7) (5 : Fin 7) = some ((2 / 15 : ℚ), false) := rfl
theorem tblS26_c_0_6 : tblS26 (0 : Fin 7) (6 : Fin 7) = some ((2 / 23 : ℚ), false) := rfl
theorem tblS26_c_1_0 : tblS26 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tblS26_c_1_1 : tblS26 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_1_2 : tblS26 (1 : Fin 7) (2 : Fin 7) = some ((459 / 1127 : ℚ), true) := rfl
theorem tblS26_c_1_3 : tblS26 (1 : Fin 7) (3 : Fin 7) = some ((51 / 161 : ℚ), true) := rfl
theorem tblS26_c_1_4 : tblS26 (1 : Fin 7) (4 : Fin 7) = some ((17 / 69 : ℚ), true) := rfl
theorem tblS26_c_1_5 : tblS26 (1 : Fin 7) (5 : Fin 7) = some ((1 / 5 : ℚ), false) := rfl
theorem tblS26_c_1_6 : tblS26 (1 : Fin 7) (6 : Fin 7) = some ((3 / 23 : ℚ), false) := rfl
theorem tblS26_c_2_0 : tblS26 (2 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tblS26_c_2_1 : tblS26 (2 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tblS26_c_2_2 : tblS26 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_2_3 : tblS26 (2 : Fin 7) (3 : Fin 7) = some ((153 / 161 : ℚ), true) := rfl
theorem tblS26_c_2_4 : tblS26 (2 : Fin 7) (4 : Fin 7) = some ((17 / 23 : ℚ), true) := rfl
theorem tblS26_c_2_5 : tblS26 (2 : Fin 7) (5 : Fin 7) = some ((3 / 5 : ℚ), false) := rfl
theorem tblS26_c_2_6 : tblS26 (2 : Fin 7) (6 : Fin 7) = some ((9 / 23 : ℚ), true) := rfl
theorem tblS26_c_3_0 : tblS26 (3 : Fin 7) (0 : Fin 7) = some ((11 / 2 : ℚ), false) := rfl
theorem tblS26_c_3_1 : tblS26 (3 : Fin 7) (1 : Fin 7) = some ((11 / 2 : ℚ), true) := rfl
theorem tblS26_c_3_2 : tblS26 (3 : Fin 7) (2 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS26_c_3_3 : tblS26 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_3_4 : tblS26 (3 : Fin 7) (4 : Fin 7) = some ((187 / 207 : ℚ), true) := rfl
theorem tblS26_c_3_5 : tblS26 (3 : Fin 7) (5 : Fin 7) = some ((11 / 15 : ℚ), false) := rfl
theorem tblS26_c_3_6 : tblS26 (3 : Fin 7) (6 : Fin 7) = some ((11 / 23 : ℚ), false) := rfl
theorem tblS26_c_4_0 : tblS26 (4 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tblS26_c_4_1 : tblS26 (4 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tblS26_c_4_2 : tblS26 (4 : Fin 7) (2 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tblS26_c_4_3 : tblS26 (4 : Fin 7) (3 : Fin 7) = some ((221 / 161 : ℚ), true) := rfl
theorem tblS26_c_4_4 : tblS26 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_4_5 : tblS26 (4 : Fin 7) (5 : Fin 7) = some ((13 / 15 : ℚ), false) := rfl
theorem tblS26_c_4_6 : tblS26 (4 : Fin 7) (6 : Fin 7) = some ((13 / 23 : ℚ), false) := rfl
theorem tblS26_c_5_0 : tblS26 (5 : Fin 7) (0 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS26_c_5_1 : tblS26 (5 : Fin 7) (1 : Fin 7) = some ((117 / 14 : ℚ), true) := rfl
theorem tblS26_c_5_2 : tblS26 (5 : Fin 7) (2 : Fin 7) = some ((17901 / 7889 : ℚ), true) := rfl
theorem tblS26_c_5_3 : tblS26 (5 : Fin 7) (3 : Fin 7) = some ((1989 / 1127 : ℚ), true) := rfl
theorem tblS26_c_5_4 : tblS26 (5 : Fin 7) (4 : Fin 7) = some ((9 / 7 : ℚ), true) := rfl
theorem tblS26_c_5_5 : tblS26 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tblS26_c_5_6 : tblS26 (5 : Fin 7) (6 : Fin 7) = some ((117 / 161 : ℚ), true) := rfl
theorem tblS26_c_6_0 : tblS26 (6 : Fin 7) (0 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tblS26_c_6_1 : tblS26 (6 : Fin 7) (1 : Fin 7) = some ((221 / 18 : ℚ), true) := rfl
theorem tblS26_c_6_2 : tblS26 (6 : Fin 7) (2 : Fin 7) = some ((153 / 49 : ℚ), true) := rfl
theorem tblS26_c_6_3 : tblS26 (6 : Fin 7) (3 : Fin 7) = some ((17 / 7 : ℚ), true) := rfl
theorem tblS26_c_6_4 : tblS26 (6 : Fin 7) (4 : Fin 7) = some ((17 / 9 : ℚ), true) := rfl
theorem tblS26_c_6_5 : tblS26 (6 : Fin 7) (5 : Fin 7) = some ((221 / 135 : ℚ), true) := rfl
theorem tblS26_c_6_6 : tblS26 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-! ## 1b. The node states and the certificate trees -/

/-- The start-zone root: DFS node 0 (depth 1, last reading row 5, exit numerator 9, frontier sup 6 / 5). -/
-- STANDING: DATA
def node0 : DfsNode := ⟨tbl0, (5 : Fin 7), (9 : ℚ), (6 / 5 : ℚ), {((5 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 1 (internal, depth 2, last reading row 4, exit numerator 9): child of node 0 by the step (4, 7, 9). -/
-- STANDING: DATA
def node1 : DfsNode := ⟨tbl1, (4 : Fin 7), (9 : ℚ), (18 / 11 : ℚ), node0.seen ∪ {((4 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 2 (internal, depth 3, last reading row 3, exit numerator 9): child of node 1 by the step (3, 7, 9). -/
-- STANDING: DATA
def node2 : DfsNode := ⟨tbl2, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node1.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 3 (internal, depth 4, last reading row 2, exit numerator 9): child of node 2 by the step (2, 7, 9). -/
-- STANDING: DATA
def node3 : DfsNode := ⟨tbl3, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node2.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 4 (reach, depth 5, last reading row 5, exit numerator 17): child of node 3 by the step (5, 15, 17). -/
-- STANDING: DATA
def node4 : DfsNode := ⟨tbl4, (5 : Fin 7), (17 : ℚ), (34 / 15 : ℚ), node3.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 5 (reach, depth 5, last reading row 6, exit numerator 25): child of node 3 by the step (6, 23, 25). -/
-- STANDING: DATA
def node5 : DfsNode := ⟨tbl5, (6 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node3.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 6 (reach, depth 5, last reading row 6, exit numerator 33): child of node 3 by the step (6, 31, 33). -/
-- STANDING: DATA
def node6 : DfsNode := ⟨tbl6, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node3.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 7 (internal, depth 4, last reading row 6, exit numerator 25): child of node 2 by the step (6, 23, 25). -/
-- STANDING: DATA
def node7 : DfsNode := ⟨tbl7, (6 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node2.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 8 (internal, depth 5, last reading row 2, exit numerator 9): child of node 7 by the step (2, 7, 9). -/
-- STANDING: DATA
def node8 : DfsNode := ⟨tbl8, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node7.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 9 (deadend, depth 6, last reading row 4, exit numerator 17): child of node 8 by the step (4, 15, 17). -/
-- STANDING: DATA
def node9 : DfsNode := ⟨tbl9, (4 : Fin 7), (17 : ℚ), (102 / 35 : ℚ), node8.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 10 (reach, depth 6, last reading row 5, exit numerator 17): child of node 8 by the step (5, 15, 17). -/
-- STANDING: DATA
def node10 : DfsNode := ⟨tbl10, (5 : Fin 7), (17 : ℚ), (34 / 15 : ℚ), node8.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 11 (internal, depth 6, last reading row 6, exit numerator 33): child of node 8 by the step (6, 31, 33). -/
-- STANDING: DATA
def node11 : DfsNode := ⟨tbl11, (6 : Fin 7), (33 : ℚ), (16038 / 5635 : ℚ), node8.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 12 (deadend, depth 7, last reading row 4, exit numerator 17): child of node 11 by the step (4, 15, 17). -/
-- STANDING: DATA
def node12 : DfsNode := ⟨tbl12, (4 : Fin 7), (17 : ℚ), (102 / 35 : ℚ), node11.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 13 (internal, depth 5, last reading row 5, exit numerator 17): child of node 7 by the step (5, 15, 17). -/
-- STANDING: DATA
def node13 : DfsNode := ⟨tbl13, (5 : Fin 7), (17 : ℚ), (34 / 15 : ℚ), node7.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 14 (internal, depth 6, last reading row 2, exit numerator 9): child of node 13 by the step (2, 7, 9). -/
-- STANDING: DATA
def node14 : DfsNode := ⟨tbl14, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node13.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 15 (deadend, depth 7, last reading row 4, exit numerator 17): child of node 14 by the step (4, 15, 17). -/
-- STANDING: DATA
def node15 : DfsNode := ⟨tbl15, (4 : Fin 7), (17 : ℚ), (102 / 35 : ℚ), node14.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 16 (internal, depth 7, last reading row 6, exit numerator 33): child of node 14 by the step (6, 31, 33). -/
-- STANDING: DATA
def node16 : DfsNode := ⟨tbl16, (6 : Fin 7), (33 : ℚ), (16038 / 5635 : ℚ), node14.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 17 (deadend, depth 8, last reading row 4, exit numerator 17): child of node 16 by the step (4, 15, 17). -/
-- STANDING: DATA
def node17 : DfsNode := ⟨tbl17, (4 : Fin 7), (17 : ℚ), (102 / 35 : ℚ), node16.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 18 (internal, depth 3, last reading row 6, exit numerator 17): child of node 1 by the step (6, 15, 17). -/
-- STANDING: DATA
def node18 : DfsNode := ⟨tbl18, (6 : Fin 7), (17 : ℚ), (34 / 23 : ℚ), node1.seen ∪ {((6 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 19 (internal, depth 4, last reading row 3, exit numerator 9): child of node 18 by the step (3, 7, 9). -/
-- STANDING: DATA
def node19 : DfsNode := ⟨tbl19, (3 : Fin 7), (9 : ℚ), (2 : ℚ), node18.seen ∪ {((3 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 20 (internal, depth 5, last reading row 2, exit numerator 9): child of node 19 by the step (2, 7, 9). -/
-- STANDING: DATA
def node20 : DfsNode := ⟨tbl20, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node19.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 21 (internal, depth 6, last reading row 4, exit numerator 17): child of node 20 by the step (4, 15, 17). -/
-- STANDING: DATA
def node21 : DfsNode := ⟨tbl21, (4 : Fin 7), (17 : ℚ), (578 / 207 : ℚ), node20.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 22 (internal, depth 7, last reading row 6, exit numerator 33): child of node 21 by the step (6, 31, 33). -/
-- STANDING: DATA
def node22 : DfsNode := ⟨tbl22, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node21.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 23 (internal, depth 8, last reading row 5, exit numerator 25): child of node 22 by the step (5, 23, 25). -/
-- STANDING: DATA
def node23 : DfsNode := ⟨tbl23, (5 : Fin 7), (25 : ℚ), (10 / 3 : ℚ), node22.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 24 (reach, depth 9, last reading row 3, exit numerator 17): child of node 23 by the step (3, 15, 17). -/
-- STANDING: DATA
def node24 : DfsNode := ⟨tbl24, (3 : Fin 7), (17 : ℚ), (578 / 161 : ℚ), node23.seen ∪ {((3 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 25 (reach, depth 6, last reading row 5, exit numerator 17): child of node 20 by the step (5, 15, 17). -/
-- STANDING: DATA
def node25 : DfsNode := ⟨tbl25, (5 : Fin 7), (17 : ℚ), (34 / 15 : ℚ), node20.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 26 (reach, depth 6, last reading row 6, exit numerator 25): child of node 20 by the step (6, 23, 25). -/
-- STANDING: DATA
def node26 : DfsNode := ⟨tbl26, (6 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node20.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 27 (internal, depth 5, last reading row 5, exit numerator 17): child of node 19 by the step (5, 15, 17). -/
-- STANDING: DATA
def node27 : DfsNode := ⟨tbl27, (5 : Fin 7), (17 : ℚ), (34 / 15 : ℚ), node19.seen ∪ {((5 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 28 (internal, depth 6, last reading row 2, exit numerator 9): child of node 27 by the step (2, 7, 9). -/
-- STANDING: DATA
def node28 : DfsNode := ⟨tbl28, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node27.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 29 (internal, depth 7, last reading row 4, exit numerator 17): child of node 28 by the step (4, 15, 17). -/
-- STANDING: DATA
def node29 : DfsNode := ⟨tbl29, (4 : Fin 7), (17 : ℚ), (15606 / 5635 : ℚ), node28.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 30 (internal, depth 8, last reading row 6, exit numerator 33): child of node 29 by the step (6, 31, 33). -/
-- STANDING: DATA
def node30 : DfsNode := ⟨tbl30, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node29.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 31 (deadend, depth 9, last reading row 5, exit numerator 25): child of node 30 by the step (5, 23, 25). -/
-- STANDING: DATA
def node31 : DfsNode := ⟨tbl31, (5 : Fin 7), (25 : ℚ), (510 / 161 : ℚ), node30.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 32 (reach, depth 7, last reading row 6, exit numerator 25): child of node 28 by the step (6, 23, 25). -/
-- STANDING: DATA
def node32 : DfsNode := ⟨tbl32, (6 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node28.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 33 (reach, depth 7, last reading row 6, exit numerator 33): child of node 28 by the step (6, 31, 33). -/
-- STANDING: DATA
def node33 : DfsNode := ⟨tbl33, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node28.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 34 (internal, depth 6, last reading row 6, exit numerator 25): child of node 27 by the step (6, 23, 25). -/
-- STANDING: DATA
def node34 : DfsNode := ⟨tbl34, (6 : Fin 7), (25 : ℚ), (50 / 23 : ℚ), node27.seen ∪ {((6 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 35 (internal, depth 7, last reading row 2, exit numerator 9): child of node 34 by the step (2, 7, 9). -/
-- STANDING: DATA
def node35 : DfsNode := ⟨tbl35, (2 : Fin 7), (9 : ℚ), (18 / 7 : ℚ), node34.seen ∪ {((2 : Fin 7), (9 : ℚ))}⟩

/-- DFS node 36 (internal, depth 8, last reading row 4, exit numerator 17): child of node 35 by the step (4, 15, 17). -/
-- STANDING: DATA
def node36 : DfsNode := ⟨tbl36, (4 : Fin 7), (17 : ℚ), (15606 / 5635 : ℚ), node35.seen ∪ {((4 : Fin 7), (17 : ℚ))}⟩

/-- DFS node 37 (internal, depth 9, last reading row 6, exit numerator 33): child of node 36 by the step (6, 31, 33). -/
-- STANDING: DATA
def node37 : DfsNode := ⟨tbl37, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node36.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- DFS node 38 (deadend, depth 10, last reading row 5, exit numerator 25): child of node 37 by the step (5, 23, 25). -/
-- STANDING: DATA
def node38 : DfsNode := ⟨tbl38, (5 : Fin 7), (25 : ℚ), (510 / 161 : ℚ), node37.seen ∪ {((5 : Fin 7), (25 : ℚ))}⟩

/-- DFS node 39 (reach, depth 8, last reading row 6, exit numerator 33): child of node 35 by the step (6, 31, 33). -/
-- STANDING: DATA
def node39 : DfsNode := ⟨tbl39, (6 : Fin 7), (33 : ℚ), (66 / 23 : ℚ), node35.seen ∪ {((6 : Fin 7), (33 : ℚ))}⟩

/-- The reach-prune leaf, DFS node 39: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree39 : DfsCert := DfsCert.prune node39

/-- The dead-end leaf, DFS node 38: no filter-passing step. -/
-- STANDING: DATA
def tree38 : DfsCert := DfsCert.deadend node38

def children37 : List DfsCert := [tree38]
/-- The subtree rooted at internal node 37: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree37 : DfsCert := DfsCert.node node37 children37

def children36 : List DfsCert := [tree37]
/-- The subtree rooted at internal node 36: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree36 : DfsCert := DfsCert.node node36 children36

def children35 : List DfsCert := [tree36, tree39]
/-- The subtree rooted at internal node 35: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree35 : DfsCert := DfsCert.node node35 children35

def children34 : List DfsCert := [tree35]
/-- The subtree rooted at internal node 34: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree34 : DfsCert := DfsCert.node node34 children34

/-- The reach-prune leaf, DFS node 33: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree33 : DfsCert := DfsCert.prune node33

/-- The reach-prune leaf, DFS node 32: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree32 : DfsCert := DfsCert.prune node32

/-- The dead-end leaf, DFS node 31: no filter-passing step. -/
-- STANDING: DATA
def tree31 : DfsCert := DfsCert.deadend node31

def children30 : List DfsCert := [tree31]
/-- The subtree rooted at internal node 30: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree30 : DfsCert := DfsCert.node node30 children30

def children29 : List DfsCert := [tree30]
/-- The subtree rooted at internal node 29: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree29 : DfsCert := DfsCert.node node29 children29

def children28 : List DfsCert := [tree29, tree32, tree33]
/-- The subtree rooted at internal node 28: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree28 : DfsCert := DfsCert.node node28 children28

def children27 : List DfsCert := [tree28, tree34]
/-- The subtree rooted at internal node 27: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree27 : DfsCert := DfsCert.node node27 children27

/-- The reach-prune leaf, DFS node 26: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree26 : DfsCert := DfsCert.prune node26

/-- The reach-prune leaf, DFS node 25: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree25 : DfsCert := DfsCert.prune node25

/-- The reach-prune leaf, DFS node 24: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree24 : DfsCert := DfsCert.prune node24

def children23 : List DfsCert := [tree24]
/-- The subtree rooted at internal node 23: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree23 : DfsCert := DfsCert.node node23 children23

def children22 : List DfsCert := [tree23]
/-- The subtree rooted at internal node 22: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree22 : DfsCert := DfsCert.node node22 children22

def children21 : List DfsCert := [tree22]
/-- The subtree rooted at internal node 21: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree21 : DfsCert := DfsCert.node node21 children21

def children20 : List DfsCert := [tree21, tree25, tree26]
/-- The subtree rooted at internal node 20: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree20 : DfsCert := DfsCert.node node20 children20

def children19 : List DfsCert := [tree20, tree27]
/-- The subtree rooted at internal node 19: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree19 : DfsCert := DfsCert.node node19 children19

def children18 : List DfsCert := [tree19]
/-- The subtree rooted at internal node 18: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree18 : DfsCert := DfsCert.node node18 children18

/-- The dead-end leaf, DFS node 17: no filter-passing step. -/
-- STANDING: DATA
def tree17 : DfsCert := DfsCert.deadend node17

def children16 : List DfsCert := [tree17]
/-- The subtree rooted at internal node 16: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree16 : DfsCert := DfsCert.node node16 children16

/-- The dead-end leaf, DFS node 15: no filter-passing step. -/
-- STANDING: DATA
def tree15 : DfsCert := DfsCert.deadend node15

def children14 : List DfsCert := [tree15, tree16]
/-- The subtree rooted at internal node 14: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree14 : DfsCert := DfsCert.node node14 children14

def children13 : List DfsCert := [tree14]
/-- The subtree rooted at internal node 13: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree13 : DfsCert := DfsCert.node node13 children13

/-- The dead-end leaf, DFS node 12: no filter-passing step. -/
-- STANDING: DATA
def tree12 : DfsCert := DfsCert.deadend node12

def children11 : List DfsCert := [tree12]
/-- The subtree rooted at internal node 11: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree11 : DfsCert := DfsCert.node node11 children11

/-- The reach-prune leaf, DFS node 10: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree10 : DfsCert := DfsCert.prune node10

/-- The dead-end leaf, DFS node 9: no filter-passing step. -/
-- STANDING: DATA
def tree9 : DfsCert := DfsCert.deadend node9

def children8 : List DfsCert := [tree9, tree10, tree11]
/-- The subtree rooted at internal node 8: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree8 : DfsCert := DfsCert.node node8 children8

def children7 : List DfsCert := [tree8, tree13]
/-- The subtree rooted at internal node 7: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree7 : DfsCert := DfsCert.node node7 children7

/-- The reach-prune leaf, DFS node 6: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree6 : DfsCert := DfsCert.prune node6

/-- The reach-prune leaf, DFS node 5: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree5 : DfsCert := DfsCert.prune node5

/-- The reach-prune leaf, DFS node 4: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree4 : DfsCert := DfsCert.prune node4

def children3 : List DfsCert := [tree4, tree5, tree6]
/-- The subtree rooted at internal node 3: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree3 : DfsCert := DfsCert.node node3 children3

def children2 : List DfsCert := [tree3, tree7]
/-- The subtree rooted at internal node 2: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree2 : DfsCert := DfsCert.node node2 children2

def children1 : List DfsCert := [tree2, tree18]
/-- The subtree rooted at internal node 1: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree1 : DfsCert := DfsCert.node node1 children1

def children0 : List DfsCert := [tree1]
/-- The subtree rooted at internal node 0: every child of every retained
internal node is retained. -/
-- STANDING: DATA
def tree0 : DfsCert := DfsCert.node node0 children0

/-- The box's WHOLE certificate forest (1 start-zone root(s), 40 nodes),
transcribed verbatim from the reconstruction. -/
-- STANDING: DATA
def forest : List DfsCert := [tree0]

/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/

theorem nodeOK_0 : DfsNodeOK node0 := by
  show uExitOK tbl0 (5 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl0_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_0
theorem nodeOK_1 : DfsNodeOK node1 := by
  show uExitOK tbl1 (4 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl1_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_1
theorem nodeOK_2 : DfsNodeOK node2 := by
  show uExitOK tbl2 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl2_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_2
theorem nodeOK_3 : DfsNodeOK node3 := by
  show uExitOK tbl3 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl3_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_3
theorem nodeOK_4 : DfsNodeOK node4 := by
  show uExitOK tbl4 (5 : Fin 7) (17 : ℚ) = false
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
  show uExitOK tbl6 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl6_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl6_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_6
theorem nodeOK_7 : DfsNodeOK node7 := by
  show uExitOK tbl7 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl7_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_7
theorem nodeOK_8 : DfsNodeOK node8 := by
  show uExitOK tbl8 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl8_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_8
theorem nodeOK_9 : DfsNodeOK node9 := by
  show uExitOK tbl9 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl9_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl9_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_9
theorem nodeOK_10 : DfsNodeOK node10 := by
  show uExitOK tbl10 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl10_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl10_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_10
theorem nodeOK_11 : DfsNodeOK node11 := by
  show uExitOK tbl11 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl11_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl11_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_11
theorem nodeOK_12 : DfsNodeOK node12 := by
  show uExitOK tbl12 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl12_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl12_c_0_4] <;> norm_num)]
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
  show uExitOK tbl14 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl14_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl14_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_14
theorem nodeOK_15 : DfsNodeOK node15 := by
  show uExitOK tbl15 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl15_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl15_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_15
theorem nodeOK_16 : DfsNodeOK node16 := by
  show uExitOK tbl16 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl16_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl16_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_16
theorem nodeOK_17 : DfsNodeOK node17 := by
  show uExitOK tbl17 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl17_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl17_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_17
theorem nodeOK_18 : DfsNodeOK node18 := by
  show uExitOK tbl18 (6 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl18_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl18_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_18
theorem nodeOK_19 : DfsNodeOK node19 := by
  show uExitOK tbl19 (3 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl19_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_19
theorem nodeOK_20 : DfsNodeOK node20 := by
  show uExitOK tbl20 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl20_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_20
theorem nodeOK_21 : DfsNodeOK node21 := by
  show uExitOK tbl21 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl21_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl21_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_21
theorem nodeOK_22 : DfsNodeOK node22 := by
  show uExitOK tbl22 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl22_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl22_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_22
theorem nodeOK_23 : DfsNodeOK node23 := by
  show uExitOK tbl23 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl23_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl23_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_23
theorem nodeOK_24 : DfsNodeOK node24 := by
  show uExitOK tbl24 (3 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl24_c_3_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl24_c_0_3] <;> norm_num)]
  rfl

#print axioms nodeOK_24
theorem nodeOK_25 : DfsNodeOK node25 := by
  show uExitOK tbl25 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl25_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl25_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_25
theorem nodeOK_26 : DfsNodeOK node26 := by
  show uExitOK tbl26 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl26_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl26_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_26
theorem nodeOK_27 : DfsNodeOK node27 := by
  show uExitOK tbl27 (5 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl27_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl27_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_27
theorem nodeOK_28 : DfsNodeOK node28 := by
  show uExitOK tbl28 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl28_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl28_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_28
theorem nodeOK_29 : DfsNodeOK node29 := by
  show uExitOK tbl29 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl29_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl29_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_29
theorem nodeOK_30 : DfsNodeOK node30 := by
  show uExitOK tbl30 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl30_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl30_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_30
theorem nodeOK_31 : DfsNodeOK node31 := by
  show uExitOK tbl31 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl31_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl31_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_31
theorem nodeOK_32 : DfsNodeOK node32 := by
  show uExitOK tbl32 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl32_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl32_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_32
theorem nodeOK_33 : DfsNodeOK node33 := by
  show uExitOK tbl33 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl33_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl33_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_33
theorem nodeOK_34 : DfsNodeOK node34 := by
  show uExitOK tbl34 (6 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl34_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl34_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_34
theorem nodeOK_35 : DfsNodeOK node35 := by
  show uExitOK tbl35 (2 : Fin 7) (9 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl35_c_2_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl35_c_0_2] <;> norm_num)]
  rfl

#print axioms nodeOK_35
theorem nodeOK_36 : DfsNodeOK node36 := by
  show uExitOK tbl36 (4 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl36_c_4_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl36_c_0_4] <;> norm_num)]
  rfl

#print axioms nodeOK_36
theorem nodeOK_37 : DfsNodeOK node37 := by
  show uExitOK tbl37 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl37_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl37_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_37
theorem nodeOK_38 : DfsNodeOK node38 := by
  show uExitOK tbl38 (5 : Fin 7) (25 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl38_c_5_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl38_c_0_5] <;> norm_num)]
  rfl

#print axioms nodeOK_38
theorem nodeOK_39 : DfsNodeOK node39 := by
  show uExitOK tbl39 (6 : Fin 7) (33 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl39_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl39_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_39

/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/

/-- Node 1's step (4, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_1_1 : uAdd tbl0 (5 : Fin 7) (4 : Fin 7) ((9 / 7 : ℚ)) true = some tbl1 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl0_c_5_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_4_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl0, tbl1] <;> norm_num)

/-- Node 1's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_1_2 : uAdd tbl1 (4 : Fin 7) (5 : Fin 7) ((9 / 9 : ℚ)) true = some tbl1 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_5] <;> norm_num)

/-- Node 1's full step equation. -/
theorem stepEq_1 : uStep tbl0 (5 : Fin 7) (4 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl1 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_1_1 addEq_1_2

/-- Node 1's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_1 : childState (boxN m4res_1_1_4_5_6_8_12) node0 (4 : Fin 7) (9 : ℚ) tbl1 = DfsCert.root tree1 :=
  by
    simp only [childState, DfsCert.root, tree1, node1]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node0.U (4 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node0, tbl0_c_0_4]
    norm_num [hlo]

#print axioms addEq_1_1
#print axioms addEq_1_2
#print axioms stepEq_1
#print axioms childEq_1

/-- Node 2's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_2_1 : uAdd tbl1 (4 : Fin 7) (3 : Fin 7) ((9 / 7 : ℚ)) true = some tbl2 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl1_c_4_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_3_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl1, tbl2] <;> norm_num)

/-- Node 2's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_2_2 : uAdd tbl2 (3 : Fin 7) (4 : Fin 7) ((9 / 9 : ℚ)) true = some tbl2 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_4] <;> norm_num)

/-- Node 2's full step equation. -/
theorem stepEq_2 : uStep tbl1 (4 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_2_1 addEq_2_2

/-- Node 2's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_2 : childState (boxN m4res_1_1_4_5_6_8_12) node1 (3 : Fin 7) (9 : ℚ) tbl2 = DfsCert.root tree2 :=
  by
    simp only [childState, DfsCert.root, tree2, node2]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node1.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node1, tbl1_c_0_3]
    norm_num [hlo]

#print axioms addEq_2_1
#print axioms addEq_2_2
#print axioms stepEq_2
#print axioms childEq_2

/-- Node 3's step (2, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_3_1 : uAdd tbl2 (3 : Fin 7) (2 : Fin 7) ((9 / 7 : ℚ)) true = some tbl3 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl2_c_3_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_2_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl2, tbl3] <;> norm_num)

/-- Node 3's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_3_2 : uAdd tbl3 (2 : Fin 7) (3 : Fin 7) ((9 / 9 : ℚ)) true = some tbl3 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_3] <;> norm_num)

/-- Node 3's full step equation. -/
theorem stepEq_3 : uStep tbl2 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl3 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_3_1 addEq_3_2

/-- Node 3's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_3 : childState (boxN m4res_1_1_4_5_6_8_12) node2 (2 : Fin 7) (9 : ℚ) tbl3 = DfsCert.root tree3 :=
  by
    simp only [childState, DfsCert.root, tree3, node3]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node2.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node2, tbl2_c_0_2]
    norm_num [hlo]

#print axioms addEq_3_1
#print axioms addEq_3_2
#print axioms stepEq_3
#print axioms childEq_3

/-- Node 4's step (5, 15, 17): add 1 propagates to the intermediate table tblS4 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_4_1 : uAdd tbl3 (2 : Fin 7) (5 : Fin 7) ((9 / 15 : ℚ)) true = some tblS4 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl3_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl3, tblS4] <;> norm_num)

/-- Node 4's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_4_2 : uAdd tblS4 (5 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl4 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS4_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tblS4_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS4, tbl4] <;> norm_num)

/-- Node 4's full step equation. -/
theorem stepEq_4 : uStep tbl3 (2 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_4_1 addEq_4_2

/-- Node 4's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_4 : childState (boxN m4res_1_1_4_5_6_8_12) node3 (5 : Fin 7) (17 : ℚ) tbl4 = DfsCert.root tree4 :=
  by
    simp only [childState, DfsCert.root, tree4, node4]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node3.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node3, tbl3_c_0_5]
    norm_num [hlo]

#print axioms addEq_4_1
#print axioms addEq_4_2
#print axioms stepEq_4
#print axioms childEq_4

/-- Node 5's step (6, 23, 25): add 1 propagates to the intermediate table tblS5 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_5_1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tblS5 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl3, tblS5] <;> norm_num)

/-- Node 5's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_5_2 : uAdd tblS5 (6 : Fin 7) (2 : Fin 7) ((25 / 9 : ℚ)) true = some tbl5 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS5_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tblS5_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS5, tbl5] <;> norm_num)

/-- Node 5's full step equation. -/
theorem stepEq_5 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl5 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_5_1 addEq_5_2

/-- Node 5's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_5 : childState (boxN m4res_1_1_4_5_6_8_12) node3 (6 : Fin 7) (25 : ℚ) tbl5 = DfsCert.root tree5 :=
  by
    simp only [childState, DfsCert.root, tree5, node5]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node3.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node3, tbl3_c_0_6]
    norm_num [hlo]

#print axioms addEq_5_1
#print axioms addEq_5_2
#print axioms stepEq_5
#print axioms childEq_5

/-- Node 6's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_6_1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((9 / 31 : ℚ)) true = some tbl6 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl3_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl3, tbl6] <;> norm_num)

/-- Node 6's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_6_2 : uAdd tbl6 (6 : Fin 7) (2 : Fin 7) ((33 / 9 : ℚ)) true = some tbl6 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl6_c_6_2] <;> norm_num)

/-- Node 6's full step equation. -/
theorem stepEq_6 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_6_1 addEq_6_2

/-- Node 6's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_6 : childState (boxN m4res_1_1_4_5_6_8_12) node3 (6 : Fin 7) (33 : ℚ) tbl6 = DfsCert.root tree6 :=
  by
    simp only [childState, DfsCert.root, tree6, node6]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node3.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node3, tbl3_c_0_6]
    norm_num [hlo]

#print axioms addEq_6_1
#print axioms addEq_6_2
#print axioms stepEq_6
#print axioms childEq_6

/-- Node 7's step (6, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_7_1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tbl7 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl2_c_6_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl2, tbl7] <;> norm_num)

/-- Node 7's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_7_2 : uAdd tbl7 (6 : Fin 7) (3 : Fin 7) ((25 / 9 : ℚ)) true = some tbl7 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_6_3] <;> norm_num)

/-- Node 7's full step equation. -/
theorem stepEq_7 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl7 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_7_1 addEq_7_2

/-- Node 7's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_7 : childState (boxN m4res_1_1_4_5_6_8_12) node2 (6 : Fin 7) (25 : ℚ) tbl7 = DfsCert.root tree7 :=
  by
    simp only [childState, DfsCert.root, tree7, node7]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node2.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node2, tbl2_c_0_6]
    norm_num [hlo]

#print axioms addEq_7_1
#print axioms addEq_7_2
#print axioms stepEq_7
#print axioms childEq_7

/-- Node 8's step (2, 7, 9): add 1 propagates to the intermediate table tblS8 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_8_1 : uAdd tbl7 (6 : Fin 7) (2 : Fin 7) ((25 / 7 : ℚ)) true = some tblS8 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl7_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl7, tblS8] <;> norm_num)

/-- Node 8's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_8_2 : uAdd tblS8 (2 : Fin 7) (6 : Fin 7) ((9 / 25 : ℚ)) true = some tbl8 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS8_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tblS8_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS8, tbl8] <;> norm_num)

/-- Node 8's full step equation. -/
theorem stepEq_8 : uStep tbl7 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_8_1 addEq_8_2

/-- Node 8's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_8 : childState (boxN m4res_1_1_4_5_6_8_12) node7 (2 : Fin 7) (9 : ℚ) tbl8 = DfsCert.root tree8 :=
  by
    simp only [childState, DfsCert.root, tree8, node8]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node7.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node7, tbl7_c_0_2]
    norm_num [hlo]

#print axioms addEq_8_1
#print axioms addEq_8_2
#print axioms stepEq_8
#print axioms childEq_8

/-- Node 9's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_9_1 : uAdd tbl8 (2 : Fin 7) (4 : Fin 7) ((9 / 15 : ℚ)) true = some tbl9 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl8_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl8, tbl9] <;> norm_num)

/-- Node 9's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_9_2 : uAdd tbl9 (4 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl9 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_4_2] <;> norm_num)

/-- Node 9's full step equation. -/
theorem stepEq_9 : uStep tbl8 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl9 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_9_1 addEq_9_2

/-- Node 9's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_9 : childState (boxN m4res_1_1_4_5_6_8_12) node8 (4 : Fin 7) (17 : ℚ) tbl9 = DfsCert.root tree9 :=
  by
    simp only [childState, DfsCert.root, tree9, node9]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node8.U (4 : Fin 7) = (35 / 6 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node8, tbl8_c_0_4]
    norm_num [hlo]

#print axioms addEq_9_1
#print axioms addEq_9_2
#print axioms stepEq_9
#print axioms childEq_9

/-- Node 10's step (5, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_10_1 : uAdd tbl8 (2 : Fin 7) (5 : Fin 7) ((9 / 15 : ℚ)) true = some tbl8 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_2_5] <;> norm_num)

/-- Node 10's step: add 2 propagates to the child table. -/
theorem addEq_10_2 : uAdd tbl8 (5 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl10 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl8_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl8, tbl10] <;> norm_num)

/-- Node 10's full step equation. -/
theorem stepEq_10 : uStep tbl8 (2 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_10_1 addEq_10_2

/-- Node 10's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_10 : childState (boxN m4res_1_1_4_5_6_8_12) node8 (5 : Fin 7) (17 : ℚ) tbl10 = DfsCert.root tree10 :=
  by
    simp only [childState, DfsCert.root, tree10, node10]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node8.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node8, tbl8_c_0_5]
    norm_num [hlo]

#print axioms addEq_10_1
#print axioms addEq_10_2
#print axioms stepEq_10
#print axioms childEq_10

/-- Node 11's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_11_1 : uAdd tbl8 (2 : Fin 7) (6 : Fin 7) ((9 / 31 : ℚ)) true = some tbl11 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl8_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl8_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl8, tbl11] <;> norm_num)

/-- Node 11's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_11_2 : uAdd tbl11 (6 : Fin 7) (2 : Fin 7) ((33 / 9 : ℚ)) true = some tbl11 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_6_2] <;> norm_num)

/-- Node 11's full step equation. -/
theorem stepEq_11 : uStep tbl8 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl11 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_11_1 addEq_11_2

/-- Node 11's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_11 : childState (boxN m4res_1_1_4_5_6_8_12) node8 (6 : Fin 7) (33 : ℚ) tbl11 = DfsCert.root tree11 :=
  by
    simp only [childState, DfsCert.root, tree11, node11]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node8.U (6 : Fin 7) = (5635 / 486 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node8, tbl8_c_0_6]
    norm_num [hlo]

#print axioms addEq_11_1
#print axioms addEq_11_2
#print axioms stepEq_11
#print axioms childEq_11

/-- Node 12's step (4, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_12_1 : uAdd tbl11 (6 : Fin 7) (4 : Fin 7) ((33 / 15 : ℚ)) true = some tbl11 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_6_4] <;> norm_num)

/-- Node 12's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_12_2 : uAdd tbl11 (4 : Fin 7) (6 : Fin 7) ((17 / 33 : ℚ)) true = some tbl11 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_4_6] <;> norm_num)

/-- Node 12's full step equation. -/
theorem stepEq_12 : uStep tbl11 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_12_1 addEq_12_2

/-- Node 12's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_12 : childState (boxN m4res_1_1_4_5_6_8_12) node11 (4 : Fin 7) (17 : ℚ) tbl12 = DfsCert.root tree12 :=
  by
    simp only [childState, DfsCert.root, tree12, node12]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node11.U (4 : Fin 7) = (35 / 6 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node11, tbl11_c_0_4]
    norm_num [hlo]

#print axioms addEq_12_1
#print axioms addEq_12_2
#print axioms stepEq_12
#print axioms childEq_12

/-- Node 13's step (5, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_13_1 : uAdd tbl7 (6 : Fin 7) (5 : Fin 7) ((25 / 15 : ℚ)) true = some tbl13 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl7_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl7_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl7, tbl13] <;> norm_num)

/-- Node 13's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_13_2 : uAdd tbl13 (5 : Fin 7) (6 : Fin 7) ((17 / 25 : ℚ)) true = some tbl13 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_6] <;> norm_num)

/-- Node 13's full step equation. -/
theorem stepEq_13 : uStep tbl7 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl13 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_13_1 addEq_13_2

/-- Node 13's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_13 : childState (boxN m4res_1_1_4_5_6_8_12) node7 (5 : Fin 7) (17 : ℚ) tbl13 = DfsCert.root tree13 :=
  by
    simp only [childState, DfsCert.root, tree13, node13]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node7.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node7, tbl7_c_0_5]
    norm_num [hlo]

#print axioms addEq_13_1
#print axioms addEq_13_2
#print axioms stepEq_13
#print axioms childEq_13

/-- Node 14's step (2, 7, 9): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_14_1 : uAdd tbl13 (5 : Fin 7) (2 : Fin 7) ((17 / 7 : ℚ)) true = some tbl13 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_2] <;> norm_num)

/-- Node 14's step: add 2 propagates to the child table. -/
theorem addEq_14_2 : uAdd tbl13 (2 : Fin 7) (5 : Fin 7) ((9 / 17 : ℚ)) true = some tbl14 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl13_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl13_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl13, tbl14] <;> norm_num)

/-- Node 14's full step equation. -/
theorem stepEq_14 : uStep tbl13 (5 : Fin 7) (2 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_14_1 addEq_14_2

/-- Node 14's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_14 : childState (boxN m4res_1_1_4_5_6_8_12) node13 (2 : Fin 7) (9 : ℚ) tbl14 = DfsCert.root tree14 :=
  by
    simp only [childState, DfsCert.root, tree14, node14]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node13.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node13, tbl13_c_0_2]
    norm_num [hlo]

#print axioms addEq_14_1
#print axioms addEq_14_2
#print axioms stepEq_14
#print axioms childEq_14

/-- Node 15's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_15_1 : uAdd tbl14 (2 : Fin 7) (4 : Fin 7) ((9 / 15 : ℚ)) true = some tbl15 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl14_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl14_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl14, tbl15] <;> norm_num)

/-- Node 15's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_15_2 : uAdd tbl15 (4 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl15 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_4_2] <;> norm_num)

/-- Node 15's full step equation. -/
theorem stepEq_15 : uStep tbl14 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl15 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_15_1 addEq_15_2

/-- Node 15's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_15 : childState (boxN m4res_1_1_4_5_6_8_12) node14 (4 : Fin 7) (17 : ℚ) tbl15 = DfsCert.root tree15 :=
  by
    simp only [childState, DfsCert.root, tree15, node15]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node14.U (4 : Fin 7) = (35 / 6 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node14, tbl14_c_0_4]
    norm_num [hlo]

#print axioms addEq_15_1
#print axioms addEq_15_2
#print axioms stepEq_15
#print axioms childEq_15

/-- Node 16's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_16_1 : uAdd tbl14 (2 : Fin 7) (6 : Fin 7) ((9 / 31 : ℚ)) true = some tbl16 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl14_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl14_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl14, tbl16] <;> norm_num)

/-- Node 16's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_16_2 : uAdd tbl16 (6 : Fin 7) (2 : Fin 7) ((33 / 9 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_6_2] <;> norm_num)

/-- Node 16's full step equation. -/
theorem stepEq_16 : uStep tbl14 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl16 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_16_1 addEq_16_2

/-- Node 16's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_16 : childState (boxN m4res_1_1_4_5_6_8_12) node14 (6 : Fin 7) (33 : ℚ) tbl16 = DfsCert.root tree16 :=
  by
    simp only [childState, DfsCert.root, tree16, node16]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node14.U (6 : Fin 7) = (5635 / 486 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node14, tbl14_c_0_6]
    norm_num [hlo]

#print axioms addEq_16_1
#print axioms addEq_16_2
#print axioms stepEq_16
#print axioms childEq_16

/-- Node 17's step (4, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_17_1 : uAdd tbl16 (6 : Fin 7) (4 : Fin 7) ((33 / 15 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_6_4] <;> norm_num)

/-- Node 17's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_17_2 : uAdd tbl16 (4 : Fin 7) (6 : Fin 7) ((17 / 33 : ℚ)) true = some tbl16 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_4_6] <;> norm_num)

/-- Node 17's full step equation. -/
theorem stepEq_17 : uStep tbl16 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl17 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_17_1 addEq_17_2

/-- Node 17's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_17 : childState (boxN m4res_1_1_4_5_6_8_12) node16 (4 : Fin 7) (17 : ℚ) tbl17 = DfsCert.root tree17 :=
  by
    simp only [childState, DfsCert.root, tree17, node17]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node16.U (4 : Fin 7) = (35 / 6 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node16, tbl16_c_0_4]
    norm_num [hlo]

#print axioms addEq_17_1
#print axioms addEq_17_2
#print axioms stepEq_17
#print axioms childEq_17

/-- Node 18's step (6, 15, 17): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_18_1 : uAdd tbl1 (4 : Fin 7) (6 : Fin 7) ((9 / 15 : ℚ)) true = some tbl1 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_6] <;> norm_num)

/-- Node 18's step: add 2 propagates to the child table. -/
theorem addEq_18_2 : uAdd tbl1 (6 : Fin 7) (4 : Fin 7) ((17 / 9 : ℚ)) true = some tbl18 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl1_c_6_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl1_c_4_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl1, tbl18] <;> norm_num)

/-- Node 18's full step equation. -/
theorem stepEq_18 : uStep tbl1 (4 : Fin 7) (6 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl18 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_18_1 addEq_18_2

/-- Node 18's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_18 : childState (boxN m4res_1_1_4_5_6_8_12) node1 (6 : Fin 7) (17 : ℚ) tbl18 = DfsCert.root tree18 :=
  by
    simp only [childState, DfsCert.root, tree18, node18]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node1.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node1, tbl1_c_0_6]
    norm_num [hlo]

#print axioms addEq_18_1
#print axioms addEq_18_2
#print axioms stepEq_18
#print axioms childEq_18

/-- Node 19's step (3, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_19_1 : uAdd tbl18 (6 : Fin 7) (3 : Fin 7) ((17 / 7 : ℚ)) true = some tbl19 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl18_c_6_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl18_c_3_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl18, tbl19] <;> norm_num)

/-- Node 19's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_19_2 : uAdd tbl19 (3 : Fin 7) (6 : Fin 7) ((9 / 17 : ℚ)) true = some tbl19 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_3_6] <;> norm_num)

/-- Node 19's full step equation. -/
theorem stepEq_19 : uStep tbl18 (6 : Fin 7) (3 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl19 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_19_1 addEq_19_2

/-- Node 19's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_19 : childState (boxN m4res_1_1_4_5_6_8_12) node18 (3 : Fin 7) (9 : ℚ) tbl19 = DfsCert.root tree19 :=
  by
    simp only [childState, DfsCert.root, tree19, node19]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node18.U (3 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node18, tbl18_c_0_3]
    norm_num [hlo]

#print axioms addEq_19_1
#print axioms addEq_19_2
#print axioms stepEq_19
#print axioms childEq_19

/-- Node 20's step (2, 7, 9): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_20_1 : uAdd tbl19 (3 : Fin 7) (2 : Fin 7) ((9 / 7 : ℚ)) true = some tbl20 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl19_c_3_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_2_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl19, tbl20] <;> norm_num)

/-- Node 20's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_20_2 : uAdd tbl20 (2 : Fin 7) (3 : Fin 7) ((9 / 9 : ℚ)) true = some tbl20 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_3] <;> norm_num)

/-- Node 20's full step equation. -/
theorem stepEq_20 : uStep tbl19 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl20 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_20_1 addEq_20_2

/-- Node 20's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_20 : childState (boxN m4res_1_1_4_5_6_8_12) node19 (2 : Fin 7) (9 : ℚ) tbl20 = DfsCert.root tree20 :=
  by
    simp only [childState, DfsCert.root, tree20, node20]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node19.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node19, tbl19_c_0_2]
    norm_num [hlo]

#print axioms addEq_20_1
#print axioms addEq_20_2
#print axioms stepEq_20
#print axioms childEq_20

/-- Node 21's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_21_1 : uAdd tbl20 (2 : Fin 7) (4 : Fin 7) ((9 / 15 : ℚ)) true = some tbl21 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl20_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl20, tbl21] <;> norm_num)

/-- Node 21's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_21_2 : uAdd tbl21 (4 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl21 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_2] <;> norm_num)

/-- Node 21's full step equation. -/
theorem stepEq_21 : uStep tbl20 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl21 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_21_1 addEq_21_2

/-- Node 21's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_21 : childState (boxN m4res_1_1_4_5_6_8_12) node20 (4 : Fin 7) (17 : ℚ) tbl21 = DfsCert.root tree21 :=
  by
    simp only [childState, DfsCert.root, tree21, node21]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node20.U (4 : Fin 7) = (207 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node20, tbl20_c_0_4]
    norm_num [hlo]

#print axioms addEq_21_1
#print axioms addEq_21_2
#print axioms stepEq_21
#print axioms childEq_21

/-- Node 22's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_22_1 : uAdd tbl21 (4 : Fin 7) (6 : Fin 7) ((17 / 31 : ℚ)) true = some tbl22 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl21_c_4_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl21_c_6_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl21, tbl22] <;> norm_num)

/-- Node 22's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_22_2 : uAdd tbl22 (6 : Fin 7) (4 : Fin 7) ((33 / 17 : ℚ)) true = some tbl22 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_6_4] <;> norm_num)

/-- Node 22's full step equation. -/
theorem stepEq_22 : uStep tbl21 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl22 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_22_1 addEq_22_2

/-- Node 22's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_22 : childState (boxN m4res_1_1_4_5_6_8_12) node21 (6 : Fin 7) (33 : ℚ) tbl22 = DfsCert.root tree22 :=
  by
    simp only [childState, DfsCert.root, tree22, node22]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node21.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node21, tbl21_c_0_6]
    norm_num [hlo]

#print axioms addEq_22_1
#print axioms addEq_22_2
#print axioms stepEq_22
#print axioms childEq_22

/-- Node 23's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_23_1 : uAdd tbl22 (6 : Fin 7) (5 : Fin 7) ((33 / 23 : ℚ)) true = some tbl23 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl22_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl22_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl22, tbl23] <;> norm_num)

/-- Node 23's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_23_2 : uAdd tbl23 (5 : Fin 7) (6 : Fin 7) ((25 / 33 : ℚ)) true = some tbl23 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl23_c_5_6] <;> norm_num)

/-- Node 23's full step equation. -/
theorem stepEq_23 : uStep tbl22 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl23 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_23_1 addEq_23_2

/-- Node 23's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_23 : childState (boxN m4res_1_1_4_5_6_8_12) node22 (5 : Fin 7) (25 : ℚ) tbl23 = DfsCert.root tree23 :=
  by
    simp only [childState, DfsCert.root, tree23, node23]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node22.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node22, tbl22_c_0_5]
    norm_num [hlo]

#print axioms addEq_23_1
#print axioms addEq_23_2
#print axioms stepEq_23
#print axioms childEq_23

/-- Node 24's step (3, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_24_1 : uAdd tbl23 (5 : Fin 7) (3 : Fin 7) ((25 / 15 : ℚ)) true = some tbl24 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl23_c_5_3] <;> norm_num)
    (by simp [uBack, uBackCond, tbl23_c_3_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl23, tbl24] <;> norm_num)

/-- Node 24's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_24_2 : uAdd tbl24 (3 : Fin 7) (5 : Fin 7) ((17 / 25 : ℚ)) true = some tbl24 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl24_c_3_5] <;> norm_num)

/-- Node 24's full step equation. -/
theorem stepEq_24 : uStep tbl23 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl24 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_24_1 addEq_24_2

/-- Node 24's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_24 : childState (boxN m4res_1_1_4_5_6_8_12) node23 (3 : Fin 7) (17 : ℚ) tbl24 = DfsCert.root tree24 :=
  by
    simp only [childState, DfsCert.root, tree24, node24]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node23.U (3 : Fin 7) = (161 / 34 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node23, tbl23_c_0_3]
    norm_num [hlo]

#print axioms addEq_24_1
#print axioms addEq_24_2
#print axioms stepEq_24
#print axioms childEq_24

/-- Node 25's step (5, 15, 17): add 1 propagates to the intermediate table tblS25 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_25_1 : uAdd tbl20 (2 : Fin 7) (5 : Fin 7) ((9 / 15 : ℚ)) true = some tblS25 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl20_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl20, tblS25] <;> norm_num)

/-- Node 25's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_25_2 : uAdd tblS25 (5 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl25 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS25_c_5_2] <;> norm_num)
    (by simp [uBack, uBackCond, tblS25_c_2_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS25, tbl25] <;> norm_num)

/-- Node 25's full step equation. -/
theorem stepEq_25 : uStep tbl20 (2 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl25 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_25_1 addEq_25_2

/-- Node 25's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_25 : childState (boxN m4res_1_1_4_5_6_8_12) node20 (5 : Fin 7) (17 : ℚ) tbl25 = DfsCert.root tree25 :=
  by
    simp only [childState, DfsCert.root, tree25, node25]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node20.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node20, tbl20_c_0_5]
    norm_num [hlo]

#print axioms addEq_25_1
#print axioms addEq_25_2
#print axioms stepEq_25
#print axioms childEq_25

/-- Node 26's step (6, 23, 25): add 1 propagates to the intermediate table tblS26 (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_26_1 : uAdd tbl20 (2 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tblS26 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl20_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl20_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl20, tblS26] <;> norm_num)

/-- Node 26's step: add 2 propagates the intermediate table to the child table. -/
theorem addEq_26_2 : uAdd tblS26 (6 : Fin 7) (2 : Fin 7) ((25 / 9 : ℚ)) true = some tbl26 :=
  uAdd_eq_some
    (by simp [uKeepCur, tblS26_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tblS26_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tblS26, tbl26] <;> norm_num)

/-- Node 26's full step equation. -/
theorem stepEq_26 : uStep tbl20 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl26 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_26_1 addEq_26_2

/-- Node 26's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_26 : childState (boxN m4res_1_1_4_5_6_8_12) node20 (6 : Fin 7) (25 : ℚ) tbl26 = DfsCert.root tree26 :=
  by
    simp only [childState, DfsCert.root, tree26, node26]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node20.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node20, tbl20_c_0_6]
    norm_num [hlo]

#print axioms addEq_26_1
#print axioms addEq_26_2
#print axioms stepEq_26
#print axioms childEq_26

/-- Node 27's step (5, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_27_1 : uAdd tbl19 (3 : Fin 7) (5 : Fin 7) ((9 / 15 : ℚ)) true = some tbl27 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl19_c_3_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl19_c_5_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl19, tbl27] <;> norm_num)

/-- Node 27's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_27_2 : uAdd tbl27 (5 : Fin 7) (3 : Fin 7) ((17 / 9 : ℚ)) true = some tbl27 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl27_c_5_3] <;> norm_num)

/-- Node 27's full step equation. -/
theorem stepEq_27 : uStep tbl19 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl27 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_27_1 addEq_27_2

/-- Node 27's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_27 : childState (boxN m4res_1_1_4_5_6_8_12) node19 (5 : Fin 7) (17 : ℚ) tbl27 = DfsCert.root tree27 :=
  by
    simp only [childState, DfsCert.root, tree27, node27]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node19.U (5 : Fin 7) = (15 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node19, tbl19_c_0_5]
    norm_num [hlo]

#print axioms addEq_27_1
#print axioms addEq_27_2
#print axioms stepEq_27
#print axioms childEq_27

/-- Node 28's step (2, 7, 9): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_28_1 : uAdd tbl27 (5 : Fin 7) (2 : Fin 7) ((17 / 7 : ℚ)) true = some tbl27 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl27_c_5_2] <;> norm_num)

/-- Node 28's step: add 2 propagates to the child table. -/
theorem addEq_28_2 : uAdd tbl27 (2 : Fin 7) (5 : Fin 7) ((9 / 17 : ℚ)) true = some tbl28 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl27_c_2_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl27_c_5_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl27, tbl28] <;> norm_num)

/-- Node 28's full step equation. -/
theorem stepEq_28 : uStep tbl27 (5 : Fin 7) (2 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl28 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_28_1 addEq_28_2

/-- Node 28's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_28 : childState (boxN m4res_1_1_4_5_6_8_12) node27 (2 : Fin 7) (9 : ℚ) tbl28 = DfsCert.root tree28 :=
  by
    simp only [childState, DfsCert.root, tree28, node28]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node27.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node27, tbl27_c_0_2]
    norm_num [hlo]

#print axioms addEq_28_1
#print axioms addEq_28_2
#print axioms stepEq_28
#print axioms childEq_28

/-- Node 29's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_29_1 : uAdd tbl28 (2 : Fin 7) (4 : Fin 7) ((9 / 15 : ℚ)) true = some tbl29 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl28_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl28_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl28, tbl29] <;> norm_num)

/-- Node 29's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_29_2 : uAdd tbl29 (4 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl29 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl29_c_4_2] <;> norm_num)

/-- Node 29's full step equation. -/
theorem stepEq_29 : uStep tbl28 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl29 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_29_1 addEq_29_2

/-- Node 29's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_29 : childState (boxN m4res_1_1_4_5_6_8_12) node28 (4 : Fin 7) (17 : ℚ) tbl29 = DfsCert.root tree29 :=
  by
    simp only [childState, DfsCert.root, tree29, node29]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node28.U (4 : Fin 7) = (5635 / 918 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node28, tbl28_c_0_4]
    norm_num [hlo]

#print axioms addEq_29_1
#print axioms addEq_29_2
#print axioms stepEq_29
#print axioms childEq_29

/-- Node 30's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_30_1 : uAdd tbl29 (4 : Fin 7) (6 : Fin 7) ((17 / 31 : ℚ)) true = some tbl30 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl29_c_4_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl29_c_6_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl29, tbl30] <;> norm_num)

/-- Node 30's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_30_2 : uAdd tbl30 (6 : Fin 7) (4 : Fin 7) ((33 / 17 : ℚ)) true = some tbl30 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl30_c_6_4] <;> norm_num)

/-- Node 30's full step equation. -/
theorem stepEq_30 : uStep tbl29 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl30 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_30_1 addEq_30_2

/-- Node 30's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_30 : childState (boxN m4res_1_1_4_5_6_8_12) node29 (6 : Fin 7) (33 : ℚ) tbl30 = DfsCert.root tree30 :=
  by
    simp only [childState, DfsCert.root, tree30, node30]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node29.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node29, tbl29_c_0_6]
    norm_num [hlo]

#print axioms addEq_30_1
#print axioms addEq_30_2
#print axioms stepEq_30
#print axioms childEq_30

/-- Node 31's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_31_1 : uAdd tbl30 (6 : Fin 7) (5 : Fin 7) ((33 / 23 : ℚ)) true = some tbl31 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl30_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl30_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl30, tbl31] <;> norm_num)

/-- Node 31's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_31_2 : uAdd tbl31 (5 : Fin 7) (6 : Fin 7) ((25 / 33 : ℚ)) true = some tbl31 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl31_c_5_6] <;> norm_num)

/-- Node 31's full step equation. -/
theorem stepEq_31 : uStep tbl30 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl31 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_31_1 addEq_31_2

/-- Node 31's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_31 : childState (boxN m4res_1_1_4_5_6_8_12) node30 (5 : Fin 7) (25 : ℚ) tbl31 = DfsCert.root tree31 :=
  by
    simp only [childState, DfsCert.root, tree31, node31]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node30.U (5 : Fin 7) = (805 / 102 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node30, tbl30_c_0_5]
    norm_num [hlo]

#print axioms addEq_31_1
#print axioms addEq_31_2
#print axioms stepEq_31
#print axioms childEq_31

/-- Node 32's step (6, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_32_1 : uAdd tbl28 (2 : Fin 7) (6 : Fin 7) ((9 / 23 : ℚ)) true = some tbl28 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl28_c_2_6] <;> norm_num)

/-- Node 32's step: add 2 propagates to the child table. -/
theorem addEq_32_2 : uAdd tbl28 (6 : Fin 7) (2 : Fin 7) ((25 / 9 : ℚ)) true = some tbl32 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl28_c_6_2] <;> norm_num)
    (by simp [uBack, uBackCond, tbl28_c_2_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl28, tbl32] <;> norm_num)

/-- Node 32's full step equation. -/
theorem stepEq_32 : uStep tbl28 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl32 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_32_1 addEq_32_2

/-- Node 32's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_32 : childState (boxN m4res_1_1_4_5_6_8_12) node28 (6 : Fin 7) (25 : ℚ) tbl32 = DfsCert.root tree32 :=
  by
    simp only [childState, DfsCert.root, tree32, node32]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node28.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node28, tbl28_c_0_6]
    norm_num [hlo]

#print axioms addEq_32_1
#print axioms addEq_32_2
#print axioms stepEq_32
#print axioms childEq_32

/-- Node 33's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_33_1 : uAdd tbl28 (2 : Fin 7) (6 : Fin 7) ((9 / 31 : ℚ)) true = some tbl33 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl28_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl28_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl28, tbl33] <;> norm_num)

/-- Node 33's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_33_2 : uAdd tbl33 (6 : Fin 7) (2 : Fin 7) ((33 / 9 : ℚ)) true = some tbl33 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl33_c_6_2] <;> norm_num)

/-- Node 33's full step equation. -/
theorem stepEq_33 : uStep tbl28 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl33 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_33_1 addEq_33_2

/-- Node 33's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_33 : childState (boxN m4res_1_1_4_5_6_8_12) node28 (6 : Fin 7) (33 : ℚ) tbl33 = DfsCert.root tree33 :=
  by
    simp only [childState, DfsCert.root, tree33, node33]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node28.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node28, tbl28_c_0_6]
    norm_num [hlo]

#print axioms addEq_33_1
#print axioms addEq_33_2
#print axioms stepEq_33
#print axioms childEq_33

/-- Node 34's step (6, 23, 25): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_34_1 : uAdd tbl27 (5 : Fin 7) (6 : Fin 7) ((17 / 23 : ℚ)) true = some tbl27 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl27_c_5_6] <;> norm_num)

/-- Node 34's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_34_2 : uAdd tbl27 (6 : Fin 7) (5 : Fin 7) ((25 / 17 : ℚ)) true = some tbl27 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl27_c_6_5] <;> norm_num)

/-- Node 34's full step equation. -/
theorem stepEq_34 : uStep tbl27 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl34 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_34_1 addEq_34_2

/-- Node 34's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_34 : childState (boxN m4res_1_1_4_5_6_8_12) node27 (6 : Fin 7) (25 : ℚ) tbl34 = DfsCert.root tree34 :=
  by
    simp only [childState, DfsCert.root, tree34, node34]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node27.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node27, tbl27_c_0_6]
    norm_num [hlo]

#print axioms addEq_34_1
#print axioms addEq_34_2
#print axioms stepEq_34
#print axioms childEq_34

/-- Node 35's step (2, 7, 9): add 1 is keep-current (the
stored bound is already tighter, table unchanged). -/
theorem addEq_35_1 : uAdd tbl34 (6 : Fin 7) (2 : Fin 7) ((25 / 7 : ℚ)) true = some tbl34 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl34_c_6_2] <;> norm_num)

/-- Node 35's step: add 2 propagates to the child table. -/
theorem addEq_35_2 : uAdd tbl34 (2 : Fin 7) (6 : Fin 7) ((9 / 25 : ℚ)) true = some tbl35 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl34_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl34_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl34, tbl35] <;> norm_num)

/-- Node 35's full step equation. -/
theorem stepEq_35 : uStep tbl34 (6 : Fin 7) (2 : Fin 7) (25 : ℚ) (7 : ℚ) (9 : ℚ) = some tbl35 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_35_1 addEq_35_2

/-- Node 35's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_35 : childState (boxN m4res_1_1_4_5_6_8_12) node34 (2 : Fin 7) (9 : ℚ) tbl35 = DfsCert.root tree35 :=
  by
    simp only [childState, DfsCert.root, tree35, node35]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node34.U (2 : Fin 7) = (7 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node34, tbl34_c_0_2]
    norm_num [hlo]

#print axioms addEq_35_1
#print axioms addEq_35_2
#print axioms stepEq_35
#print axioms childEq_35

/-- Node 36's step (4, 15, 17): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_36_1 : uAdd tbl35 (2 : Fin 7) (4 : Fin 7) ((9 / 15 : ℚ)) true = some tbl36 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl35_c_2_4] <;> norm_num)
    (by simp [uBack, uBackCond, tbl35_c_4_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl35, tbl36] <;> norm_num)

/-- Node 36's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_36_2 : uAdd tbl36 (4 : Fin 7) (2 : Fin 7) ((17 / 9 : ℚ)) true = some tbl36 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl36_c_4_2] <;> norm_num)

/-- Node 36's full step equation. -/
theorem stepEq_36 : uStep tbl35 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some tbl36 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_36_1 addEq_36_2

/-- Node 36's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_36 : childState (boxN m4res_1_1_4_5_6_8_12) node35 (4 : Fin 7) (17 : ℚ) tbl36 = DfsCert.root tree36 :=
  by
    simp only [childState, DfsCert.root, tree36, node36]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node35.U (4 : Fin 7) = (5635 / 918 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node35, tbl35_c_0_4]
    norm_num [hlo]

#print axioms addEq_36_1
#print axioms addEq_36_2
#print axioms stepEq_36
#print axioms childEq_36

/-- Node 37's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_37_1 : uAdd tbl36 (4 : Fin 7) (6 : Fin 7) ((17 / 31 : ℚ)) true = some tbl37 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl36_c_4_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl36_c_6_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl36, tbl37] <;> norm_num)

/-- Node 37's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_37_2 : uAdd tbl37 (6 : Fin 7) (4 : Fin 7) ((33 / 17 : ℚ)) true = some tbl37 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl37_c_6_4] <;> norm_num)

/-- Node 37's full step equation. -/
theorem stepEq_37 : uStep tbl36 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl37 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_37_1 addEq_37_2

/-- Node 37's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_37 : childState (boxN m4res_1_1_4_5_6_8_12) node36 (6 : Fin 7) (33 : ℚ) tbl37 = DfsCert.root tree37 :=
  by
    simp only [childState, DfsCert.root, tree37, node37]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node36.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node36, tbl36_c_0_6]
    norm_num [hlo]

#print axioms addEq_37_1
#print axioms addEq_37_2
#print axioms stepEq_37
#print axioms childEq_37

/-- Node 38's step (5, 23, 25): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_38_1 : uAdd tbl37 (6 : Fin 7) (5 : Fin 7) ((33 / 23 : ℚ)) true = some tbl38 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl37_c_6_5] <;> norm_num)
    (by simp [uBack, uBackCond, tbl37_c_5_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl37, tbl38] <;> norm_num)

/-- Node 38's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_38_2 : uAdd tbl38 (5 : Fin 7) (6 : Fin 7) ((25 / 33 : ℚ)) true = some tbl38 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl38_c_5_6] <;> norm_num)

/-- Node 38's full step equation. -/
theorem stepEq_38 : uStep tbl37 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some tbl38 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_38_1 addEq_38_2

/-- Node 38's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_38 : childState (boxN m4res_1_1_4_5_6_8_12) node37 (5 : Fin 7) (25 : ℚ) tbl38 = DfsCert.root tree38 :=
  by
    simp only [childState, DfsCert.root, tree38, node38]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node37.U (5 : Fin 7) = (805 / 102 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node37, tbl37_c_0_5]
    norm_num [hlo]

#print axioms addEq_38_1
#print axioms addEq_38_2
#print axioms stepEq_38
#print axioms childEq_38

/-- Node 39's step (6, 31, 33): add 1 propagates the parent table to the child table (the two-cycle check is
ground-false on the exact cells). -/
theorem addEq_39_1 : uAdd tbl35 (2 : Fin 7) (6 : Fin 7) ((9 / 31 : ℚ)) true = some tbl39 :=
  uAdd_eq_some
    (by simp [uKeepCur, tbl35_c_2_6] <;> norm_num)
    (by simp [uBack, uBackCond, tbl35_c_6_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, tbl35, tbl39] <;> norm_num)

/-- Node 39's step: add 2 is keep-current (the stored bound is already tighter), so the table is unchanged. -/
theorem addEq_39_2 : uAdd tbl39 (6 : Fin 7) (2 : Fin 7) ((33 / 9 : ℚ)) true = some tbl39 :=
  uAdd_eq_some_self (by simp [uKeepCur, tbl39_c_6_2] <;> norm_num)

/-- Node 39's full step equation. -/
theorem stepEq_39 : uStep tbl35 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (31 : ℚ) (33 : ℚ) = some tbl39 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) addEq_39_1 addEq_39_2

/-- Node 39's `childState` equation: the child node is exactly the DFS expansion
rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent
set plus the step pair). -/
theorem childEq_39 : childState (boxN m4res_1_1_4_5_6_8_12) node35 (6 : Fin 7) (33 : ℚ) tbl39 = DfsCert.root tree39 :=
  by
    simp only [childState, DfsCert.root, tree39, node39]
    have hlo : dfsLo (boxN m4res_1_1_4_5_6_8_12) node35.U (6 : Fin 7) = (23 / 2 : ℚ) :=
      by norm_num [dfsLo, boxN, m4res_1_1_4_5_6_8_12, node35, tbl35_c_0_6]
    norm_num [hlo]

#print axioms addEq_39_1
#print axioms addEq_39_2
#print axioms stepEq_39
#print axioms childEq_39

/-! ## 3b. The seam kills -/

/-- Seam-failure kills at node 0 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk0_seam_6_1 : uStep tbl0 (5 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl0 (5 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl0 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl0_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl0_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl0_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 1 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk1_seam_2_1 : uStep tbl1 (4 : Fin 7) (2 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl1_c_4_2] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl1_c_2_4] <;> norm_num

theorem sk1_seam_6_1 : uStep tbl1 (4 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl1 (4 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl1 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl1_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl1_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl1_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 2 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk2_seam_5_2 : uStep tbl2 (3 : Fin 7) (5 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl2_c_3_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl2_c_5_3] <;> norm_num

theorem sk2_seam_6_1 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_6] <;> norm_num)

theorem sk2_seam_6_2 : uStep tbl2 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl2 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl2 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl2_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl2_c_3_6] <;> norm_num)


/-- Seam-failure kills at node 3 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk3_seam_0_1 : uStep tbl3 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl3_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl3_c_0_2] <;> norm_num

theorem sk3_seam_4_2 : uStep tbl3 (2 : Fin 7) (4 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl3_c_2_4] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl3_c_4_2] <;> norm_num

theorem sk3_seam_6_1 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_6] <;> norm_num)

theorem sk3_seam_6_2 : uStep tbl3 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl3 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl3 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl3_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl3_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl3_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 7 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk7_seam_6_1 : uStep tbl7 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl7 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl7 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl7_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl7_c_6_6] <;> norm_num)

theorem sk7_seam_6_2 : uStep tbl7 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl7 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl7 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl7_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl7_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl7_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 8 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk8_seam_0_1 : uStep tbl8 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl8_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl8_c_0_2] <;> norm_num

theorem sk8_seam_6_1 : uStep tbl8 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl8 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl8 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl8_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl8_c_2_6] <;> norm_num)

theorem sk8_seam_6_2 : uStep tbl8 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl8 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl8 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl8_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl8_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl8_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 9 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk9_seam_0_1 : uStep tbl9 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl9_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl9_c_0_4] <;> norm_num

theorem sk9_seam_5_2 : uStep tbl9 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_4_5] <;> norm_num)

theorem sk9_seam_5_3 : uStep tbl9 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl9_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl9_c_5_4] <;> norm_num

theorem sk9_seam_6_1 : uStep tbl9 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_4_6] <;> norm_num)

theorem sk9_seam_6_2 : uStep tbl9 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_4_6] <;> norm_num)

theorem sk9_seam_6_4 : uStep tbl9 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl9 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tbl9 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl9_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl9_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl9_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 11 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk11_seam_0_1 : uStep tbl11 (6 : Fin 7) (0 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl11_c_6_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl11_c_0_6] <;> norm_num

theorem sk11_seam_5_2 : uStep tbl11 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl11 (6 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl11 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl11_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl11_c_6_5] <;> norm_num)

theorem sk11_seam_5_3 : uStep tbl11 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl11_c_6_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl11_c_5_6] <;> norm_num

theorem sk11_seam_6_1 : uStep tbl11 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl11 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl11 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl11_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl11_c_6_6] <;> norm_num)

theorem sk11_seam_6_2 : uStep tbl11 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl11 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl11 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl11_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl11_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl11_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 12 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk12_seam_0_1 : uStep tbl12 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl12_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl12_c_0_4] <;> norm_num

theorem sk12_seam_5_2 : uStep tbl12 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_4_5] <;> norm_num)

theorem sk12_seam_5_3 : uStep tbl12 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl12_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl12_c_5_4] <;> norm_num

theorem sk12_seam_6_1 : uStep tbl12 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_4_6] <;> norm_num)

theorem sk12_seam_6_2 : uStep tbl12 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl12 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl12 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl12_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl12_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl12_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 13 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk13_seam_6_1 : uStep tbl13 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_6] <;> norm_num)

theorem sk13_seam_6_2 : uStep tbl13 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl13 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl13 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl13_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl13_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl13_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 14 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk14_seam_0_1 : uStep tbl14 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl14_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl14_c_0_2] <;> norm_num

theorem sk14_seam_6_1 : uStep tbl14 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_2_6] <;> norm_num)

theorem sk14_seam_6_2 : uStep tbl14 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl14 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl14 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl14_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl14_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl14_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 15 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk15_seam_0_1 : uStep tbl15 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl15_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl15_c_0_4] <;> norm_num

theorem sk15_seam_5_3 : uStep tbl15 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl15_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl15_c_5_4] <;> norm_num

theorem sk15_seam_6_1 : uStep tbl15 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_4_6] <;> norm_num)

theorem sk15_seam_6_2 : uStep tbl15 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_4_6] <;> norm_num)

theorem sk15_seam_6_4 : uStep tbl15 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl15 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 4 - 1 : ℕ) : ℚ))) true = some tbl15 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl15_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl15_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl15_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 16 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk16_seam_0_1 : uStep tbl16 (6 : Fin 7) (0 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl16_c_6_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl16_c_0_6] <;> norm_num

theorem sk16_seam_5_3 : uStep tbl16 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl16_c_6_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl16_c_5_6] <;> norm_num

theorem sk16_seam_6_1 : uStep tbl16 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_6_6] <;> norm_num)

theorem sk16_seam_6_2 : uStep tbl16 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl16 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl16 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl16_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl16_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl16_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 17 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk17_seam_0_1 : uStep tbl17 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl17_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl17_c_0_4] <;> norm_num

theorem sk17_seam_5_3 : uStep tbl17 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl17_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl17_c_5_4] <;> norm_num

theorem sk17_seam_6_1 : uStep tbl17 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_4_6] <;> norm_num)

theorem sk17_seam_6_2 : uStep tbl17 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl17 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl17 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl17_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl17_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl17_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 18 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk18_seam_6_1 : uStep tbl18 (6 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl18 (6 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl18 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl18_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl18_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl18_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 19 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk19_seam_6_1 : uStep tbl19 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl19 (3 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl19 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl19_c_3_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl19_c_6_3] <;> norm_num)
      (by simp [uBack, uBackCond, tbl19_c_3_6] <;> norm_num)

theorem sk19_seam_6_3 : uStep tbl19 (3 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl19_c_3_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl19_c_6_3] <;> norm_num


/-- Seam-failure kills at node 20 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk20_seam_0_1 : uStep tbl20 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl20_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl20_c_0_2] <;> norm_num

theorem sk20_seam_6_1 : uStep tbl20 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl20 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl20 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl20_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl20_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl20_c_2_6] <;> norm_num)

theorem sk20_seam_6_4 : uStep tbl20 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 4 - 1 : ℕ) : ℚ)) (((8 * 4 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl20_c_2_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl20_c_6_2] <;> norm_num


/-- Seam-failure kills at node 21 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk21_seam_0_1 : uStep tbl21 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl21_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl21_c_0_4] <;> norm_num

theorem sk21_seam_5_2 : uStep tbl21 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_5_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_5] <;> norm_num)

theorem sk21_seam_5_3 : uStep tbl21 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl21_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl21_c_5_4] <;> norm_num

theorem sk21_seam_6_1 : uStep tbl21 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_6] <;> norm_num)

theorem sk21_seam_6_3 : uStep tbl21 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl21 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl21 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl21_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl21_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl21_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 22 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk22_seam_0_1 : uStep tbl22 (6 : Fin 7) (0 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl22_c_6_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl22_c_0_6] <;> norm_num

theorem sk22_seam_5_2 : uStep tbl22 (6 : Fin 7) (5 : Fin 7) (33 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (6 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_6_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_5_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_6_5] <;> norm_num)

theorem sk22_seam_6_1 : uStep tbl22 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_6_6] <;> norm_num)

theorem sk22_seam_6_3 : uStep tbl22 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl22 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl22 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl22_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl22_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl22_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 23 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk23_seam_0_1 : uStep tbl23 (5 : Fin 7) (0 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl23_c_5_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl23_c_0_5] <;> norm_num

theorem sk23_seam_5_2 : uStep tbl23 (5 : Fin 7) (5 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl23 (5 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (((8 * 2 - 1 : ℕ) : ℚ))) true = some tbl23 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl23_c_5_5] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl23_c_5_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl23_c_5_5] <;> norm_num)

theorem sk23_seam_6_1 : uStep tbl23 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl23 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl23 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl23_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl23_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl23_c_5_6] <;> norm_num)

theorem sk23_seam_6_3 : uStep tbl23 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl23 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl23 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl23_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl23_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl23_c_5_6] <;> norm_num)

theorem sk23_seam_6_5 : uStep tbl23 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 5 - 1 : ℕ) : ℚ)) (((8 * 5 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl23_c_5_6] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl23_c_6_5] <;> norm_num


/-- Seam-failure kills at node 27 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk27_seam_6_1 : uStep tbl27 (5 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl27 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl27 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl27_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl27_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl27_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 28 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk28_seam_0_1 : uStep tbl28 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl28_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl28_c_0_2] <;> norm_num

theorem sk28_seam_6_1 : uStep tbl28 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl28 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl28 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl28_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl28_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl28_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 29 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk29_seam_0_1 : uStep tbl29 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl29_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl29_c_0_4] <;> norm_num

theorem sk29_seam_5_3 : uStep tbl29 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl29_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl29_c_5_4] <;> norm_num

theorem sk29_seam_6_1 : uStep tbl29 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl29 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl29 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl29_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl29_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl29_c_4_6] <;> norm_num)

theorem sk29_seam_6_3 : uStep tbl29 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl29 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl29 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl29_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl29_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl29_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 30 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk30_seam_0_1 : uStep tbl30 (6 : Fin 7) (0 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl30_c_6_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl30_c_0_6] <;> norm_num

theorem sk30_seam_6_1 : uStep tbl30 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl30 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl30 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl30_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl30_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl30_c_6_6] <;> norm_num)

theorem sk30_seam_6_3 : uStep tbl30 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl30 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl30 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl30_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl30_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl30_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 31 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk31_seam_0_1 : uStep tbl31 (5 : Fin 7) (0 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl31_c_5_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl31_c_0_5] <;> norm_num

theorem sk31_seam_3_2 : uStep tbl31 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl31_c_5_3] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl31_c_3_5] <;> norm_num

theorem sk31_seam_6_1 : uStep tbl31 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl31 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl31 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl31_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl31_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl31_c_5_6] <;> norm_num)

theorem sk31_seam_6_3 : uStep tbl31 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl31 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 3 - 1 : ℕ) : ℚ))) true = some tbl31 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl31_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl31_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl31_c_5_6] <;> norm_num)


/-- Seam-failure kills at node 34 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk34_seam_6_1 : uStep tbl34 (6 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl34 (6 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl34 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl34_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl34_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl34_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 35 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk35_seam_0_1 : uStep tbl35 (2 : Fin 7) (0 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl35_c_2_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl35_c_0_2] <;> norm_num

theorem sk35_seam_6_1 : uStep tbl35 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl35 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl35 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl35_c_2_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl35_c_6_2] <;> norm_num)
      (by simp [uBack, uBackCond, tbl35_c_2_6] <;> norm_num)


/-- Seam-failure kills at node 36 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk36_seam_0_1 : uStep tbl36 (4 : Fin 7) (0 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl36_c_4_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl36_c_0_4] <;> norm_num

theorem sk36_seam_5_3 : uStep tbl36 (4 : Fin 7) (5 : Fin 7) (17 : ℚ) (((8 * 3 - 1 : ℕ) : ℚ)) (((8 * 3 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl36_c_4_5] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl36_c_5_4] <;> norm_num

theorem sk36_seam_6_1 : uStep tbl36 (4 : Fin 7) (6 : Fin 7) (17 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl36 (4 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl36 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl36_c_4_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl36_c_6_4] <;> norm_num)
      (by simp [uBack, uBackCond, tbl36_c_4_6] <;> norm_num)


/-- Seam-failure kills at node 37 (internal): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk37_seam_0_1 : uStep tbl37 (6 : Fin 7) (0 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl37_c_6_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl37_c_0_6] <;> norm_num

theorem sk37_seam_6_1 : uStep tbl37 (6 : Fin 7) (6 : Fin 7) (33 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl37 (6 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl37 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl37_c_6_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl37_c_6_6] <;> norm_num)
      (by simp [uBack, uBackCond, tbl37_c_6_6] <;> norm_num)


/-- Seam-failure kills at node 38 (deadend): candidates that pass the entry and
freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated
on the literal cells). -/
theorem sk38_seam_0_1 : uStep tbl38 (5 : Fin 7) (0 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl38_c_5_0] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl38_c_0_5] <;> norm_num

theorem sk38_seam_3_2 : uStep tbl38 (5 : Fin 7) (3 : Fin 7) (25 : ℚ) (((8 * 2 - 1 : ℕ) : ℚ)) (((8 * 2 + 1 : ℕ) : ℚ)) = none := by
  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_
  refine uAdd_eq_none (by simp [uKeepCur, tbl38_c_5_3] <;> norm_num) ?_
  simp [uBack, uBackCond, tbl38_c_3_5] <;> norm_num

theorem sk38_seam_6_1 : uStep tbl38 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (((8 * 1 - 1 : ℕ) : ℚ)) (((8 * 1 + 1 : ℕ) : ℚ)) = none := by
  have h1 : uAdd tbl38 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (((8 * 1 - 1 : ℕ) : ℚ))) true = some tbl38 :=
    uAdd_eq_some_self (by simp [uKeepCur, tbl38_c_5_6] <;> norm_num)
  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_
  exact uAdd_eq_none
      (by simp [uKeepCur, tbl38_c_6_5] <;> norm_num)
      (by simp [uBack, uBackCond, tbl38_c_5_6] <;> norm_num)


#print axioms sk0_seam_6_1
#print axioms sk1_seam_2_1
#print axioms sk1_seam_6_1
#print axioms sk2_seam_5_2
#print axioms sk2_seam_6_1
#print axioms sk2_seam_6_2
#print axioms sk3_seam_0_1
#print axioms sk3_seam_4_2
#print axioms sk3_seam_6_1
#print axioms sk3_seam_6_2
#print axioms sk7_seam_6_1
#print axioms sk7_seam_6_2
#print axioms sk8_seam_0_1
#print axioms sk8_seam_6_1
#print axioms sk8_seam_6_2
#print axioms sk9_seam_0_1
#print axioms sk9_seam_5_2
#print axioms sk9_seam_5_3
#print axioms sk9_seam_6_1
#print axioms sk9_seam_6_2
#print axioms sk9_seam_6_4
#print axioms sk11_seam_0_1
#print axioms sk11_seam_5_2
#print axioms sk11_seam_5_3
#print axioms sk11_seam_6_1
#print axioms sk11_seam_6_2
#print axioms sk12_seam_0_1
#print axioms sk12_seam_5_2
#print axioms sk12_seam_5_3
#print axioms sk12_seam_6_1
#print axioms sk12_seam_6_2
#print axioms sk13_seam_6_1
#print axioms sk13_seam_6_2
#print axioms sk14_seam_0_1
#print axioms sk14_seam_6_1
#print axioms sk14_seam_6_2
#print axioms sk15_seam_0_1
#print axioms sk15_seam_5_3
#print axioms sk15_seam_6_1
#print axioms sk15_seam_6_2
#print axioms sk15_seam_6_4
#print axioms sk16_seam_0_1
#print axioms sk16_seam_5_3
#print axioms sk16_seam_6_1
#print axioms sk16_seam_6_2
#print axioms sk17_seam_0_1
#print axioms sk17_seam_5_3
#print axioms sk17_seam_6_1
#print axioms sk17_seam_6_2
#print axioms sk18_seam_6_1
#print axioms sk19_seam_6_1
#print axioms sk19_seam_6_3
#print axioms sk20_seam_0_1
#print axioms sk20_seam_6_1
#print axioms sk20_seam_6_4
#print axioms sk21_seam_0_1
#print axioms sk21_seam_5_2
#print axioms sk21_seam_5_3
#print axioms sk21_seam_6_1
#print axioms sk21_seam_6_3
#print axioms sk22_seam_0_1
#print axioms sk22_seam_5_2
#print axioms sk22_seam_6_1
#print axioms sk22_seam_6_3
#print axioms sk23_seam_0_1
#print axioms sk23_seam_5_2
#print axioms sk23_seam_6_1
#print axioms sk23_seam_6_3
#print axioms sk23_seam_6_5
#print axioms sk27_seam_6_1
#print axioms sk28_seam_0_1
#print axioms sk28_seam_6_1
#print axioms sk29_seam_0_1
#print axioms sk29_seam_5_3
#print axioms sk29_seam_6_1
#print axioms sk29_seam_6_3
#print axioms sk30_seam_0_1
#print axioms sk30_seam_6_1
#print axioms sk30_seam_6_3
#print axioms sk31_seam_0_1
#print axioms sk31_seam_3_2
#print axioms sk31_seam_6_1
#print axioms sk31_seam_6_3
#print axioms sk34_seam_6_1
#print axioms sk35_seam_0_1
#print axioms sk35_seam_6_1
#print axioms sk36_seam_0_1
#print axioms sk36_seam_5_3
#print axioms sk36_seam_6_1
#print axioms sk37_seam_0_1
#print axioms sk37_seam_6_1
#print axioms sk38_seam_0_1
#print axioms sk38_seam_3_2
#print axioms sk38_seam_6_1

/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/

/-- The `match-completeness` at node 0: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_0 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node0 b A B) : ∃ c ∈ children0, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node0 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
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

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
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

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 60)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (5 : Fin 7) = (17 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨5, by norm_num⟩ : Fin 7) = (17 / 2 : ℚ) := hval0
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

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl0_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl0 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk0_seam_6_1).elim
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
theorem enumMatch_1 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node1 b A B) : ∃ c ∈ children1, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node1 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hseam sk1_seam_2_1).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree2, by simp [children1], tbl2, stepEq_2, childEq_2⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl1_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl1 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk1_seam_6_1).elim
    · exact ⟨tree18, by simp [children1], tbl18, stepEq_18, childEq_18⟩
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
theorem enumMatch_2 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node2 b A B) : ∃ c ∈ children2, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node2 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree3, by simp [children2], tbl3, stepEq_3, childEq_3⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
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

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk2_seam_5_2).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl2_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl2 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk2_seam_6_1).elim
    · exact (hseam sk2_seam_6_2).elim
    · exact ⟨tree7, by simp [children2], tbl7, stepEq_7, childEq_7⟩
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
theorem enumMatch_3 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node3 b A B) : ∃ c ∈ children3, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node3 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk3_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
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

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk3_seam_4_2).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree4, by simp [children3], tbl4, stepEq_4, childEq_4⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node3, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl3_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl3 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk3_seam_6_1).elim
    · exact (hseam sk3_seam_6_2).elim
    · exact ⟨tree5, by simp [children3], tbl5, stepEq_5, childEq_5⟩
    · exact ⟨tree6, by simp [children3], tbl6, stepEq_6, childEq_6⟩
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
theorem enumMatch_7 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node7 b A B) : ∃ c ∈ children7, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node7 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree8, by simp [children7], tbl8, stepEq_8, childEq_8⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree13, by simp [children7], tbl13, stepEq_13, childEq_13⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl7_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl7 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk7_seam_6_1).elim
    · exact (hseam sk7_seam_6_2).elim
    · exact (hfresh (by decide)).elim
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
theorem enumMatch_8 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node8 b A B) : ∃ c ∈ children8, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node8 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk8_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree9, by simp [children8], tbl9, stepEq_9, childEq_9⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree10, by simp [children8], tbl10, stepEq_10, childEq_10⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl8_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl8 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk8_seam_6_1).elim
    · exact (hseam sk8_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree11, by simp [children8], tbl11, stepEq_11, childEq_11⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 9: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_9 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node9 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk9_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 27)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (2 : Fin 7) = (1215 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨2, by norm_num⟩ : Fin 7) = (1215 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((1215 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 27 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((1215 / 322 : ℚ)) ≤ (27 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hseam sk9_seam_5_2
    · exact hseam sk9_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node9, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl9_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl9 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk9_seam_6_1
    · exact hseam sk9_seam_6_2
    · exact hfresh (by decide)
    · exact hseam sk9_seam_6_4
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 11: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_11 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node11 b A B) : ∃ c ∈ children11, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node11 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk11_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 26)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (2 : Fin 7) = (225 / 62 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨2, by norm_num⟩ : Fin 7) = (225 / 62 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 62 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 26 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 62 : ℚ)) ≤ (26 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree12, by simp [children11], tbl12, stepEq_12, childEq_12⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk11_seam_5_2).elim
    · exact (hseam sk11_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl11_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl11 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk11_seam_6_1).elim
    · exact (hseam sk11_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 12: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_12 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node12 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk12_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 26)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (2 : Fin 7) = (225 / 62 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨2, by norm_num⟩ : Fin 7) = (225 / 62 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 62 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 26 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 62 : ℚ)) ≤ (26 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hseam sk12_seam_5_2
    · exact hseam sk12_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node12, node11, node8, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl12_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl12 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk12_seam_6_1
    · exact hseam sk12_seam_6_2
    · exact hfresh (by decide)
    · exact hfresh (by decide)
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
theorem enumMatch_13 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node13 b A B) : ∃ c ∈ children13, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node13 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree14, by simp [children13], tbl14, stepEq_14, childEq_14⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl13_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl13 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk13_seam_6_1).elim
    · exact (hseam sk13_seam_6_2).elim
    · exact (hfresh (by decide)).elim
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
theorem enumMatch_14 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node14 b A B) : ∃ c ∈ children14, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node14 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk14_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 30)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (2 : Fin 7) = (164025 / 38318 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨2, by norm_num⟩ : Fin 7) = (164025 / 38318 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((164025 / 38318 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 30 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((164025 / 38318 : ℚ)) ≤ (30 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree15, by simp [children14], tbl15, stepEq_15, childEq_15⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl14_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl14 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk14_seam_6_1).elim
    · exact (hseam sk14_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree16, by simp [children14], tbl16, stepEq_16, childEq_16⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 15: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_15 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node15 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk15_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 27)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (2 : Fin 7) = (1215 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨2, by norm_num⟩ : Fin 7) = (1215 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((1215 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 27 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((1215 / 322 : ℚ)) ≤ (27 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hseam sk15_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node15, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl15_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl15 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk15_seam_6_1
    · exact hseam sk15_seam_6_2
    · exact hfresh (by decide)
    · exact hseam sk15_seam_6_4
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
theorem enumMatch_16 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node16 b A B) : ∃ c ∈ children16, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node16 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk16_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 26)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (2 : Fin 7) = (225 / 62 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨2, by norm_num⟩ : Fin 7) = (225 / 62 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 62 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 26 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 62 : ℚ)) ≤ (26 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree17, by simp [children16], tbl17, stepEq_17, childEq_17⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk16_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl16_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl16 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact (hseam sk16_seam_6_1).elim
    · exact (hseam sk16_seam_6_2).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 17: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_17 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node17 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk17_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 26)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (2 : Fin 7) = (225 / 62 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨2, by norm_num⟩ : Fin 7) = (225 / 62 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 62 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 26 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 62 : ℚ)) ≤ (26 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 35)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (3 : Fin 7) = (225 / 46 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨3, by norm_num⟩ : Fin 7) = (225 / 46 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((225 / 46 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 35 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((225 / 46 : ℚ)) ≤ (35 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 45)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (4 : Fin 7) = (2025 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨4, by norm_num⟩ : Fin 7) = (2025 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((2025 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 45 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((2025 / 322 : ℚ)) ≤ (45 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 57)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (5 : Fin 7) = (18225 / 2254 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨5, by norm_num⟩ : Fin 7) = (18225 / 2254 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((18225 / 2254 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 57 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((18225 / 2254 : ℚ)) ≤ (57 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hseam sk17_seam_5_3
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 11, M = ceil(7·hi) = 88)
    simp only [node17, node16, node14, node13, node7, node2, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (6 : Fin 7) = (25 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl17_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl17 (⟨6, by norm_num⟩ : Fin 7) = (25 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((25 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 88 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((25 / 2 : ℚ)) ≤ (88 : ℚ))
    have h8 : j ≤ 11 := by omega
    interval_cases j
    · exact hseam sk17_seam_6_1
    · exact hseam sk17_seam_6_2
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 18: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_18 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node18 b A B) : ∃ c ∈ children18, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node18 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
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

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((11 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 39 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((11 / 2 : ℚ)) ≤ (39 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree19, by simp [children18], tbl19, stepEq_19, childEq_19⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (6 : Fin 7) = (221 / 18 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl18_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl18 (⟨6, by norm_num⟩ : Fin 7) = (221 / 18 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((221 / 18 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((221 / 18 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk18_seam_6_1).elim
    · exact (hfresh (by decide)).elim
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
theorem enumMatch_19 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node19 b A B) : ∃ c ∈ children19, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node19 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree20, by simp [children19], tbl20, stepEq_20, childEq_20⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
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

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree27, by simp [children19], tbl27, stepEq_27, childEq_27⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (6 : Fin 7) = (221 / 18 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl19_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl19 (⟨6, by norm_num⟩ : Fin 7) = (221 / 18 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((221 / 18 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((221 / 18 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk19_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk19_seam_6_3).elim
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
theorem enumMatch_20 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node20 b A B) : ∃ c ∈ children20, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node20 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk20_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 39)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (3 : Fin 7) = (11 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨3, by norm_num⟩ : Fin 7) = (11 / 2 : ℚ) := hval0
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

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree21, by simp [children20], tbl21, stepEq_21, childEq_21⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree25, by simp [children20], tbl25, stepEq_25, childEq_25⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (6 : Fin 7) = (221 / 18 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl20_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl20 (⟨6, by norm_num⟩ : Fin 7) = (221 / 18 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((221 / 18 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((221 / 18 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk20_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree26, by simp [children20], tbl26, stepEq_26, childEq_26⟩
    · exact (hseam sk20_seam_6_4).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 21: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_21 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node21 b A B) : ∃ c ∈ children21, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node21 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk21_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk21_seam_5_2).elim
    · exact (hseam sk21_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl21_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl21 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk21_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk21_seam_6_3).elim
    · exact ⟨tree22, by simp [children21], tbl22, stepEq_22, childEq_22⟩
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
theorem enumMatch_22 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node22 b A B) : ∃ c ∈ children22, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node22 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk22_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk22_seam_5_2).elim
    · exact ⟨tree23, by simp [children22], tbl23, stepEq_23, childEq_23⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl22_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl22 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk22_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk22_seam_6_3).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 23: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_23 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node23 b A B) : ∃ c ∈ children23, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node23 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk23_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree24, by simp [children23], tbl24, stepEq_24, childEq_24⟩
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hseam sk23_seam_5_2).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node23, node22, node21, node20, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (6 : Fin 7) = (3861 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl23_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl23 (⟨6, by norm_num⟩ : Fin 7) = (3861 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3861 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3861 / 322 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk23_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk23_seam_6_3).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk23_seam_6_5).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 27: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_27 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node27 b A B) : ∃ c ∈ children27, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node27 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree28, by simp [children27], tbl28, stepEq_28, childEq_28⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl27_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl27 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk27_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree34, by simp [children27], tbl34, stepEq_34, childEq_34⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 28: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_28 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node28 b A B) : ∃ c ∈ children28, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node28 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk28_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 31)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (2 : Fin 7) = (1053 / 238 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨2, by norm_num⟩ : Fin 7) = (1053 / 238 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((1053 / 238 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 31 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((1053 / 238 : ℚ)) ≤ (31 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree29, by simp [children28], tbl29, stepEq_29, childEq_29⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl28_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl28 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk28_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree32, by simp [children28], tbl32, stepEq_32, childEq_32⟩
    · exact ⟨tree33, by simp [children28], tbl33, stepEq_33, childEq_33⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 29: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_29 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node29 b A B) : ∃ c ∈ children29, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node29 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk29_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk29_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl29_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl29 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk29_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk29_seam_6_3).elim
    · exact ⟨tree30, by simp [children29], tbl30, stepEq_30, childEq_30⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 30: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_30 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node30 b A B) : ∃ c ∈ children30, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node30 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk30_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree31, by simp [children30], tbl31, stepEq_31, childEq_31⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl30_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl30 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk30_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk30_seam_6_3).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 31: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_31 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node31 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk31_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hseam sk31_seam_3_2
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node31, node30, node29, node28, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (6 : Fin 7) = (3861 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl31_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl31 (⟨6, by norm_num⟩ : Fin 7) = (3861 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3861 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3861 / 322 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact hseam sk31_seam_6_1
    · exact hfresh (by decide)
    · exact hseam sk31_seam_6_3
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 34: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_34 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node34 b A B) : ∃ c ∈ children34, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node34 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
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
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 4, M = ceil(7·hi) = 32)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (2 : Fin 7) = (9 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨2, by norm_num⟩ : Fin 7) = (9 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((9 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 32 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((9 / 2 : ℚ)) ≤ (32 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact ⟨tree35, by simp [children34], tbl35, stepEq_35, childEq_35⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl34_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl34 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk34_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 35: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_35 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node35 b A B) : ∃ c ∈ children35, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node35 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk35_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 31)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (2 : Fin 7) = (53703 / 12250 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨2, by norm_num⟩ : Fin 7) = (53703 / 12250 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((53703 / 12250 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 31 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((53703 / 12250 : ℚ)) ≤ (31 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact ⟨tree36, by simp [children35], tbl36, stepEq_36, childEq_36⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl35_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl35 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk35_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree39, by simp [children35], tbl39, stepEq_39, childEq_39⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 36: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_36 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node36 b A B) : ∃ c ∈ children36, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node36 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk36_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact (hseam sk36_seam_5_3).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl36_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl36 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk36_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree37, by simp [children36], tbl37, stepEq_37, childEq_37⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `match-completeness` at node 37: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), or matched against the transcribed child. -/
theorem enumMatch_37 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node37 b A B) : ∃ c ∈ children37, DfsMatch (boxN m4res_1_1_4_5_6_8_12) node37 b A B c := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact (hseam sk37_seam_0_1).elim
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact ⟨tree38, by simp [children37], tbl38, stepEq_38, childEq_38⟩
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 86)
    simp only [node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (6 : Fin 7) = (5967 / 490 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl37_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl37 (⟨6, by norm_num⟩ : Fin 7) = (5967 / 490 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((5967 / 490 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 86 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((5967 / 490 : ℚ)) ≤ (86 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact (hseam sk37_seam_6_1).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · exact (hfresh (by decide)).elim
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry


/-- The `dead-end verdict` at node 38: for EVERY Lean-spec candidate step `(b, A, B)` -- b
ranging over all 7 rows (including rank 0, which the run never expands, and the same
reading row, which the run skips -- the reconstruction audited 0 holes there),
A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the
entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`), -/
theorem enumDead_38 (b : Fin 7) (A B : ℚ) (hf : DfsFilters (boxN m4res_1_1_4_5_6_8_12) node38 b A B) : False := by
  simp only [DfsFilters, DfsSoft, dfsZone] at hf
  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf
  subst hAj; subst hBj
  fin_cases b
  · -- b = row 0 (jmax = 2, M = ceil(7·hi) = 21)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (0 : Fin 7) = (3 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨0, by norm_num⟩ : Fin 7) = (3 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 21 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 : ℚ)) ≤ (21 : ℚ))
    have h8 : j ≤ 2 := by omega
    interval_cases j
    · exact hseam sk38_seam_0_1
    · norm_num at hentry

  · -- b = row 1 (jmax = 1, M = ceil(7·hi) = 11)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (1 : Fin 7) = (3 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_1_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨1, by norm_num⟩ : Fin 7) = (3 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 11 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3 / 2 : ℚ)) ≤ (11 : ℚ))
    have h8 : j ≤ 1 := by omega
    interval_cases j
    · norm_num at hentry

  · -- b = row 2 (jmax = 3, M = ceil(7·hi) = 28)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (2 : Fin 7) = (39 / 10 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_2_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨2, by norm_num⟩ : Fin 7) = (39 / 10 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((39 / 10 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 28 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((39 / 10 : ℚ)) ≤ (28 : ℚ))
    have h8 : j ≤ 3 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 3 (jmax = 4, M = ceil(7·hi) = 36)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (3 : Fin 7) = (351 / 70 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_3_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨3, by norm_num⟩ : Fin 7) = (351 / 70 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((351 / 70 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 36 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((351 / 70 : ℚ)) ≤ (36 : ℚ))
    have h8 : j ≤ 4 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hseam sk38_seam_3_2
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 4 (jmax = 5, M = ceil(7·hi) = 46)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (4 : Fin 7) = (13 / 2 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_4_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨4, by norm_num⟩ : Fin 7) = (13 / 2 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((13 / 2 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 46 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((13 / 2 : ℚ)) ≤ (46 : ℚ))
    have h8 : j ≤ 5 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 5 (jmax = 7, M = ceil(7·hi) = 59)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (5 : Fin 7) = (117 / 14 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_5_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨5, by norm_num⟩ : Fin 7) = (117 / 14 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((117 / 14 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 59 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((117 / 14 : ℚ)) ≤ (59 : ℚ))
    have h8 : j ≤ 7 := by omega
    interval_cases j
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry
    · norm_num at hentry

  · -- b = row 6 (jmax = 10, M = ceil(7·hi) = 84)
    simp only [node38, node37, node36, node35, node34, node27, node19, node18, node1, node0] at hzone hentry hfresh hseam
    have hval0 : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (6 : Fin 7) = (3861 / 322 : ℚ) :=
      by norm_num [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl38_c_6_0]
    have hval : dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl38 (⟨6, by norm_num⟩ : Fin 7) = (3861 / 322 : ℚ) := hval0
    rw [hval] at hzone hentry
    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * ((3861 / 322 : ℚ)) :=
      lt_of_zone (by norm_num) hzone
    have h6 : (8 * j - 1 : ℕ) < 84 :=
      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * ((3861 / 322 : ℚ)) ≤ (84 : ℚ))
    have h8 : j ≤ 10 := by omega
    interval_cases j
    · exact hseam sk38_seam_6_1
    · exact hfresh (by decide)
    · exact hfresh (by decide)
    · exact hfresh (by decide)
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
#print axioms enumMatch_7
#print axioms enumMatch_8
#print axioms enumDead_9
#print axioms enumMatch_11
#print axioms enumDead_12
#print axioms enumMatch_13
#print axioms enumMatch_14
#print axioms enumDead_15
#print axioms enumMatch_16
#print axioms enumDead_17
#print axioms enumMatch_18
#print axioms enumMatch_19
#print axioms enumMatch_20
#print axioms enumMatch_21
#print axioms enumMatch_22
#print axioms enumMatch_23
#print axioms enumMatch_27
#print axioms enumMatch_28
#print axioms enumMatch_29
#print axioms enumMatch_30
#print axioms enumDead_31
#print axioms enumMatch_34
#print axioms enumMatch_35
#print axioms enumMatch_36
#print axioms enumMatch_37
#print axioms enumDead_38

/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/

theorem closed_39 : DfsClosed tree39 := by
  simp only [tree39, DfsClosed]
  exact nodeOK_39

#print axioms closed_39
theorem closed_38 : DfsClosed tree38 := by
  simp only [tree38, DfsClosed]
  exact nodeOK_38

#print axioms closed_38
theorem closed_37 : DfsClosed tree37 := by
  simp only [tree37, DfsClosed]
  refine ⟨nodeOK_37, ?_⟩
  intro t ht
  simp only [children37, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_38
  · exact absurd ht'1 (by simp)

#print axioms closed_37
theorem closed_36 : DfsClosed tree36 := by
  simp only [tree36, DfsClosed]
  refine ⟨nodeOK_36, ?_⟩
  intro t ht
  simp only [children36, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_37
  · exact absurd ht'1 (by simp)

#print axioms closed_36
theorem closed_35 : DfsClosed tree35 := by
  simp only [tree35, DfsClosed]
  refine ⟨nodeOK_35, ?_⟩
  intro t ht
  simp only [children35, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_36
  · rcases ht'1 with rfl | ht'2
    · exact closed_39
    · exact absurd ht'2 (by simp)

#print axioms closed_35
theorem closed_34 : DfsClosed tree34 := by
  simp only [tree34, DfsClosed]
  refine ⟨nodeOK_34, ?_⟩
  intro t ht
  simp only [children34, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_35
  · exact absurd ht'1 (by simp)

#print axioms closed_34
theorem closed_33 : DfsClosed tree33 := by
  simp only [tree33, DfsClosed]
  exact nodeOK_33

#print axioms closed_33
theorem closed_32 : DfsClosed tree32 := by
  simp only [tree32, DfsClosed]
  exact nodeOK_32

#print axioms closed_32
theorem closed_31 : DfsClosed tree31 := by
  simp only [tree31, DfsClosed]
  exact nodeOK_31

#print axioms closed_31
theorem closed_30 : DfsClosed tree30 := by
  simp only [tree30, DfsClosed]
  refine ⟨nodeOK_30, ?_⟩
  intro t ht
  simp only [children30, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_31
  · exact absurd ht'1 (by simp)

#print axioms closed_30
theorem closed_29 : DfsClosed tree29 := by
  simp only [tree29, DfsClosed]
  refine ⟨nodeOK_29, ?_⟩
  intro t ht
  simp only [children29, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_30
  · exact absurd ht'1 (by simp)

#print axioms closed_29
theorem closed_28 : DfsClosed tree28 := by
  simp only [tree28, DfsClosed]
  refine ⟨nodeOK_28, ?_⟩
  intro t ht
  simp only [children28, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_29
  · rcases ht'1 with rfl | ht'2
    · exact closed_32
    · rcases ht'2 with rfl | ht'3
      · exact closed_33
      · exact absurd ht'3 (by simp)

#print axioms closed_28
theorem closed_27 : DfsClosed tree27 := by
  simp only [tree27, DfsClosed]
  refine ⟨nodeOK_27, ?_⟩
  intro t ht
  simp only [children27, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_28
  · rcases ht'1 with rfl | ht'2
    · exact closed_34
    · exact absurd ht'2 (by simp)

#print axioms closed_27
theorem closed_26 : DfsClosed tree26 := by
  simp only [tree26, DfsClosed]
  exact nodeOK_26

#print axioms closed_26
theorem closed_25 : DfsClosed tree25 := by
  simp only [tree25, DfsClosed]
  exact nodeOK_25

#print axioms closed_25
theorem closed_24 : DfsClosed tree24 := by
  simp only [tree24, DfsClosed]
  exact nodeOK_24

#print axioms closed_24
theorem closed_23 : DfsClosed tree23 := by
  simp only [tree23, DfsClosed]
  refine ⟨nodeOK_23, ?_⟩
  intro t ht
  simp only [children23, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_24
  · exact absurd ht'1 (by simp)

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
  refine ⟨nodeOK_21, ?_⟩
  intro t ht
  simp only [children21, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_22
  · exact absurd ht'1 (by simp)

#print axioms closed_21
theorem closed_20 : DfsClosed tree20 := by
  simp only [tree20, DfsClosed]
  refine ⟨nodeOK_20, ?_⟩
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_21
  · rcases ht'1 with rfl | ht'2
    · exact closed_25
    · rcases ht'2 with rfl | ht'3
      · exact closed_26
      · exact absurd ht'3 (by simp)

#print axioms closed_20
theorem closed_19 : DfsClosed tree19 := by
  simp only [tree19, DfsClosed]
  refine ⟨nodeOK_19, ?_⟩
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_20
  · rcases ht'1 with rfl | ht'2
    · exact closed_27
    · exact absurd ht'2 (by simp)

#print axioms closed_19
theorem closed_18 : DfsClosed tree18 := by
  simp only [tree18, DfsClosed]
  refine ⟨nodeOK_18, ?_⟩
  intro t ht
  simp only [children18, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_19
  · exact absurd ht'1 (by simp)

#print axioms closed_18
theorem closed_17 : DfsClosed tree17 := by
  simp only [tree17, DfsClosed]
  exact nodeOK_17

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
  exact nodeOK_15

#print axioms closed_15
theorem closed_14 : DfsClosed tree14 := by
  simp only [tree14, DfsClosed]
  refine ⟨nodeOK_14, ?_⟩
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_15
  · rcases ht'1 with rfl | ht'2
    · exact closed_16
    · exact absurd ht'2 (by simp)

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
  exact nodeOK_12

#print axioms closed_12
theorem closed_11 : DfsClosed tree11 := by
  simp only [tree11, DfsClosed]
  refine ⟨nodeOK_11, ?_⟩
  intro t ht
  simp only [children11, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_12
  · exact absurd ht'1 (by simp)

#print axioms closed_11
theorem closed_10 : DfsClosed tree10 := by
  simp only [tree10, DfsClosed]
  exact nodeOK_10

#print axioms closed_10
theorem closed_9 : DfsClosed tree9 := by
  simp only [tree9, DfsClosed]
  exact nodeOK_9

#print axioms closed_9
theorem closed_8 : DfsClosed tree8 := by
  simp only [tree8, DfsClosed]
  refine ⟨nodeOK_8, ?_⟩
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_9
  · rcases ht'1 with rfl | ht'2
    · exact closed_10
    · rcases ht'2 with rfl | ht'3
      · exact closed_11
      · exact absurd ht'3 (by simp)

#print axioms closed_8
theorem closed_7 : DfsClosed tree7 := by
  simp only [tree7, DfsClosed]
  refine ⟨nodeOK_7, ?_⟩
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_8
  · rcases ht'1 with rfl | ht'2
    · exact closed_13
    · exact absurd ht'2 (by simp)

#print axioms closed_7
theorem closed_6 : DfsClosed tree6 := by
  simp only [tree6, DfsClosed]
  exact nodeOK_6

#print axioms closed_6
theorem closed_5 : DfsClosed tree5 := by
  simp only [tree5, DfsClosed]
  exact nodeOK_5

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
  · rcases ht'1 with rfl | ht'2
    · exact closed_5
    · rcases ht'2 with rfl | ht'3
      · exact closed_6
      · exact absurd ht'3 (by simp)

#print axioms closed_3
theorem closed_2 : DfsClosed tree2 := by
  simp only [tree2, DfsClosed]
  refine ⟨nodeOK_2, ?_⟩
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_3
  · rcases ht'1 with rfl | ht'2
    · exact closed_7
    · exact absurd ht'2 (by simp)

#print axioms closed_2
theorem closed_1 : DfsClosed tree1 := by
  simp only [tree1, DfsClosed]
  refine ⟨nodeOK_1, ?_⟩
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact closed_2
  · rcases ht'1 with rfl | ht'2
    · exact closed_18
    · exact absurd ht'2 (by simp)

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

/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_39 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree39 := by
  simp only [tree39, DfsEnum]

#print axioms enum_39
theorem enum_38 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree38 := by
  simp only [tree38, DfsEnum]
  exact fun b A B hf => enumDead_38 b A B hf

#print axioms enum_38
theorem enum_37 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree37 := by
  simp only [tree37, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_37 b A B hf, ?_⟩
  intro t ht
  simp only [children37, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_38
  · exact absurd ht'1 (by simp)

#print axioms enum_37
theorem enum_36 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree36 := by
  simp only [tree36, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_36 b A B hf, ?_⟩
  intro t ht
  simp only [children36, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_37
  · exact absurd ht'1 (by simp)

#print axioms enum_36
theorem enum_35 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree35 := by
  simp only [tree35, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_35 b A B hf, ?_⟩
  intro t ht
  simp only [children35, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_36
  · rcases ht'1 with rfl | ht'2
    · exact enum_39
    · exact absurd ht'2 (by simp)

#print axioms enum_35
theorem enum_34 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree34 := by
  simp only [tree34, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_34 b A B hf, ?_⟩
  intro t ht
  simp only [children34, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_35
  · exact absurd ht'1 (by simp)

#print axioms enum_34
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_33 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree33 := by
  simp only [tree33, DfsEnum]

#print axioms enum_33
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_32 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree32 := by
  simp only [tree32, DfsEnum]

#print axioms enum_32
theorem enum_31 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree31 := by
  simp only [tree31, DfsEnum]
  exact fun b A B hf => enumDead_31 b A B hf

#print axioms enum_31
theorem enum_30 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree30 := by
  simp only [tree30, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_30 b A B hf, ?_⟩
  intro t ht
  simp only [children30, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_31
  · exact absurd ht'1 (by simp)

#print axioms enum_30
theorem enum_29 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree29 := by
  simp only [tree29, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_29 b A B hf, ?_⟩
  intro t ht
  simp only [children29, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_30
  · exact absurd ht'1 (by simp)

#print axioms enum_29
theorem enum_28 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree28 := by
  simp only [tree28, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_28 b A B hf, ?_⟩
  intro t ht
  simp only [children28, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_29
  · rcases ht'1 with rfl | ht'2
    · exact enum_32
    · rcases ht'2 with rfl | ht'3
      · exact enum_33
      · exact absurd ht'3 (by simp)

#print axioms enum_28
theorem enum_27 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree27 := by
  simp only [tree27, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_27 b A B hf, ?_⟩
  intro t ht
  simp only [children27, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_28
  · rcases ht'1 with rfl | ht'2
    · exact enum_34
    · exact absurd ht'2 (by simp)

#print axioms enum_27
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_26 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree26 := by
  simp only [tree26, DfsEnum]

#print axioms enum_26
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_25 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree25 := by
  simp only [tree25, DfsEnum]

#print axioms enum_25
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_24 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree24 := by
  simp only [tree24, DfsEnum]

#print axioms enum_24
theorem enum_23 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree23 := by
  simp only [tree23, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_23 b A B hf, ?_⟩
  intro t ht
  simp only [children23, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_24
  · exact absurd ht'1 (by simp)

#print axioms enum_23
theorem enum_22 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree22 := by
  simp only [tree22, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_22 b A B hf, ?_⟩
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_23
  · exact absurd ht'1 (by simp)

#print axioms enum_22
theorem enum_21 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree21 := by
  simp only [tree21, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_21 b A B hf, ?_⟩
  intro t ht
  simp only [children21, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_22
  · exact absurd ht'1 (by simp)

#print axioms enum_21
theorem enum_20 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree20 := by
  simp only [tree20, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_20 b A B hf, ?_⟩
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_21
  · rcases ht'1 with rfl | ht'2
    · exact enum_25
    · rcases ht'2 with rfl | ht'3
      · exact enum_26
      · exact absurd ht'3 (by simp)

#print axioms enum_20
theorem enum_19 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree19 := by
  simp only [tree19, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_19 b A B hf, ?_⟩
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_20
  · rcases ht'1 with rfl | ht'2
    · exact enum_27
    · exact absurd ht'2 (by simp)

#print axioms enum_19
theorem enum_18 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree18 := by
  simp only [tree18, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_18 b A B hf, ?_⟩
  intro t ht
  simp only [children18, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_19
  · exact absurd ht'1 (by simp)

#print axioms enum_18
theorem enum_17 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree17 := by
  simp only [tree17, DfsEnum]
  exact fun b A B hf => enumDead_17 b A B hf

#print axioms enum_17
theorem enum_16 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree16 := by
  simp only [tree16, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_16 b A B hf, ?_⟩
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_17
  · exact absurd ht'1 (by simp)

#print axioms enum_16
theorem enum_15 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree15 := by
  simp only [tree15, DfsEnum]
  exact fun b A B hf => enumDead_15 b A B hf

#print axioms enum_15
theorem enum_14 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree14 := by
  simp only [tree14, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_14 b A B hf, ?_⟩
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_15
  · rcases ht'1 with rfl | ht'2
    · exact enum_16
    · exact absurd ht'2 (by simp)

#print axioms enum_14
theorem enum_13 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree13 := by
  simp only [tree13, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_13 b A B hf, ?_⟩
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_14
  · exact absurd ht'1 (by simp)

#print axioms enum_13
theorem enum_12 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree12 := by
  simp only [tree12, DfsEnum]
  exact fun b A B hf => enumDead_12 b A B hf

#print axioms enum_12
theorem enum_11 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree11 := by
  simp only [tree11, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_11 b A B hf, ?_⟩
  intro t ht
  simp only [children11, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_12
  · exact absurd ht'1 (by simp)

#print axioms enum_11
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_10 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree10 := by
  simp only [tree10, DfsEnum]

#print axioms enum_10
theorem enum_9 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree9 := by
  simp only [tree9, DfsEnum]
  exact fun b A B hf => enumDead_9 b A B hf

#print axioms enum_9
theorem enum_8 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree8 := by
  simp only [tree8, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_8 b A B hf, ?_⟩
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_9
  · rcases ht'1 with rfl | ht'2
    · exact enum_10
    · rcases ht'2 with rfl | ht'3
      · exact enum_11
      · exact absurd ht'3 (by simp)

#print axioms enum_8
theorem enum_7 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree7 := by
  simp only [tree7, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_7 b A B hf, ?_⟩
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_8
  · rcases ht'1 with rfl | ht'2
    · exact enum_13
    · exact absurd ht'2 (by simp)

#print axioms enum_7
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_6 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree6 := by
  simp only [tree6, DfsEnum]

#print axioms enum_6
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_5 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree5 := by
  simp only [tree5, DfsEnum]

#print axioms enum_5
/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_4 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree4 := by
  simp only [tree4, DfsEnum]

#print axioms enum_4
theorem enum_3 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree3 := by
  simp only [tree3, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_3 b A B hf, ?_⟩
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_4
  · rcases ht'1 with rfl | ht'2
    · exact enum_5
    · rcases ht'2 with rfl | ht'3
      · exact enum_6
      · exact absurd ht'3 (by simp)

#print axioms enum_3
theorem enum_2 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree2 := by
  simp only [tree2, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_2 b A B hf, ?_⟩
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_3
  · rcases ht'1 with rfl | ht'2
    · exact enum_7
    · exact absurd ht'2 (by simp)

#print axioms enum_2
theorem enum_1 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree1 := by
  simp only [tree1, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_1 b A B hf, ?_⟩
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_2
  · rcases ht'1 with rfl | ht'2
    · exact enum_18
    · exact absurd ht'2 (by simp)

#print axioms enum_1
theorem enum_0 : DfsEnum (boxN m4res_1_1_4_5_6_8_12) tree0 := by
  simp only [tree0, DfsEnum]
  refine ⟨fun b A B hf => enumMatch_0 b A B hf, ?_⟩
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_1
  · exact absurd ht'1 (by simp)

#print axioms enum_0

theorem pd_39 (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree39 :=
  hprune_39

#print axioms pd_39
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_38 : DfsPruneDom tree38 := by
  simp only [tree38, DfsPruneDom]

#print axioms pd_38
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_37 : DfsPruneDom tree37 := by
  simp only [tree37, DfsPruneDom]
  intro t ht
  simp only [children37, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_38
  · exact absurd ht'1 (by simp)

#print axioms pd_37
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_36 : DfsPruneDom tree36 := by
  simp only [tree36, DfsPruneDom]
  intro t ht
  simp only [children36, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_37
  · exact absurd ht'1 (by simp)

#print axioms pd_36
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_35 (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree35 := by
  simp only [tree35, DfsPruneDom]
  intro t ht
  simp only [children35, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_36
  · rcases ht'1 with rfl | ht'2
    · exact pd_39 hprune_39 
    · exact absurd ht'2 (by simp)

#print axioms pd_35
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_34 (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree34 := by
  simp only [tree34, DfsPruneDom]
  intro t ht
  simp only [children34, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_35 hprune_39 
  · exact absurd ht'1 (by simp)

#print axioms pd_34
theorem pd_33 (hprune_33 : DfsPruneDom tree33) : DfsPruneDom tree33 :=
  hprune_33

#print axioms pd_33
theorem pd_32 (hprune_32 : DfsPruneDom tree32) : DfsPruneDom tree32 :=
  hprune_32

#print axioms pd_32
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_31 : DfsPruneDom tree31 := by
  simp only [tree31, DfsPruneDom]

#print axioms pd_31
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_30 : DfsPruneDom tree30 := by
  simp only [tree30, DfsPruneDom]
  intro t ht
  simp only [children30, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_31
  · exact absurd ht'1 (by simp)

#print axioms pd_30
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_29 : DfsPruneDom tree29 := by
  simp only [tree29, DfsPruneDom]
  intro t ht
  simp only [children29, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_30
  · exact absurd ht'1 (by simp)

#print axioms pd_29
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_28 (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) : DfsPruneDom tree28 := by
  simp only [tree28, DfsPruneDom]
  intro t ht
  simp only [children28, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_29
  · rcases ht'1 with rfl | ht'2
    · exact pd_32 hprune_32 
    · rcases ht'2 with rfl | ht'3
      · exact pd_33 hprune_33 
      · exact absurd ht'3 (by simp)

#print axioms pd_28
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_27 (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree27 := by
  simp only [tree27, DfsPruneDom]
  intro t ht
  simp only [children27, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_28 hprune_32 hprune_33 
  · rcases ht'1 with rfl | ht'2
    · exact pd_34 hprune_39 
    · exact absurd ht'2 (by simp)

#print axioms pd_27
theorem pd_26 (hprune_26 : DfsPruneDom tree26) : DfsPruneDom tree26 :=
  hprune_26

#print axioms pd_26
theorem pd_25 (hprune_25 : DfsPruneDom tree25) : DfsPruneDom tree25 :=
  hprune_25

#print axioms pd_25
theorem pd_24 (hprune_24 : DfsPruneDom tree24) : DfsPruneDom tree24 :=
  hprune_24

#print axioms pd_24
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_23 (hprune_24 : DfsPruneDom tree24) : DfsPruneDom tree23 := by
  simp only [tree23, DfsPruneDom]
  intro t ht
  simp only [children23, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_24 hprune_24 
  · exact absurd ht'1 (by simp)

#print axioms pd_23
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_22 (hprune_24 : DfsPruneDom tree24) : DfsPruneDom tree22 := by
  simp only [tree22, DfsPruneDom]
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_23 hprune_24 
  · exact absurd ht'1 (by simp)

#print axioms pd_22
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_21 (hprune_24 : DfsPruneDom tree24) : DfsPruneDom tree21 := by
  simp only [tree21, DfsPruneDom]
  intro t ht
  simp only [children21, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_22 hprune_24 
  · exact absurd ht'1 (by simp)

#print axioms pd_21
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_20 (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) : DfsPruneDom tree20 := by
  simp only [tree20, DfsPruneDom]
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_21 hprune_24 
  · rcases ht'1 with rfl | ht'2
    · exact pd_25 hprune_25 
    · rcases ht'2 with rfl | ht'3
      · exact pd_26 hprune_26 
      · exact absurd ht'3 (by simp)

#print axioms pd_20
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_19 (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree19 := by
  simp only [tree19, DfsPruneDom]
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_20 hprune_24 hprune_25 hprune_26 
  · rcases ht'1 with rfl | ht'2
    · exact pd_27 hprune_32 hprune_33 hprune_39 
    · exact absurd ht'2 (by simp)

#print axioms pd_19
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_18 (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree18 := by
  simp only [tree18, DfsPruneDom]
  intro t ht
  simp only [children18, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_19 hprune_24 hprune_25 hprune_26 hprune_32 hprune_33 hprune_39 
  · exact absurd ht'1 (by simp)

#print axioms pd_18
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_17 : DfsPruneDom tree17 := by
  simp only [tree17, DfsPruneDom]

#print axioms pd_17
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_16 : DfsPruneDom tree16 := by
  simp only [tree16, DfsPruneDom]
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_17
  · exact absurd ht'1 (by simp)

#print axioms pd_16
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_15 : DfsPruneDom tree15 := by
  simp only [tree15, DfsPruneDom]

#print axioms pd_15
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_14 : DfsPruneDom tree14 := by
  simp only [tree14, DfsPruneDom]
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_15
  · rcases ht'1 with rfl | ht'2
    · exact pd_16
    · exact absurd ht'2 (by simp)

#print axioms pd_14
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_13 : DfsPruneDom tree13 := by
  simp only [tree13, DfsPruneDom]
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_14
  · exact absurd ht'1 (by simp)

#print axioms pd_13
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_12 : DfsPruneDom tree12 := by
  simp only [tree12, DfsPruneDom]

#print axioms pd_12
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_11 : DfsPruneDom tree11 := by
  simp only [tree11, DfsPruneDom]
  intro t ht
  simp only [children11, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_12
  · exact absurd ht'1 (by simp)

#print axioms pd_11
theorem pd_10 (hprune_10 : DfsPruneDom tree10) : DfsPruneDom tree10 :=
  hprune_10

#print axioms pd_10
/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/
theorem pd_9 : DfsPruneDom tree9 := by
  simp only [tree9, DfsPruneDom]

#print axioms pd_9
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_8 (hprune_10 : DfsPruneDom tree10) : DfsPruneDom tree8 := by
  simp only [tree8, DfsPruneDom]
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_9
  · rcases ht'1 with rfl | ht'2
    · exact pd_10 hprune_10 
    · rcases ht'2 with rfl | ht'3
      · exact pd_11
      · exact absurd ht'3 (by simp)

#print axioms pd_8
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_7 (hprune_10 : DfsPruneDom tree10) : DfsPruneDom tree7 := by
  simp only [tree7, DfsPruneDom]
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_8 hprune_10 
  · rcases ht'1 with rfl | ht'2
    · exact pd_13
    · exact absurd ht'2 (by simp)

#print axioms pd_7
theorem pd_6 (hprune_6 : DfsPruneDom tree6) : DfsPruneDom tree6 :=
  hprune_6

#print axioms pd_6
theorem pd_5 (hprune_5 : DfsPruneDom tree5) : DfsPruneDom tree5 :=
  hprune_5

#print axioms pd_5
theorem pd_4 (hprune_4 : DfsPruneDom tree4) : DfsPruneDom tree4 :=
  hprune_4

#print axioms pd_4
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_3 (hprune_4 : DfsPruneDom tree4) (hprune_5 : DfsPruneDom tree5) (hprune_6 : DfsPruneDom tree6) : DfsPruneDom tree3 := by
  simp only [tree3, DfsPruneDom]
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_4 hprune_4 
  · rcases ht'1 with rfl | ht'2
    · exact pd_5 hprune_5 
    · rcases ht'2 with rfl | ht'3
      · exact pd_6 hprune_6 
      · exact absurd ht'3 (by simp)

#print axioms pd_3
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_2 (hprune_4 : DfsPruneDom tree4) (hprune_5 : DfsPruneDom tree5) (hprune_6 : DfsPruneDom tree6) (hprune_10 : DfsPruneDom tree10) : DfsPruneDom tree2 := by
  simp only [tree2, DfsPruneDom]
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_3 hprune_4 hprune_5 hprune_6 
  · rcases ht'1 with rfl | ht'2
    · exact pd_7 hprune_10 
    · exact absurd ht'2 (by simp)

#print axioms pd_2
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_1 (hprune_4 : DfsPruneDom tree4) (hprune_5 : DfsPruneDom tree5) (hprune_6 : DfsPruneDom tree6) (hprune_10 : DfsPruneDom tree10) (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree1 := by
  simp only [tree1, DfsPruneDom]
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_2 hprune_4 hprune_5 hprune_6 hprune_10 
  · rcases ht'1 with rfl | ht'2
    · exact pd_18 hprune_24 hprune_25 hprune_26 hprune_32 hprune_33 hprune_39 
    · exact absurd ht'2 (by simp)

#print axioms pd_1
/-- The per-node prune domination (internal node: inherited from the children;
the reach leaves carry the OWED (b) hypotheses). -/
theorem pd_0 (hprune_4 : DfsPruneDom tree4) (hprune_5 : DfsPruneDom tree5) (hprune_6 : DfsPruneDom tree6) (hprune_10 : DfsPruneDom tree10) (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : DfsPruneDom tree0 := by
  simp only [tree0, DfsPruneDom]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_1 hprune_4 hprune_5 hprune_6 hprune_10 hprune_24 hprune_25 hprune_26 hprune_32 hprune_33 hprune_39 
  · exact absurd ht'1 (by simp)

#print axioms pd_0

/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions (`reachutc_1_1_4_5_6_8_12.json`)

The per-prune-leaf verdict layer: the explored (frontier-sup, dump-rank) state sets
and pmax as literal data, the `no_completing_state_reachable` verdicts (discharged
HERE by literal per-case proofs over the census windows), the OWED `[P]` projection
instances (`reachutcProj_*`, discharged by the parallel `Fresh/ReachUtcProof.lean`),
and the verdict-carrying `DfsPruneDom` instances `m4fix_%s_pruneDom_*` (replacing
the identity stubs). -/

theorem hiPos_4 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl4 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl4_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_4 : List (ℚ × ℕ) := [((34 / 15 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 4
(dump state P = 34 / 15, a = 5, Aex = 17, verdict `no_completing_state_reachable`,
nst = 1, pmax = 34 / 15, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_4 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_4

theorem hiPos_5 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl5 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl5_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_5 : List (ℚ × ℕ) := [((50 / 23 : ℚ), 7), ((34 / 15 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 5
(dump state P = 50 / 23, a = 6, Aex = 25, verdict `no_completing_state_reachable`,
nst = 2, pmax = 34 / 15, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_5 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_5

theorem hiPos_6 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl6 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl6_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_6 : List (ℚ × ℕ) := [((66 / 23 : ℚ), 7), ((102 / 35 : ℚ), 5)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 6
(dump state P = 66 / 23, a = 6, Aex = 33, verdict `no_completing_state_reachable`,
nst = 2, pmax = 102 / 35, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_6 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_6

theorem hiPos_10 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl10 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl10_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_10 : List (ℚ × ℕ) := [((34 / 15 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 10
(dump state P = 34 / 15, a = 5, Aex = 17, verdict `no_completing_state_reachable`,
nst = 1, pmax = 34 / 15, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_10 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_10

theorem hiPos_24 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl24 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl24_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_24 : List (ℚ × ℕ) := [((578 / 161 : ℚ), 4), ((14850 / 3703 : ℚ), 5), ((98 / 23 : ℚ), 7), ((2178 / 529 : ℚ), 6), ((16830 / 3703 : ℚ), 3)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 24
(dump state P = 578 / 161, a = 3, Aex = 17, verdict `no_completing_state_reachable`,
nst = 5, pmax = 16830 / 3703, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_24 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_24

theorem hiPos_25 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl25 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl25_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_25 : List (ℚ × ℕ) := [((34 / 15 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 25
(dump state P = 34 / 15, a = 5, Aex = 17, verdict `no_completing_state_reachable`,
nst = 1, pmax = 34 / 15, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_25 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_25

theorem hiPos_26 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl26 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl26_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_26 : List (ℚ × ℕ) := [((50 / 23 : ℚ), 7), ((34 / 15 : ℚ), 6)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 26
(dump state P = 50 / 23, a = 6, Aex = 25, verdict `no_completing_state_reachable`,
nst = 2, pmax = 34 / 15, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_26 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_26

theorem hiPos_32 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl32 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl32_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_32 : List (ℚ × ℕ) := [((50 / 23 : ℚ), 7)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 32
(dump state P = 50 / 23, a = 6, Aex = 25, verdict `no_completing_state_reachable`,
nst = 1, pmax = 50 / 23, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_32 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_32

theorem hiPos_33 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl33 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl33_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_33 : List (ℚ × ℕ) := [((66 / 23 : ℚ), 7), ((4590 / 1519 : ℚ), 6), ((5202 / 1519 : ℚ), 4)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 33
(dump state P = 66 / 23, a = 6, Aex = 33, verdict `no_completing_state_reachable`,
nst = 3, pmax = 5202 / 1519, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_33 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_33

theorem hiPos_39 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_4_5_6_8_12) tbl39 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_4_5_6_8_12, tbl39_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_39 : List (ℚ × ℕ) := [((66 / 23 : ℚ), 7), ((4590 / 1519 : ℚ), 6), ((5202 / 1519 : ℚ), 4)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 39
(dump state P = 66 / 23, a = 6, Aex = 33, verdict `no_completing_state_reachable`,
nst = 3, pmax = 5202 / 1519, transcribed from `experiments/n8/reachutc_1_1_4_5_6_8_12.json`).  FINDING
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
theorem m4fix_1_1_4_5_6_8_12_pruneDom_39 (h : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39 := h

#print axioms m4fix_1_1_4_5_6_8_12_pruneDom_39

theorem pdZone_39 (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39 := hpruneZone_39

#print axioms pdZone_39
theorem pdZone_38 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree38 := by
  simp only [tree38, DfsPruneDomZone]

#print axioms pdZone_38
theorem pdZone_37 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree37 := by
  simp only [tree37, DfsPruneDomZone]
  intro t ht
  simp only [children37, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_38
  · exact absurd ht'1 (by simp)

#print axioms pdZone_37
theorem pdZone_36 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree36 := by
  simp only [tree36, DfsPruneDomZone]
  intro t ht
  simp only [children36, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_37
  · exact absurd ht'1 (by simp)

#print axioms pdZone_36
theorem pdZone_35 (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree35 := by
  simp only [tree35, DfsPruneDomZone]
  intro t ht
  simp only [children35, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_36
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_39 hpruneZone_39 
    · exact absurd ht'2 (by simp)

#print axioms pdZone_35
theorem pdZone_34 (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree34 := by
  simp only [tree34, DfsPruneDomZone]
  intro t ht
  simp only [children34, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_35 hpruneZone_39 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_34
theorem pdZone_33 (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33 := hpruneZone_33

#print axioms pdZone_33
theorem pdZone_32 (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32 := hpruneZone_32

#print axioms pdZone_32
theorem pdZone_31 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree31 := by
  simp only [tree31, DfsPruneDomZone]

#print axioms pdZone_31
theorem pdZone_30 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree30 := by
  simp only [tree30, DfsPruneDomZone]
  intro t ht
  simp only [children30, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_31
  · exact absurd ht'1 (by simp)

#print axioms pdZone_30
theorem pdZone_29 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree29 := by
  simp only [tree29, DfsPruneDomZone]
  intro t ht
  simp only [children29, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_30
  · exact absurd ht'1 (by simp)

#print axioms pdZone_29
theorem pdZone_28 (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree28 := by
  simp only [tree28, DfsPruneDomZone]
  intro t ht
  simp only [children28, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_29
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_32 hpruneZone_32 
    · rcases ht'2 with rfl | ht'3
      · exact pdZone_33 hpruneZone_33 
      · exact absurd ht'3 (by simp)

#print axioms pdZone_28
theorem pdZone_27 (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree27 := by
  simp only [tree27, DfsPruneDomZone]
  intro t ht
  simp only [children27, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_28 hpruneZone_32 hpruneZone_33 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_34 hpruneZone_39 
    · exact absurd ht'2 (by simp)

#print axioms pdZone_27
theorem pdZone_26 (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26 := hpruneZone_26

#print axioms pdZone_26
theorem pdZone_25 (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25 := hpruneZone_25

#print axioms pdZone_25
theorem pdZone_24 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24 := hpruneZone_24

#print axioms pdZone_24
theorem pdZone_23 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree23 := by
  simp only [tree23, DfsPruneDomZone]
  intro t ht
  simp only [children23, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_24 hpruneZone_24 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_23
theorem pdZone_22 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree22 := by
  simp only [tree22, DfsPruneDomZone]
  intro t ht
  simp only [children22, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_23 hpruneZone_24 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_22
theorem pdZone_21 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree21 := by
  simp only [tree21, DfsPruneDomZone]
  intro t ht
  simp only [children21, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_22 hpruneZone_24 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_21
theorem pdZone_20 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree20 := by
  simp only [tree20, DfsPruneDomZone]
  intro t ht
  simp only [children20, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_21 hpruneZone_24 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_25 hpruneZone_25 
    · rcases ht'2 with rfl | ht'3
      · exact pdZone_26 hpruneZone_26 
      · exact absurd ht'3 (by simp)

#print axioms pdZone_20
theorem pdZone_19 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree19 := by
  simp only [tree19, DfsPruneDomZone]
  intro t ht
  simp only [children19, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_20 hpruneZone_24 hpruneZone_25 hpruneZone_26 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_27 hpruneZone_32 hpruneZone_33 hpruneZone_39 
    · exact absurd ht'2 (by simp)

#print axioms pdZone_19
theorem pdZone_18 (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree18 := by
  simp only [tree18, DfsPruneDomZone]
  intro t ht
  simp only [children18, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_19 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 
  · exact absurd ht'1 (by simp)

#print axioms pdZone_18
theorem pdZone_17 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree17 := by
  simp only [tree17, DfsPruneDomZone]

#print axioms pdZone_17
theorem pdZone_16 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree16 := by
  simp only [tree16, DfsPruneDomZone]
  intro t ht
  simp only [children16, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_17
  · exact absurd ht'1 (by simp)

#print axioms pdZone_16
theorem pdZone_15 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree15 := by
  simp only [tree15, DfsPruneDomZone]

#print axioms pdZone_15
theorem pdZone_14 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree14 := by
  simp only [tree14, DfsPruneDomZone]
  intro t ht
  simp only [children14, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_15
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_16
    · exact absurd ht'2 (by simp)

#print axioms pdZone_14
theorem pdZone_13 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree13 := by
  simp only [tree13, DfsPruneDomZone]
  intro t ht
  simp only [children13, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_14
  · exact absurd ht'1 (by simp)

#print axioms pdZone_13
theorem pdZone_12 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree12 := by
  simp only [tree12, DfsPruneDomZone]

#print axioms pdZone_12
theorem pdZone_11 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree11 := by
  simp only [tree11, DfsPruneDomZone]
  intro t ht
  simp only [children11, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_12
  · exact absurd ht'1 (by simp)

#print axioms pdZone_11
theorem pdZone_10 (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10 := hpruneZone_10

#print axioms pdZone_10
theorem pdZone_9 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree9 := by
  simp only [tree9, DfsPruneDomZone]

#print axioms pdZone_9
theorem pdZone_8 (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree8 := by
  simp only [tree8, DfsPruneDomZone]
  intro t ht
  simp only [children8, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_9
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_10 hpruneZone_10 
    · rcases ht'2 with rfl | ht'3
      · exact pdZone_11
      · exact absurd ht'3 (by simp)

#print axioms pdZone_8
theorem pdZone_7 (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree7 := by
  simp only [tree7, DfsPruneDomZone]
  intro t ht
  simp only [children7, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_8 hpruneZone_10 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_13
    · exact absurd ht'2 (by simp)

#print axioms pdZone_7
theorem pdZone_6 (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6 := hpruneZone_6

#print axioms pdZone_6
theorem pdZone_5 (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5 := hpruneZone_5

#print axioms pdZone_5
theorem pdZone_4 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) :
    DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4 := hpruneZone_4

#print axioms pdZone_4
theorem pdZone_3 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree3 := by
  simp only [tree3, DfsPruneDomZone]
  intro t ht
  simp only [children3, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_4 hpruneZone_4 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_5 hpruneZone_5 
    · rcases ht'2 with rfl | ht'3
      · exact pdZone_6 hpruneZone_6 
      · exact absurd ht'3 (by simp)

#print axioms pdZone_3
theorem pdZone_2 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree2 := by
  simp only [tree2, DfsPruneDomZone]
  intro t ht
  simp only [children2, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_3 hpruneZone_4 hpruneZone_5 hpruneZone_6 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_7 hpruneZone_10 
    · exact absurd ht'2 (by simp)

#print axioms pdZone_2
theorem pdZone_1 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree1 := by
  simp only [tree1, DfsPruneDomZone]
  intro t ht
  simp only [children1, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_2 hpruneZone_4 hpruneZone_5 hpruneZone_6 hpruneZone_10 
  · rcases ht'1 with rfl | ht'2
    · exact pdZone_18 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 
    · exact absurd ht'2 (by simp)

#print axioms pdZone_1
theorem pdZone_0 (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree0 := by
  simp only [tree0, DfsPruneDomZone]
  intro t ht
  simp only [children0, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_1 hpruneZone_4 hpruneZone_5 hpruneZone_6 hpruneZone_10 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 
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
theorem hforestEnum : ∀ t ∈ forest, DfsEnum (boxN m4res_1_1_4_5_6_8_12) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_0
  · exact absurd ht'1 (by simp)

/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly
OWED (b)
so this proof needs no hypotheses; at dead ends and internal nodes the condition is
inherited/vacuous. -/
theorem hforestPruneDom (hprune_4 : DfsPruneDom tree4) (hprune_5 : DfsPruneDom tree5) (hprune_6 : DfsPruneDom tree6) (hprune_10 : DfsPruneDom tree10) (hprune_24 : DfsPruneDom tree24) (hprune_25 : DfsPruneDom tree25) (hprune_26 : DfsPruneDom tree26) (hprune_32 : DfsPruneDom tree32) (hprune_33 : DfsPruneDom tree33) (hprune_39 : DfsPruneDom tree39) : ∀ t ∈ forest, DfsPruneDom t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_0 hprune_4 hprune_5 hprune_6 hprune_10 hprune_24 hprune_25 hprune_26 hprune_32 hprune_33 hprune_39 
  · exact absurd ht'1 (by simp)

/-- The zone-form per-prune-leaf domination over the FOREST: at the reach-prune
leaves exactly OWED (b)'s zone-form remainder (the per-leaf zone-form stubs of
section 5b; the UNRESTRICTED form is false --
`Fresh.ReachUtcProof.unrestricted_false`). -/
theorem hforestPruneDomZone (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) : ∀ t ∈ forest, DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_0 hpruneZone_4 hpruneZone_5 hpruneZone_6 hpruneZone_10 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 
  · exact absurd ht'1 (by simp)

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;
the artifacts give only the reconstructed root states, no opening-match record.
Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade
statement of E810's strict-monotone reading for this box. -/
-- STANDING: OWED
theorem m4fix_1_1_4_5_6_8_12_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_1_4_5_6_8_12) forest) :
    DfsRootAdm (boxN m4res_1_1_4_5_6_8_12) forest := hcadm

/-! ## 7. The census envelope and the composed theorems (generic data connection) -/

/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the
record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists
only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise
exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /
`m4boxClear_of_data` directly). -/
theorem hn17_1_1_4_5_6_8_12 : ∀ i : Fin 7, boxN m4res_1_1_4_5_6_8_12 i ≤ 17 := by
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

#print axioms hn17_1_1_4_5_6_8_12

/-- **The composed certificate theorem**: the banked record (`m4resData_1_1_4_5_6_8_12`,
[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the
90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim.  The
per-prune-leaf domination hypotheses are the reach_utc projection instances
(`hproj_<l> : reachutcProj_1_1_4_5_6_8_12_<l>`, OWED (b)'s per-leaf remainder); the verdict side
of each leaf is discharged inside `m4fix_1_1_4_5_6_8_12_pruneDom_<l>` from the transcribed
`reachutc_1_1_4_5_6_8_12.json` verdicts. -/
theorem m4fix_1_1_4_5_6_8_12_cert (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) (hcadm : DfsRootAdm (boxN m4res_1_1_4_5_6_8_12) forest) :
    M4CertSound (boxN m4res_1_1_4_5_6_8_12) ∧
      ∀ k ∈ m4res_1_1_4_5_6_8_12.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  ⟨m4CertSound_of_forest_zone (boxN m4res_1_1_4_5_6_8_12) forest hforestClosed hforestEnum
    (hforestPruneDomZone hpruneZone_4 hpruneZone_5 hpruneZone_6 hpruneZone_10 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 ) hcadm, leafKeys_env90 m4res_1_1_4_5_6_8_12 m4resData_1_1_4_5_6_8_12⟩

/-- **The composed clear-point theorem (the scaling target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --
the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest
instead of a crown. -/
theorem m4fix_1_1_4_5_6_8_12_boxClear (hpruneZone_4 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree4) (hpruneZone_5 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree5) (hpruneZone_6 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree6) (hpruneZone_10 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree10) (hpruneZone_24 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree24) (hpruneZone_25 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree25) (hpruneZone_26 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree26) (hpruneZone_32 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree32) (hpruneZone_33 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree33) (hpruneZone_39 : DfsPruneDomZone (boxN m4res_1_1_4_5_6_8_12) tree39) (hcadm : DfsRootAdm (boxN m4res_1_1_4_5_6_8_12) forest)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_1_4_5_6_8_12) hn17_1_1_4_5_6_8_12)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_1_4_5_6_8_12) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_1_4_5_6_8_12) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_cert hn17_1_1_4_5_6_8_12 hcc
    (m4CertSound_of_forest_zone (boxN m4res_1_1_4_5_6_8_12) forest hforestClosed hforestEnum (hforestPruneDomZone hpruneZone_4 hpruneZone_5 hpruneZone_6 hpruneZone_10 hpruneZone_24 hpruneZone_25 hpruneZone_26 hpruneZone_32 hpruneZone_33 hpruneZone_39 ) hcadm)
    g hface

#print axioms m4fix_1_1_4_5_6_8_12_cert
#print axioms m4fix_1_1_4_5_6_8_12_boxClear

end Fresh.M4FixRung2_1_1_4_5_6_8_12

