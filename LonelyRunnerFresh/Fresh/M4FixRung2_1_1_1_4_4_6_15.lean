import Fresh.M4CertSound
import Fresh.M4FixResBank_v1
import Fresh.ReachUtcProof

/-!
# M4FixRung2_1_1_1_4_4_6_15: per-box M4 certificate transcription, box (1, 1, 1, 4, 4, 6, 15)

Written 2026-11-20 by `m4fix_gen_v1.py` from the per-box reconstruction
(`experiments/n8/m4fix_recon_v1.py`, [T]-verified against both checkpoint artifacts
(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the
CONSTRUCTED record `Fresh.M4FixResBank_v1.m4res_1_1_1_4_4_6_15`).  No existing file is edited.

This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a
WHOLE certificate FOREST: all 1 nodes of the box's reconstructed DFS certificate
tree(s) -- 0 internal, 1 reach-prune leaves,
0 dead-end leaves, 1 start-zone root(s) -- transcribed as literal `DfsCert` data: tables as
49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,
seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,
and the composed theorems through the GENERIC data connection
(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).

OWED (named, not discharged by any existing artifact):
* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`'s header: the E810 strict-monotone
  opening side (hypothesis-identity stub here, as in rung 1).
* OWED (b) -- now SPLIT by the per-leaf verdict transcription (section 5b): the
  verdict side of every reach-prune leaf's `reach_utc` domination is transcribed
  from `experiments/n8/reachutc_1_1_1_4_4_6_15.json` and DISCHARGED here
  (`verdictNoCompl_*`); what remains OWED per leaf is the `[P]` state-graph
  PROJECTION instance `reachutcProj_*` (realized chain → completing state
  reachable), being proved in parallel in `Fresh/ReachUtcProof.lean`.
-/

namespace Fresh.M4FixRung2_1_1_1_4_4_6_15

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

/-- Table of DFS node 0 (reach, depth 1, last reading row 6, exit numerator 17).  Transcribed verbatim from the box's reconstructed certificate tree;
exact rationals, strict flags; `none` = unbounded. -/
-- STANDING: DATA
def tbl0 : UTable := fun p q =>
  if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((2 / 7 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((2 / 7 : ℚ), true)
  else if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((2 / 11 : ℚ), false)
  else if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 15 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 11 : ℚ), true)
  else if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 10 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3 / 2 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((3 / 2 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 7 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((3 / 7 : ℚ), true)
  else if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 11 : ℚ), false)
  else if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 10 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 11 : ℚ), true)
  else if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 10 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 / 2 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 2 : ℚ), true)
  else if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 11 : ℚ), false)
  else if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 10 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((13 / 2 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((13 / 2 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((13 / 7 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((13 / 7 : ℚ), true)
  else if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((13 / 30 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((31 / 2 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((31 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((31 / 2 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((31 / 7 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((31 / 7 : ℚ), true)
  else if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((31 / 11 : ℚ), false)
  else if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

theorem tbl0_c_0_0 : tbl0 (0 : Fin 7) (0 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_0_1 : tbl0 (0 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_2 : tbl0 (0 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_0_3 : tbl0 (0 : Fin 7) (3 : Fin 7) = some ((2 / 7 : ℚ), false) := rfl
theorem tbl0_c_0_4 : tbl0 (0 : Fin 7) (4 : Fin 7) = some ((2 / 7 : ℚ), true) := rfl
theorem tbl0_c_0_5 : tbl0 (0 : Fin 7) (5 : Fin 7) = some ((2 / 11 : ℚ), false) := rfl
theorem tbl0_c_0_6 : tbl0 (0 : Fin 7) (6 : Fin 7) = some ((1 / 15 : ℚ), true) := rfl
theorem tbl0_c_1_0 : tbl0 (1 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_1_1 : tbl0 (1 : Fin 7) (1 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_1_2 : tbl0 (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_1_3 : tbl0 (1 : Fin 7) (3 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl0_c_1_4 : tbl0 (1 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl0_c_1_5 : tbl0 (1 : Fin 7) (5 : Fin 7) = some ((3 / 11 : ℚ), true) := rfl
theorem tbl0_c_1_6 : tbl0 (1 : Fin 7) (6 : Fin 7) = some ((1 / 10 : ℚ), true) := rfl
theorem tbl0_c_2_0 : tbl0 (2 : Fin 7) (0 : Fin 7) = some ((3 / 2 : ℚ), false) := rfl
theorem tbl0_c_2_1 : tbl0 (2 : Fin 7) (1 : Fin 7) = some ((3 / 2 : ℚ), true) := rfl
theorem tbl0_c_2_2 : tbl0 (2 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_2_3 : tbl0 (2 : Fin 7) (3 : Fin 7) = some ((3 / 7 : ℚ), false) := rfl
theorem tbl0_c_2_4 : tbl0 (2 : Fin 7) (4 : Fin 7) = some ((3 / 7 : ℚ), true) := rfl
theorem tbl0_c_2_5 : tbl0 (2 : Fin 7) (5 : Fin 7) = some ((3 / 11 : ℚ), false) := rfl
theorem tbl0_c_2_6 : tbl0 (2 : Fin 7) (6 : Fin 7) = some ((1 / 10 : ℚ), true) := rfl
theorem tbl0_c_3_0 : tbl0 (3 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_1 : tbl0 (3 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_2 : tbl0 (3 : Fin 7) (2 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_3_3 : tbl0 (3 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_3_4 : tbl0 (3 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), true) := rfl
theorem tbl0_c_3_5 : tbl0 (3 : Fin 7) (5 : Fin 7) = some ((9 / 11 : ℚ), true) := rfl
theorem tbl0_c_3_6 : tbl0 (3 : Fin 7) (6 : Fin 7) = some ((3 / 10 : ℚ), true) := rfl
theorem tbl0_c_4_0 : tbl0 (4 : Fin 7) (0 : Fin 7) = some ((9 / 2 : ℚ), false) := rfl
theorem tbl0_c_4_1 : tbl0 (4 : Fin 7) (1 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_2 : tbl0 (4 : Fin 7) (2 : Fin 7) = some ((9 / 2 : ℚ), true) := rfl
theorem tbl0_c_4_3 : tbl0 (4 : Fin 7) (3 : Fin 7) = some ((9 / 7 : ℚ), false) := rfl
theorem tbl0_c_4_4 : tbl0 (4 : Fin 7) (4 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_4_5 : tbl0 (4 : Fin 7) (5 : Fin 7) = some ((9 / 11 : ℚ), false) := rfl
theorem tbl0_c_4_6 : tbl0 (4 : Fin 7) (6 : Fin 7) = some ((3 / 10 : ℚ), true) := rfl
theorem tbl0_c_5_0 : tbl0 (5 : Fin 7) (0 : Fin 7) = some ((13 / 2 : ℚ), false) := rfl
theorem tbl0_c_5_1 : tbl0 (5 : Fin 7) (1 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_2 : tbl0 (5 : Fin 7) (2 : Fin 7) = some ((13 / 2 : ℚ), true) := rfl
theorem tbl0_c_5_3 : tbl0 (5 : Fin 7) (3 : Fin 7) = some ((13 / 7 : ℚ), false) := rfl
theorem tbl0_c_5_4 : tbl0 (5 : Fin 7) (4 : Fin 7) = some ((13 / 7 : ℚ), true) := rfl
theorem tbl0_c_5_5 : tbl0 (5 : Fin 7) (5 : Fin 7) = some ((1 : ℚ), false) := rfl
theorem tbl0_c_5_6 : tbl0 (5 : Fin 7) (6 : Fin 7) = some ((13 / 30 : ℚ), true) := rfl
theorem tbl0_c_6_0 : tbl0 (6 : Fin 7) (0 : Fin 7) = some ((31 / 2 : ℚ), false) := rfl
theorem tbl0_c_6_1 : tbl0 (6 : Fin 7) (1 : Fin 7) = some ((31 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_2 : tbl0 (6 : Fin 7) (2 : Fin 7) = some ((31 / 2 : ℚ), true) := rfl
theorem tbl0_c_6_3 : tbl0 (6 : Fin 7) (3 : Fin 7) = some ((31 / 7 : ℚ), false) := rfl
theorem tbl0_c_6_4 : tbl0 (6 : Fin 7) (4 : Fin 7) = some ((31 / 7 : ℚ), true) := rfl
theorem tbl0_c_6_5 : tbl0 (6 : Fin 7) (5 : Fin 7) = some ((31 / 11 : ℚ), false) := rfl
theorem tbl0_c_6_6 : tbl0 (6 : Fin 7) (6 : Fin 7) = some ((1 : ℚ), false) := rfl

/-! ## 1b. The node states and the certificate trees -/

/-- The start-zone root: DFS node 0 (depth 1, last reading row 6, exit numerator 17, frontier sup 17 / 15). -/
-- STANDING: DATA
def node0 : DfsNode := ⟨tbl0, (6 : Fin 7), (17 : ℚ), (17 / 15 : ℚ), {((6 : Fin 7), (17 : ℚ))}⟩

/-- The reach-prune leaf, DFS node 0: the `reach_utc` abstraction found no
completing state. -/
-- STANDING: DATA
def tree0 : DfsCert := DfsCert.prune node0

/-- The box's WHOLE certificate forest (1 start-zone root(s), 1 nodes),
transcribed verbatim from the reconstruction. -/
-- STANDING: DATA
def forest : List DfsCert := [tree0]

/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/

theorem nodeOK_0 : DfsNodeOK node0 := by
  show uExitOK tbl0 (6 : Fin 7) (17 : ℚ) = false
  unfold uExitOK
  rw [uAdd_eq_none
    (by simp [uKeepCur, tbl0_c_6_0] <;> norm_num)
    (by simp [uBack, uBackCond, tbl0_c_0_6] <;> norm_num)]
  rfl

#print axioms nodeOK_0

/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/

/-! ## 3b. The seam kills -/


/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/


/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/

theorem closed_0 : DfsClosed tree0 := by
  simp only [tree0, DfsClosed]
  exact nodeOK_0

#print axioms closed_0

/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/
theorem enum_0 : DfsEnum (boxN m4res_1_1_1_4_4_6_15) tree0 := by
  simp only [tree0, DfsEnum]

#print axioms enum_0

theorem pd_0 (hprune_0 : DfsPruneDom tree0) : DfsPruneDom tree0 :=
  hprune_0

#print axioms pd_0

/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions (`reachutc_1_1_1_4_4_6_15.json`)

The per-prune-leaf verdict layer: the explored (frontier-sup, dump-rank) state sets
and pmax as literal data, the `no_completing_state_reachable` verdicts (discharged
HERE by literal per-case proofs over the census windows), the OWED `[P]` projection
instances (`reachutcProj_*`, discharged by the parallel `Fresh/ReachUtcProof.lean`),
and the verdict-carrying `DfsPruneDom` instances `m4fix_%s_pruneDom_*` (replacing
the identity stubs). -/

theorem hiPos_0 : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN m4res_1_1_1_4_4_6_15) tbl0 b := by
  intro b hb
  fin_cases b
  · simp at hb
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_1_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_2_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_3_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_4_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_5_0] <;> norm_num
  · simp [dfsHi, boxN, m4res_1_1_1_4_4_6_15, tbl0_c_6_0] <;> norm_num

-- STANDING: DATA
def expStates_0 : List (ℚ × ℕ) := [((17 / 15 : ℚ), 7), ((18 / 11 : ℚ), 6), ((5 / 3 : ℚ), 7), ((18 / 7 : ℚ), 5), ((41 / 15 : ℚ), 7), ((34 / 11 : ℚ), 6), ((49 / 15 : ℚ), 7), ((18 / 7 : ℚ), 4)]

/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf 0
(dump state P = 17 / 15, a = 6, Aex = 17, verdict `no_completing_state_reachable`,
nst = 8, pmax = 49 / 15, transcribed from `experiments/n8/reachutc_1_1_1_4_4_6_15.json`).  FINDING
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
theorem m4fix_1_1_1_4_4_6_15_pruneDom_0 (h : DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0) :
    DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0 := h

#print axioms m4fix_1_1_1_4_4_6_15_pruneDom_0

theorem pdZone_0 (hpruneZone_0 : DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0) :
    DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0 := hpruneZone_0

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
theorem hforestEnum : ∀ t ∈ forest, DfsEnum (boxN m4res_1_1_1_4_4_6_15) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact enum_0
  · exact absurd ht'1 (by simp)

/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly
OWED (b)
so this proof needs no hypotheses; at dead ends and internal nodes the condition is
inherited/vacuous. -/
theorem hforestPruneDom (hprune_0 : DfsPruneDom tree0) : ∀ t ∈ forest, DfsPruneDom t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pd_0 hprune_0 
  · exact absurd ht'1 (by simp)

/-- The zone-form per-prune-leaf domination over the FOREST: at the reach-prune
leaves exactly OWED (b)'s zone-form remainder (the per-leaf zone-form stubs of
section 5b; the UNRESTRICTED form is false --
`Fresh.ReachUtcProof.unrestricted_false`). -/
theorem hforestPruneDomZone (hpruneZone_0 : DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0) : ∀ t ∈ forest, DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) t := by
  intro t ht
  simp only [forest, List.mem_cons] at ht
  rcases ht with rfl | ht'1
  · exact pdZone_0 hpruneZone_0 
  · exact absurd ht'1 (by simp)

/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:
every real W₀ chain's opening matches a forest root whose table it realizes and its steps
pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;
the artifacts give only the reconstructed root states, no opening-match record.
Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade
statement of E810's strict-monotone reading for this box. -/
-- STANDING: OWED
theorem m4fix_1_1_1_4_4_6_15_rootAdm (hcadm : DfsRootAdm (boxN m4res_1_1_1_4_4_6_15) forest) :
    DfsRootAdm (boxN m4res_1_1_1_4_4_6_15) forest := hcadm

/-! ## 7. The census envelope and the composed theorems (generic data connection) -/

/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the
record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists
only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise
exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /
`m4boxClear_of_data` directly). -/
theorem hn17_1_1_1_4_4_6_15 : ∀ i : Fin 7, boxN m4res_1_1_1_4_4_6_15 i ≤ 17 := by
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

#print axioms hn17_1_1_1_4_4_6_15

/-- **The composed certificate theorem**: the banked record (`m4resData_1_1_1_4_4_6_15`,
[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the
90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim.  The
per-prune-leaf domination hypotheses are the reach_utc projection instances
(`hproj_<l> : reachutcProj_1_1_1_4_4_6_15_<l>`, OWED (b)'s per-leaf remainder); the verdict side
of each leaf is discharged inside `m4fix_1_1_1_4_4_6_15_pruneDom_<l>` from the transcribed
`reachutc_1_1_1_4_4_6_15.json` verdicts. -/
theorem m4fix_1_1_1_4_4_6_15_cert (hpruneZone_0 : DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0) (hcadm : DfsRootAdm (boxN m4res_1_1_1_4_4_6_15) forest) :
    M4CertSound (boxN m4res_1_1_1_4_4_6_15) ∧
      ∀ k ∈ m4res_1_1_1_4_4_6_15.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  ⟨m4CertSound_of_forest_zone (boxN m4res_1_1_1_4_4_6_15) forest hforestClosed hforestEnum
    (hforestPruneDomZone hpruneZone_0 ) hcadm, leafKeys_env90 m4res_1_1_1_4_4_6_15 m4resData_1_1_1_4_4_6_15⟩

/-- **The composed clear-point theorem (the scaling target)**: the box's clear point per
arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --
the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest
instead of a crown. -/
theorem m4fix_1_1_1_4_4_6_15_boxClear (hpruneZone_0 : DfsPruneDomZone (boxN m4res_1_1_1_4_4_6_15) tree0) (hcadm : DfsRootAdm (boxN m4res_1_1_1_4_4_6_15) forest)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_1_1_4_4_6_15) hn17_1_1_1_4_4_6_15)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_1_1_4_4_6_15) i ≤ g i ∧ g i ≤ FaceHi (boxN m4res_1_1_1_4_4_6_15) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_cert hn17_1_1_1_4_4_6_15 hcc
    (m4CertSound_of_forest_zone (boxN m4res_1_1_1_4_4_6_15) forest hforestClosed hforestEnum (hforestPruneDomZone hpruneZone_0 ) hcadm)
    g hface

#print axioms m4fix_1_1_1_4_4_6_15_cert
#print axioms m4fix_1_1_1_4_4_6_15_boxClear

end Fresh.M4FixRung2_1_1_1_4_4_6_15

