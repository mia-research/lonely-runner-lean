import Mathlib

/-!
# The n = 8 framework, stated from first principles (stage 1: statements only)

Written 2026-10-07 under the approved plan `snug-strolling-corbato` (stage 1a).  Nothing here imports the existing
`LonelyRunner` repo.  Every item is a definition or a `Prop`; only one trivial implication is proved, as the
classification evidence required by plan item 6.  The source is the owner's own account of the framework (the
original document pasted 2026-10-07 and owner messages M000 to M100 in `docs/n8/OWNER_INSTRUCTIONS_EXTRACT_v1.md`),
read in the order of `FRAMEWORK_COMPILATION_v9.md` sections 0 to 3.

Conventions kept from the owner's ground rules: no runner is stationary or at speed 0 (M015, M016); speeds are
positive and pairwise distinct; no floats (the reals here are Lean's exact `ℝ`); no density, coverage, cap, move
count or clock appears in any statement.

Each `Prop` carries a `-- STANDING:` tag read by `check.sh`:
  DEFINITION  an object of the framework (not a claim);
  OWED        a claim; nothing in this folder proves it.
-/

open Classical

namespace Fresh

/-- Distance from `x` to the nearest integer. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-! ## Objects of the framework (original document, ground rules and constraints on "any" arrangement) -/

/-- Eight runners: every speed positive (no runner stationary), and no two speeds equal. -/
-- STANDING: DEFINITION
def IsArrangement (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v

/-- The ordered form: speeds strictly increasing.  Ordering is a relabelling (v9 section 0). -/
-- STANDING: DEFINITION
def IsOrderedArrangement (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ StrictMono v

/-- The disparities seen by subject `k`: absolute differences of speeds from the subject's speed. -/
noncomputable def disparitySet (v : Fin 8 → ℝ) (k : Fin 8) : Finset ℝ :=
  (Finset.univ.erase k).image (fun i => |v i - v k|)

/-- `m` is the smallest disparity `d_min` of subject `k`. -/
-- STANDING: DEFINITION
def IsDmin (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) : Prop :=
  IsLeast (disparitySet v k : Set ℝ) m

/-- `m` is the largest disparity of subject `k` (the subject's own `d_max`, not the owner's grid direction D_max). -/
-- STANDING: DEFINITION
def IsSubjectDmax (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) : Prop :=
  IsGreatest (disparitySet v k : Set ℝ) m

/-- Runner `k` is isolated at instant `t`: every other runner is at circle distance at least `1/8`
(the closed condition, M002).  The reading of runner `i` is the difference of speeds from the subject. -/
-- STANDING: DEFINITION
def IsolatedAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : Prop :=
  ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt ((v i - v k) * t)

/-- Runner `k` is isolated at some positive instant (the conjecture asks for an isolation, not the first). -/
-- STANDING: DEFINITION
def Isolation (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ t : ℝ, 0 < t ∧ IsolatedAt v k t

/-- All eight runners are isolated at the same instant (global isolation). -/
-- STANDING: DEFINITION
def GloballyIsolatedAt (v : Fin 8 → ℝ) (t : ℝ) : Prop :=
  ∀ k, IsolatedAt v k t

/-! ## The AP and the grid (v9 sections 2 and 3) -/

/-- The residues of the grid indices mod 8 are a complete system: no two indices share a residue. -/
-- STANDING: DEFINITION
def CompleteResidues (idx : Fin 8 → ℤ) : Prop :=
  ∀ j j', idx j % 8 = idx j' % 8 → j = j'

/-- An arithmetic progression of eight speeds with common difference `d > 0`. -/
-- STANDING: DEFINITION
def IsAP (v : Fin 8 → ℝ) : Prop :=
  ∃ d v₀ : ℝ, 0 < d ∧ ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * d

/-- A grid arrangement: speeds `v₀ + idx j · d` whose indices have a complete residue system mod 8. -/
-- STANDING: DEFINITION
def IsGrid (v : Fin 8 → ℝ) : Prop :=
  ∃ (d v₀ : ℝ) (idx : Fin 8 → ℤ), 0 < d ∧ CompleteResidues idx ∧ ∀ j, v j = v₀ + (idx j : ℝ) * d

/-- A grid arrangement with deviation `e j` (anchored `e 0 = 0`, as in v9 Theorems 5 and 6). -/
-- STANDING: DEFINITION
def IsGridWithDeviation (v : Fin 8 → ℝ) : Prop :=
  ∃ (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ),
    0 < d ∧ CompleteResidues idx ∧ e 0 = 0 ∧ ∀ j, v j = v₀ + (idx j : ℝ) * d + e j

/-- The grid is globally isolated at every instant `a/(8d)` with `a` a unit mod 8 (v9 Theorems 4 and 5 for a grid). -/
-- STANDING: OWED
def GridGlobalIsolation : Prop :=
  ∀ (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ),
    0 < d → CompleteResidues idx → (∀ j, v j = v₀ + (idx j : ℝ) * d) →
    ∀ a : ℤ, IsCoprime a 8 → GloballyIsolatedAt v ((a : ℝ) / (8 * d))

/-! ## The classical statement, as the point of comparison -/

/-- The conjecture at n = 8, on arrangements: every runner is isolated at some positive instant. -/
-- STANDING: OWED
def LonelyRunnerEight : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k, Isolation v k

/-! ## Candidate statements of "the displacement is forced" (plan item 5) -/

/-- (a) Path form (M000, M005): along a continuous path of arrangements that starts at a grid arrangement, every
point of the path has an isolation for every subject.  The obstruction is two speeds meeting (rule 4), which the path
never reaches because every point is an arrangement.  No cap, covering, density, move count or float. -/
-- STANDING: OWED
def DisplacementPath : Prop :=
  ∀ γ : ℝ → Fin 8 → ℝ, ContinuousOn γ (Set.Icc 0 1) →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, IsArrangement (γ s)) →
    IsGrid (γ 0) →
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k, Isolation (γ s) k

/-- Runner at disparity `d` is in the way at `t`: it is within `1/8` of a whole lap of the subject. -/
-- STANDING: DEFINITION
def InWay (d t : ℝ) : Prop := distInt (d * t) < 1 / 8

/-- The next opening of runner `d` after `t`: the instant at which it stands at exactly `1/8` past a lap line. -/
noncomputable def nextOpening (d t : ℝ) : ℝ := (((⌈d * t - 1 / 8⌉ : ℤ) : ℝ) + 1 / 8) / d

/-- One cascade move: go to the largest next opening among the runners in the way; fix `t` if none is in the way. -/
-- STANDING: DEFINITION
def IsMove (ds : Finset ℝ) (t t' : ℝ) : Prop :=
  ((∀ d ∈ ds, ¬ InWay d t) ∧ t' = t) ∨
  (∃ d ∈ ds, InWay d t ∧ t' = nextOpening d t ∧ ∀ d' ∈ ds, InWay d' t → nextOpening d' t ≤ t')

/-- The cascade from `t₀` reaches a fixed point. -/
-- STANDING: DEFINITION
def CascadeFixes (ds : Finset ℝ) (t₀ : ℝ) : Prop :=
  ∃ seq : ℕ → ℝ, seq 0 = t₀ ∧ (∀ n, IsMove ds (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N

/-- (b) Cascade form: from the bound `1/(8 d_min)` the cascade reaches a fixed point, for every arrangement and
subject.  KEPT ONLY TO BE CLASSIFIED: it has the termination shape that rule 7 bans as an existence argument
and is a restatement of the conjecture (`doors_agree` in the existing repo, Theorem 13 in the paper). -/
-- STANDING: OWED
def CascadeForm : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k m, IsDmin v k m → CascadeFixes (disparitySet v k) (1 / (8 * m))

/-- Some candidate scale `(k + 1/8)/e` (an opening of the flank `e`) is clear for every disparity. -/
-- STANDING: DEFINITION
def CandidateScaleClear (ds : Finset ℝ) : Prop :=
  ∃ e ∈ ds, ∃ k : ℕ, ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * (((k : ℝ) + 1 / 8) / e))

/-- (c) Candidate-scale form (Theorem 9, Localisation, in the paper): for every arrangement and subject, some opening
of some flank is clear.  A restatement (MECHANISM_MAP_v5 section 5). -/
-- STANDING: OWED
def CandidateScaleForm : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k, CandidateScaleClear (disparitySet v k)

/-! ## Classification evidence (plan item 6) -/

/-- (a) follows from the conjecture in one line: specialise it along the path.  This is the only implication
proved in this folder.  The converse needs a path from a grid arrangement to a given arrangement (the sorted positive
arrangements are a convex set containing the AP) and relabelling; neither is attempted in stage 1. -/
theorem lonelyRunnerEight_imp_displacementPath : LonelyRunnerEight → DisplacementPath :=
  fun h _ _ hγ _ s hs k => h _ (hγ s hs) k

#print axioms lonelyRunnerEight_imp_displacementPath

end Fresh
