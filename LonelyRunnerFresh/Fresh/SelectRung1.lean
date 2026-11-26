import Fresh.ChainDomPerRecBox1
import Fresh.WordCoverSide

/-!
# SelectRung1: the census-to-arbitrary-endpoint rung toward `select`

The consumer `Fresh.OpeningChainConflict.twoWindows_of_select_opening_record` takes a
`select` hypothesis: for EVERY realized first-window walk
`(⟨i, zEntry j₀, zExit j₀⟩ :: rest)` from the arrangement's own fine start table `U`,
some record `e` of `compFamOf b` attests FROM THAT WALK (`AttestsFrom e walk U`) plus an
opening record.  The banked census data (`Fresh.ChainDomPerRecBox1`,
`perrec8_diag_v1.{py,json,out}`) is per-record with the FIXED start `mkOf n` and specific
census chains.  This file banks the rung that carries a census attestation to an
arbitrary endpoint table, plus the honest statement of what the banked data does and
does not support.

## 1. The direction (derived, not assumed)

`CapsDom V y caps x` demands, for each cap `c` of the walk, a stored entry `V y z =
some (c₀, s)` with `(c₀ : ℝ) ≤ c` — a stored bound no looser than the cap.  Hence
`CapsDom` is CONTRAVARIANT in its table argument: a componentwise TIGHTER table
(smaller stored values, `none` read as loosest) dominates at least as many cap walks.
This matches the data-side split check (`perrec8_diag_v1.out`: running the census words
from the LOOSER sparse start `u0Of` survives but stops dominating —
`sparse_dominating_words = 0` — while every run from the tighter full closure `mkOf`
dominates all 4 records, `inter_fullV = 804`).  So the transfer direction is:
a census-table attestation implies attestation at any componentwise-SMALLER endpoint
table (`capsDom_tabLe`, `attestsFrom_tabLe` below).

## 2. What the banked data supports (the rung), and what it does not

* SUPPORTED (proved here): for any start table `U` whose walk-traces are pointwise
  tighter than the transcribed census trace `T8_1_3_4_5_5_5_7_12`, record r1 = ⟨6, 1,
  65, 31, [(6, 55/117)]⟩ attests the walk (its (1,6) census entry 55/117 EQUALS the
  cap).  The box-1 rung packages this into the select shape with the two data the banked
  census does NOT carry taken as explicit OWED hypotheses: (a) the endpoint-domination
  datum `hdom` (every trace of the walk's own run is tighter than the census trace),
  (b) the opening record `(j, k, R)`.
* NOT SUPPORTED — reported precisely, with an exact counterexample banked below:
  the fully-universal AttestsFrom half (for every fine table) is FALSE.  The loose
  table `constTab` (every entry `(1000, false)`) is fine for EVERY in-box arrangement
  (`ufine_constTab`), every envelope-zone chain survives on it with trace still
  `constTab` (`chainRun_constTab_env` — entries never tighten because every propagated
  product is `10^6 · c ≥ 1000`), and NO record of the box-1 family attests anything
  from it (`constTab_attests_nothing_b1`: each record's cap is `< 1000` while the trace
  entry is exactly 1000).  Thus the census data cannot carry attestations to arbitrary
  loose starts; the start table's provenance (tightness toward `mkOf n`) is a genuine
  missing datum (OWED), and a naive "tighter start => tighter trace" simulation is
  false in general (the keep-cur asymmetry: a run from a tighter start may keep-cur and
  skip the propagation that tightens OTHER pairs of the looser run's trace).

All arithmetic is exact (`norm_num` on literals; the data-side checks of
`scratch_rung1/check1.py` run `python3 -I` with `Fraction`).  Every theorem carries
`#print axioms`; the accepted profile is the standard three — `sorryAx` is failure.
-/

namespace Fresh.SelectRung1

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed
  Fresh.OneSidedGlue Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData
  Fresh.ChainDomPerRec8 Fresh.WordCoverSide

/-! ## 1. The pointwise table order and the CapsDom direction -/

/-- The pointwise bound-domination order: `TabLe W V` reads "W is componentwise
TIGHTER-OR-EQUAL than V" — every stored bound of `V` is matched at the same pair by a
stored bound of `W` with a SMALLER-OR-EQUAL value (strict flags are not compared; the
value is what `CapsDom` and the realization both consume). -/
-- STANDING: DEFINITION
def TabLe (W V : UTable) : Prop :=
  ∀ i : Fin 7, ∀ j : Fin 7, ∀ c : ℚ, ∀ s : Bool, V i j = some (c, s) →
    ∃ c' : ℚ, ∃ s' : Bool, W i j = some (c', s') ∧ ((c' : ℚ) : ℝ) ≤ ((c : ℚ) : ℝ)

theorem tabLe_refl (U : UTable) : TabLe U U := fun _ _ c s h => ⟨c, s, h, le_refl _⟩

#print axioms tabLe_refl

/-- **THE DIRECTION (deliverable 1).**  `CapsDom` is contravariant in the table:
a componentwise TIGHTER table dominates at least as many cap walks.  This is the
monotonicity that lets a census-table attestation imply attestation at any
componentwise-SMALLER endpoint table. -/
theorem capsDom_tabLe {W V : UTable} (h : TabLe W V) {y x : Fin 7}
    {caps : List (Fin 7 × ℝ)} (hd : CapsDom V y caps x) : CapsDom W y caps x := by
  induction hd with
  | nil x => exact CapsDom.nil x
  | cons y z c l w hentry hrest ih =>
    obtain ⟨c₀, s, hV, hcle⟩ := hentry
    obtain ⟨c₁, s₁, hW, hcle₁⟩ := h y z c₀ s hV
    exact CapsDom.cons y z c l w ⟨c₁, s₁, hW, le_trans hcle₁ hcle⟩ ih

#print axioms capsDom_tabLe

/-- **The attestation transfer (deliverable 1, AttestsFrom level).**  If every trace of
the run of `steps` from `U` is pointwise tighter than SOME trace of the run from the
census start `U₀`, a census attestation at `U₀` transfers to `U`. -/
theorem attestsFrom_tabLe {e : ComposedEdge} {steps : List Step} {U₀ U : UTable}
    (hatt : AttestsFrom e steps U₀)
    (hsub : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 steps = some (V, af, Af) →
      ∃ V₀ : UTable, ∃ af₀ : Fin 7, ∃ Af₀ : ℚ,
        chainRun U₀ 0 1 steps = some (V₀, af₀, Af₀) ∧ TabLe V V₀) :
    AttestsFrom e steps U := by
  intro V af Af hrun
  obtain ⟨V₀, af₀, Af₀, hrun₀, hle⟩ := hsub V af Af hrun
  exact capsDom_tabLe hle (hatt V₀ af₀ Af₀ hrun₀)

#print axioms attestsFrom_tabLe

/-- The census attestation, transfer form, record r1 = ⟨6, 1, 65, 31, [(6, 55/117)]⟩:
the census trace's (1, 6) entry 55/117 EQUALS the cap, so any trace pointwise tighter
than `T8_1_3_4_5_5_5_7_12` attests the record (its own endpoint table, any start). -/
theorem attestsFrom_r1_tabLe {U : UTable} {W : List Step}
    (hsub : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 W = some (V, af, Af) → TabLe V T8_1_3_4_5_5_5_7_12) :
    AttestsFrom ⟨6, 1, 65, 31, [(6, (55 / 117 : ℝ))]⟩ W U := by
  intro V af Af hrun
  obtain ⟨c₁, s₁, hW, hcle₁⟩ :=
    hsub V af Af hrun 1 6 (55 / 117 : ℚ) true (by simp [T8_1_3_4_5_5_5_7_12])
  refine capsDom_single ⟨c₁, s₁, hW, ?_⟩
  exact hcle₁.trans (by norm_num : ((55 / 117 : ℚ) : ℝ) ≤ (55 / 117 : ℝ))

#print axioms attestsFrom_r1_tabLe

/-- The census attestation, transfer form, record r0 = ⟨6, 0, 13, 3, [(6, 1870/13113)]⟩:
the census trace's (0, 6) entry 50/351 is strictly below the cap. -/
theorem attestsFrom_r0_tabLe {U : UTable} {W : List Step}
    (hsub : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 W = some (V, af, Af) → TabLe V T8_1_3_4_5_5_5_7_12) :
    AttestsFrom ⟨6, 0, 13, 3, [(6, (1870 / 13113 : ℝ))]⟩ W U := by
  intro V af Af hrun
  obtain ⟨c₁, s₁, hW, hcle₁⟩ :=
    hsub V af Af hrun 0 6 (50 / 351 : ℚ) true (by simp [T8_1_3_4_5_5_5_7_12])
  refine capsDom_single ⟨c₁, s₁, hW, ?_⟩
  exact hcle₁.trans (by norm_num : ((50 / 351 : ℚ) : ℝ) ≤ (1870 / 13113 : ℝ))

#print axioms attestsFrom_r0_tabLe

/-- Records r2, r3 share r1's pair and cap: the same transfer attests them. -/
theorem attestsFrom_r2_tabLe {U : UTable} {W : List Step}
    (hsub : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 W = some (V, af, Af) → TabLe V T8_1_3_4_5_5_5_7_12) :
    AttestsFrom ⟨6, 1, 5, 3, [(6, (55 / 117 : ℝ))]⟩ W U :=
  attestsFrom_r1_tabLe hsub

theorem attestsFrom_r3_tabLe {U : UTable} {W : List Step}
    (hsub : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 W = some (V, af, Af) → TabLe V T8_1_3_4_5_5_5_7_12) :
    AttestsFrom ⟨6, 1, 65, 47, [(6, (55 / 117 : ℝ))]⟩ W U :=
  attestsFrom_r1_tabLe hsub

#print axioms attestsFrom_r2_tabLe
#print axioms attestsFrom_r3_tabLe

/-- The census attestation at the census start itself (the `Attests8` datum
`attests_1_3_4_5_5_5_7_r1`, restated: `Attests8 n e steps` is `AttestsFrom e steps
(mkOf n)` by definition). -/
theorem attestsFrom_r1_census :
    AttestsFrom ⟨6, 1, 65, 31, [(6, (55 / 117 : ℝ))]⟩ steps8_1_3_4_5_5_5_7
      (mkOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) :=
  attests_1_3_4_5_5_5_7_r1

#print axioms attestsFrom_r1_census

/-! ## 2. The box-1 rung toward the `select` shape -/

/-- The box-1 family dispatch: `compFamOf` at the literal box is the banked composed
family `compFam_1_3_4_5_5_5_7` (whose 4 records are members of the dump transcription,
`control_1_3_4_5_5_5_7`). -/
theorem compFamOf_b1 :
    compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) = compFam_1_3_4_5_5_5_7 := by
  simp [compFamOf]

#print axioms compFamOf_b1

/-- **The box-1 rung** (the strongest statement the banked data supports toward
`Fresh.OpeningChainConflict.twoWindows_of_select_opening_record`'s `select`): for box
`b₁ := ![1, 3, 4, 5, 5, 5, 7]`, every realized first-window walk from the arrangement's
own fine start `U` is attested by the census record r1 (an edge of `compFamOf b₁`),
PROVIDED the two data the banked census does not carry:
* `hdom` -- STANDING: OWED (endpoint-domination datum): every trace of the walk's own
  run from `U` is pointwise tighter than the transcribed census trace.  Data-side this
  is a per-walk exact replay of `chainRun` from the walk's own start (the
  `perrec8_diag_v1.py` mirror generalizes verbatim); it is FALSE for loose starts (the
  `constTab` counterexample below), so it needs the start table's provenance.
* `hopen` -- STANDING: OWED (opening record): the per-arrangement `(j, k, R)` datum.
  Exact-arithmetic note: for r1 it forces `g 1 / g 6 > 31 / 65` (r1's own demand), so it
  can only be supplied where r1's demand is live; the evidence each arrangement needs is
  the exact per-`g` search of admissible `(j, k, R)` (rational, decidable per `g`). -/
theorem selectRung1_1_3_4_5_5_5_7
    {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hpin : g 0 = 1) {U : UTable} (hfine : UFine g U)
    (i : Fin 7) (j₀ : Fin 16) (rest : List Step)
    (hw : ChainRealized g U 0 1 (⟨i, zEntry j₀, zExit j₀⟩ :: rest))
    (henv : EnvChain i (zExit j₀) rest)
    (j : ℕ) (k : ℕ) (R : ℝ)
    (hopen : 9 ≤ R ∧ R ≤ 15 ∧ 1 ≤ k ∧ g (6 : Fin 7) * R = (j : ℝ) * 8 + 1 ∧
      inZone g (1 : Fin 7) k R ∧
      ((j : ℝ) * 8 + 1) / ((k : ℝ) * 8 - 1) ≤ (65 : ℝ) / 31)
    (hdom : ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U 0 1 (⟨i, zEntry j₀, zExit j₀⟩ :: rest) = some (V, af, Af) →
      TabLe V T8_1_3_4_5_5_5_7_12) :
    ∃ (e : ComposedEdge) (j' : ℕ) (k' : ℕ) (R' : ℝ),
      e ∈ (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)).edges ∧
      AttestsFrom e (⟨i, zEntry j₀, zExit j₀⟩ :: rest) U ∧
      9 ≤ R' ∧ R' ≤ 15 ∧ 1 ≤ k' ∧ g e.x * R' = (j' : ℝ) * 8 + 1 ∧
      inZone g e.y k' R' ∧
      ((j' : ℝ) * 8 + 1) / ((k' : ℝ) * 8 - 1) ≤ (e.A : ℝ) / (e.B : ℝ) := by
  refine ⟨⟨6, 1, 65, 31, [(6, (55 / 117 : ℝ))]⟩, j, k, R, ?_, ?_, hopen.1, hopen.2.1,
    hopen.2.2.1, ?_, ?_, ?_⟩
  · simp [compFamOf_b1, compFam_1_3_4_5_5_5_7]
  · exact attestsFrom_r1_tabLe hdom
  · exact hopen.2.2.2.1
  · exact hopen.2.2.2.2.1
  · exact hopen.2.2.2.2.2.trans (by norm_num : (65 : ℝ) / 31 ≤
      (((65 : ℤ) : ℝ)) / (((31 : ℤ) : ℝ)))

#print axioms selectRung1_1_3_4_5_5_5_7

/-! ## 3. The loose-start counterexample: the fully-universal AttestsFrom half is FALSE -/

/-- The loose table: every pair stores the loose bound `(1000, false)` — fine for EVERY
in-box arrangement, yet attesting nothing. -/
-- STANDING: DEFINITION
def constTab : UTable := fun _ _ => some ((1000 : ℚ), false)

theorem constTab_apply (p q : Fin 7) : constTab p q = some ((1000 : ℚ), false) := rfl

#print axioms constTab_apply

/-- The loose start realizes every arrangement of box b₁: the largest envelope ratio is
15/2 = 7.5 (FaceHi ≤ 15/2 on the literal box, FaceLo ≥ 1), and every stored bound is
1000. -/
theorem ufine_constTab {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i) : UFine g constTab := by
  have hhi : ∀ i, FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ (15 / 2 : ℝ) := by
    intro i; fin_cases i <;> simp [FaceHi] <;> norm_num
  intro i j c s hc
  obtain ⟨rfl, rfl⟩ := hc
  have h1 : g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i := (hface i).2
  have h2 : (1 : ℝ) ≤ g j := (faceLo_ge_one _ j).trans (hface j).1
  have hpi : (0 : ℝ) < g i := lt_of_lt_of_le zero_lt_one ((faceLo_ge_one _ i).trans (hface i).1)
  have hdiv : g i / g j ≤ g i := div_le_self (le_of_lt hpi) h2
  calc g i / g j ≤ g i := hdiv
    _ ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i := h1
    _ ≤ 15 / 2 := hhi i
    _ ≤ 1000 := by norm_num

#print axioms ufine_constTab

/-- One `add` on the loose start is a no-op: the stored 1000 beats every envelope step
bound `c ∈ (1/1000, 1000)` (keep-cur fails, the two-cycle back-check passes, and every
propagated product `10^6 · c` stays above 1000). -/
theorem uAdd_constTab (i j : Fin 7) (c : ℚ) (s : Bool) (h1 : (1 : ℚ) / 1000 < c)
    (h2 : c < 1000) : uAdd constTab i j c s = some constTab := by
  have hp : (0 : ℚ) < 1000 := by norm_num
  have h2c : (1 : ℚ) < c * 1000 := by
    have t := mul_lt_mul_of_pos_right h1 hp
    have h6 : (1 : ℚ) / 1000 * 1000 = 1 := by norm_num
    rw [h6] at t
    exact t
  have hKc : (1000 : ℚ) * c = c * 1000 := mul_comm 1000 c
  have e1 : ¬ ((1000 : ℚ) < c) := by linarith
  have e2 : ¬ ((1000 : ℚ) = c) := by linarith
  have hK : uKeepCur constTab i j c s = false := by
    show ((1000 : ℚ) < c || (1000 = c && (false || !s))) = false
    simp [e1, e2]
  have e3 : ¬ ((1000 : ℚ) * c < 1) := by rw [hKc]; linarith
  have e4 : ¬ ((1000 : ℚ) * c = 1) := by rw [hKc]; linarith
  have hB : uBack constTab i j c s = false := by
    show ((1000 : ℚ) * c < 1 || (1000 * c = 1 && (s || false))) = false
    simp [e3, e4]
  have h4 : (1000 : ℚ) < 1000 * c * 1000 := by
    have h5 := mul_lt_mul_of_pos_right h2c hp
    have h6 : (c * 1000) * 1000 = 1000 * c * 1000 := by ring
    rw [h6] at h5
    linarith
  have e5 : ¬ ((1000 : ℚ) * c * 1000 < 1000) := by linarith
  have e6 : ¬ ((1000 : ℚ) * c * 1000 = 1000) := by linarith
  have hP : uProp constTab i j c s = constTab := by
    funext p q
    show (if (1000 * c * 1000 : ℚ) < 1000 ||
          (1000 * c * 1000 = 1000 && (false || s || false) && !false)
        then some ((1000 * c * 1000 : ℚ), false || s || false)
        else some ((1000 : ℚ), false)) = some ((1000 : ℚ), false)
    rw [if_neg (by simp [e5, e6])]
  unfold uAdd
  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]
  exact congrArg some hP

#print axioms uAdd_constTab


/-- One envelope-zone `uStep` on the loose start survives with the table unchanged:
both `uAdd`s have their bound `c` in `(1/1000, 1000)`. -/
theorem uStep_constTab_env (a b : Fin 7) (Aex A B : ℚ)
    (hAex : 1 ≤ Aex ∧ Aex ≤ 200) (hA : 1 ≤ A ∧ A ≤ 200) (hB : 1 ≤ B ∧ B ≤ 200) :
    uStep constTab a b Aex A B = some constTab := by
  have hAexpos : (0 : ℚ) < Aex := by linarith
  have hApos : (0 : ℚ) < A := by linarith
  have hBpos : (0 : ℚ) < B := by linarith
  have hc1 : (1 : ℚ) / 1000 < Aex / A := by
    rw [lt_div_iff₀ hApos]
    have h5 : (1 : ℚ) / 1000 * A ≤ (1 : ℚ) / 1000 * 200 := by
      apply mul_le_mul_of_nonneg_left hA.2 (le_of_lt (by norm_num : (0 : ℚ) < 1 / 1000))
    have h6 : (1 : ℚ) / 1000 * 200 = 1 / 5 := by norm_num
    rw [h6] at h5
    linarith
  have hc1' : Aex / A < 1000 := by
    rw [div_lt_iff₀ hApos]
    linarith
  have hc2 : (1 : ℚ) / 1000 < B / Aex := by
    rw [lt_div_iff₀ hAexpos]
    have h5 : (1 : ℚ) / 1000 * Aex ≤ (1 : ℚ) / 1000 * 200 := by
      apply mul_le_mul_of_nonneg_left hAex.2 (le_of_lt (by norm_num : (0 : ℚ) < 1 / 1000))
    have h6 : (1 : ℚ) / 1000 * 200 = 1 / 5 := by norm_num
    rw [h6] at h5
    linarith
  have hc2' : B / Aex < 1000 := by
    rw [div_lt_iff₀ hAexpos]
    linarith
  simp only [uStep, uGt_pos constTab a b hAexpos hApos,
    uAdd_constTab a b (Aex / A) true hc1 hc1', Option.bind_some]
  rw [uGt_pos constTab b a hBpos hAexpos]
  exact uAdd_constTab b a (B / Aex) true hc2 hc2'

#print axioms uStep_constTab_env

/-- Any run of the loose start with envelope-zone steps survives, trace still the loose
table: by induction the state carries `(1 ≤ Aex ≤ 200)` and every step's bounds lie in
`[1, 200]`. -/
theorem chainRun_constTab_env (steps : List Step) (a : Fin 7) (Aex : ℚ)
    (hAex : 1 ≤ Aex ∧ Aex ≤ 200)
    (hsteps : ∀ st ∈ steps, 1 ≤ st.A ∧ st.A ≤ 200 ∧ 1 ≤ st.B ∧ st.B ≤ 200) :
    ∃ af : Fin 7, ∃ Af : ℚ, chainRun constTab a Aex steps = some (constTab, af, Af) := by
  induction steps generalizing a Aex with
  | nil => exact ⟨a, Aex, rfl⟩
  | cons st rest ih =>
    obtain ⟨ha1, ha2, hb1, hb2⟩ := hsteps st (by simp)
    obtain ⟨af, Af, hrun⟩ := ih st.b st.B ⟨by exact_mod_cast hb1, by exact_mod_cast hb2⟩
      (fun st' hst' => hsteps st' (by simp [hst']))
    refine ⟨af, Af, ?_⟩
    simp only [chainRun,
      uStep_constTab_env a st.b Aex st.A st.B hAex ⟨ha1, ha2⟩ ⟨hb1, hb2⟩,
      Option.bind_some]
    exact hrun

#print axioms chainRun_constTab_env

/-- The banked census word's zone bounds lie in `[1, 200]` (concrete literals). -/
theorem steps8_env : ∀ st ∈ steps8_1_3_4_5_5_5_7,
    1 ≤ st.A ∧ st.A ≤ 200 ∧ 1 ≤ st.B ∧ st.B ≤ 200 := by
  intro st hst
  simp only [steps8_1_3_4_5_5_5_7, List.mem_cons] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | h0
  all_goals try decide
  exact absurd h0 (by simp)

#print axioms steps8_env

/-- The census word runs on the loose start, trace still the loose table. -/
theorem chainRun_constTab_steps8 :
    ∃ af : Fin 7, ∃ Af : ℚ,
      chainRun constTab 0 1 steps8_1_3_4_5_5_5_7 = some (constTab, af, Af) :=
  chainRun_constTab_env steps8_1_3_4_5_5_5_7 0 1 ⟨by norm_num, by norm_num⟩ steps8_env

#print axioms chainRun_constTab_steps8

/-- The loose table dominates NO single-cap walk: its entry value is 1000, above every
record cap. -/
theorem not_capsDom_constTab (y x z : Fin 7) (cap : ℝ) (hcap : cap < 1000) :
    ¬ CapsDom constTab y [(z, cap)] x := by
  intro h
  cases h with
  | cons _ _ c l w hentry hrest =>
    obtain ⟨c₀, s, hV, hle⟩ := hentry
    have hV' : constTab y z = some ((1000 : ℚ), false) := rfl
    rw [hV'] at hV
    simp only [Option.some.injEq, Prod.mk.injEq] at hV
    obtain ⟨rfl, rfl⟩ := hV
    have hcast : ((1000 : ℚ) : ℝ) = (1000 : ℝ) := by norm_num
    linarith [hcast ▸ hle, hcap]

#print axioms not_capsDom_constTab

/-- Any record with a single cap below 1000 attests NOTHING from the loose start (whenever
the run survives — and every envelope run survives, `chainRun_constTab_env`). -/
theorem not_attestsFrom_constTab_cons (e : ComposedEdge) (steps : List Step)
    (hsurv : ∃ af : Fin 7, ∃ Af : ℚ,
      chainRun constTab 0 1 steps = some (constTab, af, Af))
    (hcaps : ∃ z : Fin 7, ∃ cap : ℝ, e.caps = [(z, cap)] ∧ cap < 1000) :
    ¬ AttestsFrom e steps constTab := by
  intro h
  obtain ⟨af, Af, hrun⟩ := hsurv
  obtain ⟨z, cap, hcl, hcaplt⟩ := hcaps
  obtain ⟨ex, ey, eA, eB, ecaps⟩ := e
  subst hcl
  exact not_capsDom_constTab ey ex z cap hcaplt (h constTab af Af hrun)

#print axioms not_attestsFrom_constTab_cons

/-- All four box-1 records have a single cap below 1000. -/
theorem constTab_caps_b1 (e : ComposedEdge)
    (he : e ∈ compFam_1_3_4_5_5_5_7.edges) :
    ∃ z : Fin 7, ∃ cap : ℝ, e.caps = [(z, cap)] ∧ cap < 1000 := by
  simp only [compFam_1_3_4_5_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact ⟨6, 1870 / 13113, rfl, by norm_num⟩
  · exact ⟨6, 55 / 117, rfl, by norm_num⟩
  · exact ⟨6, 55 / 117, rfl, by norm_num⟩
  · exact ⟨6, 55 / 117, rfl, by norm_num⟩
  · exact absurd h0 (by simp)

#print axioms constTab_caps_b1

/-- **THE REFUTATION (walk-independent form): from the loose start, NO record of the
box-1 family attests ANY surviving word** — in particular the banked census word, whose
run on the loose start survives verbatim.  The census data therefore cannot carry
attestations to arbitrary fine starts: the start table's tightness is a genuine missing
datum (the rung's OWED `hdom`). -/
theorem constTab_attests_nothing_b1 (steps : List Step)
    (hsurv : ∃ af : Fin 7, ∃ Af : ℚ,
      chainRun constTab 0 1 steps = some (constTab, af, Af))
    (e : ComposedEdge)
    (he : e ∈ (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)).edges) :
    ¬ AttestsFrom e steps constTab := by
  rw [compFamOf_b1] at he
  exact not_attestsFrom_constTab_cons e steps hsurv (constTab_caps_b1 e he)

#print axioms constTab_attests_nothing_b1

end Fresh.SelectRung1
