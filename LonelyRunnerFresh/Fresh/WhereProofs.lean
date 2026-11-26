import Mathlib
import Fresh.Framework
import Fresh.Where
import Fresh.Cascade
import Fresh.Localisation

/-!
# Where the isolation goes: proofs of the `Fresh.Where` claims (Task F)

Written 2026-10-07.  Imports `Mathlib`, `Fresh.Framework`, `Fresh.Where`, `Fresh.Cascade`, `Fresh.Localisation`;
nothing from the existing `LonelyRunner` repo.  Each claim of `Fresh/Where.lean` is proved here as a theorem whose
type is exactly that `Prop`, symbolically, for every arrangement, every subject and its `d_min`; no case is checked
by enumeration.  Exact reals only; no floats.  No counting, covering, density, cap or move budget is used in any
proof in this file (the two theorems taken from `Fresh/Cascade.lean`, `exists_fixed_of_lonely`, carry their own
`[PROVISIONAL: counting tool]` tag there; it is used here only by `cascadeFindsIsolation`, see its docstring).

Findings.
* Every claim of `Where.lean` attempted here is TRUE as stated; no counterexample arose.
* Several hypotheses are idle, and this is proved, not only remarked:
  - `PositionAtStart`: the identity `position ρ 1 = (⌊ρ⌋ mod 8) + frac ρ` holds for every real `ρ`
    (`position_one`); the arrangement, `d_min` and `i ≠ k` hypotheses are not used.
  - `ClearIffPosition`: holds for every `R` (not only `R ≥ 1`), using only `m ≠ 0` (`clear_iff_position_core`).
  - `EnteringEdgeSlotSeven`: the slot-7 hypothesis is idle (`enteringEdge_firstMove`, no slot hypothesis); so are
    the hypotheses `0 < t₀` and `t₁ ≠ t₀` of `EnteringEdgeEveryMove` (`enteringEdge_anyMove`).  Why: a move either
    fixes `t` (then nobody is in the way at `t₁ = t₀` and the conclusion is vacuous) or goes strictly forward; in the
    second case a runner in the way at `t₁` is within `1/8` of a lap line `N'` that lies strictly past the window of
    `[t₀]`'s own lap, so its entering edge `N' − 1/8` was crossed during the move.  The confirmation of Task E's
    reasoned remark is therefore [L].

Provenance (existing declarations read, not imported; no proof copied):
* `clear_iff_position_core` / `clearIffPosition`: v9 §4 "Cascade coordinate" (GL); in the repo the same change of
  variable is used in `LRC/Cascade/Reading.lean` (`reading`), proved here directly from
  `Fresh.Localisation.clear_iff_fract`.
* `startBlockers`, `startOpening`, `startDisplacement`: log E427 (start blockers are slot 0, or slot 7 with
  `ε > 0`); no Lean declaration in the repo under that name (per Where.lean).  Proved here from the decomposition
  `ρ = 8·⌊q/8⌋ + (q mod 8) + ε`.
* `firstMoveIsLargestStartOpening`: `IsMove` at the bound rewritten through the two above.
* `enteringEdge_anyMove`: `LRC/Spec/SeparationN.lean` `crossed_entering_edge` (read for the idea only).
* `landingIsFirstIsolation`, `cascadeFindsIsolation`: v9 Theorems 11 and 12; `Spec/Doors.lean`; here from
  `Fresh.Cascade` (`isMove_self_iff`, `isMove_le_of_lonely`, `bound_le_of_lonely`, `exists_fixed_of_lonely`).
-/

open Classical

namespace Fresh.WhereProofs

open Fresh.Where

/-! ## Arithmetic of the conversion -/

/-- The decomposition of a reading: `ρ = 8·⌊⌊ρ⌋/8⌋ + (⌊ρ⌋ mod 8) + frac ρ`. -/
theorem reading_decomp (ρ : ℝ) :
    ρ = 8 * ((⌊ρ⌋ / 8 : ℤ) : ℝ) + ((⌊ρ⌋ % 8 : ℤ) : ℝ) + Int.fract ρ := by
  have h := Int.emod_add_mul_ediv ⌊ρ⌋ 8
  have h' : ((⌊ρ⌋ % 8 : ℤ) : ℝ) + 8 * ((⌊ρ⌋ / 8 : ℤ) : ℝ) = (⌊ρ⌋ : ℝ) := by exact_mod_cast h
  have h2 := Int.floor_add_fract ρ
  linarith

#print axioms reading_decomp

theorem slot_bounds (q : ℤ) : 0 ≤ q % 8 ∧ q % 8 ≤ 7 := by omega

#print axioms slot_bounds

/-- `⌊ρ/8⌋ = ⌊ρ⌋ div 8`. -/
theorem floor_div_eight (ρ : ℝ) : ⌊ρ / 8⌋ = ⌊ρ⌋ / 8 := by
  rw [Int.floor_eq_iff]
  have hd := reading_decomp ρ
  have hb := slot_bounds ⌊ρ⌋
  have hr0 : (0 : ℝ) ≤ ((⌊ρ⌋ % 8 : ℤ) : ℝ) := by exact_mod_cast hb.1
  have hr7 : ((⌊ρ⌋ % 8 : ℤ) : ℝ) ≤ 7 := by exact_mod_cast hb.2
  have hf0 := Int.fract_nonneg ρ
  have hf1 := Int.fract_lt_one ρ
  constructor <;> linarith

#print axioms floor_div_eight

/-- The position at state `R` is eight times the fractional part of `R·ρ/8`. -/
theorem position_eq (ρ R : ℝ) : position ρ R = 8 * Int.fract (R * ρ / 8) := by
  unfold position Int.fract
  ring

#print axioms position_eq

/-- At the start `R = 1`: position = slot + deviation, for EVERY real `ρ`. -/
theorem position_one (ρ : ℝ) : position ρ 1 = ((⌊ρ⌋ % 8 : ℤ) : ℝ) + Int.fract ρ := by
  unfold position
  rw [one_mul, floor_div_eight]
  have hd := reading_decomp ρ
  linarith

#print axioms position_one

/-- Clearance read in the cascade coordinate: `1/8 ≤ ‖R ρ / 8‖` iff the position lies in `[1, 7]`.  Every `R`. -/
theorem clear_iff_position_core (ρ R : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (R * ρ / 8) ↔ 1 ≤ position ρ R ∧ position ρ R ≤ 7 := by
  rw [Fresh.Localisation.clear_iff_fract, position_eq]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

#print axioms clear_iff_position_core

/-- The start blocker condition on `slot + ε`. -/
theorem blocked_iff_slot (r : ℤ) (ε : ℝ) (hr : 0 ≤ r ∧ r ≤ 7) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ¬ (1 ≤ (r : ℝ) + ε ∧ (r : ℝ) + ε ≤ 7) ↔ (r = 0 ∨ (r = 7 ∧ 0 < ε)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hr0, hr7⟩ := hc
    apply h
    have h1 : (1 : ℤ) ≤ r := by omega
    have h1' : (1 : ℝ) ≤ r := by exact_mod_cast h1
    refine ⟨by linarith, ?_⟩
    by_cases h7 : r = 7
    · have := hr7 h7
      rw [h7]; push_cast; linarith
    · have h6 : r ≤ 6 := by omega
      have h6' : (r : ℝ) ≤ 6 := by exact_mod_cast h6
      linarith
  · rintro (h0 | ⟨h7, hε⟩) ⟨h1, h2⟩
    · rw [h0] at h1; push_cast at h1; linarith
    · rw [h7] at h2; push_cast at h2; linarith

#print axioms blocked_iff_slot

/-! ## Facts about an arrangement's readings -/

theorem dmin_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m) : 0 < m :=
  Fresh.Cascade.disparitySet_pos hv k m hm.1

#print axioms dmin_pos

theorem disp_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) {k i : Fin 8} (hik : i ≠ k) : 0 < |v i - v k| :=
  abs_pos.mpr (sub_ne_zero.mpr (fun h => hik (hv.2 h)))

#print axioms disp_pos

theorem disp_mem {v : Fin 8 → ℝ} {k i : Fin 8} (hik : i ≠ k) : |v i - v k| ∈ disparitySet v k :=
  Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)

#print axioms disp_mem

theorem disp_eq {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hm : m ≠ 0) (i : Fin 8) :
    |v i - v k| = m * reading v k m i := by
  unfold reading; field_simp

#print axioms disp_eq

theorem reading_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m)
    {i : Fin 8} (hik : i ≠ k) : 0 < reading v k m i :=
  div_pos (disp_pos hv hik) (dmin_pos hv hm)

#print axioms reading_pos

/-- The disparity times the instant of state `R` is `R·ρ/8`. -/
theorem disp_mul_instant {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hm : m ≠ 0) (i : Fin 8) (R : ℝ) :
    |v i - v k| * instantOf m R = R * reading v k m i / 8 := by
  rw [disp_eq hm i]; unfold instantOf; field_simp

#print axioms disp_mul_instant

/-! ## (i) The coordinates are faithful -/

/-- **`ClearIffPosition`** [L]: out of the way at the instant of state `R` iff the position is in `[1, 7]`.
(The hypotheses `i ≠ k` and the arrangement are used only to get `m ≠ 0`.) -/
theorem clearIffPosition : ClearIffPosition := by
  intro v hv k m hm R i _
  rw [Fresh.Cascade.not_inWay_iff, disp_mul_instant (dmin_pos hv hm).ne' i R]
  exact clear_iff_position_core _ R

#print axioms clearIffPosition

/-- **`PositionAtStart`** [L]: an identity, true for every real reading (`position_one`). -/
theorem positionAtStart : PositionAtStart := by
  intro v _ k m _ i _
  exact position_one _

#print axioms positionAtStart

/-! ## (ii) The start blockers -/

/-- **`StartBlockers`** [L]: in the way at the bound iff slot `0`, or slot `7` with `ε > 0`. -/
theorem startBlockers : StartBlockers := by
  intro v hv k m hm i hik
  have hc := clearIffPosition v hv k m hm 1 i hik
  have hinst : instantOf m 1 = 1 / (8 * m) := rfl
  rw [hinst, positionAtStart v hv k m hm i hik] at hc
  have key := blocked_iff_slot (slot v k m i) (deviation v k m i) (slot_bounds _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)
  unfold IsStartBlocker
  rw [← hc.not, not_not] at key
  simp only [hik, ne_eq, not_false_eq_true, true_and]
  exact key

#print axioms startBlockers

/-- The lap of a start blocker's next opening, as an integer `K` with `|ρ/8 − K| < 1/8`, and `startLap = K`. -/
theorem startBlocker_lap {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} {i : Fin 8} (hb : IsStartBlocker v k m i) :
    |reading v k m i / 8 - (startLap v k m i : ℝ)| < 1 / 8 := by
  obtain ⟨_, hs⟩ := hb
  have hd := reading_decomp (reading v k m i)
  have hf0 := Int.fract_nonneg (reading v k m i)
  have hf1 := Int.fract_lt_one (reading v k m i)
  -- `slot`, `deviation`, `gridIndex` unfold to the floor data of the reading
  have hslot : slot v k m i = ⌊reading v k m i⌋ % 8 := rfl
  have hdev : deviation v k m i = Int.fract (reading v k m i) := rfl
  have hlap : startLap v k m i = (⌊reading v k m i⌋ + 1) / 8 := rfl
  rw [hslot, hdev] at hs
  rw [hlap]
  set q := ⌊reading v k m i⌋ with hq
  rcases hs with h0 | ⟨h7, hε⟩
  · have hL : (q + 1) / 8 = q / 8 := by omega
    rw [hL]; rw [h0] at hd
    rw [abs_lt]; push_cast at hd; constructor <;> linarith
  · have hL : (q + 1) / 8 = q / 8 + 1 := by omega
    rw [hL]; rw [h7] at hd
    rw [abs_lt]; push_cast at hd ⊢; constructor <;> linarith

#print axioms startBlocker_lap

/-- **`StartOpening`** [L]: a start blocker's next opening is the state `(8L + 1)/ρ`. -/
theorem startOpening : StartOpening := by
  intro v hv k m hm i hb
  have hik := hb.1
  have hm0 := dmin_pos hv hm
  have hρ := reading_pos hv hm hik
  have hlap := startBlocker_lap hb
  have hdt : |v i - v k| * (1 / (8 * m)) - (startLap v k m i : ℝ) =
      reading v k m i / 8 - (startLap v k m i : ℝ) := by
    rw [disp_eq hm0.ne' i]; field_simp
  rw [← hdt] at hlap
  rw [Fresh.Cascade.nextOpening_eq hlap, disp_eq hm0.ne' i]
  unfold stateR startOpeningR
  field_simp

#print axioms startOpening

/-- **`StartDisplacement`** [L]: slot `0` pushes the state by `(1 − ε)/ρ`, slot `7` by `(2 − ε)/ρ`. -/
theorem startDisplacement : StartDisplacement := by
  intro v hv k m hm i hik
  have hρ := reading_pos hv hm hik
  have hd := reading_decomp (reading v k m i)
  have hslot : slot v k m i = ⌊reading v k m i⌋ % 8 := rfl
  have hdev : deviation v k m i = Int.fract (reading v k m i) := rfl
  have hlap : startLap v k m i = (⌊reading v k m i⌋ + 1) / 8 := rfl
  unfold startOpeningR
  rw [hslot, hdev, hlap]
  set q := ⌊reading v k m i⌋ with hq
  refine ⟨fun h0 => ?_, fun h7 _ => ?_⟩
  · have hL : (q + 1) / 8 = q / 8 := by omega
    rw [hL]; rw [h0] at hd; push_cast at hd
    field_simp
    linarith
  · have hL : (q + 1) / 8 = q / 8 + 1 := by omega
    rw [hL]; rw [h7] at hd; push_cast at hd ⊢
    field_simp
    linarith

#print axioms startDisplacement

/-! ## (d1) The first move -/

theorem stateR_le_iff {m : ℝ} (hm : 0 < m) {a b : ℝ} : stateR m a ≤ stateR m b ↔ a ≤ b := by
  unfold stateR
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

#print axioms stateR_le_iff

theorem stateR_inj {m : ℝ} (hm : 0 < m) {a b : ℝ} : stateR m a = stateR m b ↔ a = b := by
  constructor
  · intro h; exact le_antisymm ((stateR_le_iff hm).mp h.le) ((stateR_le_iff hm).mp h.ge)
  · rintro rfl; rfl

#print axioms stateR_inj

/-- **`FirstMoveIsLargestStartOpening`** [L]: the first move, read through the start blockers. -/
theorem firstMoveIsLargestStartOpening : FirstMoveIsLargestStartOpening := by
  intro v hv k m hm t'
  have hm0 := dmin_pos hv hm
  -- a start blocker is exactly a runner in the way at the bound
  have hSB : ∀ i, IsStartBlocker v k m i ↔ i ≠ k ∧ InWay |v i - v k| (1 / (8 * m)) := by
    intro i
    constructor
    · intro hb; exact ⟨hb.1, (startBlockers v hv k m hm i hb.1).mpr hb⟩
    · rintro ⟨hik, hw⟩; exact (startBlockers v hv k m hm i hik).mp hw
  have hSO : ∀ i, IsStartBlocker v k m i →
      startOpeningR v k m i = stateR m (nextOpening |v i - v k| (1 / (8 * m))) :=
    fun i hb => (startOpening v hv k m hm i hb).symm
  have hmemiff : ∀ d, d ∈ disparitySet v k ↔ ∃ i, i ≠ k ∧ |v i - v k| = d :=
    fun d => Fresh.Localisation.mem_disparitySet
  constructor
  · rintro (⟨hn, rfl⟩ | ⟨d, hd, hw, rfl, hmax⟩)
    · left
      refine ⟨fun i hb => ?_, rfl⟩
      obtain ⟨hik, hw⟩ := (hSB i).mp hb
      exact hn _ (disp_mem hik) hw
    · right
      obtain ⟨i, hik, rfl⟩ := (hmemiff d).mp hd
      have hb : IsStartBlocker v k m i := (hSB i).mpr ⟨hik, hw⟩
      refine ⟨i, hb, (hSO i hb).symm, fun i' hb' => ?_⟩
      rw [hSO i' hb', stateR_le_iff hm0]
      obtain ⟨hik', hw'⟩ := (hSB i').mp hb'
      exact hmax _ (disp_mem hik') hw'
  · rintro (⟨hn, rfl⟩ | ⟨i, hb, he, hmax⟩)
    · left
      refine ⟨fun d hd hw => ?_, rfl⟩
      obtain ⟨i, hik, rfl⟩ := (hmemiff d).mp hd
      exact hn i ((hSB i).mpr ⟨hik, hw⟩)
    · right
      obtain ⟨hik, hw⟩ := (hSB i).mp hb
      rw [hSO i hb, stateR_inj hm0] at he
      refine ⟨_, disp_mem hik, hw, he, fun d' hd' hw' => ?_⟩
      obtain ⟨i', hik', rfl⟩ := (hmemiff d').mp hd'
      have hb' : IsStartBlocker v k m i' := (hSB i').mpr ⟨hik', hw'⟩
      have := hmax i' hb'
      rwa [hSO i' hb', stateR_le_iff hm0] at this

#print axioms firstMoveIsLargestStartOpening

/-! ## (d3) Entering edges -/

/-- **Every runner in the way after ANY move crossed an entering edge during it** [L].  No hypothesis on `t₀`, on
`t₁ ≠ t₀`, or on slots: a fixing move leaves nobody in the way, and a forward move pushes every runner's nearest lap
line past the window of its lap at `t₀`. -/
theorem enteringEdge_anyMove (ds : Finset ℝ) (hpos : ∀ d ∈ ds, 0 < d) (t₀ t₁ : ℝ) (hmv : IsMove ds t₀ t₁) :
    ∀ d ∈ ds, InWay d t₁ → CrossedEnteringEdge d t₀ t₁ := by
  intro d hd hw1
  rcases hmv with ⟨hn, rfl⟩ | ⟨e, he, hwe, rfl, hmax⟩
  · exact absurd hw1 (hn d hd)
  have hdpos := hpos d hd
  have hlt : t₀ < nextOpening e t₀ := Fresh.Cascade.lt_nextOpening (hpos e he) hwe
  set t₁ := nextOpening e t₀ with ht₁
  obtain ⟨N', hN'⟩ := Fresh.Cascade.exists_near_int hw1
  have hN'a := abs_lt.mp hN'
  -- an integer `K` with `d t₀ ≤ K + 7/8` and `K < N'`
  have hK : ∃ K : ℤ, d * t₀ ≤ (K : ℝ) + 7 / 8 ∧ (K : ℝ) < N' := by
    by_cases hw0 : InWay d t₀
    · obtain ⟨K, hK⟩ := Fresh.Cascade.exists_near_int hw0
      have hKa := abs_lt.mp hK
      have hle : nextOpening d t₀ ≤ t₁ := hmax d hd hw0
      rw [Fresh.Cascade.nextOpening_eq hK, div_le_iff₀ hdpos] at hle
      exact ⟨K, by linarith, by linarith⟩
    · have hc := (Fresh.Localisation.clear_iff_fract (d * t₀)).mp (Fresh.Cascade.not_inWay_iff.mp hw0)
      have hdt : d * t₀ < d * t₁ := mul_lt_mul_of_pos_left hlt hdpos
      refine ⟨⌊d * t₀⌋, ?_, ?_⟩
      · unfold Int.fract at hc; linarith [hc.2]
      · unfold Int.fract at hc; linarith [hc.1]
  obtain ⟨K, hK1, hK2⟩ := hK
  have hKN : K + 1 ≤ N' := by
    have : K < N' := by exact_mod_cast hK2
    omega
  have hKN' : (K : ℝ) + 1 ≤ N' := by exact_mod_cast hKN
  exact ⟨N', by linarith, by linarith⟩

#print axioms enteringEdge_anyMove

/-- **`EnteringEdgeEveryMove`** [L], from `enteringEdge_anyMove` (its hypotheses `0 < t₀`, `t₁ ≠ t₀` are idle). -/
theorem enteringEdgeEveryMove : EnteringEdgeEveryMove := by
  intro ds hpos t₀ t₁ _ hmv _
  exact enteringEdge_anyMove ds hpos t₀ t₁ hmv

#print axioms enteringEdgeEveryMove

/-- **The first move, with no slot hypothesis** [L]: the statement of `EnteringEdgeSlotSeven` with its hypothesis
`∃ i, i ≠ k ∧ slot = 7 ∧ ε > 0` removed.  This proves that hypothesis idle. -/
theorem enteringEdge_firstMove :
    ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k m, IsDmin v k m →
    ∀ t₁ : ℝ, IsMove (disparitySet v k) (1 / (8 * m)) t₁ →
      ∀ j, j ≠ k → InWay |v j - v k| t₁ → CrossedEnteringEdge |v j - v k| (1 / (8 * m)) t₁ := by
  intro v hv k m _ t₁ hmv j hjk hw
  exact enteringEdge_anyMove _ (Fresh.Cascade.disparitySet_pos hv k) _ _ hmv _ (disp_mem hjk) hw

#print axioms enteringEdge_firstMove

/-- **`EnteringEdgeSlotSeven`** [L], from `enteringEdge_firstMove`. -/
theorem enteringEdgeSlotSeven : EnteringEdgeSlotSeven := by
  intro v hv k m hm _ t₁ hmv j hjk hw
  exact enteringEdge_firstMove v hv k m hm t₁ hmv j hjk hw

#print axioms enteringEdgeSlotSeven

/-! ## Landing and first isolation (v9 Theorems 11, 12) -/

/-- **`LandingIsFirstIsolation`** [L]: a landing of the cascade from the bound is the first isolation. -/
theorem landingIsFirstIsolation : LandingIsFirstIsolation := by
  intro v hv k m hm tStar hreach
  obtain ⟨seq, N, h0, hmv, hN, hfix⟩ := hreach
  have hpos := Fresh.Cascade.disparitySet_pos hv k
  have hm0 := dmin_pos hv hm
  have hb : 0 < 1 / (8 * m) := by positivity
  -- the moves never go backwards
  have hge : ∀ n, n ≤ N → 1 / (8 * m) ≤ seq n := by
    intro n
    induction n with
    | zero => intro _; rw [h0]
    | succ n ih =>
      intro hn
      exact le_trans (ih (by omega)) (Fresh.Cascade.le_of_isMove hpos (hmv n (by omega)))
  have hlon : Fresh.Cascade.LonelyAt (disparitySet v k) tStar := (Fresh.Cascade.isMove_self_iff hpos).mp hfix
  refine ⟨⟨lt_of_lt_of_le hb (hN ▸ hge N le_rfl), (Fresh.Cascade.isolatedAt_iff_lonelyAt v k tStar).mpr hlon⟩, ?_⟩
  rintro s ⟨hs, hiso⟩
  have hl := (Fresh.Cascade.isolatedAt_iff_lonelyAt v k s).mp hiso
  have hbs := Fresh.Cascade.bound_le_of_lonely hm.1 hm0 hl hs
  -- no overshoot, along the finitely many moves
  have hle : ∀ n, n ≤ N → seq n ≤ s := by
    intro n
    induction n with
    | zero => intro _; rw [h0]; exact hbs
    | succ n ih =>
      intro hn
      exact Fresh.Cascade.isMove_le_of_lonely hpos hl (ih (by omega)) (hmv n (by omega))
  rw [← hN]; exact hle N le_rfl

#print axioms landingIsFirstIsolation

/-- **`CascadeFindsIsolation`** [L]: given an isolation at `t > 0`, the cascade from the bound lands at or before `t`.
The finiteness of the run uses `Fresh.Cascade.exists_fixed_of_lonely`, whose last step is tagged there
`[PROVISIONAL: counting tool]` (supports: "the sequence cannot move forever below `t`"). -/
theorem cascadeFindsIsolation : CascadeFindsIsolation := by
  intro v hv k m hm t ht hiso
  have hpos := Fresh.Cascade.disparitySet_pos hv k
  have hm0 := dmin_pos hv hm
  have hb : 0 < 1 / (8 * m) := by positivity
  have hl := (Fresh.Cascade.isolatedAt_iff_lonelyAt v k t).mp hiso
  have hbt := Fresh.Cascade.bound_le_of_lonely hm.1 hm0 hl ht
  -- [PROVISIONAL: counting tool] (inside `exists_fixed_of_lonely`) supporting "the run from the bound is finite".
  obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hb hl hbt
  set seq := Fresh.Cascade.cascadeSeq (disparitySet v k) (1 / (8 * m))
  have hmv := Fresh.Cascade.cascadeSeq_isMove (disparitySet v k) (1 / (8 * m))
  refine ⟨seq N, Fresh.Cascade.seq_le_of_lonely hpos hl (le_of_eq_of_le rfl hbt) hmv N,
    seq, N, rfl, fun n _ => hmv n, rfl, ?_⟩
  have h := hmv N
  have hN' : Fresh.Cascade.cascadeSeq (disparitySet v k) (1 / (8 * m)) (N + 1) = seq N := hN
  rw [hN'] at h
  exact h

#print axioms cascadeFindsIsolation

end Fresh.WhereProofs
