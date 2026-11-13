import Mathlib
import Fresh.Framework
import Fresh.Cascade

/-!
# The K-taxonomy of cascade outcomes (log E325), native

Written 2026-11-06.  New file; nothing existing is edited.  Built on `Fresh.Framework`
(`InWay`, `nextOpening`, `IsMove`, `CascadeFixes`) and `Fresh.Cascade` (`cascadeSeq`, `LonelyAt`,
`le_of_isMove`, `exists_near_int`, `nextOpening_eq`) only.

The outcome taxonomy of E325 (`taxo_outcome_classes_v1.md`): 14 mutually exclusive classes into
which the cascade sorts the arrangements, in the order of tests used there (number of moves;
zero-width window at the landing; the closer being the opener's own reading; the opener's lap;
the opener a strip reading).  Native objects here (`ds` a finite set of positive readings,
`t₀` the start, `N` the first index at which the cascade from `t₀` is fixed):

* a reading `d` is in a zone at `t` when `InWay d t`; its next opening is the zone's right edge
  `(k + 1/8)/d`, the integer `k` being the lap;
* `StabilizesAtMin ds t₀ N`: the cascade moves strictly `N` times and is fixed at `N`; the
  landing `cascadeSeq ds t₀ N` is lonely (`stabilizesAtMin_lonely`);
* the opener is the reading of the last move (`openersAt`, `openerOf`); ties between readings
  sharing the exit are resolved by `Finset.min'`, i.e. the smallest tied reading — which is the
  smallest zone entry (`tied_opener_entry`), E325's corrected tie rule ("smallest entry, then
  highest rank"; the rank tie-break is vacuous here because tied readings are distinct);
* `ZeroWidthAt`: some reading's next zone entry coincides with the landing (the window after the
  landing has width 0); `OpenerOwnCloser`: the opener's next entry is strictly before every other
  reading's; `OpenerLapOne`/`OpenerLapTwo`: the opener's lap is 1 (landing phase `9/8`) or `>= 2`;
  `OpenerStrip`: the opener is in a zone already at the start `t₀`.

`KTag` is the 14-letter alphabet, `kTagOf` the sorter, `KClass` the 14 native predicates,
`kClass_iff_tag` the bridge; `kClass_exclusive`/`kClass_exactlyOne` are the sorting statements
(mutual exclusion; every landed cascade in exactly one class).  `k2a_empty` and `k2s1_empty` are
the two empty classes.  Provenance for the exclusions: `LRC.Spec.CascadeOutcomeExclusionsN`
(`no_late_initial_lap_one`, underlying K2a; `no_late_lap_one_self_closer`, K2s1) in the existing
repo.  That module cannot be imported under `check.sh` (its `.olean` directory is deliberately
excluded from `LEAN_PATH`; verified 2026-11-06: `unknown module prefix 'LonelyRunner'`), so the
arguments are re-derived here natively — E325's own hand argument for K2a, and E333's lemma L1
plus the previous-setter inequality for K2s1.

`landing_is_opener_exit` is the anchor law of the catalogue audit (agent C, [T 52000/52000],
`experiments/n8/catalogue_anchor_audit_v1.py/.out`): the landing is the opener's exit instant
(`R·ρ_opener = 8·lap + 1` in taxonomy units), here `openerOf * landing = k + 1/8` with `k >= 1`.
The audit's converse (a landing anchored at reading `m` forces `m` to be the opener) is not
definitionally true and is not claimed.

Divergences from E325, recorded: the own-closer classes use the strict-dominance form of
`taxo_outcome_classes_v1.md` (E325 itself: "the K1s1/K1s2/K2s1/K2s2 conditions are stated
approximately"); closer ties are not rank-broken; the opener enters as a reading, not a rank.

Standing hypotheses everywhere: `hpos : ∀ d ∈ ds, 0 < d` and `hbd : ∀ d ∈ ds, 1/8 ≤ d * t₀`
(the bound `1/(8·d_min)`; for arrangements see `disparitySet_lower`).
-/

open Classical

namespace Fresh.KTaxonomy

open Fresh Fresh.Cascade

variable {ds : Finset ℝ} {t₀ : ℝ} {N N₁ N₂ : ℕ}

/-! ## The window law at one reading -/

/-- Clear means inside a closed window between two zones (E802 item 6, one reading). -/
theorem distInt_ge_eighth_iff (x : ℝ) :
    1 / 8 ≤ distInt x ↔ ∃ k : ℤ, x ∈ Set.Icc ((k : ℝ) + 1 / 8) ((k : ℝ) + 7 / 8) := by
  constructor
  · intro h
    have hdef : distInt x = |x - (round x : ℝ)| := rfl
    rcases le_total x (round x : ℝ) with hle | hle
    · have hab : |x - (round x : ℝ)| = (round x : ℝ) - x := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hdef, hab] at h
      have hb2 : (round x : ℝ) - x ≤ 7 / 8 := by
        by_contra hc
        push_neg at hc
        have h2 := Fresh.Cascade.distInt_le x (round x - 1)
        rw [hdef, hab] at h2
        have he : x - ((round x - 1 : ℤ) : ℝ) = 1 - ((round x : ℝ) - x) := by
          push_cast; ring
        rw [he] at h2
        rcases le_or_gt ((round x : ℝ) - x) 1 with h1 | h1
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ((round x : ℝ) - x))] at h2
          have hlt : distInt x < 1 / 8 := by linarith
          linarith
        · rw [abs_of_nonpos (by linarith : (1 : ℝ) - ((round x : ℝ) - x) ≤ 0), neg_sub] at h2
          linarith
      refine ⟨round x - 1, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith
    · have hab : |x - (round x : ℝ)| = x - (round x : ℝ) := by
        rw [abs_of_nonneg (by linarith)]
      rw [hdef, hab] at h
      have hb2 : x - (round x : ℝ) ≤ 7 / 8 := by
        by_contra hc
        push_neg at hc
        have h2 := Fresh.Cascade.distInt_le x (round x + 1)
        rw [hdef, hab] at h2
        have he : x - ((round x + 1 : ℤ) : ℝ) = (x - (round x : ℝ)) - 1 := by
          push_cast; ring
        rw [he] at h2
        rcases le_or_gt (x - (round x : ℝ)) 1 with h1 | h1
        · rw [abs_of_nonpos (by linarith : x - (round x : ℝ) - 1 ≤ 0), neg_sub] at h2
          linarith
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - (round x : ℝ) - 1)] at h2
          have hlt : distInt x < 1 / 8 := by linarith
          linarith
      refine ⟨round x, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith
  · rintro ⟨k, hk⟩
    rw [Set.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    unfold distInt
    rcases le_total x (round x : ℝ) with hle | hle
    · rw [abs_of_nonpos (by linarith)]
      have hlt : ((k : ℝ)) < (round x : ℝ) := by linarith
      have hle2 : k + 1 ≤ round x := by exact_mod_cast hlt
      push_cast at hle2
      have hf1 : ((k : ℝ)) + 1 ≤ (round x : ℝ) := by exact_mod_cast hle2
      have hf2 : ((k : ℝ)) + 1 - x ≥ 1 / 8 := by linarith
      have hf3 : (round x : ℝ) - x ≥ ((k : ℝ)) + 1 - x := by linarith
      linarith
    · rw [abs_of_nonneg (by linarith)]
      have hlt : (round x : ℝ) < ((k : ℝ)) + 1 := by linarith
      have hle2 : round x ≤ k := by
        have hlt' : (round x : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
        have hlt'' : round x < k + 1 := by exact_mod_cast hlt'
        omega
      push_cast at hle2
      have hf1 : (round x : ℝ) ≤ ((k : ℝ)) := by exact_mod_cast hle2
      have hf2 : x - ((k : ℝ)) ≥ 1 / 8 := by linarith
      linarith

#print axioms distInt_ge_eighth_iff

/-! ## The next entry of a reading -/

/-- The first instant at or after `t` at which the reading `d` stands exactly `1/8` below a lap
line (the left edge of its next zone; the taxonomy's entry `n(y,k) = (8k-1)/ρ_y`). -/
noncomputable def nextEntry (d t : ℝ) : ℝ := (((⌈d * t + 1 / 8⌉ : ℤ) : ℝ) - 1 / 8) / d

/-- Inside a window, the next entry is the window's right end. -/
theorem nextEntry_eq {d t : ℝ} (hd : 0 < d) (k : ℤ) (h1 : ((k : ℝ)) + 1 / 8 ≤ d * t)
    (h2 : d * t ≤ ((k : ℝ)) + 7 / 8) : nextEntry d t = (((k : ℝ)) + 7 / 8) / d := by
  have hc : ⌈d * t + 1 / 8⌉ = k + 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  unfold nextEntry
  rw [hc]
  push_cast
  congr 1
  ring

#print axioms nextEntry_eq

theorem le_nextEntry {d t : ℝ} (hd : 0 < d) : t ≤ nextEntry d t := by
  unfold nextEntry
  have hc := Int.le_ceil (d * t + 1 / 8)
  rw [le_div_iff₀ hd]
  have hcomm : t * d = d * t := mul_comm _ _
  push_cast at hc
  linarith

#print axioms le_nextEntry

/-! ## The landing: first stabilization of the cascade -/

/-- The cascade from `t₀` moves strictly `N` times and is fixed at `N` (`N` is the number of
moves; the landing is `cascadeSeq ds t₀ N`). -/
-- STANDING: DEFINITION
def StabilizesAtMin (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  cascadeSeq ds t₀ (N + 1) = cascadeSeq ds t₀ N ∧
    ∀ n < N, cascadeSeq ds t₀ n < cascadeSeq ds t₀ (n + 1)

theorem stabilizesAtMin_imp_cascadeFixes (hS : StabilizesAtMin ds t₀ N) : CascadeFixes ds t₀ :=
  ⟨cascadeSeq ds t₀, cascadeSeq_zero _ _, cascadeSeq_isMove _ _, N, hS.1⟩

#print axioms stabilizesAtMin_imp_cascadeFixes

theorem exists_stabilizesAtMin_of_cascadeFixes (hpos : ∀ d ∈ ds, 0 < d)
    (h : CascadeFixes ds t₀) : ∃ N, StabilizesAtMin ds t₀ N := by
  obtain ⟨seq, h0, hmv, Nfix, hN⟩ := h
  have hEq : ∀ n, seq n = cascadeSeq ds t₀ n := fun n =>
    (seq_eq_cascadeSeq hmv n).trans (by rw [h0])
  have hne : ∃ n : ℕ, cascadeSeq ds t₀ (n + 1) = cascadeSeq ds t₀ n :=
    ⟨Nfix, by rw [← hEq (Nfix + 1), ← hEq Nfix, hN]⟩
  refine ⟨Nat.find hne, Nat.find_spec hne, ?_⟩
  intro n hn
  have hfix : cascadeSeq ds t₀ (n + 1) ≠ cascadeSeq ds t₀ n := Nat.find_min hne hn
  exact lt_of_le_of_ne (le_of_isMove hpos (cascadeSeq_isMove ds t₀ n)) hfix.symm

#print axioms exists_stabilizesAtMin_of_cascadeFixes

theorem stabilizesAtMin_unique (h₁ : StabilizesAtMin ds t₀ N₁) (h₂ : StabilizesAtMin ds t₀ N₂) :
    N₁ = N₂ := by
  rcases lt_trichotomy N₁ N₂ with h | h | h
  · have hlt := h₂.2 N₁ h
    rw [h₁.1] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact h
  · have hlt := h₁.2 N₂ h
    rw [h₂.1] at hlt
    exact absurd hlt (lt_irrefl _)

#print axioms stabilizesAtMin_unique

theorem cascadeSeq_mono (hpos : ∀ d ∈ ds, 0 < d) : ∀ i j, i ≤ j →
    cascadeSeq ds t₀ i ≤ cascadeSeq ds t₀ j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := Nat.le_zero.mp h; subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with he | hlt
    · cases he; exact le_rfl
    · exact le_trans (ih (Nat.le_of_lt_succ hlt)) (le_of_isMove hpos (cascadeSeq_isMove ds t₀ j))

#print axioms cascadeSeq_mono

/-- The landing is lonely (the witness each outcome type yields). -/
theorem stabilizesAtMin_lonely (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N) :
    LonelyAt ds (cascadeSeq ds t₀ N) := by
  have h := cascadeSeq_isMove ds t₀ N
  rw [hS.1] at h
  exact (isMove_self_iff hpos).mp h

#print axioms stabilizesAtMin_lonely

/-! ## The opener -/

/-- The readings whose last-move opening is the landing (the tied openers). -/
noncomputable def openersAt (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Finset ℝ :=
  ds.filter (fun d => InWay d (cascadeSeq ds t₀ (N - 1)) ∧
    nextOpening d (cascadeSeq ds t₀ (N - 1)) = cascadeSeq ds t₀ N)

theorem mem_openersAt {d : ℝ} :
    d ∈ openersAt ds t₀ N ↔ d ∈ ds ∧ InWay d (cascadeSeq ds t₀ (N - 1)) ∧
      nextOpening d (cascadeSeq ds t₀ (N - 1)) = cascadeSeq ds t₀ N := by
  simp only [openersAt, Finset.mem_filter]

theorem openersAt_nonempty (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) :
    (openersAt ds t₀ N).Nonempty := by
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hmove := cascadeSeq_isMove ds t₀ (N - 1)
  rw [hsub] at hmove
  rcases hmove with ⟨_, heq⟩ | ⟨d, hd, hw, heq, _⟩
  · have hlt := hS.2 (N - 1) (by omega)
    rw [hsub] at hlt
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact ⟨d, mem_openersAt.mpr ⟨hd, hw, heq.symm⟩⟩

#print axioms openersAt_nonempty

/-- The opener: the smallest tied opener (`Finset.min'`; the smallest zone entry by
`tied_opener_entry`, E325's corrected tie rule).  The fallback `0` is never used under
`StabilizesAtMin` with `0 < N`. -/
noncomputable def openerOf (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : ℝ :=
  if h : (openersAt ds t₀ N).Nonempty then (openersAt ds t₀ N).min' h else 0

theorem openerOf_mem_openers (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N)
    (hN : 0 < N) : openerOf ds t₀ N ∈ openersAt ds t₀ N := by
  unfold openerOf
  rw [dif_pos (openersAt_nonempty hpos hS hN)]
  exact Finset.min'_mem _ _

theorem openerOf_le (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N)
    {d : ℝ} (hd : d ∈ openersAt ds t₀ N) : openerOf ds t₀ N ≤ d := by
  unfold openerOf
  rw [dif_pos (openersAt_nonempty hpos hS hN)]
  exact Finset.min'_le _ d hd

theorem openerOf_mem (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) :
    openerOf ds t₀ N ∈ ds :=
  (mem_openersAt.mp (openerOf_mem_openers hpos hS hN)).1

theorem openerOf_pos (hpos : ∀ d ∈ ds, 0 < d) (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) :
    0 < openerOf ds t₀ N := hpos _ (openerOf_mem hpos hS hN)

#print axioms openerOf_mem_openers
#print axioms openerOf_le

/-- An opening is a lap line plus one eighth. -/
theorem opening_eq {d u : ℝ} (hd : 0 < d) (hw : InWay d u) :
    ∃ k : ℤ, nextOpening d u = (((k : ℝ)) + 1 / 8) / d ∧
      d * nextOpening d u = ((k : ℝ)) + 1 / 8 := by
  obtain ⟨k, hk⟩ := exists_near_int hw
  refine ⟨k, nextOpening_eq hk, ?_⟩
  rw [nextOpening_eq hk]
  field_simp

#print axioms opening_eq

/-- Every opening the cascade lands on has lap at least one (under the bound hypothesis). -/
theorem openersAt_lap_ge_one (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) {d : ℝ} (hd : d ∈ openersAt ds t₀ N) :
    ∃ k : ℤ, 1 ≤ k ∧ d * cascadeSeq ds t₀ N = ((k : ℝ)) + 1 / 8 := by
  obtain ⟨hds, hw, hop⟩ := mem_openersAt.mp hd
  obtain ⟨k, hval, hk2⟩ := opening_eq (hpos d hds) hw
  rw [hop] at hk2
  refine ⟨k, ?_, hk2⟩
  by_contra hcon
  push_neg at hcon
  have hk0 : k ≤ 0 := by omega
  have hk0r : ((k : ℝ)) ≤ 0 := by exact_mod_cast hk0
  have hdpos := hpos d hds
  have hdbd := hbd d hds
  have e2 : (((k : ℝ)) + 1 / 8) / d ≤ t₀ := by
    rw [div_le_iff₀ hdpos]
    have hcomm : t₀ * d = d * t₀ := mul_comm _ _
    linarith
  have hle' : nextOpening d (cascadeSeq ds t₀ (N - 1)) ≤ t₀ := by rw [hval]; exact e2
  have hgt := lt_nextOpening hdpos hw
  have hstart : t₀ ≤ cascadeSeq ds t₀ (N - 1) := cascadeSeq_mono hpos 0 (N - 1) (by omega)
  linarith

#print axioms openersAt_lap_ge_one

/-- The anchor law (catalogue audit, agent C, [T 52000/52000]): the landing of a cascade with at
least one move is the opener's own clearance edge — `R·ρ_opener = 8·lap + 1` in taxonomy units. -/
theorem landing_is_opener_exit (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) :
    ∃ k : ℤ, 1 ≤ k ∧ openerOf ds t₀ N * cascadeSeq ds t₀ N = ((k : ℝ)) + 1 / 8 :=
  openersAt_lap_ge_one hpos hbd hS (openerOf_mem_openers hpos hS hN)

#print axioms landing_is_opener_exit

/-- Among zones sharing an exit, the smaller reading has the smaller (earlier) entry: resolving
opener ties by smallest reading is E325's "smallest entry" rule. -/
theorem tied_opener_entry {T a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b) {ka kb : ℤ}
    (hva : a * T = ((ka : ℝ)) + 1 / 8) (hvb : b * T = ((kb : ℝ)) + 1 / 8) :
    (((ka : ℝ)) - 1 / 8) / a < (((kb : ℝ)) - 1 / 8) / b := by
  have h1a : ((ka : ℝ)) - 1 / 8 = a * T - 1 / 4 := by rw [hva]; ring
  have h1b : ((kb : ℝ)) - 1 / 8 = b * T - 1 / 4 := by rw [hvb]; ring
  have h2a : (a * T - 1 / 4) / a = T - 1 / (4 * a) := by
    rw [div_eq_iff (ne_of_gt ha)]
    field_simp
  have h2b : (b * T - 1 / 4) / b = T - 1 / (4 * b) := by
    rw [div_eq_iff (ne_of_gt hb)]
    field_simp
  rw [h1a, h1b, h2a, h2b]
  have key : 1 / (4 * b) < 1 / (4 * a) := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * b) (by positivity : (0 : ℝ) < 4 * a)]
    have h4 : (1 : ℝ) * (4 * a) < (1 : ℝ) * (4 * b) := by nlinarith [ha, hb, hab]
    exact h4
  linarith

#print axioms tied_opener_entry

/-! ## The class ingredients -/

/-- Some reading's next zone entry coincides with `t` (the window after `t` has width 0; the
taxonomy's `width = 0`, entry edge `8k-1` in `R·ρ` units). -/
-- STANDING: DEFINITION
def ZeroWidthAt (ds : Finset ℝ) (t : ℝ) : Prop :=
  ∃ d ∈ ds, ∃ j : ℤ, d * t = ((j : ℝ)) - 1 / 8

/-- The opener's lap is 1: its landing phase is exactly `9/8` (taxonomy exit `9/ρ_s`). -/
-- STANDING: DEFINITION
def OpenerLapOne (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  openerOf ds t₀ N * cascadeSeq ds t₀ N = 9 / 8

/-- The opener's lap is at least 2. -/
-- STANDING: DEFINITION
def OpenerLapTwo (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  ∃ k : ℤ, 2 ≤ k ∧ openerOf ds t₀ N * cascadeSeq ds t₀ N = ((k : ℝ)) + 1 / 8

/-- The closer is the opener's own reading: the opener's next entry is strictly before every
other reading's (the strict-dominance form of E325). -/
-- STANDING: DEFINITION
def OpenerOwnCloser (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  ∀ d ∈ ds, d ≠ openerOf ds t₀ N →
    nextEntry (openerOf ds t₀ N) (cascadeSeq ds t₀ N) < nextEntry d (cascadeSeq ds t₀ N)

/-- The opener is a strip reading: in a zone already at the start. -/
-- STANDING: DEFINITION
def OpenerStrip (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop := InWay (openerOf ds t₀ N) t₀

theorem openerLapTwo_not_lapOne : OpenerLapTwo ds t₀ N → ¬ OpenerLapOne ds t₀ N := by
  rintro ⟨k, hk2, hkval⟩ h1
  unfold OpenerLapOne at h1
  have hke : ((k : ℝ)) = 1 := by linarith
  have : k = 1 := by exact_mod_cast hke
  omega

#print axioms openerLapTwo_not_lapOne

theorem opener_lap_cases (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) :
    OpenerLapOne ds t₀ N ∨ OpenerLapTwo ds t₀ N := by
  obtain ⟨k, hk1, hkval⟩ := landing_is_opener_exit hpos hbd hS hN
  by_cases hk : k = 1
  · left
    subst hk
    show openerOf ds t₀ N * cascadeSeq ds t₀ N = 9 / 8
    rw [hkval]
    norm_num
  · right
    exact ⟨k, by omega, hkval⟩

#print axioms opener_lap_cases

/-! ## The 14 classes -/

/-- The 14 outcome types of E325 (the K-list). -/
inductive KTag : Type
  | K0 | K0z | K1a | K1b | K1s1 | K1s2 | K1z | K2a | K2b | K2c | K2d | K2s1 | K2s2 | K2z
deriving DecidableEq

/-- The sorter: the cascade outcome's class, in E325's order of tests (moves; width; closer;
lap; strip).  The tests after the first apply only when `N ≥ 1`. -/
noncomputable def kTagOf (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : KTag :=
  match N with
  | 0 => if ZeroWidthAt ds (cascadeSeq ds t₀ 0) then KTag.K0z else KTag.K0
  | 1 =>
    if ZeroWidthAt ds (cascadeSeq ds t₀ 1) then KTag.K1z
    else if OpenerOwnCloser ds t₀ 1 then
      (if OpenerLapOne ds t₀ 1 then KTag.K1s1 else KTag.K1s2)
    else (if OpenerLapOne ds t₀ 1 then KTag.K1a else KTag.K1b)
  | (n + 2) =>
    if ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2)) then KTag.K2z
    else if OpenerOwnCloser ds t₀ (n + 2) then
      (if OpenerLapOne ds t₀ (n + 2) then KTag.K2s1 else KTag.K2s2)
    else if OpenerStrip ds t₀ (n + 2) then
      (if OpenerLapOne ds t₀ (n + 2) then KTag.K2a else KTag.K2b)
    else (if OpenerLapOne ds t₀ (n + 2) then KTag.K2c else KTag.K2d)

theorem kTagOf_zero : kTagOf ds t₀ 0 =
    if ZeroWidthAt ds (cascadeSeq ds t₀ 0) then KTag.K0z else KTag.K0 := rfl

#print axioms kTagOf_zero

theorem kTagOf_one : kTagOf ds t₀ 1 =
    (if ZeroWidthAt ds (cascadeSeq ds t₀ 1) then KTag.K1z
    else if OpenerOwnCloser ds t₀ 1 then
      (if OpenerLapOne ds t₀ 1 then KTag.K1s1 else KTag.K1s2)
    else (if OpenerLapOne ds t₀ 1 then KTag.K1a else KTag.K1b)) := rfl

#print axioms kTagOf_one

theorem kTagOf_two (m : ℕ) : kTagOf ds t₀ (m + 2) =
    (if ZeroWidthAt ds (cascadeSeq ds t₀ (m + 2)) then KTag.K2z
    else if OpenerOwnCloser ds t₀ (m + 2) then
      (if OpenerLapOne ds t₀ (m + 2) then KTag.K2s1 else KTag.K2s2)
    else if OpenerStrip ds t₀ (m + 2) then
      (if OpenerLapOne ds t₀ (m + 2) then KTag.K2a else KTag.K2b)
    else (if OpenerLapOne ds t₀ (m + 2) then KTag.K2c else KTag.K2d)) := rfl

#print axioms kTagOf_two

/-- The 14 classes as native predicates (E325's table, `N` = number of moves; landing =
`cascadeSeq ds t₀ N`). -/
-- STANDING: DEFINITION
def KClass (t : KTag) (ds : Finset ℝ) (t₀ : ℝ) (N : ℕ) : Prop :=
  match t with
  | KTag.K0 => N = 0 ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N)
  | KTag.K0z => N = 0 ∧ ZeroWidthAt ds (cascadeSeq ds t₀ N)
  | KTag.K1a => N = 1 ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ OpenerLapOne ds t₀ N
  | KTag.K1b => N = 1 ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ OpenerLapTwo ds t₀ N
  | KTag.K1s1 => N = 1 ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      OpenerOwnCloser ds t₀ N ∧ OpenerLapOne ds t₀ N
  | KTag.K1s2 => N = 1 ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      OpenerOwnCloser ds t₀ N ∧ OpenerLapTwo ds t₀ N
  | KTag.K1z => N = 1 ∧ ZeroWidthAt ds (cascadeSeq ds t₀ N)
  | KTag.K2a => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ OpenerStrip ds t₀ N ∧ OpenerLapOne ds t₀ N
  | KTag.K2b => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ OpenerStrip ds t₀ N ∧ OpenerLapTwo ds t₀ N
  | KTag.K2c => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ ¬ OpenerStrip ds t₀ N ∧ OpenerLapOne ds t₀ N
  | KTag.K2d => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      ¬ OpenerOwnCloser ds t₀ N ∧ ¬ OpenerStrip ds t₀ N ∧ OpenerLapTwo ds t₀ N
  | KTag.K2s1 => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      OpenerOwnCloser ds t₀ N ∧ OpenerLapOne ds t₀ N
  | KTag.K2s2 => 2 ≤ N ∧ ¬ ZeroWidthAt ds (cascadeSeq ds t₀ N) ∧
      OpenerOwnCloser ds t₀ N ∧ OpenerLapTwo ds t₀ N
  | KTag.K2z => 2 ≤ N ∧ ZeroWidthAt ds (cascadeSeq ds t₀ N)

/-! ## The sorter's values per number of moves -/

theorem kTagOf_of_N0 (hN : N = 0) :
    kTagOf ds t₀ N = KTag.K0 ∨ kTagOf ds t₀ N = KTag.K0z := by
  subst hN
  rw [kTagOf_zero]
  by_cases h : ZeroWidthAt ds (cascadeSeq ds t₀ 0)
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

#print axioms kTagOf_of_N0

theorem kTagOf_of_N1 (hN : N = 1) :
    kTagOf ds t₀ N = KTag.K1z ∨ kTagOf ds t₀ N = KTag.K1a ∨ kTagOf ds t₀ N = KTag.K1b ∨
      kTagOf ds t₀ N = KTag.K1s1 ∨ kTagOf ds t₀ N = KTag.K1s2 := by
  subst hN
  rw [kTagOf_one]
  by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
  · rw [if_pos hzw]; exact Or.inl rfl
  · rw [if_neg hzw]
    by_cases hoc : OpenerOwnCloser ds t₀ 1
    · rw [if_pos hoc]
      by_cases hlap : OpenerLapOne ds t₀ 1
      · rw [if_pos hlap]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [if_neg hlap]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rw [if_neg hoc]
      by_cases hlap : OpenerLapOne ds t₀ 1
      · rw [if_pos hlap]; exact Or.inr (Or.inl rfl)
      · rw [if_neg hlap]; exact Or.inr (Or.inr (Or.inl rfl))

#print axioms kTagOf_of_N1

theorem kTagOf_of_N2 (hn : ∃ m : ℕ, N = m + 2) :
    kTagOf ds t₀ N = KTag.K2z ∨ kTagOf ds t₀ N = KTag.K2a ∨ kTagOf ds t₀ N = KTag.K2b ∨
      kTagOf ds t₀ N = KTag.K2c ∨ kTagOf ds t₀ N = KTag.K2d ∨ kTagOf ds t₀ N = KTag.K2s1 ∨
      kTagOf ds t₀ N = KTag.K2s2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [kTagOf_two]
  by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (m + 2))
  · rw [if_pos hzw]; exact Or.inl rfl
  · rw [if_neg hzw]
    by_cases hoc : OpenerOwnCloser ds t₀ (m + 2)
    · rw [if_pos hoc]
      by_cases hlap : OpenerLapOne ds t₀ (m + 2)
      · rw [if_pos hlap]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · rw [if_neg hlap]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · rw [if_neg hoc]
      by_cases hstrip : OpenerStrip ds t₀ (m + 2)
      · rw [if_pos hstrip]
        by_cases hlap : OpenerLapOne ds t₀ (m + 2)
        · rw [if_pos hlap]; exact Or.inr (Or.inl rfl)
        · rw [if_neg hlap]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [if_neg hstrip]
        by_cases hlap : OpenerLapOne ds t₀ (m + 2)
        · rw [if_pos hlap]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [if_neg hlap]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

#print axioms kTagOf_of_N2

/-! ## The bridge: class ⟺ sorter value -/

/-- The native class predicates are exactly the fibres of the sorter.  (The lap dichotomy at
`N ≥ 1` uses `opener_lap_cases`.) -/
theorem kClass_iff_tag (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) (t : KTag) : KClass t ds t₀ N ↔ kTagOf ds t₀ N = t := by
  cases t with
  | K0 =>
    constructor
    ·
      rintro ⟨rfl, hzw⟩
      rw [kTagOf_zero, if_neg hzw]
    · intro h
      cases N with
      | zero =>
        rw [kTagOf_zero] at h
        by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 0)
        · rw [if_pos hzw] at h; simp at h
        · rw [if_neg hzw] at h; exact ⟨rfl, hzw⟩
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K0z =>
    constructor
    ·
      rintro ⟨rfl, hzw⟩
      rw [kTagOf_zero, if_pos hzw]
    · intro h
      cases N with
      | zero =>
        rw [kTagOf_zero] at h
        by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 0)
        · rw [if_pos hzw] at h; exact ⟨rfl, hzw⟩
        · rw [if_neg hzw] at h; simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K1a =>
    constructor
    ·
      rintro ⟨rfl, hzw, hoc, hlap⟩
      rw [kTagOf_one, if_neg hzw, if_neg hoc, if_pos hlap]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.zero_add 1, kTagOf_one] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ 1
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; exact ⟨rfl, hzw, hoc, hlap⟩
              · rw [if_neg hlap] at h; simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K1b =>
    constructor
    ·
      rintro ⟨rfl, hzw, hoc, hlap2⟩
      have hnl1 := openerLapTwo_not_lapOne hlap2
      rw [kTagOf_one, if_neg hzw, if_neg hoc, if_neg hnl1]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.zero_add 1, kTagOf_one] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ 1
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h
                rcases opener_lap_cases hpos hbd hS (by omega) with hL1 | hL2
                · exact absurd hL1 hlap
                · exact ⟨rfl, hzw, hoc, hL2⟩
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K1s1 =>
    constructor
    ·
      rintro ⟨rfl, hzw, hoc, hlap⟩
      rw [kTagOf_one, if_neg hzw, if_pos hoc, if_pos hlap]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.zero_add 1, kTagOf_one] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ 1
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; exact ⟨rfl, hzw, hoc, hlap⟩
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K1s2 =>
    constructor
    ·
      rintro ⟨rfl, hzw, hoc, hlap2⟩
      have hnl1 := openerLapTwo_not_lapOne hlap2
      rw [kTagOf_one, if_neg hzw, if_pos hoc, if_neg hnl1]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.zero_add 1, kTagOf_one] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ 1
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h
                rcases opener_lap_cases hpos hbd hS (by omega) with hL1 | hL2
                · exact absurd hL1 hlap
                · exact ⟨rfl, hzw, hoc, hL2⟩
            · rw [if_neg hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K1z =>
    constructor
    ·
      rintro ⟨rfl, hzw⟩
      rw [kTagOf_one, if_pos hzw]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.zero_add 1, kTagOf_one] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ 1)
          · rw [if_pos hzw] at h; exact ⟨rfl, hzw⟩
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ 1
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ 1
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
        | succ n =>
          rcases kTagOf_of_N2 ⟨n, rfl⟩ with h'|h'|h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
  | K2a =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hstrip, hlap⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      rw [kTagOf_two, if_neg hzw, if_neg hoc, if_pos hstrip, if_pos hlap]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; exact ⟨by omega, hzw, hoc, hstrip, hlap⟩
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
  | K2b =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hstrip, hlap2⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      have hnl1 := openerLapTwo_not_lapOne hlap2
      rw [kTagOf_two, if_neg hzw, if_neg hoc, if_pos hstrip, if_neg hnl1]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h
                  rcases opener_lap_cases hpos hbd hS (by omega) with hL1 | hL2
                  · exact absurd hL1 hlap
                  · exact ⟨by omega, hzw, hoc, hstrip, hL2⟩
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
  | K2c =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hstrip, hlap⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      rw [kTagOf_two, if_neg hzw, if_neg hoc, if_neg hstrip, if_pos hlap]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; exact ⟨by omega, hzw, hoc, hstrip, hlap⟩
                · rw [if_neg hlap] at h; simp at h
  | K2d =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hstrip, hlap2⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      have hnl1 := openerLapTwo_not_lapOne hlap2
      rw [kTagOf_two, if_neg hzw, if_neg hoc, if_neg hstrip, if_neg hnl1]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h
                  rcases opener_lap_cases hpos hbd hS (by omega) with hL1 | hL2
                  · exact absurd hL1 hlap
                  · exact ⟨by omega, hzw, hoc, hstrip, hL2⟩
  | K2s1 =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hlap⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      rw [kTagOf_two, if_neg hzw, if_pos hoc, if_pos hlap]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; exact ⟨by omega, hzw, hoc, hlap⟩
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
  | K2s2 =>
    constructor
    ·
      rintro ⟨hN2, hzw, hoc, hlap2⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      have hnl1 := openerLapTwo_not_lapOne hlap2
      rw [kTagOf_two, if_neg hzw, if_pos hoc, if_neg hnl1]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; simp at h
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h
                rcases opener_lap_cases hpos hbd hS (by omega) with hL1 | hL2
                · exact absurd hL1 hlap
                · exact ⟨by omega, hzw, hoc, hL2⟩
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
  | K2z =>
    constructor
    ·
      rintro ⟨hN2, hzw⟩
      obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
      rw [kTagOf_two, if_pos hzw]
    · intro h
      cases N with
      | zero =>
        rcases kTagOf_of_N0 rfl with h'|h' <;> rw [h'] at h <;> simp at h
      | succ m =>
        cases m with
        | zero =>
          rcases kTagOf_of_N1 rfl with h'|h'|h'|h'|h' <;> rw [h'] at h <;> simp at h
        | succ n =>
          have hn2 : n + 1 + 1 = n + 2 := by omega
          rw [hn2] at h
          rw [kTagOf_two] at h
          by_cases hzw : ZeroWidthAt ds (cascadeSeq ds t₀ (n + 2))
          · rw [if_pos hzw] at h; exact ⟨by omega, hzw⟩
          · rw [if_neg hzw] at h
            by_cases hoc : OpenerOwnCloser ds t₀ (n + 2)
            · rw [if_pos hoc] at h
              by_cases hlap : OpenerLapOne ds t₀ (n + 2)
              · rw [if_pos hlap] at h; simp at h
              · rw [if_neg hlap] at h; simp at h
            · rw [if_neg hoc] at h
              by_cases hstrip : OpenerStrip ds t₀ (n + 2)
              · rw [if_pos hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h
              · rw [if_neg hstrip] at h
                by_cases hlap : OpenerLapOne ds t₀ (n + 2)
                · rw [if_pos hlap] at h; simp at h
                · rw [if_neg hlap] at h; simp at h

#print axioms kClass_iff_tag

/-- Mutual exclusion: two classes of the same outcome agree. -/
theorem kClass_exclusive (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) {t₁ t₂ : KTag} (h₁ : KClass t₁ ds t₀ N)
    (h₂ : KClass t₂ ds t₀ N) : t₁ = t₂ := by
  exact ((kClass_iff_tag hpos hbd hS t₁).mp h₁).symm.trans ((kClass_iff_tag hpos hbd hS t₂).mp h₂)

/-- Every outcome lies in exactly one class (the finite disjunction is exclusive and total). -/
theorem kClass_exactlyOne (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) : ∃! t : KTag, KClass t ds t₀ N := by
  refine ⟨kTagOf ds t₀ N, (kClass_iff_tag hpos hbd hS _).mpr rfl, ?_⟩
  intro t' ht'
  exact ((kClass_iff_tag hpos hbd hS t').mp ht').symm

#print axioms kClass_exclusive
#print axioms kClass_exactlyOne

/-! ## The two empty classes -/

/-- E333 lemma L1 (provenance: `MappedCascadeRules.faster_closes_before_opener`,
`LRC.Spec.CascadeOutcomeExclusionsN.later_lap_one_has_faster`): at a lonely instant, a reading
faster than one standing exactly at its clearance edge closes first. -/
theorem faster_closes_before_opener {T : ℝ} (hT : LonelyAt ds T) {s d : ℝ} (hdsmem : d ∈ ds)
    (hs : 0 < s) (hd : 0 < d) (hsd : s < d) (hedge : ∃ k : ℤ, s * T = ((k : ℝ)) + 1 / 8) :
    nextEntry d T < nextEntry s T := by
  obtain ⟨k, hk⟩ := hedge
  have hs1 : ((k : ℝ)) + 1 / 8 ≤ s * T := by rw [hk]
  have hs2 : s * T ≤ ((k : ℝ)) + 7 / 8 := by rw [hk]; linarith
  have hclr := hT d hdsmem
  obtain ⟨k', hk1, hk2⟩ := (distInt_ge_eighth_iff (d * T)).mp hclr
  have e1 : ((k : ℝ)) + 7 / 8 = s * T + 3 / 4 := by rw [hk]; ring
  have e2 : ((k' : ℝ)) + 7 / 8 ≤ d * T + 3 / 4 := by linarith
  have g1 : (((k' : ℝ)) + 7 / 8) / d ≤ (d * T + 3 / 4) / d := by
    rw [div_le_div_iff₀ hd hd]
    exact mul_le_mul_of_nonneg_right e2 hd.le
  have eqd : (d * T + 3 / 4) / d = T + 3 / (4 * d) := by
    rw [div_eq_iff (ne_of_gt hd)]
    field_simp
  have eqs : (s * T + 3 / 4) / s = T + 3 / (4 * s) := by
    rw [div_eq_iff (ne_of_gt hs)]
    field_simp
  have key : 3 / (4 * d) < 3 / (4 * s) := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * d) (by positivity : (0 : ℝ) < 4 * s)]
    have h4 : (3 : ℝ) * (4 * s) < (3 : ℝ) * (4 * d) := by nlinarith [hsd, hs, hd]
    exact h4
  rw [nextEntry_eq hd k' hk1 hk2, nextEntry_eq hs k hs1 hs2, e1, eqs]
  calc (((k' : ℝ)) + 7 / 8) / d ≤ (d * T + 3 / 4) / d := g1
    _ = T + 3 / (4 * d) := eqd
    _ < T + 3 / (4 * s) := by linarith

#print axioms faster_closes_before_opener

/-- The opener of an own-closer outcome is the fastest reading (E333 L1 consequence). -/
theorem opener_fastest_of_ownCloser (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) (hN : 0 < N) (hoc : OpenerOwnCloser ds t₀ N) :
    ∀ d ∈ ds, d ≤ openerOf ds t₀ N := by
  intro d hd
  by_contra hcon
  push_neg at hcon
  have hne : d ≠ openerOf ds t₀ N := by
    intro h
    rw [h] at hcon
    exact lt_irrefl _ hcon
  have hlonely := stabilizesAtMin_lonely hpos hS
  obtain ⟨k, hk1, hk2⟩ := landing_is_opener_exit hpos hbd hS hN
  have hfast := faster_closes_before_opener hlonely hd (openerOf_pos hpos hS hN) (hpos d hd)
    hcon ⟨k, hk2⟩
  have hslow := hoc d hd hne
  linarith

#print axioms opener_fastest_of_ownCloser

/-- **K2a is empty** (E325's hand argument; provenance `LRC.Spec.CascadeOutcomeExclusionsN.
no_late_initial_lap_one`): with two or more moves, a strip opener's initial zone already ends at
or before the first move, so its lap cannot be 1. -/
theorem k2a_empty (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) : ¬ KClass KTag.K2a ds t₀ N := by
  intro hcls
  simp only [KClass] at hcls
  obtain ⟨hN2, _hzw, _hoc, hstrip, hlap⟩ := hcls
  obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  have hNpos : 0 < n + 2 := by omega
  have hmem := openerOf_mem_openers hpos hS hNpos
  obtain ⟨hopds, hopinway, hopopen⟩ := mem_openersAt.mp hmem
  have hopos := openerOf_pos hpos hS hNpos
  have hstrip' : InWay (openerOf ds t₀ (n + 2)) t₀ := hstrip
  obtain ⟨K₀, hval, _⟩ := opening_eq hopos hstrip'
  have hK₀ : 1 ≤ K₀ := by
    by_contra hcon
    push_neg at hcon
    have hk0 : K₀ ≤ 0 := by omega
    have hk0r : ((K₀ : ℝ)) ≤ 0 := by exact_mod_cast hk0
    have hopbd := hbd _ hopds
    have hle : (((K₀ : ℝ)) + 1 / 8) / openerOf ds t₀ (n + 2) ≤ t₀ := by
      rw [div_le_iff₀ hopos]
      have hcomm : t₀ * openerOf ds t₀ (n + 2) = openerOf ds t₀ (n + 2) * t₀ := mul_comm _ _
      linarith
    have hle' : nextOpening (openerOf ds t₀ (n + 2)) t₀ ≤ t₀ := by rw [hval]; exact hle
    have hgt := lt_nextOpening hopos hstrip'
    linarith
  have hstrict0 := hS.2 0 (by omega)
  have hmove0 := cascadeSeq_isMove ds t₀ 0
  rw [Nat.zero_add 1] at hmove0
  rcases hmove0 with ⟨_, heq0⟩ | ⟨q, hq, hwq, heq0, hmax⟩
  · rw [heq0] at hstrict0; exact lt_irrefl _ hstrict0
  · have hle1 : nextOpening (openerOf ds t₀ (n + 2)) t₀ ≤ cascadeSeq ds t₀ 1 :=
      hmax (openerOf ds t₀ (n + 2)) hopds hstrip'
    rw [hval] at hle1
    have hseq1 : cascadeSeq ds t₀ 1 < cascadeSeq ds t₀ (n + 2) :=
      lt_of_lt_of_le (hS.2 1 (by omega)) (cascadeSeq_mono hpos 2 (n + 2) (by omega))
    have hTval : cascadeSeq ds t₀ (n + 2) = (9 / 8) / openerOf ds t₀ (n + 2) := by
      rw [eq_div_iff (ne_of_gt hopos), mul_comm]
      exact hlap
    rw [hTval] at hseq1
    have hfin : (((K₀ : ℝ)) + 1 / 8) / openerOf ds t₀ (n + 2)
        < (9 / 8) / openerOf ds t₀ (n + 2) := lt_of_le_of_lt hle1 hseq1
    have hc := (div_lt_div_iff₀ hopos hopos).mp hfin
    have hKlt : ((K₀ : ℝ)) + 1 / 8 < 9 / 8 := lt_of_mul_lt_mul_right hc (le_of_lt hopos)
    have hKlt' : ((K₀ : ℝ)) < 1 := by linarith
    have hKlt'' : K₀ < 1 := by exact_mod_cast hKlt'
    omega

#print axioms k2a_empty

/-- **K2s1 is empty** (E333; provenance `LRC.Spec.CascadeOutcomeExclusionsN.
no_late_lap_one_self_closer`): an own closer at lap one forces the opener fastest, and then no
previous setter can have opened strictly below the lap-one exit. -/
theorem k2s1_empty (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) : ¬ KClass KTag.K2s1 ds t₀ N := by
  intro hcls
  simp only [KClass] at hcls
  obtain ⟨hN2, _hzw, hoc, hlap⟩ := hcls
  obtain ⟨n, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  have hNpos : 0 < n + 2 := by omega
  have hfast := opener_fastest_of_ownCloser hpos hbd hS hNpos hoc
  have hmem := openerOf_mem_openers hpos hS hNpos
  obtain ⟨hopds, hopinway, hopopen⟩ := mem_openersAt.mp hmem
  have hopos := openerOf_pos hpos hS hNpos
  have hidx : n + 2 - 1 = n + 1 := by omega
  rw [hidx] at hopinway hopopen
  have hprev := cascadeSeq_isMove ds t₀ n
  have hstrn := hS.2 n (by omega)
  rcases hprev with ⟨_, heq⟩ | ⟨p, hp, hwp, heq, _⟩
  · rw [heq] at hstrn; exact lt_irrefl _ hstrn
  · have hppos := hpos p hp
    obtain ⟨K₁, hvalp, hk2p⟩ := opening_eq hppos hwp
    have hK₁ : 1 ≤ K₁ := by
      by_contra hcon
      push_neg at hcon
      have hk0 : K₁ ≤ 0 := by omega
      have hk0r : ((K₁ : ℝ)) ≤ 0 := by exact_mod_cast hk0
      have hpbd := hbd p hp
      have hle : (((K₁ : ℝ)) + 1 / 8) / p ≤ t₀ := by
        rw [div_le_iff₀ hppos]
        have hcomm : t₀ * p = p * t₀ := mul_comm _ _
        linarith
      rw [← hvalp, ← heq] at hle
      have hstart : t₀ ≤ cascadeSeq ds t₀ n := cascadeSeq_mono hpos 0 n (by omega)
      linarith
    have hpne : p ≠ openerOf ds t₀ (n + 2) := by
      intro hpe
      rw [← heq] at hk2p
      rw [hpe] at hk2p
      have hdist : distInt (openerOf ds t₀ (n + 2) * cascadeSeq ds t₀ (n + 1)) = 1 / 8 := by
        rw [hk2p, add_comm]
        exact distInt_eighth_add_int K₁
      have hcontra : distInt (openerOf ds t₀ (n + 2) * cascadeSeq ds t₀ (n + 1)) < 1 / 8 :=
        hopinway
      linarith
    have hple : p ≤ openerOf ds t₀ (n + 2) := hfast p hp
    have hplt : p < openerOf ds t₀ (n + 2) := lt_of_le_of_ne hple hpne
    have hult : cascadeSeq ds t₀ (n + 1) < cascadeSeq ds t₀ (n + 2) := hS.2 (n + 1) (by omega)
    have hTval : cascadeSeq ds t₀ (n + 2) = (9 / 8) / openerOf ds t₀ (n + 2) := by
      rw [eq_div_iff (ne_of_gt hopos), mul_comm]
      exact hlap
    rw [hTval, heq, hvalp] at hult
    by_cases hKe : K₁ = 1
    · rw [hKe] at hult
      push_cast at hult
      norm_num at hult
      have hc := (div_lt_div_iff₀ hppos hopos).mp hult
      have he2 : (9 / 8 : ℝ) * p < (9 / 8 : ℝ) * openerOf ds t₀ (n + 2) :=
        mul_lt_mul_of_pos_left hplt (by norm_num)
      linarith
    · have hK2 : 2 ≤ K₁ := by omega
      have h17 : (17 / 8 : ℝ) ≤ ((K₁ : ℝ)) + 1 / 8 := by
        have h17' : (2 : ℝ) ≤ ((K₁ : ℝ)) := by exact_mod_cast hK2
        linarith
      have hm : (17 / 8 : ℝ) / p ≤ (((K₁ : ℝ)) + 1 / 8) / p := by
        rw [div_le_div_iff₀ hppos hppos]
        exact mul_le_mul_of_nonneg_right h17 (le_of_lt hppos)
      have hult2 : (17 / 8 : ℝ) / p < (9 / 8) / openerOf ds t₀ (n + 2) := by linarith
      have hc := (div_lt_div_iff₀ hppos hopos).mp hult2
      have he2 : (9 / 8 : ℝ) * p < (9 / 8 : ℝ) * openerOf ds t₀ (n + 2) :=
        mul_lt_mul_of_pos_left hplt (by norm_num)
      have hring : (17 / 8 : ℝ) * openerOf ds t₀ (n + 2) - (9 / 8 : ℝ) * openerOf ds t₀ (n + 2)
          = openerOf ds t₀ (n + 2) := by ring
      linarith

#print axioms k2s1_empty

/-! ## Arrangements -/

/-- At the bound `1/(8·d_min)` every reading of the subject is at or past its first eighth. -/
theorem disparitySet_lower {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hv : IsArrangement v)
    (hm : IsDmin v k m) : ∀ d ∈ disparitySet v k, 1 / 8 ≤ d * (1 / (8 * m)) := by
  intro d hd
  have hpos := Fresh.Cascade.disparitySet_pos hv k
  have hmpos : 0 < m := hpos m (Finset.mem_coe.mpr hm.1)
  have hmd : m ≤ d := hm.2 (Finset.mem_coe.mpr hd)
  have h8m : (0 : ℝ) < 8 * m := by positivity
  rw [mul_one_div, le_div_iff₀ h8m]
  have e : (1 / 8 : ℝ) * (8 * m) = m := by ring
  rw [e]
  exact hmd

#print axioms disparitySet_lower

/-- The sorting statement at the arrangement level: an arrangement whose cascade lands is in
exactly one of the 14 classes. -/
theorem arrangement_classified {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) (hfix : CascadeFixes (disparitySet v k) (1 / (8 * m))) :
    ∃! t : KTag, ∃ N, StabilizesAtMin (disparitySet v k) (1 / (8 * m)) N ∧
      KClass t (disparitySet v k) (1 / (8 * m)) N := by
  have hpos := Fresh.Cascade.disparitySet_pos hv k
  have hbd := disparitySet_lower hv hm
  obtain ⟨N, hS⟩ := exists_stabilizesAtMin_of_cascadeFixes hpos hfix
  obtain ⟨t, ht⟩ := kClass_exactlyOne (ds := disparitySet v k) (t₀ := 1 / (8 * m)) (N := N)
    hpos hbd hS
  refine ⟨t, ⟨N, hS, ht.1⟩, ?_⟩
  rintro t' ⟨N', hS', ht'⟩
  have hNN : N' = N := stabilizesAtMin_unique hS' hS
  rw [hNN] at ht'
  exact ht.2 t' ht'

#print axioms arrangement_classified

end Fresh.KTaxonomy
