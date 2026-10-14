import LonelyRunner.LRC.Spec.RationalN

set_option linter.style.longLine false

/-!
# Bystanders at a first lonely instant, and the clean takeover

2026-10-06 (running log entry owed).  Fix a list `T` of disparities and its first lonely instant
`t` at threshold `1/n`.  Add one more disparity `d`.

* `firstLonely_cons_iff`: `d :: T` has the same first lonely instant `t` exactly when `d` is clear
  at `t`.  A lonely instant of `d :: T` is lonely for `T`, so nothing earlier can work.
* `clear_iff_residue`: at a rational instant `a/q` the reading `d` is clear exactly when its
  residue `r = d·a mod q` lies in the band `q ≤ n·r ≤ (n−1)·q`.  `RationalN.lonely_of_ratWorks`
  is the (⇐) direction; this adds (⇒).
* `bystander_iff`: for `t = u/w`, `d` is a bystander of `T` exactly when `d·u mod w` is in the band.
  The allowed classes are therefore the dilate of the arc by `u⁻¹` (no coupling to `T` beyond
  `u` and `w`).
* `takeover`: if `d` is blocked at `t` (within `1/n` of the integer `N`), its edge is
  `E = (N + 1/n)/d`, and `T` stays lonely on `[t, t_R]` with `E ≤ t_R`, then `E` is the first
  lonely instant of `d :: T`: the bystander takes over cleanly.  When `E > t_R` the chain can
  continue (experiments/nN/redo/modgap_takeover_v2.out), and nothing here claims otherwise.
* `lonelyList_cons_iff`, `lonelyList_add_nat`, `exists_lonely_fract`: the lonely set of `d :: T` is the
  lonely set of `T` cut by the arcs of `d`; for integer disparities it is 1-periodic, so an order-seven
  instant (`OrderSevenN.existenceAtN_seven`, the framework's own Lean theorem) for six readings
  lies in `[0, 1)`.
* `takeover_of_lonely_at`: the general form: it is enough that `T` is lonely at `E`, in any
  component of its lonely set; `lonely_at_of_firstLonely_cons` is the converse, so the bystander's
  edge is the landing exactly when `T` is lonely there.

Everything is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.Bystander

open ConstructionN LRC.RationalN

/-- `t` is lonely for the list `L` at threshold `1/n`. -/
def LonelyList (n : ℕ) (L : List ℕ) (t : ℝ) : Prop :=
  ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)

/-- `t` is the first lonely instant of `L` at threshold `1/n`. -/
def FirstLonely (n : ℕ) (L : List ℕ) (t : ℝ) : Prop :=
  0 < t ∧ LonelyList n L t ∧ ∀ s : ℝ, 0 < s → s < t → ¬ LonelyList n L s

theorem lonelyList_of_cons {n : ℕ} {d : ℕ} {T : List ℕ} {s : ℝ}
    (h : LonelyList n (d :: T) s) : LonelyList n T s :=
  fun m hm => h m (List.mem_cons_of_mem d hm)

/-- **A bystander keeps the first lonely instant exactly when it is clear there.** -/
theorem firstLonely_cons_iff {n : ℕ} {T : List ℕ} {t : ℝ} (d : ℕ) (hT : FirstLonely n T t) :
    FirstLonely n (d :: T) t ↔ (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨ht, hlon, hfirst⟩ := hT
  constructor
  · rintro ⟨-, h, -⟩
    exact h d (List.mem_cons_self ..)
  · intro hd
    refine ⟨ht, ?_, fun s hs hst hl => hfirst s hs hst (lonelyList_of_cons hl)⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hd
    · exact hlon m hm'

/-- **The residue band, both directions.**  At the rational instant `a/q`, the reading `d` clears
`1/n` exactly when `d·a mod q` lies in `[q/n, (n−1)q/n]`. -/
theorem clear_iff_residue {n : ℕ} (hn : 2 ≤ n) (d a q : ℕ) (hq : 0 < q) :
    (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((a : ℝ) / (q : ℝ))) ↔
      q ≤ n * ((d * a) % q) ∧ n * ((d * a) % q) ≤ (n - 1) * q := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set r : ℕ := (d * a) % q with hr
  have hrq : r < q := Nat.mod_lt _ hq
  have hfr : Int.fract ((r : ℝ) / (q : ℝ)) = (r : ℝ) / (q : ℝ) := by
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one hq0]; exact_mod_cast hrq
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [circDist_rat d a q hq, ← hr, circDist, hfr, le_min_iff]
  have e1 : (n : ℝ)⁻¹ ≤ (r : ℝ) / (q : ℝ) ↔ (q : ℝ) ≤ (n : ℝ) * (r : ℝ) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hn0 hq0, one_mul]; constructor <;> intro h <;> linarith
  have e2 : (n : ℝ)⁻¹ ≤ 1 - (r : ℝ) / (q : ℝ) ↔ (n : ℝ) * (r : ℝ) ≤ ((n : ℝ) - 1) * (q : ℝ) := by
    rw [le_sub_iff_add_le, inv_eq_one_div, div_add_div _ _ (ne_of_gt hn0) (ne_of_gt hq0),
      div_le_one (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((n * r : ℕ) : ℝ) ≤ (((n - 1) * q : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, hc]; exact h2
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((n * r : ℕ) : ℝ) ≤ (((n - 1) * q : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_mul, hc] at this; exact this

/-- **The bystander test at `t = u/w`.**  If `u/w` is the first lonely instant of `T`, then
`d :: T` keeps it exactly when `d·u mod w` lies in the band. -/
theorem bystander_iff {n : ℕ} (hn : 2 ≤ n) {T : List ℕ} {u w : ℕ} (hw : 0 < w)
    (hT : FirstLonely n T ((u : ℝ) / (w : ℝ))) (d : ℕ) :
    FirstLonely n (d :: T) ((u : ℝ) / (w : ℝ)) ↔
      w ≤ n * ((d * u) % w) ∧ n * ((d * u) % w) ≤ (n - 1) * w := by
  rw [firstLonely_cons_iff d hT]
  exact clear_iff_residue hn d u w hw

/-- **The clean takeover.**  Let `t` be the first lonely instant of `T`, and let `T` stay lonely
on `[t, tR]`.  If `d` is blocked at `t` (the integer `N` with `N − 1/n < d·t < N + 1/n`) and its
edge `E = (N + 1/n)/d` is at most `tR`, then `E` is the first lonely instant of `d :: T`. -/
theorem takeover {n : ℕ} (hn : 2 ≤ n) {T : List ℕ} {t tR : ℝ} (hT : FirstLonely n T t)
    (hTR : ∀ s : ℝ, t ≤ s → s ≤ tR → LonelyList n T s)
    {d : ℕ} (hd : 0 < d) {N : ℤ}
    (hN1 : (N : ℝ) - (n : ℝ)⁻¹ < (d : ℝ) * t) (hN2 : (d : ℝ) * t < (N : ℝ) + (n : ℝ)⁻¹)
    (hE : ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) ≤ tR) :
    FirstLonely n (d :: T) (((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ)) := by
  obtain ⟨ht, -, hfirst⟩ := hT
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set E : ℝ := ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) with hEdef
  have hdE : (d : ℝ) * E = (N : ℝ) + (n : ℝ)⁻¹ := by rw [hEdef]; field_simp
  have htE : t < E := by
    by_contra h
    push Not at h
    have : (d : ℝ) * E ≤ (d : ℝ) * t := mul_le_mul_of_nonneg_left h hd0.le
    linarith
  refine ⟨lt_trans ht htE, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · -- the reading `d` stands exactly at the edge of the window
      rw [hdE]
      have hinv0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
      have hinv1 : (n : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by norm_num)]
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [add_comm, circDist_add_int, circDist, Int.fract_eq_self.mpr ⟨hinv0.le, by linarith⟩]
      exact le_min le_rfl (by linarith)
    · exact hTR E htE.le hE m hm'
  · intro s hs hsE hl
    by_cases hst : s < t
    · exact hfirst s hs hst (lonelyList_of_cons hl)
    · push Not at hst
      -- `d` is still inside its window at `s`
      have h1 : (N : ℝ) - (n : ℝ)⁻¹ < (d : ℝ) * s := by
        have : (d : ℝ) * t ≤ (d : ℝ) * s := mul_le_mul_of_nonneg_left hst hd0.le
        linarith
      have h2 : (d : ℝ) * s < (N : ℝ) + (n : ℝ)⁻¹ := by
        have : (d : ℝ) * s < (d : ℝ) * E := mul_lt_mul_of_pos_left hsE hd0
        linarith
      have hlt : |(d : ℝ) * s - (N : ℝ)| < (n : ℝ)⁻¹ := by
        rw [abs_lt]; constructor <;> linarith
      have hle := circDist_le_abs_sub_int ((d : ℝ) * s) N
      have hcl := hl d (List.mem_cons_self ..)
      linarith

/-- **The takeover, in its general form.**  Let `t` be the first lonely instant of `T`, let `d` be
blocked at `t` (the integer `N` with `N − 1/n < d·t < N + 1/n`), and let `E = (N + 1/n)/d` be its
edge.  If `T` is lonely at `E`, then `E` is the first lonely instant of `d :: T`.  No condition
that `E` lies in the component of `t` is needed: it is enough that `E` lies in the lonely set of
`T`, in any of its components. -/
theorem takeover_of_lonely_at {n : ℕ} (hn : 2 ≤ n) {T : List ℕ} {t : ℝ} (hT : FirstLonely n T t)
    {d : ℕ} (hd : 0 < d) {N : ℤ}
    (hN1 : (N : ℝ) - (n : ℝ)⁻¹ < (d : ℝ) * t) (hN2 : (d : ℝ) * t < (N : ℝ) + (n : ℝ)⁻¹)
    (hlon : LonelyList n T (((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ))) :
    FirstLonely n (d :: T) (((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ)) := by
  obtain ⟨ht, -, hfirst⟩ := hT
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set E : ℝ := ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) with hEdef
  have hdE : (d : ℝ) * E = (N : ℝ) + (n : ℝ)⁻¹ := by rw [hEdef]; field_simp
  have htE : t < E := by
    by_contra h
    push Not at h
    have : (d : ℝ) * E ≤ (d : ℝ) * t := mul_le_mul_of_nonneg_left h hd0.le
    linarith
  refine ⟨lt_trans ht htE, ?_, ?_⟩
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · rw [hdE]
      have hinv0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
      have hinv1 : (n : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by norm_num)]
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [add_comm, circDist_add_int, circDist, Int.fract_eq_self.mpr ⟨hinv0.le, by linarith⟩]
      exact le_min le_rfl (by linarith)
    · exact hlon m hm'
  · intro s hs hsE hl
    by_cases hst : s < t
    · exact hfirst s hs hst (lonelyList_of_cons hl)
    · push Not at hst
      have h1 : (N : ℝ) - (n : ℝ)⁻¹ < (d : ℝ) * s := by
        have : (d : ℝ) * t ≤ (d : ℝ) * s := mul_le_mul_of_nonneg_left hst hd0.le
        linarith
      have h2 : (d : ℝ) * s < (N : ℝ) + (n : ℝ)⁻¹ := by
        have : (d : ℝ) * s < (d : ℝ) * E := mul_lt_mul_of_pos_left hsE hd0
        linarith
      have hlt : |(d : ℝ) * s - (N : ℝ)| < (n : ℝ)⁻¹ := by
        rw [abs_lt]; constructor <;> linarith
      have hle := circDist_le_abs_sub_int ((d : ℝ) * s) N
      have hcl := hl d (List.mem_cons_self ..)
      linarith

/-- **The converse.**  If `E` is the first lonely instant of `d :: T`, then `T` is lonely at `E`. -/
theorem lonely_at_of_firstLonely_cons {n : ℕ} {T : List ℕ} {d : ℕ} {E : ℝ}
    (h : FirstLonely n (d :: T) E) : LonelyList n T E :=
  lonelyList_of_cons h.2.1

/-- **The lonely set of `d :: T` is that of `T` cut by the arcs of `d`.** -/
theorem lonelyList_cons_iff {n : ℕ} (d : ℕ) (T : List ℕ) (s : ℝ) :
    LonelyList n (d :: T) s ↔ (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * s) ∧ LonelyList n T s := by
  unfold LonelyList
  simp

/-- **Integer disparities: loneliness is 1-periodic in `t`.** -/
theorem lonelyList_add_nat {n : ℕ} (L : List ℕ) (s : ℝ) (k : ℕ) :
    LonelyList n L (s + k) ↔ LonelyList n L s := by
  unfold LonelyList
  have e : ∀ d : ℕ, (d : ℝ) * (s + k) = (d : ℝ) * s + (((d * k : ℕ) : ℤ) : ℝ) := by
    intro d; push_cast; ring
  constructor
  · intro h d hd
    have := h d hd
    rw [e d, circDist_add_int] at this
    exact this
  · intro h d hd
    rw [e d, circDist_add_int]
    exact h d hd

/-- **A lonely instant can be taken in `[0, 1)`** (integer disparities). -/
theorem exists_lonely_fract {n : ℕ} (L : List ℕ) (h : ∃ s : ℝ, LonelyList n L s) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ LonelyList n L s := by
  obtain ⟨s, hs⟩ := h
  refine ⟨Int.fract s, Int.fract_nonneg s, Int.fract_lt_one s, ?_⟩
  have e : s = Int.fract s + (⌊s⌋ : ℤ) := (Int.fract_add_floor s).symm
  unfold LonelyList at hs ⊢
  intro d hd
  have := hs d hd
  have e2 : (d : ℝ) * s = (d : ℝ) * Int.fract s + (((d : ℤ) * ⌊s⌋ : ℤ) : ℝ) := by
    conv_lhs => rw [e]
    push_cast; ring
  rw [e2, circDist_add_int] at this
  exact this

/-- **A long enough interval holds a clear point.**  The blocked windows of the disparity `d` at
threshold `1/n` are disjoint open intervals of length `2/(n d)`; a closed interval of length at
least `2/(n d)` therefore contains an instant at distance at least `1/n` from the integers for `d`.
(The record's `lonely_eight_of_fast` argument, stated for a single added disparity.) -/
theorem exists_clear_in_interval {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) {a b : ℝ}
    (hab : a + 2 / ((n : ℝ) * (d : ℝ)) ≤ b) :
    ∃ t : ℝ, a ≤ t ∧ t ≤ b ∧ (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases ha : (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * a)
  · have hnd : 0 ≤ 2 / ((n : ℝ) * (d : ℝ)) := by positivity
    exact ⟨a, le_rfl, by linarith, ha⟩
  · push Not at ha
    obtain ⟨N, hN⟩ := circDist_eq_abs_sub_some_int ((d : ℝ) * a)
    rw [hN] at ha
    have hlt := abs_lt.mp ha
    set E : ℝ := ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) with hEdef
    have hdE : (d : ℝ) * E = (N : ℝ) + (n : ℝ)⁻¹ := by rw [hEdef]; field_simp
    have hinv0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
    have hinv1 : (n : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by norm_num)]
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have haE : a ≤ E := by
      by_contra h
      push Not at h
      have : (d : ℝ) * E < (d : ℝ) * a := mul_lt_mul_of_pos_left h hd0
      linarith [hlt.1, hlt.2]
    have hEb : E ≤ a + 2 / ((n : ℝ) * (d : ℝ)) := by
      have h2 : (d : ℝ) * (2 / ((n : ℝ) * (d : ℝ))) = 2 * (n : ℝ)⁻¹ := by
        field_simp
      have h3 : (d : ℝ) * E ≤ (d : ℝ) * (a + 2 / ((n : ℝ) * (d : ℝ))) := by
        rw [hdE, mul_add, h2]
        linarith [hlt.1, hlt.2]
      exact le_of_mul_le_mul_left h3 hd0
    refine ⟨E, haE, le_trans hEb hab, ?_⟩
    rw [hdE, add_comm, circDist_add_int, circDist, Int.fract_eq_self.mpr ⟨hinv0.le, by linarith⟩]
    exact le_min le_rfl (by linarith)

/-- **The criterion for a clear point in a closed interval.**  `d` has an instant at distance at
least `1/n` from the integers in `[l, r]` exactly when it is clear at `l`, or `l` lies in the
window around some integer `N` (`|d·l − N| < 1/n`) and the window's exit `(N + 1/n)/d` is at most `r`. -/
theorem clear_in_interval_iff {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) {l r : ℝ} (hlr : l ≤ r) :
    (∃ t : ℝ, l ≤ t ∧ t ≤ r ∧ (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ↔
      (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * l) ∨
        ∃ N : ℤ, |(d : ℝ) * l - N| < (n : ℝ)⁻¹ ∧ ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) ≤ r := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hinv0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hinv1 : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by norm_num)]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  constructor
  · rintro ⟨t, hlt, htr, hcl⟩
    by_cases hl : (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * l)
    · exact Or.inl hl
    · right
      push Not at hl
      obtain ⟨N, hN⟩ := circDist_eq_abs_sub_some_int ((d : ℝ) * l)
      rw [hN] at hl
      refine ⟨N, hl, ?_⟩
      by_contra hE
      push Not at hE
      have hab := abs_lt.mp hl
      have h1 : (N : ℝ) - (n : ℝ)⁻¹ < (d : ℝ) * t := by
        have : (d : ℝ) * l ≤ (d : ℝ) * t := mul_le_mul_of_nonneg_left hlt hd0.le
        linarith [hab.1]
      have h2 : (d : ℝ) * t < (N : ℝ) + (n : ℝ)⁻¹ := by
        have : (d : ℝ) * t < (d : ℝ) * (((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ)) :=
          mul_lt_mul_of_pos_left (lt_of_le_of_lt htr hE) hd0
        have e : (d : ℝ) * (((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ)) = (N : ℝ) + (n : ℝ)⁻¹ := by
          field_simp
        linarith
      have hlt' : |(d : ℝ) * t - (N : ℝ)| < (n : ℝ)⁻¹ := by
        rw [abs_lt]; constructor <;> linarith
      have hle := circDist_le_abs_sub_int ((d : ℝ) * t) N
      linarith
  · rintro (hl | ⟨N, hN, hE⟩)
    · exact ⟨l, le_rfl, hlr, hl⟩
    · have hab := abs_lt.mp hN
      set E : ℝ := ((N : ℝ) + (n : ℝ)⁻¹) / (d : ℝ) with hEdef
      have hdE : (d : ℝ) * E = (N : ℝ) + (n : ℝ)⁻¹ := by rw [hEdef]; field_simp
      have hlE : l ≤ E := by
        by_contra h
        push Not at h
        have : (d : ℝ) * E < (d : ℝ) * l := mul_lt_mul_of_pos_left h hd0
        linarith [hab.1, hab.2]
      refine ⟨E, hlE, hE, ?_⟩
      rw [hdE, add_comm, circDist_add_int, circDist, Int.fract_eq_self.mpr ⟨hinv0.le, by linarith⟩]
      exact le_min le_rfl (by linarith)

/-- **Threshold `1/7` carries threshold `1/8`.**  A lonely instant at `1/7` is lonely at `1/8`.
This is the margin used when an arrangement is lonely at `1/7`: the cascade at `1/7` is the same
cascade with a larger window, and sets with no lonely instant at `1/7` are the only ones left. -/
theorem lonelyList_seven_to_eight (L : List ℕ) (s : ℝ) (h : LonelyList 7 L s) : LonelyList 8 L s := by
  intro d hd
  have := h d hd
  have h78 : ((8 : ℕ) : ℝ)⁻¹ ≤ ((7 : ℕ) : ℝ)⁻¹ := by norm_num
  exact le_trans h78 this

/-- **At `t = 1/q`, `2 ≤ q ≤ 7`, a disparity is clear at `1/7` iff `q` does not divide it.** -/
theorem clear_seven_at_inv {q : ℕ} (hq2 : 2 ≤ q) (hq7 : q ≤ 7) (d : ℕ) :
    ((7 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (((1 : ℕ) : ℝ) / (q : ℝ))) ↔ ¬ q ∣ d := by
  have hq : 0 < q := by omega
  rw [clear_iff_residue (n := 7) (by norm_num) d 1 q hq]
  have hmod : d * 1 % q = d % q := by simp
  rw [hmod]
  constructor
  · rintro ⟨h1, h2⟩ hdv
    have : d % q = 0 := Nat.mod_eq_zero_of_dvd hdv
    rw [this] at h1
    omega
  · intro hnd
    have hne : d % q ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hlt : d % q < q := Nat.mod_lt _ hq
    constructor <;> omega

/-- **No lonely instant at `1/7` forces a multiple of every `q ≤ 7`.** -/
theorem exists_dvd_of_no_lonely_seven (L : List ℕ) (h : ∀ s : ℝ, ¬ LonelyList 7 L s)
    {q : ℕ} (hq2 : 2 ≤ q) (hq7 : q ≤ 7) : ∃ d ∈ L, q ∣ d := by
  have hn := h (((1 : ℕ) : ℝ) / (q : ℝ))
  unfold LonelyList at hn
  push Not at hn
  obtain ⟨d, hd, hlt⟩ := hn
  refine ⟨d, hd, ?_⟩
  by_contra hnd
  exact absurd ((clear_seven_at_inv hq2 hq7 d).mpr hnd) (not_le.mpr hlt)

/-- **At `t = a/8` with `a` odd, clear at `1/7` iff the residue `d·a mod 8` is in `[2, 6]`.** -/
theorem clear_seven_at_eighth (a d : ℕ) :
    ((7 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((a : ℝ) / ((8 : ℕ) : ℝ))) ↔ 2 ≤ d * a % 8 ∧ d * a % 8 ≤ 6 := by
  rw [clear_iff_residue (n := 7) (by norm_num) d a 8 (by norm_num)]
  omega

/-- **No lonely instant at `1/7` forces a disparity `≡ 0, ±1` and one `≡ 0, ±3 (mod 8)`.** -/
theorem exists_residue_of_no_lonely_seven (L : List ℕ) (h : ∀ s : ℝ, ¬ LonelyList 7 L s) :
    (∃ d ∈ L, d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 7) ∧ (∃ d ∈ L, d % 8 = 0 ∨ d % 8 = 3 ∨ d % 8 = 5) := by
  have key : ∀ a : ℕ, ∃ d ∈ L, ¬ (2 ≤ d * a % 8 ∧ d * a % 8 ≤ 6) := by
    intro a
    have hn := h ((a : ℝ) / ((8 : ℕ) : ℝ))
    unfold LonelyList at hn
    push Not at hn
    obtain ⟨d, hd, hlt⟩ := hn
    refine ⟨d, hd, fun hc => ?_⟩
    exact absurd ((clear_seven_at_eighth a d).mpr hc) (not_le.mpr hlt)
  obtain ⟨d1, hd1, h1⟩ := key 1
  obtain ⟨d3, hd3, h3⟩ := key 3
  refine ⟨⟨d1, hd1, by omega⟩, ⟨d3, hd3, ?_⟩⟩
  have hm : d3 * 3 % 8 = (d3 % 8) * 3 % 8 := by rw [Nat.mul_mod]
  have hr : d3 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm] at h3
  generalize d3 % 8 = r at h3 hr ⊢
  interval_cases r <;> simp_all

/-- **No lonely instant at `1/7` bounds every component of the six others.**  If `S = d :: T` has no
lonely instant at `1/7`, then no closed interval of length at least `2/(7 d)` inside the lonely set
of `T` at `1/7` exists: every such interval would hold a point clear for `d`. -/
theorem no_long_interval_of_no_lonely_seven {T : List ℕ} {d : ℕ} (hd : 0 < d)
    (h : ∀ s : ℝ, ¬ LonelyList 7 (d :: T) s) {a b : ℝ}
    (hab : a + 2 / (((7 : ℕ) : ℝ) * (d : ℝ)) ≤ b)
    (hT : ∀ s : ℝ, a ≤ s → s ≤ b → LonelyList 7 T s) : False := by
  obtain ⟨t, hat, htb, hcl⟩ := exists_clear_in_interval (n := 7) (by norm_num) hd hab
  exact h t ((lonelyList_cons_iff d T t).mpr ⟨hcl, hT t hat htb⟩)

/-- **The band `[1/n, 1 − 1/n]` is clear.**  A real number between `1/n` and `1 − 1/n` is at distance
at least `1/n` from the integers (`n ≥ 2`). -/
theorem circDist_ge_of_band {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (h1 : (n : ℝ)⁻¹ ≤ x) (h2 : x ≤ 1 - (n : ℝ)⁻¹) :
    (n : ℝ)⁻¹ ≤ circDist x := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hinv0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hinv1 : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hn0 (by norm_num)]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [circDist, hfr]
  exact le_min h1 (by linarith)

/-- **The first clear arc of a reading `m`.**  For `t` in `[1/(n m), (1 − 1/n)/m]` the reading `m` is at
distance at least `1/n` from the integers.  In the cascade's coordinate `u = n·m·t` this is `u ∈ [1, n − 1]`. -/
theorem clear_on_first_arc {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {t : ℝ}
    (h1 : 1 / ((n : ℝ) * (m : ℝ)) ≤ t) (h2 : t ≤ (1 - (n : ℝ)⁻¹) / (m : ℝ)) :
    (n : ℝ)⁻¹ ≤ circDist ((m : ℝ) * t) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  apply circDist_ge_of_band hn
  · have : (m : ℝ) * (1 / ((n : ℝ) * (m : ℝ))) = (n : ℝ)⁻¹ := by field_simp
    calc (n : ℝ)⁻¹ = (m : ℝ) * (1 / ((n : ℝ) * (m : ℝ))) := this.symm
      _ ≤ (m : ℝ) * t := mul_le_mul_of_nonneg_left h1 hm0.le
  · have : (m : ℝ) * ((1 - (n : ℝ)⁻¹) / (m : ℝ)) = 1 - (n : ℝ)⁻¹ := by field_simp
    calc (m : ℝ) * t ≤ (m : ℝ) * ((1 - (n : ℝ)⁻¹) / (m : ℝ)) := mul_le_mul_of_nonneg_left h2 hm0.le
      _ = 1 - (n : ℝ)⁻¹ := this

/-- **A cluster instant inside the first clear arc of `m` is a lonely instant of `m :: T`.**  This is
the form the cluster case needs: the six readings `T` are lonely at `t`, and `t` lies in the first
clear arc `u ∈ [1, n − 1]` of the smallest reading `m`. -/
theorem lonely_cons_of_arc {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {T : List ℕ} {t : ℝ}
    (hT : LonelyList n T t) (h1 : 1 / ((n : ℝ) * (m : ℝ)) ≤ t) (h2 : t ≤ (1 - (n : ℝ)⁻¹) / (m : ℝ)) :
    LonelyList n (m :: T) t :=
  (lonelyList_cons_iff m T t).mpr ⟨clear_on_first_arc hn hm h1 h2, hT⟩

end LRC.Bystander
