import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# Order seven: the split fold and the stretch recursion (band `[1/7, 6/7]`)

A **window** of a set of speeds is a time interval on which every speed reads inside `[1/7, 6/7]` (mod 1).
`GapProp F G w`: every time interval of length `G` contains a window of length `w` for `F`.

* `split_fold`: a window of `S` of length `≥ G` and `GapProp F G w` give a window of length `w` for `S ∪ F`.
* `gap_empty`: `GapProp ∅ w w`.
* `gap_stretch`: if `GapProp F G w` and `G ≤ 5/(7u)`, then `GapProp (insert u F) (2/(7u) + 2G) w` — a full band
  stretch of `u` (length `5/(7u)`) lies in every interval of length `2/(7u) + 2G` together with room for `G`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Split

open LRC.MirrorCentre

/-- Every speed of `S` reads inside the band on `I`. -/
def InBandOn (S : Finset ℕ) (I : Set ℝ) : Prop :=
  ∀ s ∈ I, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * s)

/-- Every interval of length `G` contains a window of length `w` for `F`. -/
def GapProp (F : Finset ℕ) (G w : ℝ) : Prop :=
  ∀ a : ℝ, ∃ L : ℝ, a ≤ L ∧ L + w ≤ a + G ∧ InBandOn F (Set.Icc L (L + w))

theorem inBandOn_mono {S : Finset ℕ} {I J : Set ℝ} (h : InBandOn S J) (hIJ : I ⊆ J) : InBandOn S I :=
  fun s hs d hd => h s (hIJ hs) d hd

theorem inBandOn_union {S F : Finset ℕ} {I : Set ℝ} (hS : InBandOn S I) (hF : InBandOn F I) :
    InBandOn (S ∪ F) I := by
  intro s hs d hd
  rcases Finset.mem_union.mp hd with h | h
  · exact hS s hs d h
  · exact hF s hs d h

/-- **Split fold.** -/
theorem split_fold {S F : Finset ℕ} {a W G w : ℝ} (hS : InBandOn S (Set.Icc a (a + W))) (hGW : G ≤ W)
    (hF : GapProp F G w) : ∃ L : ℝ, InBandOn (S ∪ F) (Set.Icc L (L + w)) := by
  obtain ⟨L, haL, hLw, hFL⟩ := hF a
  refine ⟨L, inBandOn_union (inBandOn_mono hS ?_) hFL⟩
  intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem gap_empty (w : ℝ) : GapProp ∅ w w :=
  fun a => ⟨a, le_rfl, le_rfl, fun _ _ d hd => absurd hd (Finset.notMem_empty d)⟩

/-- One speed `u` in band on its `m`-th stretch. -/
theorem inBand_stretch {u : ℕ} (hu : 0 < u) (m : ℤ) {L R : ℝ}
    (hL : ((m : ℝ) + 1 / 7) / u ≤ L) (hR : R ≤ ((m : ℝ) + 6 / 7) / u) :
    InBandOn {u} (Set.Icc L R) := by
  intro s hs d hd
  rw [Finset.mem_singleton] at hd; subst hd
  have hu' : (0 : ℝ) < d := by exact_mod_cast hu
  have h1 : (m : ℝ) + 1 / 7 ≤ d * s := by
    have := (div_le_iff₀ hu').mp (le_trans hL hs.1); linarith
  have h2 : (d : ℝ) * s ≤ m + 6 / 7 := by
    have := (le_div_iff₀ hu').mp (le_trans hs.2 hR); linarith
  exact circDist_ge_of_window h1 (by linarith) (by norm_num)

/-- **Stretch recursion.** -/
theorem gap_stretch {u : ℕ} (hu : 0 < u) {F : Finset ℕ} {G w : ℝ} (hw : 0 ≤ w) (hF : GapProp F G w)
    (hG : G ≤ 5 / (7 * u)) : GapProp (insert u F) (2 / (7 * u) + 2 * G) w := by
  intro a
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hGw : w ≤ G := by obtain ⟨L, h1, h2, -⟩ := hF a; linarith
  have h7u : (0 : ℝ) < 2 / (7 * u) := by positivity
  set m : ℤ := ⌊(u : ℝ) * a - 1 / 7⌋ with hm
  have hm1 : (m : ℝ) ≤ u * a - 1 / 7 := Int.floor_le _
  have hm2 : (u : ℝ) * a - 1 / 7 < m + 1 := Int.lt_floor_add_one _
  have hs0 : ((m : ℝ) + 1 / 7) / u ≤ a := by rw [div_le_iff₀ hu']; linarith
  have hs1 : a < (((m + 1 : ℤ) : ℝ) + 1 / 7) / u := by rw [lt_div_iff₀ hu']; push_cast; linarith
  have hstep : (((m + 1 : ℤ) : ℝ) + 1 / 7) / u = ((m : ℝ) + 6 / 7) / u + 2 / (7 * u) := by
    push_cast; field_simp; ring
  have hlen : (((m + 1 : ℤ) : ℝ) + 6 / 7) / u = (((m + 1 : ℤ) : ℝ) + 1 / 7) / u + 5 / (7 * u) := by
    push_cast; field_simp; ring
  by_cases hA : a + G ≤ ((m : ℝ) + 6 / 7) / u
  · obtain ⟨L, haL, hLw, hFL⟩ := hF a
    refine ⟨L, haL, by linarith, ?_⟩
    have hu1 : InBandOn {u} (Set.Icc L (L + w)) :=
      inBand_stretch hu m (by linarith) (by linarith)
    rw [Finset.insert_eq]; exact inBandOn_union hu1 hFL
  · rw [not_le] at hA
    set s1 : ℝ := (((m + 1 : ℤ) : ℝ) + 1 / 7) / u with hs1def
    obtain ⟨L, hsL, hLw, hFL⟩ := hF s1
    refine ⟨L, by linarith, by linarith, ?_⟩
    have hu1 : InBandOn {u} (Set.Icc L (L + w)) :=
      inBand_stretch hu (m + 1) (by rw [← hs1def]; exact hsL) (by rw [hlen]; linarith)
    rw [Finset.insert_eq]; exact inBandOn_union hu1 hFL


/-! ### The cluster window (intermediate value with a margin) -/

/-- **IVT window.**  `envL` continuous and antitone, `envU` falls at slope at most `c`; if the envelope gap is at
least `(b + c) w` on `[α, α + 1/b]`, some `t₀` there and integer `N` keep `b s − N` between the envelopes on all of
`[t₀, t₀ + w]`. -/
theorem ivt_window {b c w α : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (_hw : 0 ≤ w) {envL envU : ℝ → ℝ}
    (hLc : Continuous envL) (hLa : Antitone envL)
    (hUs : ∀ t s, t ≤ s → envU t - c * (s - t) ≤ envU s)
    (hgap : ∀ t, α ≤ t → t ≤ α + 1 / b → (b + c) * w ≤ envU t - envL t) :
    ∃ t₀ : ℝ, α ≤ t₀ ∧ t₀ ≤ α + 1 / b ∧ ∃ N : ℤ, ∀ s, t₀ ≤ s → s ≤ t₀ + w →
      envL s ≤ b * s - N ∧ b * s - N ≤ envU s := by
  set f : ℝ → ℝ := fun t => b * t - envL t with hf
  have hfc : Continuous f := (continuous_const.mul continuous_id).sub hLc
  have hb1 : 0 < 1 / b := by positivity
  have hle : α ≤ α + 1 / b := by linarith
  have hrise : f α + 1 ≤ f (α + 1 / b) := by
    have := hLa hle
    simp only [hf]
    have : b * (α + 1 / b) = b * α + 1 := by field_simp
    linarith
  set N : ℤ := ⌈f α⌉ with hN
  have hN1 : f α ≤ N := Int.le_ceil _
  have hN2 : (N : ℝ) ≤ f (α + 1 / b) := by have := Int.ceil_lt_add_one (f α); linarith
  obtain ⟨t₀, ⟨h0l, h0r⟩, hft⟩ := intermediate_value_Icc hle hfc.continuousOn ⟨hN1, hN2⟩
  refine ⟨t₀, h0l, h0r, N, fun s hs1 hs2 => ⟨?_, ?_⟩⟩
  · have := hLa hs1
    simp only [hf] at hft
    nlinarith
  · have hU := hUs t₀ s hs1
    have hg := hgap t₀ h0l h0r
    simp only [hf] at hft
    have h1 : b * s - N = envL t₀ + b * (s - t₀) := by linarith
    have h2 : b * (s - t₀) ≤ b * w := by nlinarith
    have h3 : c * (s - t₀) ≤ c * w := by nlinarith
    nlinarith

/-- **Cluster window.**  Speeds `d = b + e d` of a nonempty `F` (`0 ≤ e d ≤ c`), laps `m d`.  If on `[α, α + 1/b]`
the envelopes `max (m d + 1/7 − e d t)` and `min (m d + 6/7 − e d t)` are at least `(b + c) w` apart, `F` has a
window of length `w` starting in `[α, α + 1/b]`. -/
theorem cluster_window {F : Finset ℕ} (hne : F.Nonempty) {b c w α : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hw : 0 ≤ w)
    (e : ℕ → ℝ) (m : ℕ → ℤ) (he : ∀ d ∈ F, (d : ℝ) = b + e d) (he0 : ∀ d ∈ F, 0 ≤ e d)
    (hec : ∀ d ∈ F, e d ≤ c)
    (hgap : ∀ t, α ≤ t → t ≤ α + 1 / b →
      (b + c) * w ≤ F.inf' hne (fun d => (m d : ℝ) + 6 / 7 - e d * t)
        - F.sup' hne (fun d => (m d : ℝ) + 1 / 7 - e d * t)) :
    ∃ t₀ : ℝ, α ≤ t₀ ∧ t₀ ≤ α + 1 / b ∧ InBandOn F (Set.Icc t₀ (t₀ + w)) := by
  set envL : ℝ → ℝ := fun t => F.sup' hne (fun d => (m d : ℝ) + 1 / 7 - e d * t) with hL
  set envU : ℝ → ℝ := fun t => F.inf' hne (fun d => (m d : ℝ) + 6 / 7 - e d * t) with hU
  have hLc : Continuous envL := by
    rw [hL]
    exact Continuous.finset_sup'_apply hne (fun d _ => continuous_const.sub (continuous_const.mul continuous_id))
  have hLa : Antitone envL := by
    intro t s hts
    simp only [hL]
    apply Finset.sup'_le
    intro d hd
    refine le_trans ?_ (Finset.le_sup' (fun d => (m d : ℝ) + 1 / 7 - e d * t) hd)
    have := he0 d hd
    nlinarith
  have hUs : ∀ t s, t ≤ s → envU t - c * (s - t) ≤ envU s := by
    intro t s hts
    simp only [hU]
    apply Finset.le_inf'
    intro d hd
    have h1 := Finset.inf'_le (fun d => (m d : ℝ) + 6 / 7 - e d * t) hd
    have h2 := hec d hd
    have h3 : e d * (s - t) ≤ c * (s - t) := by nlinarith
    simp only at h1
    nlinarith
  obtain ⟨t₀, h0l, h0r, N, hN⟩ := ivt_window hb hc hw hLc hLa hUs hgap
  refine ⟨t₀, h0l, h0r, fun s hs d hd => ?_⟩
  obtain ⟨hlo, hhi⟩ := hN s hs.1 hs.2
  have hlo' := le_trans (Finset.le_sup' (fun d => (m d : ℝ) + 1 / 7 - e d * s) hd) hlo
  have hhi' := le_trans hhi (Finset.inf'_le (fun d => (m d : ℝ) + 6 / 7 - e d * s) hd)
  simp only at hlo' hhi'
  have hds : (d : ℝ) * s = b * s + e d * s := by rw [he d hd]; ring
  apply circDist_ge_of_window (m := N + m d) _ _ (by norm_num : (0 : ℝ) < 1 / 7)
  · push_cast; linarith
  · push_cast; linarith

end LRC.O7Split
