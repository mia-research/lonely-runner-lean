import LonelyRunner.LRC.Spec.CoreWindowInsertionN

/-!
# Core windows force named zones in the actual run

E366, in ordinary time t (the experimental R is 8t).
Any finite zone run that passes a closed core-clear interval must use the
inserted reading's unique zone containing that interval. Singleton intervals
are allowed. No termination, exhaustive template list, or gate-at-9 claim is
assumed. The result applies to any core size, not only six readings.
-/

namespace LRC.CoreWindowRun

open MomentIterationN ConstructionN

/-- Strengthen Run.covers: the covering zone occurs in the supplied path. -/
theorem used_zone_covers {S : Finset ℝ} :
    ∀ (path : List (ℝ × ℤ)) (b T : ℝ), Run 8 S b path T →
      ∀ t, b ≤ t → t < T →
        ∃ d K, (d, K) ∈ path ∧ d ∈ S ∧ zoneLo 8 d K < t ∧ t < zoneHi 8 d K := by
  intro path
  induction path with
  | nil =>
    intro b T hr t hl hu
    change T = b at hr
    subst T
    linarith
  | cons p path ih =>
    obtain ⟨d, K⟩ := p
    intro b T hr t hl hu
    obtain ⟨hd, hlo, hhi, hrest⟩ := hr
    by_cases ht : t < zoneHi 8 d K
    · exact ⟨d, K, by simp, hd, hlo.trans_le hl, ht⟩
    · obtain ⟨e, J, hm, he, hL, hU⟩ := ih _ _ hrest t (le_of_not_gt ht) hu
      exact ⟨e, J, List.mem_cons_of_mem _ hm, he, hL, hU⟩

theorem zone_label_unique {d t : ℝ} (hd : 0 < d) {K J : ℤ}
    (hKl : zoneLo 8 d K < t) (hKu : t < zoneHi 8 d K)
    (hJl : zoneLo 8 d J < t) (hJu : t < zoneHi 8 d J) : K = J := by
  unfold zoneLo zoneHi at *
  rw [div_lt_iff₀ hd] at hKl hJl
  rw [lt_div_iff₀ hd] at hKu hJu
  norm_num at hKl hJl hKu hJu
  have h1 : (K : ℝ) < J + 1 := by linarith
  have h2 : (J : ℝ) < K + 1 := by linarith
  have h1i : K < J + 1 := by exact_mod_cast h1
  have h2i : J < K + 1 := by exact_mod_cast h2
  omega

/-- At a core-clear point passed by the run, a used setter zone belongs
to the inserted reading. This is path membership, not just obstruction. -/
theorem inserted_zone_used {S : Finset ℝ} {V b T t : ℝ}
    (_hV : 0 < V) (hpos : ∀ d ∈ S, 0 < d)
    {path : List (ℝ × ℤ)} (hr : Run 8 (insert V S) b path T)
    (hl : b ≤ t) (hu : t < T)
    (hcore : ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d * t)) :
    ∃ K : ℤ, (V, K) ∈ path ∧ zoneLo 8 V K < t ∧ t < zoneHi 8 V K := by
  obtain ⟨d, K, hm, hd, hL, hU⟩ := used_zone_covers path b T hr t hl hu
  rcases Finset.mem_insert.mp hd with he | hs
  · subst d
    exact ⟨K, hm, hL, hU⟩
  · have hw := (inWay_iff_zone (n := 8) (hpos d hs)).mpr ⟨K, hL, hU⟩
    exact ((not_lt_of_ge (hcore d hs)) hw).elim

/-- Every passed closed core window is swallowed by exactly one inserted
zone, and that zone is an actual member of the run. No positive width needed. -/
theorem window_forces_used_zone {S : Finset ℝ} {V b T L U : ℝ}
    (hV : 0 < V) (hpos : ∀ d ∈ S, 0 < d)
    {path : List (ℝ × ℤ)} (hr : Run 8 (insert V S) b path T)
    (hbL : b ≤ L) (hLU : L ≤ U) (hUT : U < T)
    (hcore : ∀ t, L ≤ t → t ≤ U → ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d * t)) :
    ∃ K : ℤ, (V, K) ∈ path ∧ zoneLo 8 V K < L ∧ U < zoneHi 8 V K ∧
      ∀ J : ℤ, zoneLo 8 V J < L → L < zoneHi 8 V J → J = K := by
  have hblocked : ∀ t, L ≤ t → t ≤ U → circDist (V * t) < (8 : ℝ)⁻¹ := by
    intro t htL htU
    obtain ⟨K, _, hl, hu⟩ := inserted_zone_used hV hpos hr (hbL.trans htL)
      (htU.trans_lt hUT) (hcore t htL htU)
    exact (inWay_iff_zone (n := 8) hV).mpr ⟨K, hl, hu⟩
  obtain ⟨K, hKl, hKu⟩ := (CoreWindowInsertion.swallowed_iff hV hLU).mp hblocked
  have hL : zoneLo 8 V K < L := by
    unfold zoneLo
    apply (div_lt_iff₀ hV).mpr
    norm_num
    linarith
  have hU : U < zoneHi 8 V K := by
    unfold zoneHi
    apply (lt_div_iff₀ hV).mpr
    norm_num
    linarith
  obtain ⟨J, hm, hJl, hJu⟩ := inserted_zone_used hV hpos hr hbL
    (hLU.trans_lt hUT) (hcore L le_rfl hLU)
  have heq := zone_label_unique hV hJl hJu hL (hLU.trans_lt hU)
  subst J
  exact ⟨K, hm, hL, hU, fun J hjl hju =>
    zone_label_unique hV hjl hju hL (hLU.trans_lt hU)⟩

/-- The actual max-opening iteration supplies the zone path automatically. -/
theorem window_forces_iterate_zone {S : Finset ℝ} {V b L U : ℝ}
    (hV : 0 < V) (hpos : ∀ d ∈ S, 0 < d) (N : ℕ)
    (hbL : b ≤ L) (hLU : L ≤ U)
    (hUT : U < (move 8 (insert V S))^[N] b)
    (hcore : ∀ t, L ≤ t → t ≤ U → ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist (d * t)) :
    ∃ path : List (ℝ × ℤ), Run 8 (insert V S) b path ((move 8 (insert V S))^[N] b) ∧
      ∃ K : ℤ, (V, K) ∈ path ∧ zoneLo 8 V K < L ∧ U < zoneHi 8 V K := by
  have hp : ∀ d ∈ insert V S, 0 < d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hV
    · exact hpos d hd
  obtain ⟨path, hr⟩ := run_of_iterate (n := 8) hp b N
  obtain ⟨K, hm, hl, hu, _⟩ := window_forces_used_zone hV hpos hr hbL hLU hUT hcore
  exact ⟨path, hr, K, hm, hl, hu⟩

/-- A blocked core point between two core-clear points brings a whole core
zone between them. Endpoint equality is allowed. -/
theorem core_gap_contains_zone {d a s b : ℝ} (hd : 0 < d)
    (has : a < s) (hsb : s < b)
    (ha : (8 : ℝ)⁻¹ ≤ circDist (d * a))
    (hb : (8 : ℝ)⁻¹ ≤ circDist (d * b)) (hw : inWay 8 d s) :
    ∃ J : ℤ, a ≤ zoneLo 8 d J ∧ zoneHi 8 d J ≤ b := by
  obtain ⟨J, hl, hu⟩ := (inWay_iff_zone (n := 8) hd).mp hw
  refine ⟨J, ?_, ?_⟩
  · by_contra h
    have hwa := (inWay_iff_zone (n := 8) hd).mpr
      ⟨J, lt_of_not_ge h, has.trans hu⟩
    exact (not_lt_of_ge ha) hwa
  · by_contra h
    have hwb := (inWay_iff_zone (n := 8) hd).mpr
      ⟨J, hl.trans hsb, lt_of_not_ge h⟩
    exact (not_lt_of_ge hb) hwb

/-- Different core components require different inserted zones when V is
at least as fast as the core. The separating blocked point replaces an
assumption about a precomputed component list. This upgrades E366's
observed distinctness to a symbolic implication. -/
theorem different_components_different_labels {V d a s b : ℝ}
    (hd : 0 < d) (hdV : d ≤ V) (has : a < s) (hsb : s < b)
    (ha : (8 : ℝ)⁻¹ ≤ circDist (d * a))
    (hb : (8 : ℝ)⁻¹ ≤ circDist (d * b)) (hw : inWay 8 d s)
    {K H : ℤ} (hKa : zoneLo 8 V K < a) (hHb : b < zoneHi 8 V H) : K ≠ H := by
  intro heq
  subst H
  have hV : 0 < V := hd.trans_le hdV
  obtain ⟨J, hL, hU⟩ := core_gap_contains_zone hd has hsb ha hb hw
  simp only [zoneLo, zoneHi] at hL hU hKa hHb
  rw [div_le_iff₀ hd] at hU
  rw [le_div_iff₀ hd] at hL
  rw [div_lt_iff₀ hV] at hKa
  rw [lt_div_iff₀ hV] at hHb
  norm_num at hL hU hKa hHb
  have hg : 0 ≤ b - a := sub_nonneg.mpr (has.trans hsb).le
  have hm := mul_le_mul_of_nonneg_right hdV hg
  nlinarith

/-- Distinct inserted zones meeting ordered windows have increasing lap labels. -/
theorem labels_ordered {V a b : ℝ} (hV : 0 < V) (hab : a ≤ b)
    {K H : ℤ} (hKa : zoneLo 8 V K < a) (hHb : b < zoneHi 8 V H)
    (hne : K ≠ H) : K < H := by
  simp only [zoneLo, zoneHi] at hKa hHb
  rw [div_lt_iff₀ hV] at hKa
  rw [lt_div_iff₀ hV] at hHb
  norm_num at hKa hHb
  have hm := mul_le_mul_of_nonneg_right hab hV.le
  have hh : (K : ℝ) < H + 1 := by linarith
  have hhi : K < H + 1 := by exact_mod_cast hh
  omega

end LRC.CoreWindowRun
