import LonelyRunner.LRC.Spec.ParityDescentN

set_option linter.style.longLine false

/-!
# Silenced readings: the quarter and eighth levels, and the mixed instant (order eight)

2026-10-05 (running log E402).  Continues `ParityDescentN`.  At the shifts `t + j/2^a` the readings
divisible by `2^a` keep their positions; a reading with exactly `a − 1` factors of `2` sits at two
positions half a lap apart, and blocks no shift when its double is at least `1/4` from the integers
(`quarter_silent`, and `ParityDescent.silent_of_quarter` at the eighth level).  So a case reduces to
a **mixed instant**: an `s` at which the still readings (divided by `2^a`) are clear at `1/8`
and the silenced ones (divided by `2^(a−1)`, odd) are clear at `1/4`.

* `exists_mixed_le_three`: at most three numbers in all, by order four directly.
* `exists_mixed_three_one`: three at `1/8` and one odd at `1/4`, by order four and a half step.
* `lonely_eight_of_quarter_silent`: at most three odd readings and a mixed instant for the multiples
  of `4` and the readings `≡ 2 (mod 4)`.
* `lonely_eight_of_eighth_silent`: the parity split for the non-multiples other than the readings
  `≡ 4 (mod 8)`, and a mixed instant for the multiples of `8` and those readings.

Everything here is proved; no `sorry`, no `native_decide`.
-/


namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-- **At most three numbers in all**: order four clears them at `1/4`, hence the first group at `1/8`. -/
theorem exists_mixed_le_three (A B : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b)
    (hcard : A.card + B.card ≤ 3) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * τ)) ∧
      ∀ b ∈ B, (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * τ) := by
  classical
  set D : Finset ℝ := (A ∪ B).image (fun n : ℕ => (n : ℝ)) with hD
  have hDpos : ∀ x ∈ D, 0 < x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hn with h | h
    · exact_mod_cast hA n h
    · exact_mod_cast hB n h
  have hDcard : D.card ≤ 4 - 1 := by
    have h1 : D.card ≤ (A ∪ B).card := Finset.card_image_le
    have h2 := Finset.card_union_le A B
    omega
  obtain ⟨τ, hτ, hl⟩ := LRC.SpecN.existenceAtN_four D hDpos hDcard
  refine ⟨τ, hτ, fun a ha => ?_, fun b hb => ?_⟩
  · have := hl (a : ℝ) (Finset.mem_image.mpr ⟨a, Finset.mem_union_left _ ha, rfl⟩)
    exact le_trans (by norm_num) this
  · have := hl (b : ℝ) (Finset.mem_image.mpr ⟨b, Finset.mem_union_right _ hb, rfl⟩)
    simpa using this

/-- **Three at `1/8` and one odd at `1/4`.**  Order four clears `c/2` (`c` even) and `c` (`c` odd) at
`1/4` at some `σ`; one of `σ/2`, `σ/2 + 1/2` clears every `c` at `1/8` (an even `c` moves by whole laps,
an odd one has `‖2y‖ ≥ 1/4` at `y = cσ/2`) and puts `u` at least `1/4` from the integers. -/
theorem exists_mixed_three_one (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hcard : A.card ≤ 3)
    {u : ℕ} (hu : ¬ 2 ∣ u) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * τ)) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((u : ℝ) * τ) := by
  classical
  set g : ℕ → ℝ := fun c => if 2 ∣ c then (c : ℝ) / 2 else (c : ℝ) with hg
  set A' : Finset ℝ := A.image g with hA'def
  have hA'pos : ∀ x ∈ A', 0 < x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    have := hA c hc
    simp only [hg]
    split_ifs <;> positivity
  have hA'card : A'.card ≤ 4 - 1 := by
    have h1 : A'.card ≤ A.card := Finset.card_image_le
    omega
  obtain ⟨σ, hσ, hσA⟩ := LRC.SpecN.existenceAtN_four A' hA'pos hA'card
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u = 2 * m + 1 := ⟨u / 2, by omega⟩
  obtain ⟨ε, hε01, hεu⟩ : ∃ ε : ℕ, ε < 2 ∧ (4 : ℝ)⁻¹ ≤ circDist ((u : ℝ) * (σ / 2 + (ε : ℝ) / 2)) := by
    rcases half_or_quarter ((u : ℝ) * σ / 2) with h0 | h1
    · refine ⟨0, by norm_num, ?_⟩
      have : (u : ℝ) * (σ / 2 + ((0 : ℕ) : ℝ) / 2) = (u : ℝ) * σ / 2 := by push_cast; ring
      rw [this]; exact h0
    · refine ⟨1, by norm_num, ?_⟩
      have : (u : ℝ) * (σ / 2 + ((1 : ℕ) : ℝ) / 2) = ((u : ℝ) * σ / 2 + 1 / 2) + ((m : ℤ) : ℝ) := by
        rw [hm]; push_cast; ring
      rw [this, circDist_add_int]; exact h1
  refine ⟨σ / 2 + (ε : ℝ) / 2, by positivity, fun c hc => ?_, hεu⟩
  have hσc := hσA (g c) (Finset.mem_image_of_mem g hc)
  by_cases h2 : 2 ∣ c
  · obtain ⟨c', rfl⟩ := h2
    have hgc : g (2 * c') = ((2 * c' : ℕ) : ℝ) / 2 := by simp [hg]
    rw [hgc] at hσc
    have heq : ((2 * c' : ℕ) : ℝ) * (σ / 2 + (ε : ℝ) / 2)
        = ((2 * c' : ℕ) : ℝ) / 2 * σ + (((c' * ε : ℕ) : ℤ) : ℝ) := by push_cast; ring
    rw [heq, circDist_add_int]
    exact le_trans (by norm_num) hσc
  · have hgc : g c = (c : ℝ) := by simp [hg, h2]
    rw [hgc] at hσc
    have hd := eighth_of_double (y := (c : ℝ) * σ / 2) (by
      have : 2 * ((c : ℝ) * σ / 2) = (c : ℝ) * σ := by ring
      rw [this]; exact hσc)
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, c = 2 * m' + 1 := ⟨c / 2, by omega⟩
    rcases (show ε = 0 ∨ ε = 1 by omega) with he | he
    · have heq : (c : ℝ) * (σ / 2 + (ε : ℝ) / 2) = (c : ℝ) * σ / 2 := by rw [he]; push_cast; ring
      rw [heq]; exact hd.1
    · have heq : (c : ℝ) * (σ / 2 + (ε : ℝ) / 2) = ((c : ℝ) * σ / 2 + 1 / 2) + ((m' : ℤ) : ℝ) := by
        rw [he, hm']; push_cast; ring
      rw [heq, circDist_add_int]; exact hd.2

/-- **A reading `2u` (`u` odd) with `‖u·4t‖ ≥ 1/4` is clear at every quarter shift `t + j/4`.** -/
theorem quarter_silent {u : ℕ} (hu : ¬ 2 ∣ u) {t : ℝ}
    (h : (4 : ℝ)⁻¹ ≤ circDist ((u : ℝ) * (4 * t))) (j : ℕ) :
    (8 : ℝ)⁻¹ ≤ circDist (((2 * u : ℕ) : ℝ) * (t + (j : ℝ) / 4)) := by
  have hd := eighth_of_double (y := ((2 * u : ℕ) : ℝ) * t) (by
    have : 2 * (((2 * u : ℕ) : ℝ) * t) = (u : ℝ) * (4 * t) := by push_cast; ring
    rw [this]; exact h)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u = 2 * m + 1 := ⟨u / 2, by omega⟩
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · have heq : ((2 * u : ℕ) : ℝ) * (t + (j : ℝ) / 4) = ((2 * u : ℕ) : ℝ) * t + (((u * i : ℕ) : ℤ) : ℝ) := by
      rw [hi]; push_cast; ring
    rw [heq, circDist_add_int]; exact hd.1
  · have heq : ((2 * u : ℕ) : ℝ) * (t + (j : ℝ) / 4)
        = (((2 * u : ℕ) : ℝ) * t + 1 / 2) + (((2 * m * i + m + i : ℕ) : ℤ) : ℝ) := by
      rw [hi, hm]; push_cast; ring
    rw [heq, circDist_add_int]; exact hd.2

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **Quarter level with silenced readings `≡ 2 (mod 4)`.**  At most three odd readings, and an `s` at
which every `a/4` (`4 ∣ a`) is clear at `1/8` and every `d/2` (`d ≡ 2 mod 4`) at `1/4`: the set is lonely
at some `s/4 + j/4`. -/
theorem lonely_eight_of_quarter_silent {S : Finset ℕ}
    (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3)
    (hmix : ∃ s : ℝ, 0 < s ∧ (∀ a ∈ S, 4 ∣ a → (8 : ℝ)⁻¹ ≤ circDist (((a / 4 : ℕ) : ℝ) * s)) ∧
      ∀ d ∈ S, d % 4 = 2 → (4 : ℝ)⁻¹ ≤ circDist (((d / 2 : ℕ) : ℝ) * s)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨s, hs, hA, hT⟩ := hmix
  set A := S.filter (fun d => 4 ∣ d) with hAdef
  set B := S.filter (fun d => ¬ 2 ∣ d) with hBdef
  have hAt : ∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * (s / 4)) := by
    intro a ha
    obtain ⟨haS, h4⟩ := Finset.mem_filter.mp ha
    have heq : (a : ℝ) * (s / 4) = ((a / 4 : ℕ) : ℝ) * s := by
      obtain ⟨c, rfl⟩ := h4
      rw [show 4 * c / 4 = c by omega]; push_cast; ring
    rw [heq]; exact hA a haS h4
  obtain ⟨j, -, hAj, hBj⟩ := exists_quarter_shift A B (fun a ha => (Finset.mem_filter.mp ha).2)
    (fun b hb => (Finset.mem_filter.mp hb).2) hodd (s / 4) hAt
  refine ⟨s / 4 + (j : ℝ) / 4, by positivity, fun d hd => ?_⟩
  by_cases h2 : 2 ∣ d
  · by_cases h4 : 4 ∣ d
    · exact hAj d (Finset.mem_filter.mpr ⟨hd, h4⟩)
    · have hd2 : d % 4 = 2 := by omega
      obtain ⟨u, hu, rfl⟩ : ∃ u : ℕ, ¬ 2 ∣ u ∧ d = 2 * u := ⟨d / 2, by omega, by omega⟩
      have hsil := hT (2 * u) hd hd2
      rw [show 2 * u / 2 = u by omega] at hsil
      exact quarter_silent hu (t := s / 4) (by rw [show 4 * (s / 4) = s by ring]; exact hsil) j
  · exact hBj d (Finset.mem_filter.mpr ⟨hd, h2⟩)

/-- **Eighth level with silenced readings `≡ 4 (mod 8)`.**  The parity split for the non-multiples
of `8` that are not `≡ 4 (mod 8)`, and a `τ` at which every `m/8` (`8 ∣ m`) is clear at `1/8` and every
`f/4` (`f ≡ 4 mod 8`) at `1/4`: the set is lonely at some `(τ + k)/8`. -/
theorem lonely_eight_of_eighth_silent {S : Finset ℕ}
    (hsplit : ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)))
    (hmix : ∃ τ : ℝ, 0 < τ ∧ (∀ m ∈ S, 8 ∣ m → (8 : ℝ)⁻¹ ≤ circDist (((m / 8 : ℕ) : ℝ) * τ)) ∧
      ∀ f ∈ S, f % 8 = 4 → (4 : ℝ)⁻¹ ≤ circDist (((f / 4 : ℕ) : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨τ, hτ, hM, hF⟩ := hmix
  set R := S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4) with hRdef
  have hR8 : ∀ e ∈ R, ¬ 8 ∣ e := fun e he => (Finset.mem_filter.mp he).2.1
  obtain ⟨k, -, hk⟩ := exists_free_shift R hR8 hsplit τ
  refine ⟨(τ + k) / 8, by positivity, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨c, rfl⟩ := h8
    have hc := hM (8 * c) hd (dvd_mul_right 8 c)
    rw [show 8 * c / 8 = c by omega] at hc
    have heq : ((8 * c : ℕ) : ℝ) * ((τ + k) / 8) = (c : ℝ) * τ + (((c * k : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, circDist_add_int]; exact hc
  · by_cases h4 : d % 8 = 4
    · obtain ⟨u, hu, hd4⟩ : ∃ u : ℕ, ¬ 2 ∣ u ∧ d = 4 * u := ⟨d / 4, by omega, by omega⟩
      have hf := hF d hd h4
      rw [hd4, show 4 * u / 4 = u by omega] at hf
      have hsil := silent_of_quarter hu (τ := τ) hf k
      unfold Blocked at hsil
      push Not at hsil
      have heq : (d : ℝ) * ((τ + k) / 8) = ((4 * u : ℕ) : ℝ) * τ / 8 + ((4 * u : ℕ) : ℝ) * (k : ℝ) / 8 := by
        rw [hd4]; ring
      rw [heq]; exact hsil
    · have hb := hk d (Finset.mem_filter.mpr ⟨hd, h8, h4⟩)
      unfold Blocked at hb
      push Not at hb
      have heq : (d : ℝ) * ((τ + k) / 8) = (d : ℝ) * τ / 8 + (d : ℝ) * (k : ℝ) / 8 := by ring
      rw [heq]; exact hb

/-- The quotients `a/4` of the multiples of `4` are positive. -/
theorem quot_pos {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (q : ℕ) (hq : 0 < q) :
    ∀ x ∈ (S.filter (fun d => q ∣ d)).image (fun d => d / q), 0 < x := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hdS, hqd⟩ := Finset.mem_filter.mp hd
  exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) hqd) hq

/-- **Quarter level, settled cases.**  At most three odd readings, at most three multiples of `4`, at most
one reading `≡ 2 (mod 4)` (the mixed instant by `exists_mixed_three_one`). -/
theorem lonely_eight_of_quarter_three_one {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3)
    (h4 : (S.filter (fun d => 4 ∣ d)).card ≤ 3)
    (ht : (S.filter (fun d => d % 4 = 2)).card ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 4 ∣ d)).image (fun d => d / 4) with hAdef
  have hAcard : A.card ≤ 3 := le_trans Finset.card_image_le h4
  rcases Finset.eq_empty_or_nonempty (S.filter (fun d => d % 4 = 2)) with hE | ⟨d₀, hd₀⟩
  · obtain ⟨s, hs, hsA, -⟩ := exists_mixed_le_three A ∅ (quot_pos hpos 4 (by norm_num)) (by simp)
      (by simpa using hAcard)
    refine lonely_eight_of_quarter_silent hodd ⟨s, hs, fun a ha h4a => ?_, fun d hd hd2 => ?_⟩
    · exact hsA (a / 4) (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h4a⟩, rfl⟩)
    · exact absurd (Finset.mem_filter.mpr ⟨hd, hd2⟩) (by rw [hE]; exact Finset.notMem_empty _)
  · obtain ⟨hd₀S, hd₀2⟩ := Finset.mem_filter.mp hd₀
    have huniq : ∀ d ∈ S, d % 4 = 2 → d = d₀ := fun d hd hd2 =>
      Finset.card_le_one.mp ht d (Finset.mem_filter.mpr ⟨hd, hd2⟩) d₀ hd₀
    have hu : ¬ 2 ∣ d₀ / 2 := by omega
    obtain ⟨s, hs, hsA, hsu⟩ := exists_mixed_three_one A (quot_pos hpos 4 (by norm_num)) hAcard hu
    refine lonely_eight_of_quarter_silent hodd ⟨s, hs, fun a ha h4a => ?_, fun d hd hd2 => ?_⟩
    · exact hsA (a / 4) (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h4a⟩, rfl⟩)
    · rw [huniq d hd hd2]; exact hsu

/-- **Eighth level, settled cases.**  The parity split for the non-multiples other than those
`≡ 4 (mod 8)`, and at most three multiples of `8` and readings `≡ 4 (mod 8)` together (order four directly). -/
theorem lonely_eight_of_eighth_le_three {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hsplit : ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)))
    (h : (S.filter (fun d => 8 ∣ d)).card + (S.filter (fun d => d % 8 = 4)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hAdef
  set B := (S.filter (fun d => d % 8 = 4)).image (fun d => d / 4) with hBdef
  have hBpos : ∀ x ∈ B, 0 < x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdS, hd4⟩ := Finset.mem_filter.mp hd
    exact Nat.div_pos (by have := hpos d hdS; omega) (by norm_num)
  have hcard : A.card + B.card ≤ 3 := by
    have h1 : A.card ≤ (S.filter (fun d => 8 ∣ d)).card := Finset.card_image_le
    have h2 : B.card ≤ (S.filter (fun d => d % 8 = 4)).card := Finset.card_image_le
    omega
  obtain ⟨τ, hτ, hτA, hτB⟩ := exists_mixed_le_three A B (quot_pos hpos 8 (by norm_num)) hBpos hcard
  refine lonely_eight_of_eighth_silent hsplit ⟨τ, hτ, fun m hm h8 => ?_, fun f hf h4 => ?_⟩
  · exact hτA (m / 8) (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, h8⟩, rfl⟩)
  · exact hτB (f / 4) (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h4⟩, rfl⟩)

end LRC.OrderEightN
