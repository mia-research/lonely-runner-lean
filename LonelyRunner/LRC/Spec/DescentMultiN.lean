import LonelyRunner.LRC.Spec.DescentN

/-!
# The descent with several non-multiples: the shift budget

2026-09-24.  `lonely_descent_iff` removes one disparity not divisible by `n`.  This file removes
several at once, provided their cost fits inside the `n` available shifts.

Split the disparities into a finite set `E` of non-multiples of `n` and the multiples `n·m`,
`m ∈ M`.  At an instant `τ` clearing `M`, try `t = (τ + k)/n` for `k = 0, …, n − 1`.  Each
multiple reads `m·(τ + k)`, unchanged mod 1.  A non-multiple `e` reads `e·τ/n + e·k/n`, and it
blocks at most `max 2 (gcd e n)` of the `n` shifts (`card_bad_le`):

* if `gcd(e, n) = 1`, at most two — three blocked shifts would need three integer steps of size
  at most 1, none zero, one the sum of the other two;
* if `g = gcd(e, n) ≥ 2`, every step is a multiple of `g` of size at most 1, hence zero, so the
  blocked shifts share one residue class mod `n/g`, and there are at most `g` of them.

**The shift budget** (`lonely_multi_descent_iff`).  If `∑_{e ∈ E} max 2 (gcd e n) < n`, some
shift clears every non-multiple, and `E ∪ n·M` is lonely at threshold `1/n` exactly when `M` is.
A pigeonhole over the shifts, used as a tool.  `lonely_descent_iff` is the case `E = {e}`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.Descent

open ConstructionN

variable {n : ℕ}

/-- **Two blocked shifts differ by an integer step of size at most 1.** -/
theorem bad_step (hn : 0 < n) (x : ℝ) (e : ℕ) {k₁ k₂ : ℕ} {K₁ K₂ : ℤ}
    (h₁ : |x + (e : ℝ) * (k₁ : ℝ) / n - K₁| < (n : ℝ)⁻¹)
    (h₂ : |x + (e : ℝ) * (k₂ : ℝ) / n - K₂| < (n : ℝ)⁻¹) :
    |(e : ℤ) * ((k₁ : ℤ) - k₂) - n * (K₁ - K₂)| ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≠ 0 := hnpos.ne'
  have heq : (((e : ℤ) * ((k₁ : ℤ) - k₂) - n * (K₁ - K₂) : ℤ) : ℝ)
      = n * ((x + (e : ℝ) * (k₁ : ℝ) / n - K₁) - (x + (e : ℝ) * (k₂ : ℝ) / n - K₂)) := by
    push_cast; field_simp; ring
  have hb := scaled_sub_lt_two hnpos h₁ h₂
  rw [← heq] at hb
  have hi : |(e : ℤ) * ((k₁ : ℤ) - k₂) - n * (K₁ - K₂)| < 2 := by exact_mod_cast hb
  rw [abs_lt] at hi
  rw [abs_le]
  omega

/-- **A non-multiple blocks at most `max 2 (gcd e n)` of the `n` shifts.** -/
theorem card_bad_le (hn : 0 < n) (x : ℝ) (e : ℕ) :
    ((Finset.range n).filter
        (fun k : ℕ => circDist (x + (e : ℝ) * (k : ℝ) / n) < (n : ℝ)⁻¹)).card
      ≤ max 2 (Nat.gcd e n) := by
  classical
  set B := (Finset.range n).filter
    (fun k : ℕ => circDist (x + (e : ℝ) * (k : ℝ) / n) < (n : ℝ)⁻¹) with hB
  have hK : ∀ k : ℕ, ∃ K : ℤ,
      circDist (x + (e : ℝ) * (k : ℝ) / n) = |x + (e : ℝ) * (k : ℝ) / n - K| :=
    fun k => circDist_eq_abs_sub_some_int _
  choose K hK using hK
  have hbad : ∀ k ∈ B, |x + (e : ℝ) * (k : ℝ) / n - K k| < (n : ℝ)⁻¹ := by
    intro k hk; rw [← hK k]; exact (Finset.mem_filter.mp hk).2
  have hlt : ∀ k ∈ B, k < n := fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  set σ : ℕ → ℕ → ℤ := fun a b => (e : ℤ) * ((a : ℤ) - b) - n * (K a - K b) with hσ
  have hσle : ∀ a ∈ B, ∀ b ∈ B, |σ a b| ≤ 1 :=
    fun a ha b hb => bad_step hn x e (hbad a ha) (hbad b hb)
  have hσdvd : ∀ a b, σ a b = 0 → (n : ℤ) ∣ (e : ℤ) * ((a : ℤ) - b) := by
    intro a b h
    exact ⟨K a - K b, by simp only [hσ] at h; linarith⟩
  set g := Nat.gcd e n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right e hn
  rcases Nat.lt_or_ge g 2 with hg1 | hg2
  · -- `gcd(e, n) = 1`: at most two blocked shifts
    have hcop : Nat.Coprime e n := by
      unfold Nat.Coprime
      omega
    have hzero : ∀ a ∈ B, ∀ b ∈ B, σ a b = 0 → a = b := by
      intro a ha b hb h
      have hdvd := hσdvd a b h
      have hic : IsCoprime (n : ℤ) (e : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
      have hab : (n : ℤ) ∣ ((a : ℤ) - b) := hic.dvd_of_dvd_mul_left hdvd
      obtain ⟨c, hc⟩ := hab
      have ha' : (a : ℤ) < n := by exact_mod_cast hlt a ha
      have hb' : (b : ℤ) < n := by exact_mod_cast hlt b hb
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      rw [hc0, mul_zero] at hc
      omega
    have h2 : B.card ≤ 2 := by
      by_contra hc
      push Not at hc
      obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
      have h1 := hσle a ha b hb
      have h2 := hσle b hb c hc'
      have h3 := hσle a ha c hc'
      have n1 : σ a b ≠ 0 := fun h => hab (hzero a ha b hb h)
      have n2 : σ b c ≠ 0 := fun h => hbc (hzero b hb c hc' h)
      have n3 : σ a c ≠ 0 := fun h => hac (hzero a ha c hc' h)
      have hadd : σ a c = σ a b + σ b c := by simp only [hσ]; ring
      rw [abs_le] at h1 h2 h3
      omega
    exact le_trans h2 (le_max_left _ _)
  · -- `g = gcd(e, n) ≥ 2`: every step is zero, so one residue class mod `n / g`
    have hsame : ∀ a ∈ B, ∀ b ∈ B, σ a b = 0 := by
      intro a ha b hb
      have hgd : (g : ℤ) ∣ σ a b := by
        have h1 : (g : ℤ) ∣ (e : ℤ) := by exact_mod_cast Nat.gcd_dvd_left e n
        have h2 : (g : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.gcd_dvd_right e n
        exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)
      have h := hσle a ha b hb
      rw [abs_le] at h
      obtain ⟨q, hq⟩ := hgd
      have hg2' : (2 : ℤ) ≤ g := by exact_mod_cast hg2
      rw [hq] at h ⊢
      rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
      · nlinarith
      · rw [hq0, mul_zero]
      · nlinarith
    set m := n / g with hm
    have hmg : n = m * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right e n)).symm
    have heg : e = (e / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left e n)).symm
    have hcop : Nat.Coprime (e / g) m := Nat.coprime_div_gcd_div_gcd hg0
    have hmod : ∀ a ∈ B, ∀ b ∈ B, a % m = b % m := by
      intro a ha b hb
      have hdvd := hσdvd a b (hsame a ha b hb)
      have hdvd' : ((g : ℤ) * m) ∣ (g : ℤ) * ((e / g : ℕ) * ((a : ℤ) - b)) := by
        have e1 : (n : ℤ) = (g : ℤ) * m := by rw [hmg]; push_cast; ring
        have e2 : (e : ℤ) * ((a : ℤ) - b) = (g : ℤ) * ((e / g : ℕ) * ((a : ℤ) - b)) := by
          conv_lhs => rw [heg]
          push_cast; ring
        rw [← e1, ← e2]; exact hdvd
      have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
      have hm1 : (m : ℤ) ∣ (e / g : ℕ) * ((a : ℤ) - b) := Int.dvd_of_mul_dvd_mul_left hg0' hdvd'
      have hic : IsCoprime (m : ℤ) ((e / g : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
      have hm2 : (m : ℤ) ∣ ((a : ℤ) - b) := hic.dvd_of_dvd_mul_left hm1
      have hm3 : (m : ℤ) ∣ ((b : ℤ) - a) := by
        have := dvd_neg.mpr hm2
        rwa [neg_sub] at this
      have hzm : (a : ℤ) % m = (b : ℤ) % m := (Int.modEq_iff_dvd.mpr hm3)
      exact_mod_cast hzm
    have hinj : Set.InjOn (fun k => k / m) (B : Set ℕ) := by
      intro a ha b hb hab
      have hr := hmod a ha b hb
      simp only at hab
      rw [← Nat.div_add_mod a m, ← Nat.div_add_mod b m, hab, hr]
    have hmaps : ∀ k ∈ B, k / m ∈ Finset.range g := by
      intro k hk
      rw [Finset.mem_range]
      have hk := hlt k hk
      rw [hmg] at hk
      exact Nat.div_lt_of_lt_mul hk
    have hc := Finset.card_le_card_of_injOn (fun k => k / m) hmaps hinj
    rw [Finset.card_range] at hc
    exact le_trans hc (le_max_right _ _)

/-- **The shift budget.**  Let `E` be a set of disparities not divisible by `n`, and `M` the
cofactors of the multiples of `n`.  If `∑_{e ∈ E} max 2 (gcd e n) < n`, then `E ∪ n·M` is lonely
at threshold `1/n` exactly when `M` is lonely at the same threshold. -/
theorem lonely_multi_descent_iff (hn : 0 < n) (E : Finset ℕ) (M : List ℕ)
    (hcost : ∑ e ∈ E, max 2 (Nat.gcd e n) < n) :
    (∃ t : ℝ, 0 < t ∧ (∀ e ∈ E, (n : ℝ)⁻¹ ≤ circDist ((e : ℝ) * t)) ∧
        ∀ m ∈ M, (n : ℝ)⁻¹ ≤ circDist (((n * m : ℕ) : ℝ) * t)) ↔
      (∃ τ : ℝ, 0 < τ ∧ ∀ m ∈ M, (n : ℝ)⁻¹ ≤ circDist ((m : ℝ) * τ)) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≠ 0 := hnpos.ne'
  constructor
  · rintro ⟨t, ht, -, hM⟩
    refine ⟨n * t, mul_pos hnpos ht, fun m hm => ?_⟩
    have h := hM m hm
    have heq : ((n * m : ℕ) : ℝ) * t = (m : ℝ) * (n * t) := by push_cast; ring
    rwa [heq] at h
  · rintro ⟨τ, hτ, hM⟩
    set Bad : ℕ → Finset ℕ := fun e => (Finset.range n).filter
      (fun k : ℕ => circDist ((e : ℝ) * τ / n + (e : ℝ) * (k : ℝ) / n) < (n : ℝ)⁻¹) with hBad
    have hcard : (E.biUnion Bad).card < (Finset.range n).card := by
      rw [Finset.card_range]
      calc (E.biUnion Bad).card ≤ ∑ e ∈ E, (Bad e).card := Finset.card_biUnion_le
        _ ≤ ∑ e ∈ E, max 2 (Nat.gcd e n) :=
          Finset.sum_le_sum fun e _ => card_bad_le hn ((e : ℝ) * τ / n) e
        _ < n := hcost
    obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨(τ + k) / n, by positivity, fun e he => ?_, fun m hm => ?_⟩
    · have hnot : k ∉ Bad e := fun h => hkn (Finset.mem_biUnion.mpr ⟨e, he, h⟩)
      have hclear : ¬ circDist ((e : ℝ) * τ / n + (e : ℝ) * (k : ℝ) / n) < (n : ℝ)⁻¹ :=
        fun h => hnot (Finset.mem_filter.mpr ⟨hk, h⟩)
      have heq : (e : ℝ) * ((τ + k) / n) = (e : ℝ) * τ / n + (e : ℝ) * (k : ℝ) / n := by ring
      rw [heq]
      exact not_lt.mp hclear
    · have heq : ((n * m : ℕ) : ℝ) * ((τ + k) / n) = (m : ℝ) * τ + (((m * k : ℕ) : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [heq, circDist_add_int]
      exact hM m hm

end LRC.Descent
