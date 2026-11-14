import Fresh.HarmonicPhase

namespace Fresh.Harmonic

open Fresh.Cascade

private theorem two_times_valid (m : ℕ) (hm : m ∈ ([1,2] : List ℕ)) :
    0 < m ∧ m ≤ 5 := by
  simp at hm
  omega

/-- A certificate for every shift on a replayed harmonic circle. -/
def ClearsTwice {n : ℕ} (p : Vector ℕ n) (margin : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ∃ m ∈ ([1,2] : List ℕ), ∃ φ : ℝ,
    ∀ i, margin ≤ distInt ((p.get i : ℝ)*φ+(m:ℝ)*x i)

theorem clears_twice_of_replay {n : ℕ} {p : Vector ℕ n}
    (hp : ∀ i : Fin n, 0 < p[i.val])
    (hs : Monotone (fun i : Fin n => p[i.val]))
    (hc : (replay p [1,2]).isEmpty = true) :
    ClearsTwice p (13/100) := by
  intro x
  obtain ⟨m,hm,φ,hφ⟩ := drift_of_replay x 1 hp hs two_times_valid hc
  refine ⟨m,hm,φ,fun i => ?_⟩
  simpa [mul_comm, mul_left_comm, mul_assoc] using (hφ i).le

private theorem clearance_near (x c : ℝ) (hc : 0 ≤ c) (hhalf : c < 1/2) :
    ∃ y : ℝ, |x-y| ≤ c ∧ c ≤ distInt y := by
  by_cases hx : c ≤ distInt x
  · exact ⟨x, by simpa, hx⟩
  have hr : |x-(round x : ℝ)| < c := lt_of_not_ge hx
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hr
  have hcd : distInt c = c := by
    have h0 : round c = 0 := round_eq_zero_iff.2 ⟨by linarith, hhalf⟩
    simp [distInt,h0,abs_of_nonneg hc]
  by_cases h : (round x : ℝ) ≤ x
  · refine ⟨c+(round x : ℝ), abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
    rw [distInt_add_int,hcd]
  · refine ⟨-c+(round x : ℝ), abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
    rw [distInt_add_int,distInt_neg,hcd]

/-- A sufficiently large appended slope is removed by moving inside the
four-reading phase window. This theorem has no upper bound on the slope. -/
theorem separated_append {p : Vector ℕ 4} {n M : ℕ}
    (hp : ∀ i : Fin 4, p[i.val] ≤ M) (hM : 0 < M) (hn : 26*M ≤ n)
    (core : ClearsTwice p (13/100)) :
    ClearsTwice (appendSlope p n) (1251/10000) := by
  intro x
  obtain ⟨m,hm,φ,hφ⟩ := core (fun i => x i.castSucc)
  let z := (n:ℝ)*φ+(m:ℝ)*x (Fin.last 4)
  obtain ⟨y,hy,hyc⟩ := clearance_near z (1251/10000) (by norm_num) (by norm_num)
  have hnpos : (0:ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  let ψ := φ+(y-z)/(n:ℝ)
  refine ⟨m,hm,ψ,fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hh : (n:ℝ)*ψ+(m:ℝ)*x (Fin.last 4) = y := by
      dsimp [ψ,z]
      field_simp
      ring
    change (1251/10000:ℝ) ≤ distInt (((p.push n)[4] : ℝ)*ψ+(m:ℝ)*x (Fin.last 4))
    change (n:ℝ)*ψ+(m:ℝ)*x (4 : Fin 5) = y at hh
    simpa [Vector.getElem_push,hh] using hyc
  · have hp' : (p.get j : ℝ) ≤ (M:ℝ) := by exact_mod_cast hp j
    have hn' : 26*(M:ℝ) ≤ n := by exact_mod_cast hn
    have hr : |(p.get j : ℝ)*φ+(m:ℝ)*x j.castSucc -
        ((p.get j : ℝ)*ψ+(m:ℝ)*x j.castSucc)| ≤ 49/10000 := by
      rw [show (p.get j : ℝ)*φ+(m:ℝ)*x j.castSucc -
        ((p.get j : ℝ)*ψ+(m:ℝ)*x j.castSucc) =
        (p.get j : ℝ)*((z-y)/(n:ℝ)) by dsimp [ψ]; ring]
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ p.get j), abs_div,
        abs_of_pos hnpos]
      apply (mul_le_mul hp' ((div_le_div_iff_of_pos_right hnpos).2 hy)
        (by positivity) (by positivity)).trans
      rw [← mul_div_assoc, div_le_iff₀ hnpos]
      linarith
    have hbound := phase_distance_le ((p.get j : ℝ)*φ+(m:ℝ)*x j.castSucc)
      ((p.get j : ℝ)*ψ+(m:ℝ)*x j.castSucc)
    have hgood := hφ j
    have hc : (1251/10000:ℝ) ≤ distInt ((p.get j : ℝ)*ψ+(m:ℝ)*x j.castSucc) := by
      linarith
    change (1251/10000:ℝ) ≤ distInt (((p.push n)[j.val] : ℝ)*ψ+(m:ℝ)*x j.castSucc)
    simpa [Vector.getElem_push,j.isLt] using hc

/-- Slicing a shifted plane transfers a five-coordinate phase certificate
to six coordinates when the frozen coordinate survives both dilations. -/
theorem slice_six {p : Vector ℕ 5} {c : ℝ} (hc : c ≤ 1/3)
    (h : ClearsTwice p c) (x : Fin 5 → ℝ) (z : ℝ) (a : Fin 5 → ℝ) :
    ∃ m ∈ ([1,2] : List ℕ), ∃ u v : ℝ,
      c ≤ distInt ((m:ℝ)*z+u) ∧
      ∀ i, c ≤ distInt ((m:ℝ)*x i + a i*u + (p.get i:ℝ)*v) := by
  let w := (1/3:ℝ)-z
  obtain ⟨m,hm,v,hv⟩ := h (fun i => x i+a i*w)
  refine ⟨m,hm,(m:ℝ)*w,v,?_,fun i => ?_⟩
  · have he : (m:ℝ)*z+(m:ℝ)*w = (m:ℝ)/3 := by unfold w; ring
    rw [he]
    apply hc.trans
    simp at hm
    rcases hm with rfl | rfl <;> norm_num [distInt, round_eq_iff]
  · convert hv i using 2
    ring

#print axioms separated_append
#print axioms slice_six



/-- Integer shifts of the common phase preserve the four divisible
slopes and traverse the full residue grid of the coprime fifth slope. -/
theorem coprime_append {p : Vector ℕ 4} {n g : ℕ}
    (hg : 2 ≤ g) (hn : Nat.Coprime n g) (hp : ∀ i : Fin 4, g ∣ p[i.val])
    (core : ClearsTwice p (13/100)) :
    ClearsTwice (appendSlope p n) (13/100) := by
  intro x
  obtain ⟨m,hm,φ,hφ⟩ := core (fun i => x i.castSucc)
  let z := (n:ℝ)*φ+(m:ℝ)*x (4 : Fin 5)
  let k : ℤ := round ((1/2-z)*(g:ℝ))
  let u : ℤ := k * Nat.gcdA n g
  let ψ := φ + (u:ℝ)/(g:ℝ)
  have hg' : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (0:ℝ) < g := by linarith
  have hbz : (1:ℝ) = (n:ℝ)*(Nat.gcdA n g : ℤ) + (g:ℝ)*(Nat.gcdB n g : ℤ) := by
    have hb := Nat.gcd_eq_gcd_ab n g
    rw [hn.gcd_eq_one] at hb
    exact_mod_cast hb
  refine ⟨m,hm,ψ,fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hmove : (n:ℝ)*ψ+(m:ℝ)*x (4 : Fin 5) =
        (z + (k:ℝ)/(g:ℝ)) + ((-(k * Nat.gcdB n g) : ℤ) : ℝ) := by
      dsimp [ψ,u,z]
      push_cast
      field_simp
      linear_combination (k:ℝ)*hbz.symm
    have hr : -(1/2:ℝ) ≤ (1/2-z)*(g:ℝ)-(k:ℝ) ∧
        (1/2-z)*(g:ℝ)-(k:ℝ) ≤ 1/2 :=
      abs_le.mp (abs_sub_round ((1/2-z)*(g:ℝ)))
    have hl : (1/4:ℝ) ≤ z+(k:ℝ)/(g:ℝ) := by
      have hl' : (1/4-z)*(g:ℝ) ≤ k := by nlinarith only [hr.2,hg']
      linarith only [(le_div_iff₀ hgp).2 hl']
    have hh : z+(k:ℝ)/(g:ℝ) ≤ 3/4 := by
      have hh' : (k:ℝ) ≤ (3/4-z)*(g:ℝ) := by nlinarith only [hr.1,hg']
      linarith only [(div_le_iff₀ hgp).2 hh']
    have hquarter : (1/4:ℝ) ≤ distInt (z+(k:ℝ)/(g:ℝ)) := by
      let v := z+(k:ℝ)/(g:ℝ)
      change (1/4:ℝ) ≤ |v-(round v:ℝ)|
      by_cases hr0 : round v ≤ 0
      · have hr0' : (round v:ℝ) ≤ 0 := by exact_mod_cast hr0
        exact (by linarith [hl] : (1/4:ℝ) ≤ v-(round v:ℝ)).trans (le_abs_self _)
      · have hr1' : (1:ℝ) ≤ round v := by
          exact_mod_cast (show (1:ℤ) ≤ round v by omega)
        exact (by linarith [hh] : (1/4:ℝ) ≤ -(v-(round v:ℝ))).trans (neg_le_abs _)
    change (13/100:ℝ) ≤ distInt (((p.push n)[4] : ℝ)*ψ+(m:ℝ)*x (4 : Fin 5))
    rw [Vector.getElem_push, dif_neg (by decide : ¬ (4:ℕ) < 4), hmove, distInt_add_int]
    exact (by norm_num : (13/100:ℝ) ≤ 1/4).trans hquarter
  · obtain ⟨a,ha⟩ := hp j
    have hmove : (p.get j:ℝ)*ψ+(m:ℝ)*x j.castSucc =
        ((p.get j:ℝ)*φ+(m:ℝ)*x j.castSucc) + (((a:ℤ)*u : ℤ):ℝ) := by
      dsimp [ψ]
      have hpa : (p.get j:ℝ) = (g:ℝ)*a := by exact_mod_cast ha
      rw [hpa]
      push_cast
      field_simp
      ring
    change (13/100:ℝ) ≤ distInt (((p.push n)[j.val] : ℝ)*ψ+(m:ℝ)*x j.castSucc)
    rw [Vector.getElem_push,dif_pos j.isLt]
    change (13/100:ℝ) ≤ distInt ((p.get j:ℝ)*ψ+(m:ℝ)*x j.castSucc)
    rw [hmove,distInt_add_int]
    exact hφ j

#print axioms coprime_append

end Fresh.Harmonic
