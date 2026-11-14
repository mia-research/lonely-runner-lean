import Fresh.HarmonicDBM
import Fresh.HarmonicLift

set_option maxHeartbeats 2000000

namespace Fresh.Harmonic

open Filter Set
open scoped Topology

private theorem next_interval {α : Type*} {S : Finset α} {L U : α → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝[>] x, ∃ i ∈ S, y ∈ Icc (L i) (U i)) :
    ∃ i ∈ S, L i ≤ x ∧ x < U i := by
  by_contra! hn
  have hmiss : ∀ᶠ y in 𝓝[>] x, ∀ i ∈ S, y ∉ Icc (L i) (U i) := by
    apply (eventually_all_finset S).2
    intro i hi
    by_cases hl : L i ≤ x
    · filter_upwards [self_mem_nhdsWithin (s := Ioi x)] with y hy h
      exact (not_lt_of_ge ((h.2).trans (hn i hi hl))) hy
    · filter_upwards [Ioo_mem_nhdsGT (lt_of_not_ge hl)] with y hy h
      exact (not_lt_of_ge h.1) hy.2
  have hx := (h.and hmiss).exists
  obtain ⟨y,⟨i,hi,hy⟩,hm⟩ := hx
  exact hm i hi hy

private theorem entry_divides (p : Vector ℕ n) (i : Fin n) :
    p[i.val] ∣ p.toList.prod := by
  apply List.dvd_prod
  simp [← Vector.getElem_toList]

private theorem product_pos (p : Vector ℕ n) (hp : ∀ i : Fin n, 0 < p[i.val]) :
    0 < p.toList.prod := by
  apply Nat.pos_of_ne_zero
  intro h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp (List.prod_eq_zero_iff.mp h)
  have hh := hp ⟨i, by simpa using hi.1⟩
  exact (Nat.ne_of_gt hh) (by simpa using hi.2)

private theorem unit_divides (p : Vector ℕ n) (i : Fin n) {m : ℕ}
    (hm : 0 < m ∧ m ≤ 5) : 100*m*p[i.val] ∣ unit p := by
  have h : m ∣ 60 := by
    obtain ⟨_,_⟩ := hm
    interval_cases m <;> decide
  exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 100 h) (entry_divides p i)

private theorem cast_div {scale d : ℕ} (hd : 0 < d) (hh : d ∣ scale) :
    ((scale/d : ℕ) : ℝ) = (scale : ℝ)/d := by
  apply (eq_div_iff (show (d : ℝ) ≠ 0 by positivity)).2
  exact_mod_cast Nat.div_mul_cancel hh

theorem root_sound {p : Vector ℕ n} {x : Fin n → ℝ}
    (hp : ∀ i : Fin n, 0 < p[i.val])
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1/(p[i.val] : ℝ))
    (hs : ∀ i j, i < j → p[i.val]=p[j.val] → x i ≤ x j) :
    Fits (root p) (fun i => (unit p : ℝ)*x i) := by
  intro i j
  change Bound.Holds ((root p)[i.val][j.val]) _
  unfold root
  simp only [matrix, Vector.getElem_ofFn]
  by_cases hij : i=j
  · subst j
    simp [Bound.Holds]
  · simp only [if_neg hij]
    split
    · rename_i h
      have hh : i < j ∧ p[i.val]=p[j.val] := by simpa using h
      have hz := mul_le_mul_of_nonneg_left (hs i j hh.1 hh.2) (by positivity : (0:ℝ) ≤ unit p)
      simpa [Bound.Holds] using sub_nonpos.mpr hz
    · have hd : p[i.val] ∣ unit p := by
        have h := unit_divides p i (m := 1) (by decide)
        exact (dvd_mul_left _ _).trans h
      have hi := hp i
      change (unit p : ℝ)*x i-(unit p : ℝ)*x j ≤ ((unit p/p[i.val] : ℕ) : ℝ)
      rw [cast_div hi hd]
      have hh := mul_le_mul_of_nonneg_left (hx i).2 (by positivity : (0:ℝ) ≤ unit p)
      have hj := mul_nonneg (by positivity : (0:ℝ) ≤ unit p) (hx j).1
      rw [mul_one_div] at hh
      linarith

theorem clauses_sound {p : Vector ℕ n} {x : Fin n → ℝ} {m : ℕ}
    (hp : ∀ i : Fin n, 0 < p[i.val]) (hm : 0 < m ∧ m ≤ 5)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1/(p[i.val] : ℝ))
    (hroot : Fits (root p) (fun i => (unit p : ℝ)*x i))
    (bad : ∀ y : ℝ, ∃ i : Fin n, distInt ((p[i.val] : ℝ)*(y+(m : ℝ)*x i)) ≤ 13/100) :
    Satisfies (clauses p m) (fun i => (unit p : ℝ)*x i) := by
  intro c hc
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  let E := ((j : ℝ)+13/100)/(p[i.val] : ℝ)-(m : ℝ)*x i
  have ppos (i : Fin n) : (0 : ℝ) < p[i.val] := by exact_mod_cast hp i
  let R : ℝ := p.toList.prod
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast product_pos p hp
  have pmax (i : Fin n) : (p[i.val] : ℝ) ≤ R := by
    dsimp [R]
    exact_mod_cast Nat.le_of_dvd (product_pos p hp) (entry_divides p i)
  have scale_pos : (0:ℝ) < unit p := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 6000) (product_pos p hp)
  have mpos : (0 : ℝ) < m := by exact_mod_cast hm.1
  have mx (i : Fin n) : (m : ℝ)*x i ≤ m :=
    mul_le_of_le_one_right mpos.le ((hx i).2.trans (by
      apply (div_le_iff₀ (ppos i)).2
      norm_num
      exact_mod_cast (show 1 ≤ p[i.val] from (hp i))))
  have mxpos (i : Fin n) : 0 ≤ (m : ℝ)*x i := mul_nonneg mpos.le (hx i).1
  have Elo : -(m : ℝ) ≤ E := by
    dsimp [E]
    linarith [mx i,div_nonneg (show 0 ≤ (j : ℝ)+13/100 by positivity) (ppos i).le]
  have Ehi : E < 1 := by
    have hj' : (j : ℝ)+13/100 < p[i.val] := by
      have hh : (j : ℝ)+1 ≤ p[i.val] := by exact_mod_cast (List.mem_range.mp hj)
      linarith
    have hh : ((j : ℝ)+13/100)/(p[i.val] : ℝ) < 1 :=
      (div_lt_iff₀ (ppos i)).2 (by simpa using hj')
    dsimp [E]
    linarith [mxpos i]
  let S := (Finset.univ : Finset (Fin n)).biUnion fun h =>
    (Finset.Icc (-(m*p[h.val] : ℕ)-1 : ℤ) ((m*p[h.val]+p[h.val]+1 : ℕ) : ℤ)).image
      (fun k => (h,k))
  let L := fun a : Fin n × ℤ => ((a.2 : ℝ)-13/100)/(p[a.1.val] : ℝ)-(m : ℝ)*x a.1
  let U := fun a : Fin n × ℤ => ((a.2 : ℝ)+13/100)/(p[a.1.val] : ℝ)-(m : ℝ)*x a.1
  have hcover : ∀ᶠ y in 𝓝[>] E, ∃ a ∈ S, y ∈ Icc (L a) (U a) := by
    have hrad : 0 < (1:ℝ)/R := by positivity
    filter_upwards [Ioo_mem_nhdsGT (show E < E+1/R by linarith only [hrad])] with y hy
    obtain ⟨h,hh⟩ := bad y
    let k : ℤ := round ((p[h.val] : ℝ)*(y+(m : ℝ)*x h))
    change |(p[h.val] : ℝ)*(y+(m : ℝ)*x h)-(k : ℝ)| ≤ 13/100 at hh
    obtain ⟨ha,hb⟩ := abs_le.mp hh
    have hlo : -((m : ℝ)*p[h.val]) ≤ (p[h.val] : ℝ)*(y+(m : ℝ)*x h) := by
      have hyy : -(m:ℝ) ≤ y+(m:ℝ)*x h := by linarith [Elo,hy.1,mxpos h]
      have hz := mul_le_mul_of_nonneg_left hyy (ppos h).le
      nlinarith only [hz]
    have hhi : (p[h.val] : ℝ)*(y+(m : ℝ)*x h) < (m : ℝ)*p[h.val]+p[h.val]+1 := by
      have hyy : y+(m:ℝ)*x h < (m:ℝ)+1+1/R := by linarith [Ehi,hy.2,mx h]
      have hz := mul_lt_mul_of_pos_left hyy (ppos h)
      have hcap : (p[h.val] : ℝ)*(1/R) ≤ 1 := by
        rw [mul_one_div, div_le_one hR]
        exact pmax h
      nlinarith only [hz,hcap]
    have kl : -(m*p[h.val] : ℕ)-1 ≤ k := by
      exact_mod_cast (show -((m : ℝ)*p[h.val])-1 ≤ k by linarith)
    have ku : k ≤ ((m*p[h.val]+p[h.val]+1 : ℕ) : ℤ) := by
      by_contra! hk
      have hh : (m : ℝ)*p[h.val]+p[h.val]+2 ≤ k := by
        exact_mod_cast (show ((m*p[h.val]+p[h.val]+2 : ℕ) : ℤ) ≤ k by omega)
      linarith
    refine ⟨(h,k), ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨h,Finset.mem_univ _,Finset.mem_image.mpr
        ⟨k,Finset.mem_Icc.mpr ⟨kl,ku⟩,rfl⟩⟩
    · change ((k : ℝ)-13/100)/(p[h.val] : ℝ)-(m:ℝ)*x h ≤ y ∧
        y ≤ ((k : ℝ)+13/100)/(p[h.val] : ℝ)-(m:ℝ)*x h
      constructor
      · apply sub_le_iff_le_add.mpr
        exact (div_le_iff₀ (ppos h)).2 (by linarith only [ha, mul_comm (y+(m:ℝ)*x h) (p[h.val] : ℝ)])
      · apply le_sub_iff_add_le.mpr
        exact (le_div_iff₀ (ppos h)).2 (by linarith only [hb, mul_comm (y+(m:ℝ)*x h) (p[h.val] : ℝ)])
  obtain ⟨⟨h,k⟩,hS,hL,hU⟩ := next_interval hcover
  have hd : i ≠ h := by
    intro he
    subst h
    change ((k:ℝ)-13/100)/(p[i.val]:ℝ)-(m:ℝ)*x i ≤ E at hL
    change E < ((k:ℝ)+13/100)/(p[i.val]:ℝ)-(m:ℝ)*x i at hU
    have h₁ : (k:ℝ)-13/100 ≤ (j:ℝ)+13/100 :=
      (div_le_div_iff_of_pos_right (ppos i)).mp (by dsimp [E] at hL; linarith)
    have h₂ : (j:ℝ) < k := by
      have hh : (j:ℝ)+13/100 < (k:ℝ)+13/100 :=
        (div_lt_div_iff_of_pos_right (ppos i)).mp (by dsimp [E] at hU; linarith)
      linarith
    have hz0 : (j:ℤ) < k := by exact_mod_cast h₂
    have hz : (j:ℝ)+1 ≤ k := by exact_mod_cast (show (j:ℤ)+1 ≤ k by omega)
    linarith
  obtain ⟨h',_,hh'⟩ := Finset.mem_biUnion.mp hS
  obtain ⟨k',hk',hk⟩ := Finset.mem_image.mp hh'
  cases hk
  have hk := Finset.mem_Icc.mp hk'
  let a : ℕ := (k+((m*p[h.val]+1 : ℕ) : ℤ)).toNat
  have ha : (a : ℤ) = k+((m*p[h.val]+1 : ℕ) : ℤ) := Int.toNat_of_nonneg (by push_cast; omega)
  have har : a < 2*m*p[h.val]+p[h.val]+3 := by
    rw [show 2*m*p[h.val] = 2*(m*p[h.val]) by ring]
    have hk2 := hk.2
    push_cast at ha hk2
    omega
  let u : ℕ := unit p/(100*m*p[i.val])
  let v : ℕ := unit p/(100*m*p[h.val])
  let w : Choice n := (i,h,
    ⟨(100*(j:ℤ)+13)*(u:ℤ)-(100*k-13)*(v:ℤ),false⟩,
    ⟨(100*k+13)*(v:ℤ)-(100*(j:ℤ)+13)*(u:ℤ),true⟩)
  have hw : w ∈ choices p m i j := by
    apply List.mem_flatMap.mpr
    refine ⟨h,List.mem_finRange _,?_⟩
    simp only [if_neg hd]
    exact List.mem_map.mpr ⟨a,List.mem_range.mpr har,by simp [w,u,v,ha]⟩
  suffices hv : Valid w (fun i => (unit p : ℝ)*x i) from
    ⟨w, List.mem_filter.mpr ⟨hw,possible_true hroot hv⟩,hv⟩
  have hu : (u:ℝ) = (unit p:ℝ)/(100*(m:ℝ)*p[i.val]) := by
    simpa only [u,Nat.cast_mul,Nat.cast_ofNat] using
      cast_div (Nat.mul_pos (Nat.mul_pos (by decide) hm.1) (hp i)) (unit_divides p i hm)
  have hv : (v:ℝ) = (unit p:ℝ)/(100*(m:ℝ)*p[h.val]) := by
    simpa only [v,Nat.cast_mul,Nat.cast_ofNat] using
      cast_div (Nat.mul_pos (Nat.mul_pos (by decide) hm.1) (hp h)) (unit_divides p h hm)
  change ((k:ℝ)-13/100)/(p[h.val]:ℝ)-(m:ℝ)*x h ≤ E at hL
  change E < ((k:ℝ)+13/100)/(p[h.val]:ℝ)-(m:ℝ)*x h at hU
  unfold Valid Bound.Holds
  dsimp only [w]
  simp only [Bool.false_eq_true, if_false, if_true]
  push_cast
  rw [hu,hv]
  have heq (r z : ℝ) (hp : 0 < r) :
      (100*z)*((unit p:ℝ)/(100*(m:ℝ)*r)) = ((unit p:ℝ)/m)*(z/r) := by
    field_simp
  rw [show 100*(j:ℝ)+13=100*((j:ℝ)+13/100) by ring,
      show 100*(k:ℝ)-13=100*((k:ℝ)-13/100) by ring,
      show 100*(k:ℝ)+13=100*((k:ℝ)+13/100) by ring]
  rw [heq _ _ (ppos i), heq _ _ (ppos h), heq _ _ (ppos h)]
  dsimp [E] at hL hU
  have scaleMul (z : ℝ) : ((unit p:ℝ)/m)*((m:ℝ)*z) = (unit p:ℝ)*z := by
    field_simp
  constructor
  · have h' : (m:ℝ)*(x i-x h) ≤ ((j:ℝ)+13/100)/p[i.val]-((k:ℝ)-13/100)/p[h.val] := by
      linarith [mul_sub (m:ℝ) (x i) (x h)]
    have hc := mul_le_mul_of_nonneg_left h' (show 0 ≤ (unit p:ℝ)/m by positivity)
    rw [scaleMul, mul_sub, mul_sub] at hc
    exact hc
  · have h' : (m:ℝ)*(x h-x i) < ((k:ℝ)+13/100)/p[h.val]-((j:ℝ)+13/100)/p[i.val] := by
      linarith [mul_sub (m:ℝ) (x h) (x i)]
    have hc := mul_lt_mul_of_pos_left h' (div_pos scale_pos mpos)
    rw [scaleMul, mul_sub, mul_sub] at hc
    exact hc

#print axioms clauses_sound
end Fresh.Harmonic
