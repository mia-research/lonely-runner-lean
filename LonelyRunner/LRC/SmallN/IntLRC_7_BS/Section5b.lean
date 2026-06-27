import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5

/-!
# n = 7 (Barajas–Serra) — §5 mixed-residue dispatch + `four_band`
-/

open Finset

namespace IntLRC7BS

def sel3 (d : Fin 4 → ℤ) (i0 i1 i2 : Fin 4) : Fin 3 → ℤ := ![d i0, d i1, d i2]
def sel2 (d : Fin 4 → ℤ) (i0 i1 : Fin 4) : Fin 2 → ℤ := ![d i0, d i1]

set_option maxHeartbeats 2000000 in
private theorem classify_fin3 :
    ∀ (r : Fin 4 → Fin 3), ¬ (∀ i, r i = r 0) →
    (∃ (i0 i1 i2 e : Fin 4),
      (∀ j, j = i0 ∨ j = i1 ∨ j = i2 ∨ j = e) ∧
      r i0 = r i1 ∧ r i0 = r i2 ∧ r e ≠ r i0) ∨
    (∃ (i0 i1 e1 e2 : Fin 4),
      (∀ j, j = i0 ∨ j = i1 ∨ j = e1 ∨ j = e2) ∧
      r i0 = r i1 ∧ r e1 ≠ r i0 ∧ r e2 ≠ r i0) := by decide

private theorem ratio_in_24 : ∀ (a b : ZMod 7),
    a ∈ ({1, 2, 4} : Finset (ZMod 7)) → b ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    a ≠ b → (a * b⁻¹ = 2 ∨ a * b⁻¹ = 4) := by decide

private theorem ratio4_swap : ∀ (a b : ZMod 7),
    a ∈ ({1, 2, 4} : Finset (ZMod 7)) → b ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    a * b⁻¹ = 4 → b * a⁻¹ = 2 := by decide

private theorem ratio4_eq (a b c : ZMod 7)
    (hc : c ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (ha : a * c⁻¹ = 4) (hb : b * c⁻¹ = 4) : a = b := by
  have key : ∀ (a b c : ZMod 7), c ∈ ({1, 2, 4} : Finset (ZMod 7)) →
    a * c⁻¹ = 4 → b * c⁻¹ = 4 → a = b := by decide
  exact key a b c hc ha hb

private noncomputable def encode124 (x : ZMod 7) : Fin 3 :=
  if x = 1 then 0 else if x = 2 then 1 else 2

private theorem encode_eq_of_eq (x y : ZMod 7)
    (h : x = y) : encode124 x = encode124 y := by rw [h]

private theorem eq_of_encode_eq (x y : ZMod 7)
    (hx : x ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hy : y ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (h : encode124 x = encode124 y) : x = y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [encode124] at h; split_ifs at h <;> simp_all (config := { decide := true }))

/-- Run case2 or case3_int_avoid on a sub-tuple and map back to Fin 4. -/
private theorem case2_dispatch (m : ℕ) (hm : 0 < m) (d : Fin 4 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (i0 i1 i2 e : Fin 4)
    (hcover : ∀ j, j = i0 ∨ j = i1 ∨ j = i2 ∨ j = e)
    (hsame01 : (d i1 : ZMod 7) = (d i0 : ZMod 7))
    (hsame02 : (d i2 : ZMod 7) = (d i0 : ZMod 7))
    (hne : (d e : ZMod 7) ≠ (d i0 : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  have hsame : ∀ i, (sel3 d i0 i1 i2 i : ZMod 7) = (sel3 d i0 i1 i2 0 : ZMod 7) := by
    intro i; fin_cases i <;> simp [sel3, hsame01, hsame02]
  have hndvd_s : ∀ i, ¬ (7 : ℤ) ∣ sel3 d i0 i1 i2 i := by
    intro i; fin_cases i <;> simp [sel3] <;> exact hndvd _
  have hcoeff : (d e : ZMod 7) * ((sel3 d i0 i1 i2 0 : ZMod 7))⁻¹ = 2 ∨
      (d e : ZMod 7) * ((sel3 d i0 i1 i2 0 : ZMod 7))⁻¹ = 4 := by
    simp only [sel3, Matrix.cons_val_zero]; exact ratio_in_24 _ _ (hres e) (hres i0) hne
  obtain ⟨lam, hlam, havoid_s, havoid_e⟩ :=
    case2_int_avoid m hm (sel3 d i0 i1 i2) (d e) hndvd_s (hndvd e) hsame hcoeff
  refine ⟨lam, hlam, fun i => ?_⟩
  rcases hcover i with rfl | rfl | rfl | rfl
  · have h := havoid_s 0; simp only [sel3] at h; exact band_of_qz_ne m _ h.1 h.2
  · have h := havoid_s 1; simp only [sel3] at h; exact band_of_qz_ne m _ h.1 h.2
  · have h := havoid_s 2; simp only [sel3] at h; exact band_of_qz_ne m _ h.1 h.2
  · exact band_of_qz_ne m _ havoid_e.1 havoid_e.2

private theorem case3_dispatch (m : ℕ) (hm : 0 < m) (d : Fin 4 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (a0 a1 b1 b2 : Fin 4)
    (hcover : ∀ j, j = a0 ∨ j = a1 ∨ j = b1 ∨ j = b2)
    (hsame : (d a1 : ZMod 7) = (d a0 : ZMod 7))
    (hcfg : let c1 := (d b1 : ZMod 7) * ((d a0 : ZMod 7))⁻¹
            let c2 := (d b2 : ZMod 7) * ((d a0 : ZMod 7))⁻¹
            (c1 = 2 ∧ c2 = 2) ∨ (c1 = 2 ∧ c2 = 4) ∨ (c1 = 4 ∧ c2 = 2)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  have hsame_sel : ∀ i, (sel2 d a0 a1 i : ZMod 7) = (sel2 d a0 a1 0 : ZMod 7) := by
    intro i; fin_cases i <;> simp [sel2, hsame]
  have hndvd_s : ∀ i, ¬ (7 : ℤ) ∣ sel2 d a0 a1 i := by
    intro i; fin_cases i <;> simp [sel2] <;> exact hndvd _
  have hcfg' : let c1 := (d b1 : ZMod 7) * ((sel2 d a0 a1 0 : ZMod 7))⁻¹
               let c2 := (d b2 : ZMod 7) * ((sel2 d a0 a1 0 : ZMod 7))⁻¹
               (c1 = 2 ∧ c2 = 2) ∨ (c1 = 2 ∧ c2 = 4) ∨ (c1 = 4 ∧ c2 = 2) := by
    convert hcfg using 2 <;> simp [sel2]
  obtain ⟨lam, hlam, havoid_s, havoid_e1, havoid_e2⟩ :=
    case3_int_avoid m hm (sel2 d a0 a1) (d b1) (d b2) hndvd_s (hndvd b1) (hndvd b2) hsame_sel hcfg'
  refine ⟨lam, hlam, fun i => ?_⟩
  rcases hcover i with rfl | rfl | rfl | rfl
  · have h := havoid_s 0; simp only [sel2] at h; exact band_of_qz_ne m _ h.1 h.2
  · have h := havoid_s 1; simp only [sel2] at h; exact band_of_qz_ne m _ h.1 h.2
  · exact band_of_qz_ne m _ havoid_e1.1 havoid_e1.2
  · exact band_of_qz_ne m _ havoid_e2.1 havoid_e2.2

theorem section5_mixed (m : ℕ) (hm : 0 < m) (d : Fin 4 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hnall : ¬ ∀ i, (d i : ZMod 7) = (d 0 : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  classical
  set rc : Fin 4 → Fin 3 := fun i => encode124 ((d i : ZMod 7))
  have hrc_fwd : ∀ i j, rc i = rc j → (d i : ZMod 7) = (d j : ZMod 7) :=
    fun i j h => eq_of_encode_eq _ _ (hres i) (hres j) h
  have hrc_bwd : ∀ i j, (d i : ZMod 7) = (d j : ZMod 7) → rc i = rc j :=
    fun i j h => encode_eq_of_eq _ _ h
  have hnall' : ¬ ∀ i, rc i = rc 0 :=
    fun h => hnall (fun i => hrc_fwd i 0 (h i))
  rcases classify_fin3 rc hnall' with
    ⟨i0, i1, i2, e, hcover, h01, h02, hne⟩ |
    ⟨i0, i1, e1, e2, hcover, h01, hne1, hne2⟩
  · exact case2_dispatch m hm d hndvd hres i0 i1 i2 e hcover
      (hrc_fwd i1 i0 h01.symm) (hrc_fwd i2 i0 h02.symm)
      (fun h => hne (hrc_bwd e i0 h))
  · -- 2+2 case: dispatch on coefficient config
    have hsame01 : (d i1 : ZMod 7) = (d i0 : ZMod 7) := hrc_fwd i1 i0 h01.symm
    have hne_e1 : (d e1 : ZMod 7) ≠ (d i0 : ZMod 7) := fun h => hne1 (hrc_bwd e1 i0 h)
    have hne_e2 : (d e2 : ZMod 7) ≠ (d i0 : ZMod 7) := fun h => hne2 (hrc_bwd e2 i0 h)
    have hc1 := ratio_in_24 _ _ (hres e1) (hres i0) hne_e1
    have hc2 := ratio_in_24 _ _ (hres e2) (hres i0) hne_e2
    rcases hc1 with hc1_2 | hc1_4 <;> rcases hc2 with hc2_2 | hc2_4
    · exact case3_dispatch m hm d hndvd hres i0 i1 e1 e2 hcover hsame01
        (Or.inl ⟨hc1_2, hc2_2⟩)
    · exact case3_dispatch m hm d hndvd hres i0 i1 e1 e2 hcover hsame01
        (Or.inr (Or.inl ⟨hc1_2, hc2_4⟩))
    · exact case3_dispatch m hm d hndvd hres i0 i1 e1 e2 hcover hsame01
        (Or.inr (Or.inr ⟨hc1_4, hc2_2⟩))
    · -- (4,4): relabel. Swap A_s ↔ extras.
      have hsame_e : (d e2 : ZMod 7) = (d e1 : ZMod 7) :=
        ratio4_eq _ _ _ (hres i0) hc2_4 hc1_4
      have hswap := ratio4_swap _ _ (hres e1) (hres i0) hc1_4
      exact case3_dispatch m hm d hndvd hres e1 e2 i0 i1
        (fun j => by rcases hcover j with h | h | h | h <;> simp [h])
        hsame_e (Or.inl ⟨hswap, by rwa [hsame01]⟩)

theorem four_band (m : ℕ) (hm : 0 < m) (d : Fin 4 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  set d' : Fin 4 → ℤ := fun i => normalize7 (d i)
  have hd'_ndvd : ∀ i, ¬ (7 : ℤ) ∣ d' i := fun i => normalize7_ndvd _ (hnotdvd i)
  suffices h : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d' i) % 7 ^ (m + 1) ∧
      (lam * d' i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m by
    obtain ⟨lam, hlam, hband⟩ := h
    exact ⟨lam, hlam, fun i => normalize7_band m lam (d i) (hband i)⟩
  have hd'_res : ∀ i, (d' i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) :=
    fun i => normalize7_res _ (hnotdvd i)
  by_cases hall : ∀ i, (d' i : ZMod 7) = (d' 0 : ZMod 7)
  · obtain ⟨lam, hlam, havoid⟩ := case1_int_avoid m hm d' hd'_ndvd hall
    exact ⟨lam, hlam, fun i => band_of_qz_ne m _ (havoid i).1 (havoid i).2⟩
  · exact section5_mixed m hm d' hd'_ndvd hd'_res hall

end IntLRC7BS
