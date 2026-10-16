import LonelyRunner.LRC.Spec.OrderSixSecSevenNativeN

/-!
# BHK §8 natively: slow-block windows, lap boxes and a kernel-checked cell certificate

Moved into the tree 2026-10-16 from `experiments/n6_native/S8CertFull_v1.lean` (log E85, E86). `lonely_8_native`
replaces `lonely_8` in the order-six dispatch `lonely6_of_lt`. The certificate (`certTree`, 322 leaves; 760 before E90) is checked by
`decide +kernel`; no `native_decide`.

## Data types, checker, and leaf soundness

Speeds `v : Fin 5 → ℝ`, `v 0` the slowest. A cell bounds the ratios `v (i+1) / v 0` by rationals:
`lo i · v 0 ≤ v (i+1) ≤ hi i · v 0`; `hi 3 = 0` means no upper bound on `v 4` (every real bound used is `≥ 1`).
A statement certifies a cell when its rational check passes; `stmt_sound` turns a passing check into a lonely instant
for every point of the cell. The tree and its covering proof are in the companion file.
-/

namespace LRC.S8Native
open LRC.S7Native

structure Cell where
  lo : Fin 4 → ℚ
  hi : Fin 4 → ℚ

/-- Lower and upper ratio bounds on all five runners (runner 0 is the unit). -/
def LO (c : Cell) : Fin 5 → ℚ := Fin.cases 1 c.lo
def HI (c : Cell) : Fin 5 → ℚ := Fin.cases 1 c.hi

def InCell (c : Cell) (v : Fin 5 → ℝ) : Prop :=
  ∀ i : Fin 4, ((c.lo i : ℚ) : ℝ) * v 0 ≤ v i.succ ∧ (c.hi i ≠ 0 → v i.succ ≤ ((c.hi i : ℚ) : ℝ) * v 0)

/-- The statements. Windows carry their endpoints `L`, `U` in units of `1 / v 0`. -/
inductive Stmt
  | w3 (m : Fin 3 → ℕ) (L U : ℚ)
  | f4 (m : Fin 4 → ℕ) (L U : ℚ)
  | box (k : Fin 5 → ℕ)

/-- Every runner `i` in the block reads in its lap band at both window ends, for every point of the cell. -/
def bandOK (c : Cell) (n : ℕ) (m : Fin n → ℕ) (L U : ℚ) (emb : Fin n → Fin 5) : Bool :=
  (List.finRange n).all fun i =>
    decide (0 < LO c (emb i)) && decide (0 < HI c (emb i)) &&
    decide (((6 * m i + 1 : ℕ) : ℚ) / 6 ≤ LO c (emb i) * L) && decide (HI c (emb i) * U ≤ ((6 * m i + 5 : ℕ) : ℚ) / 6)

def emb3 : Fin 3 → Fin 5 := fun i => ⟨i, by omega⟩
def emb4 : Fin 4 → Fin 5 := fun i => ⟨i, by omega⟩

/-- `window_two` on runners 3 and 4 (`a = v 3`, `b = v 4`), checked at the cell's worst corner. -/
def w3OK (c : Cell) (m : Fin 3 → ℕ) (L U : ℚ) : Bool :=
  let l := U - L
  let a := c.lo 2
  let b := c.lo 3
  bandOK c 3 m L U emb3 && decide (0 ≤ L) && decide (0 < a) && decide (a ≤ b) &&
  (if c.hi 3 = 0 then decide (1 / (3 * a) + 2 / (3 * b) ≤ l)
   else decide (1 / (3 * a) + 1 / (3 * b) ≤ l) && decide (a + c.hi 3 ≤ 3 * 64 * a) &&
     (List.range 64).all fun mm => !decide (3 * (mm : ℚ) * a < a + c.hi 3) || decide (((mm : ℚ) + 1 / 3) / b ≤ l))

def f4OK (c : Cell) (m : Fin 4 → ℕ) (L U : ℚ) : Bool :=
  bandOK c 4 m L U emb4 && decide (0 ≤ L) && decide (0 < c.lo 3) && decide (1 / 3 ≤ c.lo 3 * (U - L))

def boxOK (c : Cell) (k : Fin 5 → ℕ) : Bool :=
  decide (c.hi 3 ≠ 0) && (List.finRange 5).all fun i => (List.finRange 5).all fun j =>
    decide (0 < LO c i) && decide (0 < HI c j) &&
      decide (((6 * k i + 1 : ℕ) : ℚ) * HI c j ≤ ((6 * k j + 5 : ℕ) : ℚ) * LO c i)

def stmtOK (c : Cell) : Stmt → Bool
  | .w3 m L U => w3OK c m L U
  | .f4 m L U => f4OK c m L U
  | .box k => boxOK c k


/-! ## Proved window and box lemmas used by the leaves (copied from `S8Windows_v1/v2`, `S8Cert_v1`) -/

theorem fold_one {b J₀ ℓ : ℝ} (hb : 0 < b) (hℓ : 1 / (3 * b) ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  set y := b * J₀ with hy
  set f := Int.fract y with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋ : ℝ) + f := by rw [hf]; exact (Int.floor_add_fract y).symm
  have hℓ' : 1 / 3 ≤ b * ℓ := by rw [div_le_iff₀ (by positivity)] at hℓ; linarith
  by_cases hmid : 1 / 6 ≤ f ∧ f ≤ 5 / 6
  · refine ⟨J₀, le_rfl, by nlinarith [hℓ'], ?_⟩
    apply clear_of_band (p := ⌊y⌋) <;> [linarith [hmid.1]; linarith [hmid.2]]
  · push Not at hmid
    by_cases hlow : f < 1 / 6
    · refine ⟨J₀ + (1 / 6 - f) / b, by have : 0 ≤ (1 / 6 - f) / b := div_nonneg (by linarith) hb.le; linarith, ?_, ?_⟩
      · have : (1 / 6 - f) / b ≤ ℓ := by rw [div_le_iff₀ hb]; nlinarith
        linarith
      · apply clear_of_band (p := ⌊y⌋)
        · rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
        · rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
    · push Not at hlow
      have hhi : 5 / 6 < f := hmid hlow
      refine ⟨J₀ + (7 / 6 - f) / b, by have : 0 ≤ (7 / 6 - f) / b := div_nonneg (by linarith) hb.le; linarith, ?_, ?_⟩
      · have : (7 / 6 - f) / b ≤ ℓ := by rw [div_le_iff₀ hb]; nlinarith
        linarith
      · apply clear_of_band (p := ⌊y⌋ + 1)
        · push_cast; rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
        · push_cast; rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith

theorem window_two_simple {a b J₀ ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 / (3 * a) + 2 / (3 * b) ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  apply window_two ha hab
  · have : 1 / (3 * b) ≤ 2 / (3 * b) := by gcongr; norm_num
    linarith
  · intro m hm
    have key : ((m : ℝ) + 1 / 3) / b ≤ 1 / (3 * a) + 2 / (3 * b) := by
      rw [div_le_iff₀ hb]
      have : (m : ℝ) * (3 * a) < a + b := by linarith
      have e : (1 / (3 * a) + 2 / (3 * b)) * b = b / (3 * a) + 2 / 3 := by field_simp
      rw [e]
      have : (m : ℝ) < (a + b) / (3 * a) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have e2 : (a + b) / (3 * a) = 1 / 3 + b / (3 * a) := by field_simp
      linarith
    linarith

/-! ## Reading the cell -/

theorem lo_le {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (j : Fin 5) : ((LO c j : ℚ) : ℝ) * v 0 ≤ v j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [LO]
  · simpa [LO] using (hv i).1

theorem le_hi {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (j : Fin 5) (h : HI c j ≠ 0) :
    v j ≤ ((HI c j : ℚ) : ℝ) * v 0 := by
  revert h
  refine Fin.cases ?_ (fun i => ?_) j
  · intro _; simp [HI]
  · intro h; simpa [HI] using (hv i).2 (by simpa [HI] using h)

/-- A passing band check puts each block runner in its lap band across `[L / v 0, U / v 0]`. -/
theorem band_sound {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (h0 : 0 < v 0) {n : ℕ} {m : Fin n → ℕ}
    {L U : ℚ} {emb : Fin n → Fin 5} (hb : bandOK c n m L U emb = true) (hL : 0 ≤ L) (i : Fin n) {t : ℝ}
    (ht1 : (L : ℝ) / v 0 ≤ t) (ht2 : t ≤ (U : ℝ) / v 0) : (6 : ℝ)⁻¹ ≤ circDist (v (emb i) * t) := by
  simp only [bandOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hlo, hhi⟩, hA⟩, hB⟩ := hb i
  have hloR : (0 : ℝ) < (LO c (emb i) : ℝ) := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) < (HI c (emb i) : ℝ) := by exact_mod_cast hhi
  have hAR := (Rat.cast_le (K := ℝ)).mpr hA
  push_cast at hAR
  have hBR := (Rat.cast_le (K := ℝ)).mpr hB
  push_cast at hBR
  have l1 := lo_le hv (emb i)
  have u1 := le_hi hv (emb i) (by exact_mod_cast hhi.ne')
  have hLR : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have ht0 : 0 ≤ t := le_trans (div_nonneg hLR h0.le) ht1
  have tL : (L : ℝ) ≤ t * v 0 := by rwa [div_le_iff₀ h0] at ht1
  have tU : t * v 0 ≤ (U : ℝ) := by rwa [le_div_iff₀ h0] at ht2
  apply clear_of_band (p := (m i : ℤ))
  · push_cast at hAR ⊢
    have : (LO c (emb i) : ℝ) * L ≤ v (emb i) * t := by nlinarith
    linarith
  · push_cast at hBR ⊢
    have : v (emb i) * t ≤ (HI c (emb i) : ℝ) * U := by nlinarith
    linarith

def Lonely (v : Fin 5 → ℝ) : Prop := ∃ t : ℝ, ∀ i, (6 : ℝ)⁻¹ ≤ circDist (v i * t)

/-! ## Leaf soundness -/

theorem recip_le {x y : ℝ} (q : ℝ) (hq : 0 < q) (hy : 0 < y) (h : q * y ≤ x) : 1 / x ≤ (1 / q) / y := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h
  rw [div_div, div_le_div_iff₀ hx (by positivity)]; linarith

theorem w3_sound {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (h0 : 0 < v 0) (h34 : v 3 ≤ v 4)
    {m : Fin 3 → ℕ} {L U : ℚ} (hc : w3OK c m L U = true) : Lonely v := by
  unfold w3OK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hb, hL⟩, ha⟩, hab⟩, hrest⟩ := hc
  have l3 : ((c.lo 2 : ℚ) : ℝ) * v 0 ≤ v 3 := lo_le hv 3
  have l4 : ((c.lo 3 : ℚ) : ℝ) * v 0 ≤ v 4 := lo_le hv 4
  have haR : (0 : ℝ) < (c.lo 2 : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (c.lo 3 : ℝ) := by exact_mod_cast lt_of_lt_of_le ha hab
  have hv3 : 0 < v 3 := lt_of_lt_of_le (by positivity) l3
  have r3 := recip_le _ (by positivity : (0:ℝ) < 3 * (c.lo 2 : ℝ)) h0 (by nlinarith : 3 * (c.lo 2 : ℝ) * v 0 ≤ 3 * v 3)
  have r4 := recip_le _ (by positivity : (0:ℝ) < 3 * (c.lo 3 : ℝ)) h0 (by nlinarith : 3 * (c.lo 3 : ℝ) * v 0 ≤ 3 * v 4)
  -- the window [L/v0, U/v0] and its length
  obtain ⟨t, ht1, ht2, c3, c4⟩ : ∃ t : ℝ, (L : ℝ) / v 0 ≤ t ∧ t ≤ (L : ℝ) / v 0 + ((U : ℝ) - L) / v 0 ∧
      (6 : ℝ)⁻¹ ≤ circDist (v 3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v 4 * t) := by
    by_cases hinf : c.hi 3 = 0
    · simp only [hinf, if_true, decide_eq_true_eq] at hrest
      have hR := (Rat.cast_le (K := ℝ)).mpr hrest; push_cast at hR
      apply window_two_simple hv3 h34
      have e2 : 2 / (3 * v 4) = 2 * (1 / (3 * v 4)) := by ring
      have e2' : 2 / (3 * (c.lo 3 : ℝ)) = 2 * (1 / (3 * (c.lo 3 : ℝ))) := by ring
      have : 1 / (3 * v 3) + 2 / (3 * v 4) ≤ (1 / (3 * (c.lo 2 : ℝ)) + 2 / (3 * (c.lo 3 : ℝ))) / v 0 := by
        rw [add_div, e2, e2', mul_div_assoc]; linarith
      have hl : (1 / (3 * (c.lo 2 : ℝ)) + 2 / (3 * (c.lo 3 : ℝ))) / v 0 ≤ ((U : ℝ) - L) / v 0 :=
        div_le_div_of_nonneg_right (by linarith) h0.le
      linarith
    · simp only [hinf, if_false, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hrest
      obtain ⟨⟨hbase, h64⟩, hres⟩ := hrest
      have hbaseR := (Rat.cast_le (K := ℝ)).mpr hbase; push_cast at hbaseR
      have u4 : v 4 ≤ ((c.hi 3 : ℚ) : ℝ) * v 0 := le_hi hv 4 (by simpa [HI] using hinf)
      apply window_two hv3 h34
      · have : 1 / (3 * v 3) + 1 / (3 * v 4) ≤ (1 / (3 * (c.lo 2 : ℝ)) + 1 / (3 * (c.lo 3 : ℝ))) / v 0 := by
          rw [add_div]; linarith
        have hl : (1 / (3 * (c.lo 2 : ℝ)) + 1 / (3 * (c.lo 3 : ℝ))) / v 0 ≤ ((U : ℝ) - L) / v 0 :=
          div_le_div_of_nonneg_right (by linarith) h0.le
        linarith
      · intro mm hmm
        have hlpos : (0 : ℝ) ≤ ((U : ℝ) - L) / v 0 := by
          apply div_nonneg _ h0.le; have : (0:ℝ) < 1 / (3 * (c.lo 2 : ℝ)) + 1 / (3 * (c.lo 3 : ℝ)) := by positivity
          linarith
        rcases lt_or_ge mm 0 with hneg | hnn
        · have : ((mm : ℝ) + 1 / 3) / v 4 ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
            have : (mm : ℝ) ≤ -1 := by exact_mod_cast (show mm ≤ -1 by omega)
            linarith
          linarith
        · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
          have hk : 3 * (k : ℚ) * c.lo 2 < c.lo 2 + c.hi 3 := by
            have hR : 3 * (k : ℝ) * v 3 < v 3 + v 4 := by exact_mod_cast hmm
            have : (3 * (k : ℝ) - 1) * ((c.lo 2 : ℝ) * v 0) < ((c.hi 3 : ℚ) : ℝ) * v 0 := by
              rcases eq_or_lt_of_le (Nat.zero_le k) with h | h
              · subst h
                have : 0 < ((c.hi 3 : ℚ) : ℝ) * v 0 := lt_of_lt_of_le (by linarith) u4
                simp; nlinarith
              · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h
                nlinarith
            have : (3 * (k : ℝ) - 1) * (c.lo 2 : ℝ) < ((c.hi 3 : ℚ) : ℝ) := by
              by_contra hc; push Not at hc; nlinarith
            have : ((3 * (k : ℚ) * c.lo 2 : ℚ) : ℝ) < ((c.lo 2 + c.hi 3 : ℚ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          have hk64 : k < 64 := by
            by_contra hc; push Not at hc
            have : (64 : ℚ) ≤ k := by exact_mod_cast hc
            have h64' : c.lo 2 + c.hi 3 ≤ 3 * 64 * c.lo 2 := h64
            nlinarith
          have := hres k hk64
          rcases this with h | h
          · exact absurd hk (not_lt.mpr h)
          · have hR := (Rat.cast_le (K := ℝ)).mpr h; push_cast at hR
            have e : ((k : ℤ) : ℝ) = (k : ℝ) := by norm_cast
            rw [e]
            have : ((k : ℝ) + 1 / 3) / v 4 ≤ ((k : ℝ) + 1 / 3) / (c.lo 3 : ℝ) / v 0 := by
              rw [div_div]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
            have hl : ((k : ℝ) + 1 / 3) / (c.lo 3 : ℝ) / v 0 ≤ ((U : ℝ) - L) / v 0 :=
              div_le_div_of_nonneg_right (by linarith) h0.le
            linarith
  have ht2' : t ≤ (U : ℝ) / v 0 := by
    have e : (L : ℝ) / v 0 + ((U : ℝ) - L) / v 0 = (U : ℝ) / v 0 := by field_simp; ring
    linarith
  refine ⟨t, fun i => ?_⟩
  fin_cases i
  · exact band_sound hv h0 hb hL (0 : Fin 3) ht1 ht2'
  · exact band_sound hv h0 hb hL (1 : Fin 3) ht1 ht2'
  · exact band_sound hv h0 hb hL (2 : Fin 3) ht1 ht2'
  · exact c3
  · exact c4

/-- The five-runner lap box (as `S8Windows_v2.box5`). -/
theorem box5' (d : Fin 5 → ℝ) (k : Fin 5 → ℕ) (hd : ∀ i, 0 < d i)
    (h : ∀ i j, (6 * (k i : ℝ) + 1) * d j ≤ (6 * (k j : ℝ) + 5) * d i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (6 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  set l : Fin 5 → ℝ := fun i => (6 * (k i : ℝ) + 1) / (6 * d i) with hl
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
  refine ⟨l i₀, by simp only [hl]; have := hd i₀; positivity, fun i => ?_⟩
  have hdi := hd i
  have lo : (k i : ℝ) + 1 / 6 ≤ d i * l i₀ := by
    have := hi₀ i (Finset.mem_univ _); simp only [hl] at this ⊢
    rw [div_le_div_iff₀ (by positivity) (by have := hd i₀; positivity)] at this
    rw [mul_div_assoc', le_div_iff₀ (by have := hd i₀; positivity)]; nlinarith
  have hi : d i * l i₀ ≤ (k i : ℝ) + 5 / 6 := by
    have := h i₀ i; simp only [hl]
    rw [mul_div_assoc', div_le_iff₀ (by have := hd i₀; positivity)]; nlinarith
  exact clear_of_band (p := (k i : ℤ)) (by push_cast; linarith) (by push_cast; linarith)

theorem f4_sound {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (h0 : 0 < v 0)
    {m : Fin 4 → ℕ} {L U : ℚ} (hc : f4OK c m L U = true) : Lonely v := by
  unfold f4OK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hb, hL⟩, ha⟩, hf⟩ := hc
  have l4 : ((c.lo 3 : ℚ) : ℝ) * v 0 ≤ v 4 := lo_le hv 4
  have haR : (0 : ℝ) < (c.lo 3 : ℝ) := by exact_mod_cast ha
  have hv4 : 0 < v 4 := lt_of_lt_of_le (by positivity) l4
  have hfR := (Rat.cast_le (K := ℝ)).mpr hf; push_cast at hfR
  obtain ⟨t, ht1, ht2, c4⟩ := fold_one (J₀ := (L : ℝ) / v 0) (ℓ := ((U : ℝ) - L) / v 0) hv4 (by
    rw [div_le_div_iff₀ (by positivity) h0]; nlinarith)
  have ht2' : t ≤ (U : ℝ) / v 0 := by
    have e : (L : ℝ) / v 0 + ((U : ℝ) - L) / v 0 = (U : ℝ) / v 0 := by field_simp; ring
    linarith
  refine ⟨t, fun i => ?_⟩
  fin_cases i
  · exact band_sound hv h0 hb hL (0 : Fin 4) ht1 ht2'
  · exact band_sound hv h0 hb hL (1 : Fin 4) ht1 ht2'
  · exact band_sound hv h0 hb hL (2 : Fin 4) ht1 ht2'
  · exact band_sound hv h0 hb hL (3 : Fin 4) ht1 ht2'
  · exact c4

theorem box_sound {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (h0 : 0 < v 0)
    {k : Fin 5 → ℕ} (hc : boxOK c k = true) : Lonely v := by
  unfold boxOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies] at hc
  obtain ⟨hinf, hpairs⟩ := hc
  have hd : ∀ i, 0 < v i := fun i => by
    have := lo_le hv i; have hl : (0 : ℝ) < (LO c i : ℝ) := by exact_mod_cast (hpairs i i).1.1
    exact lt_of_lt_of_le (by positivity) this
  have hHI : ∀ j, HI c j ≠ 0 := fun j => ne_of_gt (hpairs 0 j).1.2
  obtain ⟨t, -, ht⟩ := box5' v k hd (fun i j => by
    have hp := (hpairs i j).2
    have hpR := (Rat.cast_le (K := ℝ)).mpr hp; push_cast at hpR
    have u := le_hi hv j (hHI j)
    have l := lo_le hv i
    have hA : (0 : ℝ) ≤ 6 * (k i : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) ≤ 6 * (k j : ℝ) + 5 := by positivity
    calc (6 * (k i : ℝ) + 1) * v j ≤ (6 * (k i : ℝ) + 1) * ((HI c j : ℝ) * v 0) := mul_le_mul_of_nonneg_left u hA
      _ = ((6 * (k i : ℝ) + 1) * (HI c j : ℝ)) * v 0 := by ring
      _ ≤ ((6 * (k j : ℝ) + 5) * (LO c i : ℝ)) * v 0 := mul_le_mul_of_nonneg_right hpR h0.le
      _ = (6 * (k j : ℝ) + 5) * ((LO c i : ℝ) * v 0) := by ring
      _ ≤ (6 * (k j : ℝ) + 5) * v i := mul_le_mul_of_nonneg_left l hB)
  exact ⟨t, ht⟩

theorem stmt_sound {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (h0 : 0 < v 0) (h34 : v 3 ≤ v 4)
    {s : Stmt} (hc : stmtOK c s = true) : Lonely v := by
  cases s with
  | w3 m L U => exact w3_sound hv h0 h34 hc
  | f4 m L U => exact f4_sound hv h0 hc
  | box k => exact box_sound hv h0 hc

/-! ## Clipping by the order, the tree, and its soundness -/

/-- The §8 order on five speeds, with the first window's range for runner 4. -/
def Ord (v : Fin 5 → ℝ) : Prop :=
  0 < v 0 ∧ v 0 ≤ v 1 ∧ v 1 ≤ v 2 ∧ v 2 ≤ v 3 ∧ v 3 ≤ v 4 ∧ v 2 ≤ 3 * v 0

def clip (c : Cell) : Cell :=
  let a2 := max (c.lo 0) 1
  let a3 := max (c.lo 1) a2
  let a4 := max (c.lo 2) a3
  let a5 := max (c.lo 3) a4
  let b4 := if c.hi 3 = 0 then c.hi 2 else min (c.hi 2) (c.hi 3)
  let b3 := min (min (c.hi 1) 3) b4
  let b2 := min (c.hi 0) b3
  ⟨![a2, a3, a4, a5], ![b2, b3, b4, c.hi 3]⟩

def bounded3 (c : Cell) : Bool := decide (0 < c.hi 0) && decide (0 < c.hi 1) && decide (0 < c.hi 2)

def emptyB (c : Cell) : Bool :=
  decide (c.hi 0 < c.lo 0) || decide (c.hi 1 < c.lo 1) || decide (c.hi 2 < c.lo 2) ||
    (decide (c.hi 3 ≠ 0) && decide (c.hi 3 < c.lo 3))

def setHi (c : Cell) (d : Fin 4) (x : ℚ) : Cell := ⟨c.lo, Function.update c.hi d x⟩
def setLo (c : Cell) (d : Fin 4) (x : ℚ) : Cell := ⟨Function.update c.lo d x, c.hi⟩

inductive Tree
  | none
  | leaf (s : Stmt)
  | node (d : Fin 4) (mid : ℚ) (l r : Tree)

def checkTree : Tree → Cell → Bool
  | .none, c => bounded3 c && bounded3 (clip c) && emptyB (clip c)
  | .leaf s, c => bounded3 c && bounded3 (clip c) && (emptyB (clip c) || stmtOK (clip c) s)
  | .node d mid l r, c => bounded3 c && bounded3 (clip c) &&
      (emptyB (clip c) || (checkTree l (setHi (clip c) d mid) && checkTree r (setLo (clip c) d mid)))

theorem clip_sound {c : Cell} {v : Fin 5 → ℝ} (ho : Ord v) (hv : InCell c v) (hb : bounded3 c = true) :
    InCell (clip c) v := by
  obtain ⟨h0, h01, h12, h23, h34, h2⟩ := ho
  simp only [bounded3, Bool.and_eq_true, decide_eq_true_eq] at hb
  have L0 := (hv 0).1; have L1 := (hv 1).1; have L2 := (hv 2).1; have L3 := (hv 3).1
  have U0 := (hv 0).2 (ne_of_gt hb.1.1); have U1 := (hv 1).2 (ne_of_gt hb.1.2)
  have U2 := (hv 2).2 (ne_of_gt hb.2); have U3 := (hv 3).2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at L0 L1 U0 U1
  have e2 : (Fin.succ (2 : Fin 4)) = 3 := rfl
  have e3 : (Fin.succ (3 : Fin 4)) = 4 := rfl
  rw [e2] at L2 U2; rw [e3] at L3 U3
  have m2 : ((max (c.lo 0) 1 : ℚ) : ℝ) * v 0 ≤ v 1 := by
    rw [Rat.cast_max]; push_cast; rcases le_total (c.lo 0 : ℝ) 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have m3 : ((max (c.lo 1) (max (c.lo 0) 1) : ℚ) : ℝ) * v 0 ≤ v 2 := by
    rw [Rat.cast_max, max_mul_of_nonneg _ _ h0.le]; exact max_le L1 (by linarith)
  have m4 : ((max (c.lo 2) (max (c.lo 1) (max (c.lo 0) 1)) : ℚ) : ℝ) * v 0 ≤ v 3 := by
    rw [Rat.cast_max, max_mul_of_nonneg _ _ h0.le]; exact max_le L2 (by linarith)
  have m5 : ((max (c.lo 3) (max (c.lo 2) (max (c.lo 1) (max (c.lo 0) 1))) : ℚ) : ℝ) * v 0 ≤ v 4 := by
    rw [Rat.cast_max, max_mul_of_nonneg _ _ h0.le]; exact max_le L3 (by linarith)
  have mb4 : v 3 ≤ (((if c.hi 3 = 0 then c.hi 2 else min (c.hi 2) (c.hi 3)) : ℚ) : ℝ) * v 0 := by
    split_ifs with h
    · exact U2
    · rw [Rat.cast_min, min_mul_of_nonneg _ _ h0.le]; exact le_min U2 (le_trans h34 (U3 h))
  have mb3 : v 2 ≤ ((min (min (c.hi 1) 3) (if c.hi 3 = 0 then c.hi 2 else min (c.hi 2) (c.hi 3)) : ℚ) : ℝ) * v 0 := by
    rw [Rat.cast_min, Rat.cast_min, min_mul_of_nonneg _ _ h0.le, min_mul_of_nonneg _ _ h0.le]
    refine le_min (le_min U1 (by push_cast; linarith)) (le_trans h23 mb4)
  have mb2 : v 1 ≤ ((min (c.hi 0) (min (min (c.hi 1) 3) (if c.hi 3 = 0 then c.hi 2 else min (c.hi 2) (c.hi 3))) : ℚ) : ℝ) * v 0 := by
    rw [Rat.cast_min, min_mul_of_nonneg _ _ h0.le]; exact le_min U0 (le_trans h12 mb3)
  intro i
  fin_cases i
  · exact ⟨m2, fun _ => mb2⟩
  · exact ⟨m3, fun _ => mb3⟩
  · exact ⟨m4, fun _ => mb4⟩
  · exact ⟨m5, U3⟩

theorem empty_sound {c : Cell} {v : Fin 5 → ℝ} (h0 : 0 < v 0) (hv : InCell c v) (hb : bounded3 c = true)
    (he : emptyB c = true) : False := by
  simp only [bounded3, Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [emptyB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he
  have key : ∀ i : Fin 4, c.hi i ≠ 0 → c.hi i < c.lo i → False := fun i hz hlt => by
    have l := (hv i).1; have u := (hv i).2 hz
    have : ((c.hi i : ℚ) : ℝ) < (c.lo i : ℝ) := by exact_mod_cast hlt
    nlinarith
  rcases he with ((h | h) | h) | ⟨hz, h⟩
  · exact key 0 (ne_of_gt hb.1.1) h
  · exact key 1 (ne_of_gt hb.1.2) h
  · exact key 2 (ne_of_gt hb.2) h
  · exact key 3 hz h

theorem setHi_in {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (d : Fin 4) (x : ℚ)
    (h : v d.succ ≤ (x : ℝ) * v 0) : InCell (setHi c d x) v := by
  intro i
  by_cases hi : i = d
  · subst hi; exact ⟨(hv i).1, fun _ => by simpa [setHi] using h⟩
  · exact ⟨(hv i).1, fun hz => by
      simp only [setHi, Function.update_of_ne hi] at hz ⊢; exact (hv i).2 hz⟩

theorem setLo_in {c : Cell} {v : Fin 5 → ℝ} (hv : InCell c v) (d : Fin 4) (x : ℚ)
    (h : (x : ℝ) * v 0 ≤ v d.succ) : InCell (setLo c d x) v := by
  intro i
  by_cases hi : i = d
  · subst hi; exact ⟨by simpa [setLo] using h, (hv i).2⟩
  · exact ⟨by simp only [setLo, Function.update_of_ne hi]; exact (hv i).1, (hv i).2⟩

theorem tree_sound : ∀ (t : Tree) (c : Cell) (v : Fin 5 → ℝ), checkTree t c = true → Ord v → InCell c v → Lonely v
  | .none, c, v, h, ho, hv => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact (empty_sound ho.1 (clip_sound ho hv h.1.1) h.1.2 h.2).elim
  | .leaf s, c, v, h, ho, hv => by
      simp only [checkTree, Bool.and_eq_true, Bool.or_eq_true] at h
      have hc := clip_sound ho hv h.1.1
      rcases h.2 with he | hs
      · exact (empty_sound ho.1 hc h.1.2 he).elim
      · exact stmt_sound hc ho.1 ho.2.2.2.2.1 hs
  | .node d mid l r, c, v, h, ho, hv => by
      simp only [checkTree, Bool.and_eq_true, Bool.or_eq_true] at h
      have hc := clip_sound ho hv h.1.1
      rcases h.2 with he | ⟨hl, hr⟩
      · exact (empty_sound ho.1 hc h.1.2 he).elim
      · rcases le_total (v d.succ) ((mid : ℝ) * v 0) with hle | hge
        · exact tree_sound l _ v hl ho (setHi_in hc d mid hle)
        · exact tree_sound r _ v hr ho (setLo_in hc d mid hge)




/-! ## The certificate -/

def root : Cell := ⟨![1, 1, 1, 1], ![3, 3, 6, 0]⟩

set_option maxRecDepth 100000 in
def certTree : Tree :=
(Tree.node 0 (2 : ℚ)
 (Tree.node 1 (2 : ℚ)
 (Tree.node 2 (2 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/12 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/12 : ℚ))))
 (Tree.node 2 (3 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (3 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.node 2 (4 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (5 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (6 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/12 : ℚ)))
 (Tree.node 3 (7 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/12 : ℚ))))))
 (Tree.node 2 (3 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (3 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.node 2 (4 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (5 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (6 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (1/3 : ℚ))))
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (5/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (2/3 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (11/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))
 (Tree.node 0 (11/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))
 (Tree.node 0 (5/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (2/3 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (23/4 : ℚ)
 (Tree.node 0 (11/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (1/3 : ℚ))))
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (13/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))
 (Tree.node 0 (13/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6]))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (15/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (31/8 : ℚ)
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))))
 (Tree.node 0 (15/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6])))))))
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (23/4 : ℚ)
 (Tree.node 0 (13/8 : ℚ)
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (21/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (23/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (23/4 : ℚ)
 (Tree.node 0 (15/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))))))))))
 (Tree.node 3 (7 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))
 (Tree.node 2 (5 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (5 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (6 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (5/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (14/33 : ℚ) (11/18 : ℚ))))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (11/8 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (14/33 : ℚ) (20/33 : ℚ)))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.node 2 (33/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))
 (Tree.node 2 (33/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (28/69 : ℚ) (5/9 : ℚ))))))
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))))
 (Tree.node 0 (5/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (11/18 : ℚ)))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 1, 1, 2]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4]))))
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))))
 (Tree.node 3 (7 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (13/2 : ℚ)
 (Tree.node 0 (5/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (11/18 : ℚ)))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (13/2 : ℚ)
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1])))))
 (Tree.node 3 (8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (9 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (10 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (11 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (12 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (23/2 : ℚ)
 (Tree.node 0 (5/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (11/18 : ℚ)))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (14/33 : ℚ) (5/9 : ℚ)))))
 (Tree.node 0 (5/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (11/18 : ℚ)))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (14/33 : ℚ) (5/9 : ℚ))))))
 (Tree.node 3 (23/2 : ℚ)
 (Tree.node 0 (5/4 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (7/15 : ℚ) (11/18 : ℚ)))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (10/33 : ℚ)))
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (14/33 : ℚ) (5/9 : ℚ)))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3])))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (23/2 : ℚ)
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9]))))
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9])))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9])))))
 (Tree.node 3 (23/2 : ℚ)
 (Tree.node 0 (7/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (10/33 : ℚ)))
 (Tree.node 2 (19/4 : ℚ)
 (Tree.node 3 (45/4 : ℚ)
 (Tree.node 0 (13/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8]))))
 (Tree.node 0 (13/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.node 2 (37/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9]))
 (Tree.node 3 (91/8 : ℚ)
 (Tree.node 0 (25/16 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 1] (28/69 : ℚ) (8/15 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9])))))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (14/57 : ℚ) (5/18 : ℚ)))))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (10/33 : ℚ)))
 (Tree.node 2 (19/4 : ℚ)
 (Tree.node 3 (45/4 : ℚ)
 (Tree.node 0 (15/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8]))))
 (Tree.node 0 (15/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (20/69 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 8])))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (14/57 : ℚ) (5/18 : ℚ))))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3]))))))
 (Tree.node 3 (13 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (14 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (15 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (16 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (17 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (18 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (19 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (20 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (21 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/27 : ℚ)))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (5/18 : ℚ)))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/27 : ℚ)))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (5/18 : ℚ))))))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))))))))))))))))))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (6 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 3 (7 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 3 (8 : ℚ)
 (Tree.node 0 (3/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (11/36 : ℚ)))
 (Tree.node 2 (11/2 : ℚ)
 (Tree.node 3 (15/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/33 : ℚ) (5/18 : ℚ)))))
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (11/36 : ℚ)))
 (Tree.node 2 (11/2 : ℚ)
 (Tree.node 3 (15/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/33 : ℚ) (5/18 : ℚ))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))))))
 (Tree.node 2 (3 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (3 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.node 2 (4 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (5 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (6 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/21 : ℚ) (17/24 : ℚ))))
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (9/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6]))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (17/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![1, 3, 4, 6, 8]))
 (Tree.node 2 (31/8 : ℚ)
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4]))))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![1, 3, 4, 6, 8]))
 (Tree.node 2 (31/8 : ℚ)
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7]))
 (Tree.node 3 (41/8 : ℚ)
 (Tree.node 0 (35/16 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7])))
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6]))))))
 (Tree.leaf (Stmt.box ![1, 2, 3, 4, 6])))))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (19/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7])))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7]))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (19/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7])))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7]))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))))))
 (Tree.node 0 (9/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))))
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))))))))
 (Tree.node 2 (7/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/21 : ℚ)))
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (11/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (21/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (29/8 : ℚ)
 (Tree.node 3 (41/8 : ℚ)
 (Tree.node 0 (41/16 : ℚ)
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7]))
 (Tree.node 1 (47/16 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 1, 1] (56/123 : ℚ) (88/141 : ℚ)))
 (Tree.leaf (Stmt.w3 ![2, 6, 7] (344/141 : ℚ) (164/63 : ℚ)))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7]))))
 (Tree.leaf (Stmt.w3 ![0, 1, 1] (4/9 : ℚ) (11/18 : ℚ))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (21/8 : ℚ)
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![1, 3, 4, 5, 7])))
 (Tree.leaf (Stmt.w3 ![0, 1, 1] (4/9 : ℚ) (11/18 : ℚ))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3])))))
 (Tree.leaf (Stmt.w3 ![0, 1, 1] (14/33 : ℚ) (11/18 : ℚ))))
 (Tree.node 0 (11/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.node 2 (15/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))))
 (Tree.leaf (Stmt.w3 ![0, 1, 1] (14/33 : ℚ) (11/18 : ℚ)))))))
 (Tree.node 3 (7 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/24 : ℚ))))
 (Tree.node 2 (5 : ℚ)
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (5 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 0]))
 (Tree.node 3 (6 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (11/2 : ℚ)
 (Tree.node 0 (9/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 2 (17/4 : ℚ)
 (Tree.node 3 (21/4 : ℚ)
 (Tree.node 0 (17/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4]))
 (Tree.node 1 (23/8 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (28/51 : ℚ) (44/69 : ℚ)))
 (Tree.node 2 (33/8 : ℚ)
 (Tree.node 3 (41/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 2]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))
 (Tree.node 3 (41/8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 2]))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4]))))))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 4])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/24 : ℚ) (11/18 : ℚ))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/24 : ℚ) (11/18 : ℚ)))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/27 : ℚ) (17/30 : ℚ)))))
 (Tree.node 3 (7 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (13/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3]))
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1])))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3])))
 (Tree.node 3 (8 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (9 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (10 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (11 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 0, 1]))
 (Tree.node 3 (12 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.node 3 (23/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 6]))
 (Tree.node 0 (9/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (7/12 : ℚ) (17/27 : ℚ)))
 (Tree.leaf (Stmt.box ![0, 1, 2, 3, 9])))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/24 : ℚ) (11/18 : ℚ)))))
 (Tree.node 3 (23/2 : ℚ)
 (Tree.node 0 (9/4 : ℚ)
 (Tree.node 1 (11/4 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (10/33 : ℚ)))
 (Tree.node 2 (19/4 : ℚ)
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 6]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (14/57 : ℚ) (5/18 : ℚ)))))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (14/27 : ℚ) (17/30 : ℚ))))
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 3])))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 6])))
 (Tree.node 3 (13 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (14 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (15 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (16 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (17 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (18 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (19 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (20 : ℚ)
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ)))
 (Tree.node 3 (21 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/24 : ℚ) (1/3 : ℚ)))
 (Tree.node 2 (9/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 0] (1/6 : ℚ) (5/27 : ℚ)))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/27 : ℚ) (5/18 : ℚ)))))
 (Tree.leaf (Stmt.f4 ![0, 1, 1, 2] (13/24 : ℚ) (17/30 : ℚ))))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))))))))))))))))))
 (Tree.leaf (Stmt.w3 ![0, 0, 0] (1/6 : ℚ) (5/18 : ℚ))))
 (Tree.node 3 (30 : ℚ)
 (Tree.node 3 (6 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 3 (7 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.node 3 (8 : ℚ)
 (Tree.node 0 (5/2 : ℚ)
 (Tree.node 1 (5/2 : ℚ)
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (11/36 : ℚ)))
 (Tree.node 2 (11/2 : ℚ)
 (Tree.node 3 (15/2 : ℚ)
 (Tree.leaf (Stmt.box ![0, 0, 0, 1, 1]))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/33 : ℚ) (5/18 : ℚ)))))
 (Tree.leaf (Stmt.box ![0, 1, 1, 2, 3])))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))))
 (Tree.leaf (Stmt.f4 ![0, 0, 0, 1] (7/30 : ℚ) (5/18 : ℚ))))))))

set_option maxRecDepth 100000 in
theorem cert_ok : checkTree certTree root = true := by decide +kernel

/-- **§8 with runner 4 within six times runner 1, every real arrangement in order.** -/
theorem lonely_8_box {v : Fin 5 → ℝ} (ho : Ord v) (h4 : v 3 ≤ 6 * v 0) : Lonely v := by
  apply tree_sound certTree root v cert_ok ho
  obtain ⟨h0, h01, h12, h23, h34, h2⟩ := ho
  intro i
  fin_cases i
  · exact ⟨by simp [root]; linarith, fun _ => by simp [root]; linarith⟩
  · exact ⟨by simp [root]; linarith, fun _ => by simp [root]; linarith⟩
  · exact ⟨by simp [root]; linarith, fun _ => by simp [root]; linarith⟩
  · exact ⟨by simp [root]; linarith, fun hz => absurd (by simp [root]) hz⟩

/-- Runner 4 at least six times runner 1: the first slow-block window closes runners 4 and 5 (`S8Windows_v1`). -/
theorem lonely_8_far {v : Fin 5 → ℝ} (ho : Ord v) (h4 : 6 * v 0 ≤ v 3) : Lonely v := by
  obtain ⟨h0, h01, h12, h23, h34, h2⟩ := ho
  have hv3 : 0 < v 3 := by linarith
  set ℓ := 5 / (6 * v 2) - 1 / (6 * v 0) with hℓ
  have hv2 : 0 < v 2 := by linarith
  have hlen : 2 / (3 * v 3) ≤ ℓ := by
    rw [hℓ, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht1, ht2, c3, c4⟩ := window_two_uniform (J₀ := 1 / (6 * v 0)) hv3 h34 hlen
  have ht2' : t ≤ 5 / (6 * v 2) := by rw [hℓ] at ht2; linarith
  have blk : ∀ i : Fin 5, i.val ≤ 2 → (6 : ℝ)⁻¹ ≤ circDist (v i * t) := by
    intro i hi
    have hlo : v 0 ≤ v i := by
      fin_cases i <;> simp at hi ⊢ <;> linarith
    have hhi : v i ≤ v 2 := by
      fin_cases i <;> simp at hi ⊢ <;> linarith
    have hvi : 0 < v i := by linarith
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
    apply clear_of_band (p := 0)
    · rw [Int.cast_zero, zero_add]; rw [div_le_iff₀ (by positivity)] at ht1; nlinarith
    · rw [Int.cast_zero, zero_add]; rw [le_div_iff₀ (by positivity)] at ht2'; nlinarith
  refine ⟨t, fun i => ?_⟩
  fin_cases i
  · exact blk 0 (by decide)
  · exact blk 1 (by decide)
  · exact blk 2 (by decide)
  · exact c3
  · exact c4

/-- **§8 natively, every ordered real arrangement** (`v₀ ≤ v₁ ≤ v₂ ≤ v₃ ≤ v₄`, `v₂ ≤ 3 v₀`). -/
theorem lonely_8_real {v : Fin 5 → ℝ} (ho : Ord v) : Lonely v := by
  rcases le_total (v 3) (6 * v 0) with h | h
  · exact lonely_8_box ho h
  · exact lonely_8_far ho h

end LRC.S8Native

namespace LRC.S8Native

/-- `circDist` is unchanged by a whole-number shift. -/
theorem s8_circDist_add_int (x : ℝ) (k : ℤ) : circDist (x + k) = circDist x := by
  unfold circDist; rw [Int.fract_add_intCast]

/-- **BHK §8 natively, in the dispatch's form.** Same hypotheses and conclusion as `lonely_8`. -/
theorem lonely_8_native {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hlarge : v3 ≤ 3 * v1) :
    ∃ t : ℝ, 0 < t ∧ LRC.OrderSixN.Lonely6 v1 v2 v3 v4 v5 t := by
  have ho : Ord ![(v1 : ℝ), v2, v3, v4, v5] := by
    refine ⟨by simp; exact_mod_cast h0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    · exact_mod_cast h12.le
    · exact_mod_cast h23.le
    · exact_mod_cast h34.le
    · exact_mod_cast h45.le
    · exact_mod_cast hlarge
  obtain ⟨s, hs⟩ := lonely_8_real ho
  obtain ⟨m, hm⟩ := exists_nat_gt (-s)
  have key : ∀ v : ℕ, circDist ((v : ℝ) * (s + ((m + 1 : ℕ) : ℝ))) = circDist ((v : ℝ) * s) := by
    intro v
    have e : (v : ℝ) * (s + ((m + 1 : ℕ) : ℝ)) = (v : ℝ) * s + ((v * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e, s8_circDist_add_int]
  refine ⟨s + ((m + 1 : ℕ) : ℝ), by push_cast; linarith, ?_⟩
  have h := fun i => hs i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [key, one_div]; simpa using h 0
  · rw [key, one_div]; simpa using h 1
  · rw [key, one_div]; simpa using h 2
  · rw [key, one_div]; simpa using h 3
  · rw [key, one_div]; simpa using h 4

end LRC.S8Native
