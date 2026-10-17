import LonelyRunner.LRC.Spec.OrderSevenAbsN
import LonelyRunner.LRC.Spec.OrderSevenNu2FinalN

/-!
# Order seven on 7-adic grids: every set of at most six speeds

`gridG_all`: given the three finite statements `AbsU5`, `AbsP1`, `AbsP2` (named in `OrderSevenAbsN`, checked by
exact search, not proved in Lean), every set of at most six positive integers is in band at a unit instant
`k / 7^a`.

* No speed divisible by `343`: `grid_nu2_of` with the kernel-checked certificates A, B, C.
* Top valuation `n ≥ 3`, no unit: divide by `7`.
* Top valuation `n ≥ 3`, a unit present, level `a = n + 1` (the top class is automatic):
  - every class below `n` has at most three runners: the greedy free digit (`greedy_ext`), class `v` decided at
    digit `a - 1 - v`, each runner blocking at most two of the seven values (`digit_block`);
  - four or five units: `units_all`, `units_val1_all`, `units_valw_all`;
  - four runners of one valuation `v ≥ 1`: their cofactors at level `n + 1 - v`, then the greedy for the unit.

No `sorry`, no `native_decide`.
-/

namespace LRC.O7All
open LRC.O7Grid LRC.O7Abs LRC.O7L3

/-! ## Valuations -/

/-- 7-adic valuation. -/
def vv (d : ℕ) : ℕ := d.factorization 7

/-- Cofactor prime to 7. -/
def mm (d : ℕ) : ℕ := d / 7 ^ vv d

theorem p7 : Nat.Prime 7 := by norm_num

theorem vv_spec {d : ℕ} (hd : d ≠ 0) : d = 7 ^ vv d * mm d ∧ ¬ 7 ∣ mm d :=
  ⟨(Nat.ordProj_mul_ordCompl_eq_self d 7).symm, Nat.not_dvd_ordCompl p7 hd⟩

theorem pow_dvd_iff_vv {d k : ℕ} (hd : d ≠ 0) : 7 ^ k ∣ d ↔ k ≤ vv d := p7.pow_dvd_iff_le_factorization hd

theorem vv_zero_iff {d : ℕ} (hd : d ≠ 0) : vv d = 0 ↔ ¬ 7 ∣ d := by
  have := pow_dvd_iff_vv (k := 1) hd
  rw [pow_one] at this
  omega

/-- A speed at level `a` is its cofactor at level `a - vv d`. -/
theorem gridOK_vv {a k d : ℕ} (hd : d ≠ 0) (hv : vv d < a) : GridOK a k d ↔ GridOK (a - vv d) k (mm d) := by
  have h := gridOK_pow7 (L := a - vv d) (by omega) k (mm d) (vv d)
  rw [show a - vv d + vv d = a by omega, ← (vv_spec hd).1] at h
  exact h

/-! ## One digit: each runner blocks at most two values -/

theorem block_table : ∀ q < 7, ∀ u0 < 7, u0 ≠ 0 →
    ((Finset.range 7).filter fun s => (q + u0 * s) % 7 = 0 ∨ (q + u0 * s) % 7 = 6).card ≤ 2 := by
  decide

theorem split_mod {N Q r : ℕ} (hN : 0 < N) (hr : r < N) : (N * Q + r) % (N * 7) = N * (Q % 7) + r := by
  have hq := Nat.mod_lt Q (by norm_num : 7 > 0)
  have hlt : N * (Q % 7) + r < N * 7 := by nlinarith
  have hsplit : N * Q + r = (N * (Q % 7) + r) + N * 7 * (Q / 7) := by
    have := Nat.mod_add_div Q 7
    calc N * Q + r = N * (Q % 7 + 7 * (Q / 7)) + r := by rw [this]
      _ = _ := by ring
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem digit_block {J u k0 : ℕ} (hJ : 1 ≤ J) (hu : ¬ 7 ∣ u) (hk : ¬ 7 ∣ k0) :
    ((Finset.range 7).filter fun s => ¬ GridOK (J + 1) (k0 + 7 ^ J * s) u).card ≤ 2 := by
  set N := 7 ^ J with hN
  have hNpos : 0 < N := by positivity
  have hN7 : 7 ∣ N := dvd_pow_self 7 (by omega)
  set x := u * k0 % (N * 7) with hx
  set q := x / N
  set r := x % N
  have hxqr : x = N * q + r := (Nat.div_add_mod x N).symm
  have hr0 : r ≠ 0 := by
    have hrr : r = u * k0 % N := by
      simp only [r, x]; exact Nat.mod_mod_of_dvd _ (dvd_mul_right N 7)
    intro h0; rw [hrr] at h0
    have : 7 ∣ u * k0 := dvd_trans hN7 (Nat.dvd_of_mod_eq_zero h0)
    exact ((Nat.Prime.dvd_mul p7).mp this).elim hu hk
  have hrlt : r < N := Nat.mod_lt _ hNpos
  have hval : ∀ s, u * (k0 + N * s) % (N * 7) = N * ((q + u * s) % 7) + r := by
    intro s
    have e : u * (k0 + N * s) % (N * 7) = (N * (q + u * s) + r) % (N * 7) := by
      rw [show u * (k0 + N * s) = u * k0 + N * (u * s) by ring, Nat.add_mod, ← hx, hxqr,
        show N * (u * s) % (N * 7) = N * (u * s % 7) by rw [Nat.mul_mod_mul_left]]
      rw [show N * q + r + N * (u * s % 7) = N * (q + u * s % 7) + r by ring]
      rw [split_mod hNpos hrlt, split_mod hNpos hrlt]
      congr 2; simp [Nat.add_mod]
    rw [e, split_mod hNpos hrlt]
  have hsub : ((Finset.range 7).filter fun s => ¬ GridOK (J + 1) (k0 + N * s) u) ⊆
      ((Finset.range 7).filter fun s => (q % 7 + u % 7 * s) % 7 = 0 ∨ (q % 7 + u % 7 * s) % 7 = 6) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    refine ⟨hs.1, ?_⟩
    have hg := hs.2
    unfold GridOK at hg
    rw [show J + 1 - 1 = J by omega, pow_succ, ← hN, hval s] at hg
    have hm : (q + u * s) % 7 = (q % 7 + u % 7 * s) % 7 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [← hm]
    have hd := Nat.mod_lt (q + u * s) (by norm_num : 7 > 0)
    by_contra hne; push Not at hne
    apply hg
    set t := (q + u * s) % 7
    have h1 : 1 ≤ t := by omega
    have h5 : t ≤ 5 := by omega
    constructor
    · have : N * 1 ≤ N * t := Nat.mul_le_mul_left N h1
      omega
    · have : N * t ≤ N * 5 := Nat.mul_le_mul_left N h5
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  exact block_table _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (fun h => hu (Nat.dvd_of_mod_eq_zero h))

/-- **Free digit at any level `J + 1 ≥ 2`**: at most three units leave a free digit `s`. -/
theorem free_digit_gen {J : ℕ} (hJ : 1 ≤ J) {W : Finset ℕ} (hW : W.card ≤ 3) (hu : ∀ u ∈ W, ¬ 7 ∣ u)
    {k0 : ℕ} (hk : ¬ 7 ∣ k0) : ∃ s, s < 7 ∧ ∀ u ∈ W, GridOK (J + 1) (k0 + 7 ^ J * s) u := by
  by_contra hno
  push Not at hno
  have hcover : Finset.range 7 ⊆ W.biUnion
      (fun u => (Finset.range 7).filter fun s => ¬ GridOK (J + 1) (k0 + 7 ^ J * s) u) := by
    intro s hs
    obtain ⟨u, hu', hbad⟩ := hno s (Finset.mem_range.mp hs)
    exact Finset.mem_biUnion.mpr ⟨u, hu', Finset.mem_filter.mpr ⟨hs, hbad⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le (s := W)
    (t := fun u => (Finset.range 7).filter fun s => ¬ GridOK (J + 1) (k0 + 7 ^ J * s) u)
  have h3 : ∑ u ∈ W, ((Finset.range 7).filter fun s => ¬ GridOK (J + 1) (k0 + 7 ^ J * s) u).card ≤ W.card * 2 :=
    Finset.sum_le_card_nsmul _ _ _ (fun u hu' => digit_block hJ (hu u hu') hk)
  simp at h1
  omega

/-! ## The greedy extension -/

theorem greedy_ext {S : Finset ℕ} {a : ℕ} (hS : ∀ d ∈ S, d ≠ 0 ∧ vv d < a) :
    ∀ n J k, J + n = a → 1 ≤ J → ¬ 7 ∣ k →
      (∀ d ∈ S, a ≤ J + vv d → GridOK (a - vv d) k (mm d)) →
      (∀ d ∈ S, J + vv d < a → (S.filter fun e => vv e = vv d).card ≤ 3) →
      ∃ k', ¬ 7 ∣ k' ∧ ∀ d ∈ S, GridOK (a - vv d) k' (mm d) := by
  intro n
  induction n with
  | zero =>
    intro J k hJa _ hk hstart _
    exact ⟨k, hk, fun d hd => hstart d hd (by omega)⟩
  | succ n ih =>
    intro J k hJa hJ hk hstart hsmall
    set W := (S.filter fun e => vv e = a - 1 - J).image mm with hW
    have hWc : W.card ≤ 3 := by
      rcases (S.filter fun e => vv e = a - 1 - J).eq_empty_or_nonempty with he | ⟨d, hd⟩
      · rw [hW, he]; simp
      · obtain ⟨hdS, hdv⟩ := Finset.mem_filter.mp hd
        have := hsmall d hdS (by omega)
        rw [hdv] at this
        exact le_trans Finset.card_image_le this
    have hWu : ∀ u ∈ W, ¬ 7 ∣ u := by
      intro u hu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
      exact (vv_spec (hS d (Finset.mem_filter.mp hd).1).1).2
    have hk0 : ¬ 7 ∣ k % 7 ^ J := by
      rw [not7_mod (dvd_pow_self 7 (by omega))]; exact hk
    obtain ⟨s, -, hs⟩ := free_digit_gen hJ hWc hWu hk0
    set k' := k % 7 ^ J + 7 ^ J * s with hk'
    have hk'7 : ¬ 7 ∣ k' := by
      have h7J : 7 ∣ 7 ^ J := dvd_pow_self 7 (by omega)
      intro h
      rw [hk'] at h
      exact hk0 ((Nat.dvd_add_left (dvd_mul_of_dvd_left h7J s)).mp h)
    refine ih (J + 1) k' (by omega) (by omega) hk'7 ?_ ?_
    · intro d hd hle
      by_cases hold : a ≤ J + vv d
      · have h := hstart d hd hold
        have hL : a - vv d ≤ J := by omega
        rw [gridOK_mod_k] at h ⊢
        have hdvd : 7 ^ (a - vv d) ∣ 7 ^ J := pow_dvd_pow 7 hL
        have e1 : (k % 7 ^ J + 7 ^ J * s) % 7 ^ (a - vv d) = k % 7 ^ (a - vv d) := by
          rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd,
            Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdvd s), add_zero, Nat.mod_mod]
        rw [hk', e1]; exact h
      · have hv : vv d = a - 1 - J := by omega
        have hm : mm d ∈ W := Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hv⟩, rfl⟩
        rw [show a - vv d = J + 1 by omega]
        exact hs _ hm
    · intro d hd hlt
      exact hsmall d hd (by omega)

/-! ## Counting -/

theorem card_two_more {S A B : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) {x y : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hxA : x ∉ A ∪ B) (hyA : y ∉ A ∪ B) (hxy : x ≠ y) :
    A.card + B.card + 2 ≤ S.card := by
  have hsub : insert y (insert x (A ∪ B)) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_union] at hz
    rcases hz with rfl | rfl | h | h
    · exact hy
    · exact hx
    · exact hA h
    · exact hB h
  have := Finset.card_le_card hsub
  have hy' : y ∉ insert x (A ∪ B) := by
    rw [Finset.mem_insert]; push Not; exact ⟨Ne.symm hxy, hyA⟩
  rw [Finset.card_insert_of_notMem hy', Finset.card_insert_of_notMem hxA, Finset.card_union_of_disjoint hAB] at this
  omega

theorem card_one_more {S A B : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) {x : ℕ}
    (hx : x ∈ S) (hxA : x ∉ A ∪ B) : A.card + B.card + 1 ≤ S.card := by
  have hsub : insert x (A ∪ B) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_union] at hz
    rcases hz with rfl | h | h
    · exact hx
    · exact hA h
    · exact hB h
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxA, Finset.card_union_of_disjoint hAB] at this
  omega

/-! ## The case split at top valuation `n ≥ 3` -/

theorem grid_top (hU5 : AbsU5) (hP1 : AbsP1) (hP2 : AbsP2) {n : ℕ} (hn : 3 ≤ n) {S : Finset ℕ}
    (hS : S.card ≤ 6) (hpos : ∀ d ∈ S, d ≠ 0) (hle : ∀ d ∈ S, vv d ≤ n) {e : ℕ} (he : e ∈ S) (hev : vv e = n)
    {u0 : ℕ} (hu0 : u0 ∈ S) (hu0v : vv u0 = 0) : GridG S := by
  have hlt : ∀ d ∈ S, vv d < n + 1 := fun d hd => by have := hle d hd; omega
  have top : ∀ k, ¬ 7 ∣ k → ∀ d ∈ S, vv d = n → GridOK (n + 1) k d := fun k hk d hd hv => by
    rw [gridOK_vv (hpos d hd) (hlt d hd), show n + 1 - vv d = 1 by omega]
    exact gridOK_one (vv_spec (hpos d hd)).2 hk
  have fin : ∀ k, ¬ 7 ∣ k → (∀ d ∈ S, GridOK (n + 1 - vv d) k (mm d)) → GridG S := fun k hk h =>
    ⟨n + 1, k, by omega, hk, fun d hd => (gridOK_vv (hpos d hd) (hlt d hd)).mpr (h d hd)⟩
  have unitv : ∀ d ∈ S, vv d = 0 → ¬ 7 ∣ d := fun d hd h => (vv_zero_iff (hpos d hd)).mp h
  by_cases big : ∃ d ∈ S, vv d < n ∧ 4 ≤ (S.filter fun e' => vv e' = vv d).card
  · obtain ⟨d0, hd0, hd0n, h4⟩ := big
    set v := vv d0 with hvdef
    set A := S.filter fun e' => vv e' = v with hA
    have hAS : A ⊆ S := Finset.filter_subset _ _
    have heA : e ∉ A := fun h => by have := (Finset.mem_filter.mp h).2; omega
    by_cases hv0 : v = 0
    · -- four or five units
      set Mid := S.filter fun d => 1 ≤ vv d ∧ vv d < n with hMid
      have hMS : Mid ⊆ S := Finset.filter_subset _ _
      have hdis : Disjoint A Mid := by
        rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
      have heAM : e ∉ A ∪ Mid := by
        rw [Finset.mem_union]; push Not
        exact ⟨heA, fun h => by have := (Finset.mem_filter.mp h).2; omega⟩
      have hcnt := card_one_more hAS hMS hdis he heAM
      have hu : ∀ u ∈ A, ¬ 7 ∣ u := fun u hu' => unitv u (hAS hu') (by rw [(Finset.mem_filter.mp hu').2, hv0])
      have hAne : A.Nonempty := ⟨u0, Finset.mem_filter.mpr ⟨hu0, by rw [hu0v, hv0]⟩⟩
      rcases Mid.eq_empty_or_nonempty with hM0 | ⟨z, hz⟩
      · obtain ⟨k, hk, hkA⟩ := units_all hU5 (show 3 ≤ n + 1 by omega) (by omega) hu
        refine ⟨n + 1, k, by omega, hk, fun d hd => ?_⟩
        by_cases hdA : d ∈ A
        · exact hkA d hdA
        · have hv : vv d ≠ 0 := fun h => hdA (Finset.mem_filter.mpr ⟨hd, by rw [h, hv0]⟩)
          have hnm : d ∉ Mid := by rw [hM0]; simp
          have : vv d = n := by
            by_contra hne
            exact hnm (Finset.mem_filter.mpr ⟨hd, by have := hle d hd; omega, by have := hle d hd; omega⟩)
          exact top k hk d hd this
      · obtain ⟨hzS, hz1, hzn⟩ := Finset.mem_filter.mp hz
        have hMc : Mid.card ≤ 1 := by omega
        have hzonly : ∀ d ∈ S, 1 ≤ vv d → vv d < n → d = z := fun d hd h1 h2 =>
          Finset.card_le_one.mp hMc d (Finset.mem_filter.mpr ⟨hd, h1, h2⟩) z hz
        have hMpos : 1 ≤ Mid.card := Finset.card_pos.mpr ⟨z, hz⟩
        obtain ⟨hzeq, hzm⟩ := vv_spec (hpos z hzS)
        have hfinish : ∀ k, ¬ 7 ∣ k → (∀ u ∈ A, GridOK (n + 1) k u) → GridOK (n + 1) k z → GridG S :=
          fun k hk hkA hkz => ⟨n + 1, k, by omega, hk, fun d hd => by
            by_cases hdA : d ∈ A
            · exact hkA d hdA
            · have hv : vv d ≠ 0 := fun h => hdA (Finset.mem_filter.mpr ⟨hd, by rw [h, hv0]⟩)
              by_cases hdn : vv d = n
              · exact top k hk d hd hdn
              · rw [hzonly d hd (by omega) (by have := hle d hd; omega)]; exact hkz⟩
        by_cases hw1 : vv z = 1
        · obtain ⟨k, hk, hkA, hkz⟩ := units_val1_all hP1 (show 4 ≤ n + 1 by omega) (by omega) hAne hu hzm
          refine hfinish k hk hkA ?_
          rw [hzeq, hw1, pow_one]; exact hkz
        · obtain ⟨k, hk, hkA, hkz⟩ :=
            units_valw_all hP2 (w := vv z) (show 2 ≤ vv z by omega) (show vv z + 2 ≤ n + 1 by omega) (by omega)
              hAne hu hzm
          exact hfinish k hk hkA (by rw [hzeq]; exact hkz)
    · -- four runners of valuation v ≥ 1, one unit
      set B := S.filter fun d => vv d = 0 with hB
      have hBS : B ⊆ S := Finset.filter_subset _ _
      have hdis : Disjoint A B := by
        rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
      have heAB : e ∉ A ∪ B := by
        rw [Finset.mem_union]; push Not
        exact ⟨heA, fun h => by have := (Finset.mem_filter.mp h).2; omega⟩
      have hcnt := card_one_more hAS hBS hdis he heAB
      have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨u0, Finset.mem_filter.mpr ⟨hu0, hu0v⟩⟩
      have honly : ∀ d ∈ S, vv d ≠ 0 → vv d ≠ v → vv d = n := by
        intro d hd h0 hv
        by_contra hne
        have hdAB : d ∉ A ∪ B := by
          rw [Finset.mem_union]; push Not
          exact ⟨fun h => hv (Finset.mem_filter.mp h).2, fun h => h0 (Finset.mem_filter.mp h).2⟩
        have hde : e ≠ d := fun h => hne (h ▸ hev)
        have := card_two_more hAS hBS hdis he hd heAB hdAB hde
        omega
      set W := A.image mm with hW
      have hWc : W.card ≤ 4 := le_trans Finset.card_image_le (by omega)
      have hWu : ∀ u ∈ W, ¬ 7 ∣ u := by
        intro u hu; obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu; exact (vv_spec (hpos d (hAS hd))).2
      have hvpos : 1 ≤ v := Nat.pos_of_ne_zero hv0
      obtain ⟨k1, hk1, hk1W⟩ : ∃ k, ¬ 7 ∣ k ∧ ∀ u ∈ W, GridOK (n + 1 - v) k u := by
        by_cases hL2 : n + 1 - v = 2
        · rw [hL2]; exact units_level_two hWc hWu
        · exact units_all hU5 (by omega) (by omega) hWu
      obtain ⟨k', hk', hall⟩ := greedy_ext (fun d hd => ⟨hpos d hd, hlt d hd⟩) v (n + 1 - v) k1 (by omega)
        (by omega) hk1
        (fun d hd hge => by
          by_cases hdv : vv d = v
          · rw [hdv]; exact hk1W _ (Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hdv⟩, rfl⟩)
          · have : vv d = n := honly d hd (by omega) hdv
            rw [show n + 1 - vv d = 1 by omega]
            exact gridOK_one (vv_spec (hpos d hd)).2 hk1)
        (fun d hd hlt' => by
          have h0 : vv d = 0 := by
            by_contra h0
            by_cases hdv : vv d = v
            · omega
            · have := honly d hd h0 hdv; omega
          rw [h0]; show B.card ≤ 3; omega)
      exact fin k' hk' hall
  · push Not at big
    obtain ⟨k', hk', hall⟩ := greedy_ext (fun d hd => ⟨hpos d hd, hlt d hd⟩) n 1 1 (by omega) le_rfl
      (by norm_num)
      (fun d hd h => by
        have := hle d hd
        rw [show n + 1 - vv d = 1 by omega]; exact gridOK_one (vv_spec (hpos d hd)).2 (by norm_num))
      (fun d hd h => Nat.le_of_lt_succ (big d hd (by omega)))
    exact fin k' hk' hall

/-! ## Induction on the top valuation -/

theorem grid_below (hU5 : AbsU5) (hP1 : AbsP1) (hP2 : AbsP2) :
    ∀ n, 3 ≤ n → ∀ S : Finset ℕ, S.card ≤ 6 → (∀ d ∈ S, d ≠ 0) → (∀ d ∈ S, vv d < n) → GridG S := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro S hS hpos hv
    refine grid_nu2_of chunkAH_all chunkBH_all chunkC1_ok chunkC2_all hS (fun d hd h => ?_)
    have := (pow_dvd_iff_vv (k := 3) (hpos d hd)).mp (by norm_num; exact h)
    have := hv d hd; omega
  | succ n hn ih =>
    intro S hS hpos hv
    by_cases hall : ∀ d ∈ S, vv d < n
    · exact ih S hS hpos hall
    push Not at hall
    obtain ⟨e, he, hen⟩ := hall
    have hev : vv e = n := by have := hv e he; omega
    by_cases hu : ∃ u ∈ S, vv u = 0
    · obtain ⟨u0, hu0, hu0v⟩ := hu
      exact grid_top hU5 hP1 hP2 hn hS hpos (fun d hd => by have := hv d hd; omega) he hev hu0 hu0v
    · push Not at hu
      have h7 : ∀ d ∈ S, 7 ∣ d := fun d hd => by
        by_contra h; exact hu d hd ((vv_zero_iff (hpos d hd)).mpr h)
      obtain ⟨a, k, ha, hk, hok⟩ := ih (S.image (· / 7)) (le_trans Finset.card_image_le hS)
        (fun d' hd' => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
          obtain ⟨m, rfl⟩ := h7 d hd
          rw [Nat.mul_div_cancel_left m (by norm_num)]
          intro h0; exact hpos _ hd (by rw [h0])
        )
        (fun d' hd' => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
          obtain ⟨m, rfl⟩ := h7 d hd
          rw [Nat.mul_div_cancel_left m (by norm_num)]
          have hm0 : m ≠ 0 := fun h0 => hpos _ hd (by rw [h0])
          by_contra hge; push Not at hge
          have h1 := (pow_dvd_iff_vv hm0).mpr hge
          have h2 : 7 ^ (n + 1) ∣ 7 * m := by rw [pow_succ']; exact Nat.mul_dvd_mul_left 7 h1
          have := (pow_dvd_iff_vv (hpos _ hd)).mp h2
          have := hv _ hd; omega)
      refine ⟨a + 1, k, by omega, hk, fun d hd => ?_⟩
      obtain ⟨m, rfl⟩ := h7 d hd
      rw [gridOK_succ_seven' ha]
      exact hok m (Finset.mem_image.mpr ⟨7 * m, hd, Nat.mul_div_cancel_left m (by norm_num)⟩)

/-- **Every set of at most six positive integers is in band at a unit instant `k / 7^a`** (from the three
finite statements). -/
theorem gridG_all (hU5 : AbsU5) (hP1 : AbsP1) (hP2 : AbsP2) {S : Finset ℕ} (hS : S.card ≤ 6)
    (hpos : ∀ d ∈ S, 0 < d) : GridG S := by
  refine grid_below hU5 hP1 hP2 (S.sup id + 3) (by omega) S hS (fun d hd => (hpos d hd).ne') (fun d hd => ?_)
  have hd0 : d ≠ 0 := (hpos d hd).ne'
  have h1 : 7 ^ vv d ≤ d := Nat.le_of_dvd (hpos d hd) (by
    have := (vv_spec hd0).1; exact ⟨mm d, this⟩)
  have h2 : vv d < 7 ^ vv d := Nat.lt_pow_self (by norm_num)
  have h3 : d ≤ S.sup id := Finset.le_sup (f := id) hd
  omega

/-- **Order seven on whole numbers, on 7-adic grids** (from the three finite statements): every set of at most
six positive whole-number disparities is lonely at `1/7`, at a time `k / 7^a`. -/
theorem lonely_seven_nat_grid (hU5 : AbsU5) (hP1 : AbsP1) (hP2 : AbsP2) (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hcard : S.card ≤ 6) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨a, k, ha, hk, hok⟩ := gridG_all hU5 hP1 hP2 hcard hpos
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero 7))
  refine ⟨(k : ℝ) / 7 ^ a, by positivity, fun d hd => ?_⟩
  have := lonely_of_grid ha (fun d hd => hok d hd) d hd
  simpa [one_div] using this

end LRC.O7All
