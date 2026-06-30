import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5b
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas7_9
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas10_12
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Case_A5_Lambda0

/-!
# n = 7 (Barajas–Serra) — §6, the case `|A| = 5`

Source: `sources_barajas_serra_2008.txt`, lines 507–830 (§6, `m > 1`) and 786–805
(§7, `m = 1`). The involved case: five elements coprime to 7.

This file states the master theorem `five_band` (the 5-element analogue of
`four_band`) and reduces it, via normalization to residues `{1,2,4}` and the
q-avoidance bridge `band_of_qz_ne`, to the §6/§7 case analysis `five_avoid`.

Subcases on the structure of `A₁` (and `A₂`, `A₄`), using Lemmas 10–12:
- **6.1 `|A₁| = 5`** (L507) + Lemma 10 (L509) — numbering of `E = (A₁−A₁)\{0}`.
- **6.2 `|A₁| = 4`** (L547), `r(d₅) ∈ {2s,4s}`.
- **6.3 `|A₁| = 3, |A₂| = 1, |A₄| = 1`** (L565) + Lemma 11 (L569) — labeling.
- **6.4 `|A₁| = 3, |A₂| = 2`** (L665) + Lemma 12 (L667).
- **6.5 `|A₁| = 3, |A₄| = 2`** (L698).
- **6.6 `|A₁| = 2`** (L743).
- **§7 `m = 1`** (L786) — exhaustive search over `ZMod 49`/`ZMod 98`.

See `docs/n7_bs/SECTION6_PLAN.md`.
-/

open Finset

namespace IntLRC7BS

/-- **§7 (`m = 1`).** The `|A|=5`, `m=1` case: exhaustive search over `ZMod 49`
(and `ZMod 98` for the three exceptional dilation classes). BS L786–805.

**STATEMENT IS FALSE AS WRITTEN — needs redraft.**

BS §7 (L786–805) finds exactly **three** exceptional 5-element sets
`{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}` (in ZMod 49, up to unit
dilation) for which *no* unit multiplier works. These are NOT fixable by any unit
`lam` coprime to 7.

BS resolves these via a JOINT argument with the 6th element `d₆ = 7k` (the
level-1 element of `D₇(1)` in the full 6-element speed set): lifting to
`N' = 2*49 = 98`, the only remaining 3 bad `(5-set, d₆)` combinations all have
`gcd(D) ≥ 2`, which contradicts the LRC normalization `gcd(D) = 1`.

**Required redraft:** this theorem must receive `d₆ : ℤ` (the 6th element at
level 1, i.e. `7 ∣ d₆ ∧ ¬ 49 ∣ d₆`) and the coprimality constraint
`¬ ∃ p : ℕ, p.Prime ∧ (∀ i, (p : ℤ) ∣ d i) ∧ (p : ℤ) ∣ d₆` (the full gcd = 1
condition), OR the m=1 |A|=5 case must be handled jointly at the `bs_discrete_q`
dispatch level where all 6 elements are simultaneously available.

**Alternative reformulation (most Lean-compatible):** state the joint 6-element
theorem for m=1 directly: `∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i : Fin 5, qz 1 (lam * d i) ≠ 0 ∧ qz 1 (lam * d i) ≠ 6 ∧ qz 1 (lam * d₆) ≠ 0 ∧ qz 1 (lam * d₆) ≠ 6`
over `ZMod 98` with the gcd=1 constraint. This is a single computable `decide`
over a finite search space (968 valid + 3 resolved-by-gcd cases).

See `docs/n7_bs/SECTION6_PLAN.md` for details. -/
theorem five_avoid_m1 (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz 1 (lam * d i) ≠ 0 ∧ qz 1 (lam * d i) ≠ 6 := by
  sorry

/-- **Relabeling by a unit `{1,2,4}` multiplier composes.** If the `|A|=5`
conclusion holds for the dilated tuple `lam₀ · d` (with multiplier `lam`), then it
holds for `d` with multiplier `lam * lam₀`. This is the WLOG device of BS §6:
since `{1,2,4}` is the order-3 subgroup of `(ZMod 7)*`, dilating by `2` or `4`
cyclically permutes the residue classes `C₁,C₂,C₄`, letting us assume `A₁` is the
most popular class. -/
theorem five_compress_relabel (m : ℕ) (d : Fin 5 → ℤ) (lam₀ : ℤ)
    (hlam₀ : ¬ (7 : ℤ) ∣ lam₀)
    (h : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * (lam₀ * d i)) ≠ 0 ∧ qz m (lam * (lam₀ * d i)) ≠ 6) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  obtain ⟨lam, hlam, hgoal⟩ := h
  refine ⟨lam * lam₀, ?_, fun i => ?_⟩
  · intro hdvd
    have e : ((7 : ℕ) : ℤ) = (7 : ℤ) := by norm_num
    rw [← e, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd hlam hlam₀
    push_cast at hdvd
    rcases mul_eq_zero.mp hdvd with h7 | h7
    · exact hlam h7
    · exact hlam₀ h7
  · have hi := hgoal i
    rw [mul_assoc]
    exact hi

/-- Filter card permutation under unit multiplication in `ZMod 7`. If `u` maps each
residue `r' ∈ {1,2,4}` to `r` (i.e. `u * r' = r`), then the count of indices with
`q(u·dᵢ) = r` equals the count with `q(dᵢ) = r'`. -/
private theorem mul_res_perm (d : Fin 5 → ℤ)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (u : ℤ) (r r' : ZMod 7)
    (hrr' : ∀ x ∈ ({1, 2, 4} : Finset (ZMod 7)),
      ((u : ZMod 7) * x = r ↔ x = r')) :
    (Finset.univ.filter (fun i : Fin 5 => ((u * d i : ℤ) : ZMod 7) = r)).card
    = (Finset.univ.filter (fun i : Fin 5 => (d i : ZMod 7) = r')).card := by
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show ((u * d i : ℤ) : ZMod 7) = (u : ZMod 7) * (d i : ZMod 7) from by push_cast; ring]
  exact hrr' _ (hres i)

/-- Coprimality is preserved by a unit dilation: `¬ 7 ∣ u` and `¬ 7 ∣ dᵢ` ⇒
`¬ 7 ∣ u·dᵢ` (7 prime). -/
private theorem mul_ndvd (d : Fin 5 → ℤ) (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (u : ℤ) (hu : ¬ (7 : ℤ) ∣ u) : ∀ i, ¬ (7 : ℤ) ∣ (u * d i) := by
  intro i h
  have hp : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  rcases hp.dvd_or_dvd h with h7 | h7
  · exact hu h7
  · exact hndvd i h7

/-- A nonzero dilation preserves injectivity: `dᵢ` distinct ⇒ `u·dᵢ` distinct. -/
private theorem mul_inj (d : Fin 5 → ℤ) (hinj : Function.Injective d)
    (u : ℤ) (hu : u ≠ 0) : Function.Injective (fun i => u * d i) :=
  fun _ _ h => hinj (mul_left_cancel₀ hu h)

/-- The residue set `{1,2,4}` is closed under dilation by `2` or `4` (the order-3
subgroup of `(ZMod 7)*`). -/
private theorem mul_res_mem (d : Fin 5 → ℤ)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (u : ℤ) (hu : u = 2 ∨ u = 4) :
    ∀ i, ((u * d i : ℤ) : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
  intro i
  rw [show ((u * d i : ℤ) : ZMod 7) = (u : ZMod 7) * (d i : ZMod 7) from by push_cast; ring]
  have h := hres i
  rcases hu with rfl | rfl <;>
    (simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
     rcases h with h | h | h <;> rw [h] <;> decide)

/- The seven §6 representative cases: five integers coprime to 7, residues in
`{1,2,4}`, with a fixed `(n₁,n₂,n₄)` residue-class partition. Each case theorem
fixes the three card values. -/
section Repr
variable (m : ℕ) (d : Fin 5 → ℤ)

/-- **Case 6.1 `(5,0,0)`** (BS L507). `|A₁| = 5`. Labeling via Lemma 10, then
`ℓ(A₁) ≤ 5` by Lemma 9 / Remark 8(i), closed by Lemma 5 (`five_lambda0`). -/
private theorem case_61 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =5)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.2 `(4,1,0)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₂`. Labeling via Lemma 10;
`ℓ(A₁) ≤ 4` then Lemma 6(i) `lemma6_510` with `ẽ(d₄,d₅) ∉ {2,3}` from Lemma 7. -/
private theorem case_62a (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

set_option maxRecDepth 4000 in
/-- **`(4,0,1)` branch (i) avoidance core.** After `lemma9_i_dispatch` compresses
3 of the 4 `A₁` arcs to a 2-window `{a,a+1}`, the 4th `A₁` arc `v₄` and the lone
`A₄` arc `q₄` (residue `4`, shift coefficient `4·k'`) can always be jointly
avoided by some shift `k'`. Exhaustive `decide` over `ZMod 7` (reduced to 3 free
variables: the shift `k` and residue `r` collapse to a single `k' = k·r`). -/
private theorem avoid_62b_branch_i (a v₄ q₄ : ZMod 7) :
    ∃ k' : ZMod 7,
      a + k' ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k' ∉ ({0, 6} : Finset (ZMod 7)) ∧
      v₄ + k' ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₄ + 4 * k' ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert a v₄ q₄; decide

set_option maxRecDepth 4000 in
/-- **`(4,0,1)` branch (ii), `h=m`, ratio-`{3,4}` avoidance core.** After an
affine `r⁻¹`-dilation places the 4 `A₁` arcs at a contiguous window `{a,…,a+3}`,
the lone `A₄` arc `q₄` (residue `4`) can be jointly avoided by some shift `k'`. -/
private theorem avoid_62b_branch_ii_m (a q₄ : ZMod 7) :
    ∃ k' : ZMod 7,
      (∀ j : Fin 4, a + (j.val : ZMod 7) + k' ∉ ({0, 6} : Finset (ZMod 7))) ∧
      q₄ + 4 * k' ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert a q₄; decide

set_option maxHeartbeats 800000 in
/-- **Case 6.2 `(4,0,1)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₄`. Labeling via Lemma 10;
`ℓ(A₁) ≤ 4` then Lemma 5 with `(4,0,1)` partition. -/
private theorem case_62b (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  -- Extract S₁ (4 elements, residue 1) and S₄ (1 element, residue 4).
  set S₁ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1) with hS₁_def
  set S₄ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4) with hS₄_def
  -- Enumerate A₁ via orderIsoOfFin; b₁ is the A₁-restriction.
  set g₁ : Fin 4 → Fin 5 := fun k => (S₁.orderIsoOfFin hC₁ k).val
  have hg₁_res : ∀ k, (d (g₁ k) : ZMod 7) = 1 := fun k => by
    have := (S₁.orderIsoOfFin hC₁ k).prop
    simp only [hS₁_def, mem_filter, mem_univ, true_and] at this; exact this
  have hg₁_inj : Function.Injective g₁ :=
    fun a b h => (S₁.orderIsoOfFin hC₁).injective (Subtype.val_injective h)
  set b₁ : Fin 4 → ℤ := fun k => d (g₁ k)
  have hb₁_inj : Function.Injective b₁ := fun a b h => hg₁_inj (hinj h)
  -- Extract the unique A₄-element i₄.
  obtain ⟨i₄, hS₄sing⟩ := Finset.card_eq_one.mp hC₄
  have hi₄_res : (d i₄ : ZMod 7) = 4 := by
    have : i₄ ∈ S₄ := by rw [hS₄sing]; exact mem_singleton_self _
    simp only [hS₄_def, mem_filter, mem_univ, true_and] at this; exact this
  -- Every d i of residue 1 is b₁ k for some k.
  have hA₁_cover : ∀ i : Fin 5, (d i : ZMod 7) = 1 → ∃ k : Fin 4, g₁ k = i :=
    fun i hi =>
      ⟨(S₁.orderIsoOfFin hC₁).symm ⟨i, by simp [hS₁_def, hi]⟩,
       congr_arg Subtype.val
         ((S₁.orderIsoOfFin hC₁).right_inv ⟨i, by simp [hS₁_def, hi]⟩)⟩
  -- Every index is either an A₁-element (= g₁ k₀) or the A₄-element i₄ (hC₂ = 0
  -- rules out residue 2). Shared dichotomy used by all branches below.
  have hi_dichotomy : ∀ i : Fin 5, (∃ k₀ : Fin 4, g₁ k₀ = i) ∨ i = i₄ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h1 | h2 | h4
    · exact Or.inl (hA₁_cover i h1)
    · exfalso
      have hmem : i ∈ univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2) := by
        simp [h2]
      rw [Finset.card_eq_zero.mp hC₂] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    · refine Or.inr ?_
      have hi_mem : i ∈ S₄ := by
        simp only [hS₄_def, mem_filter, mem_univ, true_and]; exact h4
      rwa [hS₄sing, Finset.mem_singleton] at hi_mem
  -- Apply Lemma 10 to b₁ : Fin 4 → ℤ.
  obtain ⟨e₁, e₂, e₃, e₄, hperm, h_struct⟩ := lemma10 b₁ hb₁_inj
  -- hperm: ∀ f, {f e₁,..,f e₄} = {f (b₁ 0),..,f (b₁ 3)}  (so arcs of e's = arcs of A₁)
  rcases h_struct with
      -- (i) e₂−e₁ and e₃−e₁ at DISTINCT 7-adic levels h₁ ≠ h₂
      ⟨h₁, h₂, hne, hd2, hd2', hd3, hd3'⟩ |
      -- (ii) all three differences at the SAME level h; r₃ = 2r₂; r₄ ∈ {3r₂, 4r₂}
      ⟨h, hd2, hd2', hd3, hd3', hd4, hd4', hr32, hr41⟩
  · -- ── Branch (i): L9(i) dispatch compresses {e₁,e₂,e₃} to ℓ(B) ≤ 2.
    -- BS §6.2 L547–L553: q(e₄) ≠ 3 → ℓ(A₁) ≤ 4; q(e₄) = 3 → ×2 → ℓ ≤ 4.
    -- In both cases five_lambda0 (4,0,1) closes.
    obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
      lemma9_i_dispatch m h₁ h₂ e₂ e₃ e₁ hne hd2 hd2' hd3 hd3'
    -- hB_fit : fitsInterval {q(lam₀·e₂), q(lam₀·e₃), q(lam₀·e₁)} a 2
    obtain ⟨k', hka, hka1, hkv₄, hkq₄⟩ :=
      avoid_62b_branch_i a (qz m (lam₀ * e₄)) (qz m (lam₀ * d i₄))
    have hr₀_ne : (lam₀ : ZMod 7) ≠ 0 := by
      intro hr₀
      apply hlam₀
      have e : ((7 : ℕ) : ℤ) = (7 : ℤ) := by norm_num
      rw [← e, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hr₀
    refine five_compress_relabel m d lam₀ hlam₀ ?_
    refine lambda0_lift m (by omega) (fun i => lam₀ * d i) (k' * (lam₀ : ZMod 7)⁻¹) (fun i => ?_)
    have hcast : ((lam₀ * d i : ℤ) : ZMod 7) = (lam₀ : ZMod 7) * (d i : ZMod 7) := by
      push_cast; ring
    have halg : (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ * d i : ℤ) : ZMod 7) = k' * (d i : ZMod 7) := by
      rw [hcast,
        show (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ : ZMod 7) * (d i : ZMod 7))
            = k' * ((lam₀ : ZMod 7)⁻¹ * (lam₀ : ZMod 7)) * (d i : ZMod 7) from by ring,
        inv_mul_cancel₀ hr₀_ne]
      ring
    rw [halg]
    rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
    · -- A₁ element: i = g₁ k₀, residue 1.
      subst hk₀
      rw [hg₁_res k₀, mul_one]
      show qz m (lam₀ * b₁ k₀) + k' ∉ ({0, 6} : Finset (ZMod 7))
      have hmem : qz m (lam₀ * b₁ k₀) ∈
          ({qz m (lam₀ * e₁), qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₄)}
            : Finset (ZMod 7)) := by
        rw [hperm (fun x => qz m (lam₀ * x))]
        fin_cases k₀ <;> simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have he1 : qz m (lam₀ * e₁) = a ∨ qz m (lam₀ * e₁) = a + 1 := by
        obtain ⟨j, hj⟩ := hB_fit (qz m (lam₀ * e₁)) (by simp)
        fin_cases j <;> simp_all
      have he2 : qz m (lam₀ * e₂) = a ∨ qz m (lam₀ * e₂) = a + 1 := by
        obtain ⟨j, hj⟩ := hB_fit (qz m (lam₀ * e₂)) (by simp)
        fin_cases j <;> simp_all
      have he3 : qz m (lam₀ * e₃) = a ∨ qz m (lam₀ * e₃) = a + 1 := by
        obtain ⟨j, hj⟩ := hB_fit (qz m (lam₀ * e₃)) (by simp)
        fin_cases j <;> simp_all
      rcases hmem with h1 | h2 | h3 | h4
      · rcases he1 with h | h <;> rw [h1, h] <;> [exact hka; exact hka1]
      · rcases he2 with h | h <;> rw [h2, h] <;> [exact hka; exact hka1]
      · rcases he3 with h | h <;> rw [h3, h] <;> [exact hka; exact hka1]
      · rw [h4]; exact hkv₄
    · -- A₄ element: i = i₄, residue 4.
      subst hi
      rw [hi₄_res, mul_comm k' 4]
      exact hkq₄
  · -- ── Branch (ii): same level h; ratio 2 for e₃-e₁; ratio 3 or 4 for e₄-e₁.
    rcases hr41 with hr3 | hr4
    · -- (ii.1) ratio 3: r(e₄-e₁) = 3·r(e₂-e₁).
      by_cases hheq : h = m
      · -- h = m: r⁻¹-dilation sends A₁ arcs to {a, a+1, a+2, a+3}.
        -- Rewrite h → m in the hypotheses that need it (avoids subst direction issues).
        rw [hheq] at hd2 hd2' hd3 hd4 hr32 hr3
        -- r = leading coeff of e₂-e₁ at level m; nonzero by hd2'.
        set r : ZMod 7 := (((e₂ - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd2
          have hdiv : (e₂ - e₁) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd2' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        -- Integer representative of r⁻¹.
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ)
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by
          simp [u_int, Int.cast_natCast, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          have h2 : r⁻¹ = (0 : ZMod 7) := hu_cast ▸ h1
          exact hr_ne (inv_eq_zero.mp h2)
        -- Arc of e₁ is a_m (definition).
        set a_m : ZMod 7 := qz m (u_int * e₁)
        -- Arc of e₂ = a_m + 1 (r⁻¹·r = 1).
        have hqe2 : qz m (u_int * e₂) = a_m + 1 := by
          rw [qz_top_affine m u_int e₂ e₁ hd2, hu_cast, ← hr_def, inv_mul_cancel₀ hr_ne]
        -- Arc of e₃ = a_m + 2 (r⁻¹·(2r) = 2).
        have hqe3 : qz m (u_int * e₃) = a_m + 2 := by
          rw [qz_top_affine m u_int e₃ e₁ hd3, hu_cast, hr32]
          congr 1
          rw [show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        -- Arc of e₄ = a_m + 3 (r⁻¹·(3r) = 3).
        have hqe4 : qz m (u_int * e₄) = a_m + 3 := by
          rw [qz_top_affine m u_int e₄ e₁ hd4, hu_cast, hr3]
          congr 1
          rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        -- Avoidance: shift s' moves all 4 A₁ arcs and A₄ arc outside {0,6}.
        obtain ⟨s', hs'_A₁, hs'_A₄⟩ := avoid_62b_branch_ii_m a_m (qz m (u_int * d i₄))
        -- Compose u_int into lam, then apply lambda0_lift with shift s'·r.
        refine five_compress_relabel m d u_int hu_ndvd ?_
        refine lambda0_lift m (by omega) (fun i => u_int * d i) (s' * r) (fun i => ?_)
        -- Reduce shift: (s'·r)·(u_int·d i : ZMod7) = s'·(d i : ZMod7).
        have halg : (s' * r) * ((u_int * d i : ℤ) : ZMod 7) = s' * (d i : ZMod 7) := by
          have hcast : ((u_int * d i : ℤ) : ZMod 7) = r⁻¹ * (d i : ZMod 7) := by
            push_cast; rw [hu_cast]
          rw [hcast, show (s' * r) * (r⁻¹ * (d i : ZMod 7)) = s' * (r * r⁻¹) * (d i : ZMod 7)
              from by ring, mul_inv_cancel₀ hr_ne]
          ring
        rw [halg]
        rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
        · -- A₁ element: residue 1, so shift contribution = s'·1 = s'.
          subst hk₀
          rw [hg₁_res k₀, mul_one]
          show qz m (u_int * b₁ k₀) + s' ∉ ({0, 6} : Finset (ZMod 7))
          -- Arc of b₁ k₀ lands in {a_m, a_m+1, a_m+2, a_m+3}.
          have hmem : qz m (u_int * b₁ k₀) ∈
              ({a_m, a_m + 1, a_m + 2, a_m + 3} : Finset (ZMod 7)) := by
            have hmem' : qz m (u_int * b₁ k₀) ∈
                ({a_m, qz m (u_int * e₂), qz m (u_int * e₃), qz m (u_int * e₄)}
                  : Finset (ZMod 7)) := by
              have := hperm (fun x => qz m (u_int * x))
              rw [this]; fin_cases k₀ <;> simp
            rwa [hqe2, hqe3, hqe4] at hmem'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2 | h3 | h4
          · rw [h1]; simpa using hs'_A₁ ⟨0, by omega⟩
          · rw [h2]; exact hs'_A₁ ⟨1, by omega⟩
          · rw [h3]; exact hs'_A₁ ⟨2, by omega⟩
          · rw [h4]; exact hs'_A₁ ⟨3, by omega⟩
        · -- A₄ element: residue 4, shift contribution = s'·4.
          subst hi
          rw [hi₄_res, show s' * 4 = 4 * s' from by ring]
          exact hs'_A₄
      · -- h ≠ m: split h < m (lemma9_ii_j2 route) vs h > m (all arcs coincide).
        rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: lemma9_ii_j2 on B={e₁,e₂,e₃} with ratio-2 → 2-window.
          -- Same close as branch (i): avoid_62b_branch_i + five_compress_relabel.
          -- All e_j have residue 1: they're in the image of b₁ (all residue 1 by hg₁_res).
          have hb₁_all_1 : ∀ k : Fin 4, (b₁ k : ZMod 7) = 1 := hg₁_res
          have he_res_aux : ∀ x : ZMod 7, x ∈ ({(b₁ 0:ZMod 7),(b₁ 1:ZMod 7),(b₁ 2:ZMod 7),(b₁ 3:ZMod 7)} : Finset _) → x = 1 := by
            intro x hx
            simp only [hb₁_all_1 0, hb₁_all_1 1, hb₁_all_1 2, hb₁_all_1 3,
                       Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h | h | h <;> exact h
          have he₁_res : (e₁ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          have he₂_res : (e₂ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          have he₃_res : (e₃ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt e₂ e₃ e₁
              (he₂_res.trans he₁_res.symm) (he₃_res.trans he₁_res.symm)
              hd2 hd2' hd3 hd3' hr32
          obtain ⟨k', hka, hka1, hkv₄, hkq₄⟩ :=
            avoid_62b_branch_i a (qz m (lam₀ * e₄)) (qz m (lam₀ * d i₄))
          have hr₀_ne : (lam₀ : ZMod 7) ≠ 0 := by
            intro hr₀; apply hlam₀
            rw [← show ((7 : ℕ) : ℤ) = (7 : ℤ) from by norm_num,
                ← ZMod.intCast_zmod_eq_zero_iff_dvd]
            exact hr₀
          refine five_compress_relabel m d lam₀ hlam₀ ?_
          refine lambda0_lift m (by omega) (fun i => lam₀ * d i)
              (k' * (lam₀ : ZMod 7)⁻¹) (fun i => ?_)
          have hcast : ((lam₀ * d i : ℤ) : ZMod 7) = (lam₀ : ZMod 7) * (d i : ZMod 7) := by
            push_cast; ring
          have halg : (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ * d i : ℤ) : ZMod 7) =
              k' * (d i : ZMod 7) := by
            rw [hcast,
              show (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ : ZMod 7) * (d i : ZMod 7))
                  = k' * ((lam₀ : ZMod 7)⁻¹ * (lam₀ : ZMod 7)) * (d i : ZMod 7) from by ring,
              inv_mul_cancel₀ hr₀_ne]; ring
          rw [halg]
          rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
          · subst hk₀; rw [hg₁_res k₀, mul_one]
            show qz m (lam₀ * b₁ k₀) + k' ∉ ({0, 6} : Finset (ZMod 7))
            have hmem : qz m (lam₀ * b₁ k₀) ∈
                ({qz m (lam₀ * e₁), qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₄)}
                  : Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m (lam₀ * x))]; fin_cases k₀ <;> simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            have hfit_aux : ∀ v : ZMod 7, v ∈ ({qz m (lam₀*e₂), qz m (lam₀*e₃), qz m (lam₀*e₁)} : Finset _) →
                v = a ∨ v = a + 1 := by
              intro v hv
              obtain ⟨j, hj⟩ := hB_fit v hv
              fin_cases j
              · exact Or.inl (by simpa using hj)
              · exact Or.inr hj
            have he1 : qz m (lam₀ * e₁) = a ∨ qz m (lam₀ * e₁) = a + 1 :=
              hfit_aux _ (by simp)
            have he2 : qz m (lam₀ * e₂) = a ∨ qz m (lam₀ * e₂) = a + 1 :=
              hfit_aux _ (by simp)
            have he3 : qz m (lam₀ * e₃) = a ∨ qz m (lam₀ * e₃) = a + 1 :=
              hfit_aux _ (by simp)
            rcases hmem with h1 | h2 | h3 | h4
            · rcases he1 with h | h <;> rw [h1, h] <;> [exact hka; exact hka1]
            · rcases he2 with h | h <;> rw [h2, h] <;> [exact hka; exact hka1]
            · rcases he3 with h | h <;> rw [h3, h] <;> [exact hka; exact hka1]
            · rw [h4]; exact hkv₄
          · subst hi; rw [hi₄_res, mul_comm k' 4]; exact hkq₄
        · -- h > m: 7^(m+1) ∣ all A₁ differences → qz m arcs coincide.
          -- ℓ(A₁) = 1, so avoid_62b_branch_ii_m closes directly (j=0 shift).
          have hqe_eq : ∀ j : ℤ, (7 : ℤ) ^ h ∣ (j - e₁) → qz m j = qz m e₁ := by
            intro j hjdvd
            have hd_m : (7 : ℤ) ^ m ∣ (j - e₁) :=
              dvd_trans (pow_dvd_pow 7 (by omega : m ≤ h)) hjdvd
            have hcoeff0 : (((j - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) = 0 := by
              rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
              obtain ⟨c, hc⟩ := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h)) hjdvd
              refine ⟨c, ?_⟩
              have hc' : j - e₁ = (7 : ℤ) ^ m * (7 * c) := by rw [hc, pow_succ]; ring
              calc (j - e₁) / (7 : ℤ) ^ m
                  = ((7 : ℤ) ^ m * (7 * c)) / (7 : ℤ) ^ m := by rw [hc']
                _ = 7 * c := Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num))
            have heq := qz_top_affine m 1 j e₁ hd_m
            simp only [one_mul, Int.cast_one, hcoeff0, mul_zero, add_zero] at heq
            exact heq
          have hqe2 : qz m e₂ = qz m e₁ := hqe_eq e₂ hd2
          have hqe3 : qz m e₃ = qz m e₁ := hqe_eq e₃ hd3
          have hqe4 : qz m e₄ = qz m e₁ := hqe_eq e₄ hd4
          -- State in terms of d (g₁ k) so rw works cleanly in the goal.
          have hbk_arc : ∀ k : Fin 4, qz m (d (g₁ k)) = qz m e₁ := fun k => by
            have hmem : qz m (d (g₁ k)) ∈
                ({qz m e₁, qz m e₂, qz m e₃, qz m e₄} : Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m x)]
              fin_cases k <;>
                simp [show (b₁ : Fin 4 → ℤ) = fun k => d (g₁ k) from rfl]
            rw [hqe2, hqe3, hqe4] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h | h <;> exact h
          obtain ⟨s', hs'_A₁, hs'_A₄⟩ := avoid_62b_branch_ii_m (qz m e₁) (qz m (d i₄))
          refine lambda0_lift m (by omega) d s' (fun i => ?_)
          rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
          · subst hk₀; rw [hg₁_res k₀, mul_one, hbk_arc k₀]
            have h_aux := hs'_A₁ (0 : Fin 4)
            simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h_aux
            exact h_aux
          · subst hi; rw [hi₄_res, mul_comm s' 4]; exact hs'_A₄
    · -- (ii.2) ratio 4: r(e₄-e₁) = 4·r(e₂-e₁).
      -- h<m and h>m: IDENTICAL to (ii.1) h≠m (lemma9_ii_j2 uses only the ratio-2
      -- pair {e₂,e₃,e₁}; e₄ with ratio-4 is handled by avoid_62b_branch_i).
      -- h=m: arcs at {a_m,a_m+1,a_m+2,a_m+4} (length-5 window, not contiguous);
      --       need Lemma 7 applied to (2d₄, d₅) pair + lemma6_501 to close.
      by_cases hheq : h = m
      · -- h = m, ratio 4: TODO (requires Lemma 7 for ẽ(d4,d5) control + lemma6_501).
        sorry
      · -- h ≠ m: split h < m (lemma9_ii_j2 route) vs h > m (all arcs coincide).
        -- Proof is IDENTICAL to branch (ii.1) h≠m — ratio-4 only differs at h=m.
        rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: lemma9_ii_j2 on B={e₂,e₃,e₁} with ratio-2 → 2-window.
          have hb₁_all_1 : ∀ k : Fin 4, (b₁ k : ZMod 7) = 1 := hg₁_res
          have he_res_aux : ∀ x : ZMod 7, x ∈ ({(b₁ 0:ZMod 7),(b₁ 1:ZMod 7),(b₁ 2:ZMod 7),(b₁ 3:ZMod 7)} : Finset _) → x = 1 := by
            intro x hx
            simp only [hb₁_all_1 0, hb₁_all_1 1, hb₁_all_1 2, hb₁_all_1 3,
                       Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with h | h | h | h <;> exact h
          have he₁_res : (e₁ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          have he₂_res : (e₂ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          have he₃_res : (e₃ : ZMod 7) = 1 := he_res_aux _ (by
            rw [← hperm (fun x => (x : ZMod 7))]; simp)
          obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt e₂ e₃ e₁
              (he₂_res.trans he₁_res.symm) (he₃_res.trans he₁_res.symm)
              hd2 hd2' hd3 hd3' hr32
          obtain ⟨k', hka, hka1, hkv₄, hkq₄⟩ :=
            avoid_62b_branch_i a (qz m (lam₀ * e₄)) (qz m (lam₀ * d i₄))
          have hr₀_ne : (lam₀ : ZMod 7) ≠ 0 := by
            intro hr₀; apply hlam₀
            rw [← show ((7 : ℕ) : ℤ) = (7 : ℤ) from by norm_num,
                ← ZMod.intCast_zmod_eq_zero_iff_dvd]
            exact hr₀
          refine five_compress_relabel m d lam₀ hlam₀ ?_
          refine lambda0_lift m (by omega) (fun i => lam₀ * d i)
              (k' * (lam₀ : ZMod 7)⁻¹) (fun i => ?_)
          have hcast : ((lam₀ * d i : ℤ) : ZMod 7) = (lam₀ : ZMod 7) * (d i : ZMod 7) := by
            push_cast; ring
          have halg : (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ * d i : ℤ) : ZMod 7) =
              k' * (d i : ZMod 7) := by
            rw [hcast,
              show (k' * (lam₀ : ZMod 7)⁻¹) * ((lam₀ : ZMod 7) * (d i : ZMod 7))
                  = k' * ((lam₀ : ZMod 7)⁻¹ * (lam₀ : ZMod 7)) * (d i : ZMod 7) from by ring,
              inv_mul_cancel₀ hr₀_ne]; ring
          rw [halg]
          rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
          · subst hk₀; rw [hg₁_res k₀, mul_one]
            show qz m (lam₀ * b₁ k₀) + k' ∉ ({0, 6} : Finset (ZMod 7))
            have hmem : qz m (lam₀ * b₁ k₀) ∈
                ({qz m (lam₀ * e₁), qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₄)}
                  : Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m (lam₀ * x))]; fin_cases k₀ <;> simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            have hfit_aux : ∀ v : ZMod 7, v ∈ ({qz m (lam₀*e₂), qz m (lam₀*e₃), qz m (lam₀*e₁)} : Finset _) →
                v = a ∨ v = a + 1 := by
              intro v hv
              obtain ⟨j, hj⟩ := hB_fit v hv
              fin_cases j
              · exact Or.inl (by simpa using hj)
              · exact Or.inr hj
            have he1 : qz m (lam₀ * e₁) = a ∨ qz m (lam₀ * e₁) = a + 1 :=
              hfit_aux _ (by simp)
            have he2 : qz m (lam₀ * e₂) = a ∨ qz m (lam₀ * e₂) = a + 1 :=
              hfit_aux _ (by simp)
            have he3 : qz m (lam₀ * e₃) = a ∨ qz m (lam₀ * e₃) = a + 1 :=
              hfit_aux _ (by simp)
            rcases hmem with h1 | h2 | h3 | h4
            · rcases he1 with h | h <;> rw [h1, h] <;> [exact hka; exact hka1]
            · rcases he2 with h | h <;> rw [h2, h] <;> [exact hka; exact hka1]
            · rcases he3 with h | h <;> rw [h3, h] <;> [exact hka; exact hka1]
            · rw [h4]; exact hkv₄
          · subst hi; rw [hi₄_res, mul_comm k' 4]; exact hkq₄
        · -- h > m: all A₁ arcs coincide at qz m e₁ (7^(m+1) ∣ all differences).
          have hqe_eq : ∀ j : ℤ, (7 : ℤ) ^ h ∣ (j - e₁) → qz m j = qz m e₁ := by
            intro j hjdvd
            have hd_m : (7 : ℤ) ^ m ∣ (j - e₁) :=
              dvd_trans (pow_dvd_pow 7 (by omega : m ≤ h)) hjdvd
            have hcoeff0 : (((j - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) = 0 := by
              rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
              obtain ⟨c, hc⟩ := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h)) hjdvd
              refine ⟨c, ?_⟩
              have hc' : j - e₁ = (7 : ℤ) ^ m * (7 * c) := by rw [hc, pow_succ]; ring
              calc (j - e₁) / (7 : ℤ) ^ m
                  = ((7 : ℤ) ^ m * (7 * c)) / (7 : ℤ) ^ m := by rw [hc']
                _ = 7 * c := Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num))
            have heq := qz_top_affine m 1 j e₁ hd_m
            simp only [one_mul, Int.cast_one, hcoeff0, mul_zero, add_zero] at heq
            exact heq
          have hqe2 : qz m e₂ = qz m e₁ := hqe_eq e₂ hd2
          have hqe3 : qz m e₃ = qz m e₁ := hqe_eq e₃ hd3
          have hqe4 : qz m e₄ = qz m e₁ := hqe_eq e₄ hd4
          have hbk_arc : ∀ k : Fin 4, qz m (d (g₁ k)) = qz m e₁ := fun k => by
            have hmem : qz m (d (g₁ k)) ∈
                ({qz m e₁, qz m e₂, qz m e₃, qz m e₄} : Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m x)]
              fin_cases k <;>
                simp [show (b₁ : Fin 4 → ℤ) = fun k => d (g₁ k) from rfl]
            rw [hqe2, hqe3, hqe4] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h | h <;> exact h
          obtain ⟨s', hs'_A₁, hs'_A₄⟩ := avoid_62b_branch_ii_m (qz m e₁) (qz m (d i₄))
          refine lambda0_lift m (by omega) d s' (fun i => ?_)
          rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
          · subst hk₀; rw [hg₁_res k₀, mul_one, hbk_arc k₀]
            have h_aux := hs'_A₁ (0 : Fin 4)
            simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h_aux
            exact h_aux
          · subst hi; rw [hi₄_res, mul_comm s' 4]; exact hs'_A₄

/-- **Case 6.3 `(3,1,1)`** (BS L565). `|A₁|=3, |A₂|=|A₄|=1`. Labeling via Lemma 11
(6 subcases + q-tables), Lemma 7(i) securing the `(3,1,1)` `ẽ ∉ {2,4}` carve-out
of Lemma 5. -/
private theorem case_63 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.4 `(3,2,0)`** (BS L665). `|A₁|=3, |A₂|=2`. Labeling via Lemma 11 +
Lemma 12; `lemma6_330` endpoint. -/
private theorem case_64 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 2)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.5 `(3,0,2)`** (BS L698). `|A₁|=3, |A₄|=2`. Labeling via Lemma 11;
`lemma6_402` endpoint (symmetric to 6.4). -/
private theorem case_65 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 2) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.6 `(2,2,1)`** (BS L743). `|A₁|=2, |A₂|=2, |A₄|=1`. Self-contained:
Lemma 2 / Lemma 9(i)/(ii) compress `A₁,A₂` to `ℓ ≤ 2`, then Lemma 5; ν=m subcases
use the explicit `(a)/(b)` q-tables. -/
private theorem case_66 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =2)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 2)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

end Repr

/-- **§6 representative dispatch (`m ≥ 2`, `A₁` most popular).** After WLOG dilation,
`n₁ ≥ n₂` and `n₁ ≥ n₄`; exactly 7 partitions `(n₁,n₂,n₄)` survive, each routed to
its BS §6 case theorem (`case_61` … `case_66`). The other 14 partitions are killed
by `hpop₂/hpop₄`. -/
private theorem five_compress_repr (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (n₁ n₂ n₄ : ℕ) (hpart : n₁ + n₂ + n₄ = 5) (hpop₂ : n₂ ≤ n₁) (hpop₄ : n₄ ≤ n₁)
    (hC₁ : (Finset.univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = n₁)
    (hC₂ : (Finset.univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = n₂)
    (hC₄ : (Finset.univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = n₄) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  have hn₁5 : n₁ ≤ 5 := by omega
  have hn₂5 : n₂ ≤ 5 := by omega
  have hn₄5 : n₄ ≤ 5 := by omega
  interval_cases n₁ <;> interval_cases n₂ <;> interval_cases n₄ <;>
    first
    | (exfalso; omega)
    | exact case_61 m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_62a m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_62b m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_63 m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_64 m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_65 m d hm hndvd hres hinj hC₁ hC₂ hC₄
    | exact case_66 m d hm hndvd hres hinj hC₁ hC₂ hC₄
    -- `(2,1,2)` ties C₁=C₄ at max; a max-preserving ×2 dilation sends it to the
    -- canonical `(2,2,1)` (BS Case 6.6). new (C₁,C₂,C₄) = old (C₄,C₁,C₂) = (2,2,1).
    | (apply five_compress_relabel m d 2 (by decide)
       exact case_66 m _ hm (mul_ndvd d hndvd 2 (by decide)) (mul_res_mem d hres 2 (Or.inl rfl))
         (mul_inj d hinj 2 (by decide))
         ((mul_res_perm d hres 2 1 4 (by decide)).trans hC₄)
         ((mul_res_perm d hres 2 2 1 (by decide)).trans hC₁)
         ((mul_res_perm d hres 2 4 2 (by decide)).trans hC₂))

/-- **§6 compression (`m ≥ 2`), structured case analysis.** Five integers coprime
to 7 with residues in `{1,2,4}` admit a unit multiplier sending every arc index
`q(lam·dᵢ)` outside `{0,6}`.

The proof applies a WLOG dilation by `lam₀ ∈ {1,2,4}` (via `five_compress_relabel`)
to make the residue-1 class `C₁` the most popular, then dispatches to
`five_compress_repr` which handles the 7 representative partitions with
`n₁ ≥ n₂, n₄` (BS §6 cases 6.1–6.6). -/
theorem five_compress (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  -- Residue class partition
  set C₁ : Finset (Fin 5) := univ.filter (fun i => (d i : ZMod 7) = 1) with hC₁_def
  set C₂ : Finset (Fin 5) := univ.filter (fun i => (d i : ZMod 7) = 2) with hC₂_def
  set C₄ : Finset (Fin 5) := univ.filter (fun i => (d i : ZMod 7) = 4) with hC₄_def
  have hpart : C₁.card + C₂.card + C₄.card = 5 := by
    have hunion : C₁ ∪ C₂ ∪ C₄ = univ := by
      ext i
      simp only [hC₁_def, hC₂_def, hC₄_def, mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      have := hres i; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
    have hd12 : Disjoint C₁ C₂ := by
      simp only [hC₁_def, hC₂_def, Finset.disjoint_filter]
      intro i _ h1; rw [h1]; decide
    have hd14 : Disjoint (C₁ ∪ C₂) C₄ := by
      simp only [hC₁_def, hC₂_def, hC₄_def, Finset.disjoint_union_left, Finset.disjoint_filter]
      exact ⟨fun i _ h1 => by rw [h1]; decide, fun i _ h2 => by rw [h2]; decide⟩
    have hcard := Finset.card_union_of_disjoint hd14
    rw [Finset.card_union_of_disjoint hd12, hunion] at hcard
    simpa [Fintype.card_fin] using hcard.symm
  -- Helpers for unit-dilated tuples
  have hndvd_u : ∀ u : ℤ, ¬ (7 : ℤ) ∣ u → ∀ i, ¬ (7 : ℤ) ∣ (u * d i) :=
    fun u hu => mul_ndvd d hndvd u hu
  have hres_u : ∀ u : ℤ, u = 2 ∨ u = 4 →
      ∀ i, ((u * d i : ℤ) : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) :=
    fun u hu => mul_res_mem d hres u hu
  have hinj_u : ∀ u : ℤ, u ≠ 0 → Function.Injective (fun i => u * d i) :=
    fun u hu => mul_inj d hinj u hu
  -- WLOG: dilate to make C₁ the most popular class.
  -- ×2: (n₁,n₂,n₄) → (n₄,n₁,n₂);  ×4: (n₁,n₂,n₄) → (n₂,n₄,n₁)
  by_cases h₁₂ : C₂.card ≤ C₁.card <;> by_cases h₁₄ : C₄.card ≤ C₁.card
  · -- C₁ dominant: no dilation
    exact five_compress_repr m hm d hndvd hres hinj C₁.card C₂.card C₄.card hpart h₁₂ h₁₄
      rfl rfl rfl
  · -- C₄ > C₁ ≥ C₂: dilate by 2
    push_neg at h₁₄
    apply five_compress_relabel m d 2 (by decide)
    exact five_compress_repr m hm _ (hndvd_u 2 (by decide)) (hres_u 2 (Or.inl rfl))
      (hinj_u 2 (by decide)) C₄.card C₁.card C₂.card (by omega) (by omega) (by omega)
      (mul_res_perm d hres 2 1 4 (by decide))
      (mul_res_perm d hres 2 2 1 (by decide))
      (mul_res_perm d hres 2 4 2 (by decide))
  · -- C₂ > C₁ ≥ C₄: dilate by 4
    push_neg at h₁₂
    apply five_compress_relabel m d 4 (by decide)
    exact five_compress_repr m hm _ (hndvd_u 4 (by decide)) (hres_u 4 (Or.inr rfl))
      (hinj_u 4 (by decide)) C₂.card C₄.card C₁.card (by omega) (by omega) (by omega)
      (mul_res_perm d hres 4 1 2 (by decide))
      (mul_res_perm d hres 4 2 4 (by decide))
      (mul_res_perm d hres 4 4 1 (by decide))
  · -- Both C₂ > C₁ and C₄ > C₁: pick the larger
    push_neg at h₁₂ h₁₄
    by_cases h₂₄ : C₄.card ≤ C₂.card
    · -- C₂ ≥ C₄ > C₁: dilate by 4
      apply five_compress_relabel m d 4 (by decide)
      exact five_compress_repr m hm _ (hndvd_u 4 (by decide)) (hres_u 4 (Or.inr rfl))
        (hinj_u 4 (by decide)) C₂.card C₄.card C₁.card (by omega) h₂₄ (by omega)
        (mul_res_perm d hres 4 1 2 (by decide))
        (mul_res_perm d hres 4 2 4 (by decide))
        (mul_res_perm d hres 4 4 1 (by decide))
    · -- C₄ > C₂ > C₁: dilate by 2
      push_neg at h₂₄
      apply five_compress_relabel m d 2 (by decide)
      exact five_compress_repr m hm _ (hndvd_u 2 (by decide)) (hres_u 2 (Or.inl rfl))
        (hinj_u 2 (by decide)) C₄.card C₁.card C₂.card (by omega) (by omega) (by omega)
        (mul_res_perm d hres 2 1 4 (by decide))
        (mul_res_perm d hres 2 2 1 (by decide))
        (mul_res_perm d hres 2 4 2 (by decide))

/-- **§6/§7 core (q-avoidance form).** Five integers coprime to 7, already
normalized to residues `{1,2,4}`, admit a unit multiplier `lam` sending every
arc index `q(lam·dᵢ)` outside `{0,6}`. This is the entire `|A|=5` case analysis
(BS §6 for `m ≥ 2`, §7 for `m = 1`). Dispatches to `five_avoid_m1` (§7) and
`five_compress` (§6); the Λ₀ assembly bridge is `five_lambda0`. -/
theorem five_avoid (m : ℕ) (hm : 1 ≤ m) (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  · exact five_compress m (by omega) d hndvd hres hinj
  · interval_cases m
    · exact five_avoid_m1 d hndvd hres hinj

/-- **Master `|A| = 5` theorem (5-element analogue of `four_band`).** Five integers
coprime to 7 admit a unit multiplier `lam` placing every residue `(lam·dᵢ)_N` in
the central band `[7^m, 6·7^m]`. Proved by normalizing to residues `{1,2,4}` and
applying `band_of_qz_ne` to `five_avoid`. The single level-`m` element of `D₇` is
handled separately by `band_top` (any unit `lam` keeps it in band). -/
theorem five_band (m : ℕ) (hm : 1 ≤ m) (d : Fin 5 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i) (hpos : ∀ i, 0 < d i)
    (hinj : Function.Injective d) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  set d' : Fin 5 → ℤ := fun i => normalize7 (d i) with hd'_def
  have hd'_ndvd : ∀ i, ¬ (7 : ℤ) ∣ d' i := fun i => normalize7_ndvd _ (hnotdvd i)
  have hd'_inj : Function.Injective d' := normalize7_injOn_pos d hpos hinj
  -- It suffices to band the normalized elements (normalize7_band transports back).
  suffices h : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d' i) % 7 ^ (m + 1) ∧
      (lam * d' i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m by
    obtain ⟨lam, hlam, hband⟩ := h
    exact ⟨lam, hlam, fun i => normalize7_band m lam (d i) (hband i)⟩
  have hd'_res : ∀ i, (d' i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) :=
    fun i => normalize7_res _ (hnotdvd i)
  obtain ⟨lam, hlam, havoid⟩ := five_avoid m hm d' hd'_ndvd hd'_res hd'_inj
  exact ⟨lam, hlam, fun i => band_of_qz_ne m (lam * d' i) (havoid i).1 (havoid i).2⟩

end IntLRC7BS
