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

/-- `(2 : ZMod 7) ≠ 0` (hoisted so `decide` runs in a `let`-free context). -/
private theorem two_ne_zero_z7 : (2 : ZMod 7) ≠ 0 := by decide

/-- `(7 : ZMod 7) = 0` (hoisted: local `Fact (Nat.Prime 7)` instances block `decide`). -/
private theorem seven_eq_zero_z7 : (7 : ZMod 7) = 0 := by decide

/-- Complement of `{2,3,4,5}` in `ZMod 7` is `{0,1,6}` (the `ẽ ∈ {0,1,6}` carve-out). -/
private theorem mem_016_of_notmem_2345 (w : ZMod 7)
    (hw : w ∉ ({2, 3, 4, 5} : Finset (ZMod 7))) : w ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert hw; revert w; decide

/-- `{2,3,4,5} ∩ ({2,3,4,5}+1) = {3,4,5}` (the `hXX`-set of `lemma7_ii` for `X={2,3,4,5}`). -/
private theorem inter_2345_image_subset_345 (w : ZMod 7)
    (hw : w ∈ (({2,3,4,5} : Finset (ZMod 7)) ∩
      (({2,3,4,5} : Finset (ZMod 7)).image (· + 1)))) : w ∈ ({3,4,5} : Finset (ZMod 7)) := by
  revert hw; revert w; decide

/-- `7`-power divisibility transfers off a coprime factor: if `7 ∤ u` and `7^m ∤ X`
then `7^m ∤ u·X`. (Used to make the `hXX` premise of `close_via_L7` vacuous when the
`ẽ`-difference sits below level `m`.) -/
private theorem pow7_ndvd_mul (m : ℕ) (u X : ℤ) (hu : ¬ (7 : ℤ) ∣ u)
    (hX : ¬ (7 : ℤ) ^ m ∣ X) : ¬ (7 : ℤ) ^ m ∣ (u * X) := by
  intro hdvd
  have hp : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  have hcop : IsCoprime (u) ((7 : ℤ) ^ m) :=
    hp.irreducible.coprime_pow_of_not_dvd m hu
  exact hX (hcop.symm.dvd_of_dvd_mul_left hdvd)

set_option maxHeartbeats 1600000 in
/-- **Case 6.4 fallback endgame table (BS L693–696).** For any pair of `u`-frame
`ẽ`-arc values `t₄, t₅ ∈ {3,4,5}` there are a frame unit `c`, a doubling carry
`δ ∈ {0,1}`, and a base arc `A` such that the `A₁` arcs `{A, A+c, A+3·c}` and the
`A₂` arcs `{2·A+δ−c·t₄, 2·A+δ−c·t₅}` all avoid `{0,6}`. (One finite search covers
both of BS's `ν(e₄₅)` sub-cases — the `ν(e₄₅) = m` renaming and the degenerate
`ν(e₄₅) > m` coincidence — since the table also solves the diagonal `t₄ = t₅`.) -/
private theorem fallback_64_choice (t₄ t₅ : ZMod 7)
    (h₄ : t₄ ∈ ({3, 4, 5} : Finset (ZMod 7)))
    (h₅ : t₅ ∈ ({3, 4, 5} : Finset (ZMod 7))) :
    ∃ c δ A : ZMod 7, c ≠ 0 ∧ (δ = 0 ∨ δ = 1) ∧
      A ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + c ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 3 * c ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * A + δ - c * t₄ ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * A + δ - c * t₅ ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert h₄ h₅; revert t₄ t₅; decide

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

/-- **Λ₀ lift with an explicit shift, apex-relabeled.** Given a unit `lam₀`, a
`ZMod 7` shift `k`, and a per-index proof that the shifted arc `q(lam₀·dᵢ) + k·r(dᵢ)`
avoids `{0,6}`, compose `lam₀` and lift `k` to an integer multiplier. This is the
`five_compress_relabel ∘ lambda0_lift` two-step, packaged so the case branches only
supply the `ZMod 7` avoidance. -/
private theorem lift_shift (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ) (lam₀ : ℤ)
    (hlam₀ : ¬ (7 : ℤ) ∣ lam₀) (k : ZMod 7)
    (havoid : ∀ i, qz m (lam₀ * d i) + k * (d i : ZMod 7) ∉ ({0, 6} : Finset (ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  have hr₀_ne : (lam₀ : ZMod 7) ≠ 0 := by
    intro hr₀; apply hlam₀
    rw [← show ((7 : ℕ) : ℤ) = (7 : ℤ) from by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hr₀
  refine five_compress_relabel m d lam₀ hlam₀ ?_
  refine lambda0_lift m hm (fun i => lam₀ * d i) (k * (lam₀ : ZMod 7)⁻¹) (fun i => ?_)
  have hcast : ((lam₀ * d i : ℤ) : ZMod 7) = (lam₀ : ZMod 7) * (d i : ZMod 7) := by
    push_cast; ring
  have halg : (k * (lam₀ : ZMod 7)⁻¹) * ((lam₀ * d i : ℤ) : ZMod 7) = k * (d i : ZMod 7) := by
    rw [hcast,
      show (k * (lam₀ : ZMod 7)⁻¹) * ((lam₀ : ZMod 7) * (d i : ZMod 7))
          = k * ((lam₀ : ZMod 7)⁻¹ * (lam₀ : ZMod 7)) * (d i : ZMod 7) from by ring,
      inv_mul_cancel₀ hr₀_ne]; ring
  rw [halg]; exact havoid i

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

/-- **`(4,1,0)` 2-window endgame.** 2-window `{a,a+1}` (three `A₁` arcs), 4th `A₁`
arc `v₄ ≠ a+4`, and the `A₂` arc `q₅` (shift coefficient `2`). The excluded
antipodal `v₄ = a+4` is BS's `q(d₄) = 3` case, handled by ×2 dilation. -/
private theorem avoid_62a_2win (a v₄ q₅ : ZMod 7) (hexc : v₄ ≠ a + 4) :
    ∃ k : ZMod 7,
      a + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      v₄ + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₅ + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert hexc; revert a v₄ q₅; decide

/-- **`(4,1,0)` contiguous 4-window endgame** (`(ii.1)` `h=m`, and the doubled
antipodal case): window `{a,…,a+3}` plus a free `A₂` arc (coeff `2`).
Unconditional. -/
private theorem avoid_62a_4win (a q₅ : ZMod 7) :
    ∃ k : ZMod 7,
      a + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 2 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 3 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₅ + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert a q₅; decide

/-- **`(4,1,0)` holed 5-window endgame** (`(ii.2)` `h=m`): `A₁` arcs
`{A, A+1, A+2, A+4}`, `A₂` arc `q₅` with `ẽ(d₁,d₅) = 2A − q₅ ∉ {2,3}` (Lemma 7). -/
private theorem avoid_62a_holewin (A q₅ : ZMod 7)
    (he : 2 * A - q₅ ∉ ({2, 3} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      A + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 2 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 4 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₅ + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert he; revert A q₅; decide

set_option maxHeartbeats 1600000 in
/-- **Case 6.2 `(4,1,0)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₂`. Labeling via Lemma 10;
branch (i) / `h≠m` compress to a 2-window (`avoid_62a_2win`, ×2 dilation for the
antipode); `(ii.1)` `h=m` gives a contiguous 4-window; `(ii.2)` `h=m` gives the
holed window `{0,1,2,4}` and Lemma 7 forces `ẽ(d₁,d₅) ∉ {2,3}` (the `qz(e)=3`
carve-out is BS's `e₄₅ = 3N/7`, resolved by doubling the frame). -/
private theorem case_62a (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  -- Extract S₁ (4 elements, residue 1) and the unique A₂-element i₅.
  set S₁ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1) with hS₁_def
  set S₂ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2) with hS₂_def
  set g₁ : Fin 4 → Fin 5 := fun k => (S₁.orderIsoOfFin hC₁ k).val with hg₁_def
  have hg₁_res : ∀ k, (d (g₁ k) : ZMod 7) = 1 := fun k => by
    have := (S₁.orderIsoOfFin hC₁ k).prop
    simp only [hS₁_def, mem_filter, mem_univ, true_and] at this; exact this
  have hg₁_inj : Function.Injective g₁ :=
    fun a b h => (S₁.orderIsoOfFin hC₁).injective (Subtype.val_injective h)
  set b₁ : Fin 4 → ℤ := fun k => d (g₁ k) with hb₁_def
  have hb₁_inj : Function.Injective b₁ := fun a b h => hg₁_inj (hinj h)
  obtain ⟨i₅, hS₂sing⟩ := Finset.card_eq_one.mp hC₂
  have hi₅_res : (d i₅ : ZMod 7) = 2 := by
    have : i₅ ∈ S₂ := by rw [hS₂sing]; exact mem_singleton_self _
    simp only [hS₂_def, mem_filter, mem_univ, true_and] at this; exact this
  have hA₁_cover : ∀ i : Fin 5, (d i : ZMod 7) = 1 → ∃ k : Fin 4, g₁ k = i :=
    fun i hi =>
      ⟨(S₁.orderIsoOfFin hC₁).symm ⟨i, by simp [hS₁_def, hi]⟩,
       congr_arg Subtype.val
         ((S₁.orderIsoOfFin hC₁).right_inv ⟨i, by simp [hS₁_def, hi]⟩)⟩
  have hi_dichotomy : ∀ i : Fin 5, (∃ k₀ : Fin 4, g₁ k₀ = i) ∨ i = i₅ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h1 | h2 | h4
    · exact Or.inl (hA₁_cover i h1)
    · refine Or.inr ?_
      have hi_mem : i ∈ S₂ := by
        simp only [hS₂_def, mem_filter, mem_univ, true_and]; exact h2
      rwa [hS₂sing, Finset.mem_singleton] at hi_mem
    · exfalso
      have hmem : i ∈ univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4) := by simp [h4]
      rw [Finset.card_eq_zero.mp hC₄] at hmem
      exact absurd hmem (Finset.notMem_empty i)
  -- Apply Lemma 10 to label A₁.
  obtain ⟨e₁, e₂, e₃, e₄, hperm, h_struct⟩ := lemma10 b₁ hb₁_inj
  -- Residues: all four labels have residue 1.
  have hb₁_all_1 : ∀ k : Fin 4, (b₁ k : ZMod 7) = 1 := hg₁_res
  have he_res_aux : ∀ x : ZMod 7,
      x ∈ ({(b₁ 0 : ZMod 7), (b₁ 1 : ZMod 7), (b₁ 2 : ZMod 7), (b₁ 3 : ZMod 7)}
        : Finset _) → x = 1 := by
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
  have he₁_ndvd : ¬ (7 : ℤ) ∣ e₁ := by
    intro hdvd
    have h0 : (e₁ : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd e₁ 7).mpr hdvd
    rw [he₁_res] at h0; exact one_ne_zero h0
  have hi₅_ndvd : ¬ (7 : ℤ) ∣ d i₅ := by
    intro hdvd
    have h0 : (d i₅ : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (d i₅) 7).mpr hdvd
    rw [hi₅_res] at h0; exact two_ne_zero_z7 h0
  -- ── Shared closer: all four A₁ arcs in {a, a+1, q(lam₀·e₄)} ⇒ done. The
  --    antipodal `q(lam₀·e₄) = a+4` doubles the frame into a 4-window at 2a. ──
  have close_2win : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ a : ZMod 7,
      (∀ k₀ : Fin 4, qz m (lam₀ * b₁ k₀) ∈
        ({a, a + 1, qz m (lam₀ * e₄)} : Finset (ZMod 7))) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ a hwin
    by_cases hbad : qz m (lam₀ * e₄) = a + 4
    · -- Antipodal: double the frame; all A₁ arcs land in {2a, …, 2a+3}.
      have h2lam₀ : ¬ (7 : ℤ) ∣ (2 * lam₀) := by
        intro hdvd
        rcases hp7.dvd_mul.mp hdvd with hh | hh
        · exact absurd hh (by decide)
        · exact hlam₀ hh
      obtain ⟨k', hw0, hw1, hw2, hw3, hkq₅⟩ :=
        avoid_62a_4win (2 * a) (qz m ((2 * lam₀) * d i₅))
      refine lift_shift m (by omega) d (2 * lam₀) h2lam₀ k' (fun i => ?_)
      rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
      · subst hk₀
        rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
        have hdbl : qz m ((2 * lam₀) * b₁ k₀) = 2 * qz m (lam₀ * b₁ k₀) ∨
            qz m ((2 * lam₀) * b₁ k₀) = 2 * qz m (lam₀ * b₁ k₀) + 1 := by
          have h := qz_add_carry m (lam₀ * b₁ k₀) (lam₀ * b₁ k₀)
          rw [show lam₀ * b₁ k₀ + lam₀ * b₁ k₀ = (2 * lam₀) * b₁ k₀ from by ring] at h
          rcases h with h | h
          · exact Or.inl (by rw [h]; ring)
          · exact Or.inr (by rw [h]; ring)
        have hmem := hwin k₀
        rw [hbad] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hv | hv | hv <;> rcases hdbl with hd | hd <;> rw [hd, hv]
        · exact hw0
        · exact hw1
        · rw [show (2 : ZMod 7) * (a + 1) = 2 * a + 2 from by ring]; exact hw2
        · rw [show (2 : ZMod 7) * (a + 1) + 1 = 2 * a + 3 from by ring]; exact hw3
        · rw [show (2 : ZMod 7) * (a + 4) = 2 * a + 1 from by
            linear_combination seven_eq_zero_z7]
          exact hw1
        · rw [show (2 : ZMod 7) * (a + 4) + 1 = 2 * a + 2 from by
            linear_combination seven_eq_zero_z7]
          exact hw2
      · subst hi
        rw [hi₅_res, mul_comm k' (2 : ZMod 7)]
        exact hkq₅
    · -- Non-antipodal: direct decide.
      obtain ⟨k', hka, hka1, hkv₄, hkq₅⟩ :=
        avoid_62a_2win a (qz m (lam₀ * e₄)) (qz m (lam₀ * d i₅)) hbad
      refine lift_shift m (by omega) d lam₀ hlam₀ k' (fun i => ?_)
      rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
      · subst hk₀
        rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
        have hmem := hwin k₀
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hv | hv | hv <;> rw [hv]
        · exact hka
        · exact hka1
        · exact hkv₄
      · subst hi
        rw [hi₅_res, mul_comm k' (2 : ZMod 7)]
        exact hkq₅
  -- ── Closer from a 2-window fit on {e₂,e₃,e₁} (L9 output shape). ──
  have close_fit2 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ a : ZMod 7,
      fitsInterval ({qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₁)}
        : Finset (ZMod 7)) a 2 →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ a hB_fit
    refine close_2win lam₀ hlam₀ a (fun k₀ => ?_)
    have hfit : ∀ z ∈ ({qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₁)}
        : Finset (ZMod 7)), z = a ∨ z = a + 1 := by
      intro z hz
      obtain ⟨j, hj⟩ := hB_fit z hz
      fin_cases j
      · exact Or.inl (by simpa using hj)
      · exact Or.inr (by simpa using hj)
    have hmem : qz m (lam₀ * b₁ k₀) ∈
        ({qz m (lam₀ * e₁), qz m (lam₀ * e₂), qz m (lam₀ * e₃), qz m (lam₀ * e₄)}
          : Finset (ZMod 7)) := by
      rw [hperm (fun x => qz m (lam₀ * x))]; fin_cases k₀ <;> simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h1 | h1 | h1 | h1
    · rcases hfit (qz m (lam₀ * e₁)) (by simp) with hv | hv
      · exact Or.inl (h1.trans hv)
      · exact Or.inr (Or.inl (h1.trans hv))
    · rcases hfit (qz m (lam₀ * e₂)) (by simp) with hv | hv
      · exact Or.inl (h1.trans hv)
      · exact Or.inr (Or.inl (h1.trans hv))
    · rcases hfit (qz m (lam₀ * e₃)) (by simp) with hv | hv
      · exact Or.inl (h1.trans hv)
      · exact Or.inr (Or.inl (h1.trans hv))
    · exact Or.inr (Or.inr h1)
  -- ── Closer for h > m: all A₁ arcs coincide. ──
  have close_hgt : (7 : ℤ) ^ (m + 1) ∣ (e₂ - e₁) → (7 : ℤ) ^ (m + 1) ∣ (e₃ - e₁) →
      (7 : ℤ) ^ (m + 1) ∣ (e₄ - e₁) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro hdv2 hdv3 hdv4
    refine close_2win 1 (by norm_num) (qz m (1 * e₁)) (fun k₀ => ?_)
    have hmem : qz m (1 * b₁ k₀) ∈
        ({qz m (1 * e₁), qz m (1 * e₂), qz m (1 * e₃), qz m (1 * e₄)}
          : Finset (ZMod 7)) := by
      rw [hperm (fun x => qz m (1 * x))]; fin_cases k₀ <;> simp
    rw [qz_eq_of_high_dvd m e₂ e₁ 1 hdv2, qz_eq_of_high_dvd m e₃ e₁ 1 hdv3,
        qz_eq_of_high_dvd m e₄ e₁ 1 hdv4] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hmem
    rw [hmem]
    exact Finset.mem_insert_self _ _
  rcases h_struct with
      ⟨h₁, h₂, hne, hd2, hd2', hd3, hd3'⟩ |
      ⟨h, hd2, hd2', hd3, hd3', hd4, hd4', hr32, hr41⟩
  · -- ── Branch (i): distinct levels; L9(i) compresses {e₂,e₃,e₁} to a 2-window.
    obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
      lemma9_i_dispatch m h₁ h₂ e₂ e₃ e₁ hne hd2 hd2' hd3 hd3'
    exact close_fit2 lam₀ hlam₀ a hB_fit
  · -- ── Branch (ii): equal level h; e₃ ratio 2, e₄ ratio 3 or 4.
    rcases hr41 with hr3 | hr4
    · -- (ii.1) ratio 3 for e₄.
      by_cases hheq : h = m
      · -- h = m: r⁻¹-dilation gives the contiguous window {a_m, …, a_m+3}.
        rw [hheq] at hd2 hd2' hd3 hd4 hr32 hr3
        set r : ZMod 7 := (((e₂ - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd2
          have hdiv : (e₂ - e₁) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd2' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ) with hu_def
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by
          simp [hu_def, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          exact hr_ne (inv_eq_zero.mp (hu_cast ▸ h1))
        set a_m : ZMod 7 := qz m (u_int * e₁) with ha_m_def
        have hqe2 : qz m (u_int * e₂) = a_m + 1 := by
          rw [qz_top_affine m u_int e₂ e₁ hd2, hu_cast, ← hr_def, inv_mul_cancel₀ hr_ne,
            ← ha_m_def]
        have hqe3 : qz m (u_int * e₃) = a_m + 2 := by
          rw [qz_top_affine m u_int e₃ e₁ hd3, hr32, hu_cast,
            show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne,
            mul_one, ← ha_m_def]
        have hqe4 : qz m (u_int * e₄) = a_m + 3 := by
          rw [qz_top_affine m u_int e₄ e₁ hd4, hr3, hu_cast,
            show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne,
            mul_one, ← ha_m_def]
        obtain ⟨k', hw0, hw1, hw2, hw3, hkq₅⟩ := avoid_62a_4win a_m (qz m (u_int * d i₅))
        refine lift_shift m (by omega) d u_int hu_ndvd k' (fun i => ?_)
        rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
        · subst hk₀
          rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
          have hmem : qz m (u_int * b₁ k₀) ∈
              ({qz m (u_int * e₁), qz m (u_int * e₂), qz m (u_int * e₃), qz m (u_int * e₄)}
                : Finset (ZMod 7)) := by
            rw [hperm (fun x => qz m (u_int * x))]; fin_cases k₀ <;> simp
          rw [hqe2, hqe3, hqe4, ← ha_m_def] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h1 | h1 | h1 <;> rw [h1]
          · exact hw0
          · exact hw1
          · exact hw2
          · exact hw3
        · subst hi
          rw [hi₅_res, mul_comm k' (2 : ZMod 7)]
          exact hkq₅
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: L9(ii) j=2 on {e₂,e₃,e₁} (ratio 2 via hr32).
          obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt e₂ e₃ e₁
              (he₂_res.trans he₁_res.symm) (he₃_res.trans he₁_res.symm)
              hd2 hd2' hd3 hd3' hr32
          exact close_fit2 lam₀ hlam₀ a hB_fit
        · -- h > m: all A₁ arcs coincide.
          exact close_hgt
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd3)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd4)
    · -- (ii.2) ratio 4 for e₄.
      by_cases hheq : h = m
      · -- h = m: holed window {A, A+1, A+2, A+4}; Lemma 7 forces ẽ(e₁,d₅) ∉ {2,3}.
        rw [hheq] at hd2 hd2' hd3 hd4 hr32 hr4
        set r : ZMod 7 := (((e₂ - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd2
          have hdiv : (e₂ - e₁) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd2' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ) with hu_def
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by
          simp [hu_def, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          exact hr_ne (inv_eq_zero.mp (hu_cast ▸ h1))
        set e : ℤ := 2 * e₁ - d i₅ with he_def
        -- Shared finisher: a frame w with residue r⁻¹ or 2·r⁻¹ and ẽ ∉ {2,3} closes.
        have finish : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w →
            ((w : ZMod 7) = r⁻¹ ∨ (w : ZMod 7) = 2 * r⁻¹) →
            2 * qz m (w * e₁) - qz m (w * d i₅) ∉ ({2, 3} : Finset (ZMod 7)) →
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
              qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
          intro w hw_ndvd hw_res hetal
          set A : ZMod 7 := qz m (w * e₁) with hA_def
          obtain ⟨k', hh0, hh1, hh2, hh4, hkq₅⟩ :=
            avoid_62a_holewin A (qz m (w * d i₅)) hetal
          have harc2 : qz m (w * e₂) = A + (w : ZMod 7) * r := by
            rw [qz_top_affine m w e₂ e₁ hd2, ← hr_def, ← hA_def]
          have harc3 : qz m (w * e₃) = A + (w : ZMod 7) * (2 * r) := by
            rw [qz_top_affine m w e₃ e₁ hd3, hr32, ← hA_def]
          have harc4 : qz m (w * e₄) = A + (w : ZMod 7) * (4 * r) := by
            rw [qz_top_affine m w e₄ e₁ hd4, hr4, ← hA_def]
          refine lift_shift m (by omega) d w hw_ndvd k' (fun i => ?_)
          rcases hi_dichotomy i with ⟨k₀, hk₀⟩ | hi
          · subst hk₀
            rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
            have hmem : qz m (w * b₁ k₀) ∈
                ({qz m (w * e₁), qz m (w * e₂), qz m (w * e₃), qz m (w * e₄)}
                  : Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m (w * x))]; fin_cases k₀ <;> simp
            rw [harc2, harc3, harc4, ← hA_def] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hw_res with hres_w | hres_w
            · -- residue r⁻¹: offsets (1, 2, 4).
              rw [hres_w] at hmem
              rw [show r⁻¹ * r = 1 from inv_mul_cancel₀ hr_ne,
                  show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring,
                  show r⁻¹ * (4 * r) = 4 * (r⁻¹ * r) from by ring,
                  inv_mul_cancel₀ hr_ne, mul_one, mul_one] at hmem
              rcases hmem with h' | h' | h' | h' <;> rw [h']
              · exact hh0
              · exact hh1
              · exact hh2
              · exact hh4
            · -- residue 2·r⁻¹: offsets (2, 4, 8≡1) — same window set.
              rw [hres_w] at hmem
              rw [show 2 * r⁻¹ * r = 2 * (r⁻¹ * r) from by ring,
                  show 2 * r⁻¹ * (2 * r) = 4 * (r⁻¹ * r) from by ring,
                  show 2 * r⁻¹ * (4 * r) = 8 * (r⁻¹ * r) from by ring,
                  inv_mul_cancel₀ hr_ne, mul_one, mul_one, mul_one,
                  show (8 : ZMod 7) = 1 from by decide] at hmem
              rcases hmem with h' | h' | h' | h' <;> rw [h']
              · exact hh0
              · exact hh2
              · exact hh4
              · exact hh1
          · subst hi
            rw [hi₅_res, mul_comm k' (2 : ZMod 7)]
            exact hkq₅
        -- Pair facts for Lemma 7 in a frame v (v ∈ {u_int, 2·u_int}).
        have hpair : ∀ (v : ℤ), ¬ (7 : ℤ) ∣ v →
            (¬ (7 : ℤ) ∣ (v * e₁)) ∧ (¬ (7 : ℤ) ∣ (v * d i₅)) ∧
            ((v * d i₅ : ℤ) : ZMod 7) = 2 * ((v * e₁ : ℤ) : ZMod 7) := by
          intro v hv
          refine ⟨fun hdvd => ?_, fun hdvd => ?_, ?_⟩
          · rcases hp7.dvd_mul.mp hdvd with hh | hh
            · exact hv hh
            · exact he₁_ndvd hh
          · rcases hp7.dvd_mul.mp hdvd with hh | hh
            · exact hv hh
            · exact hi₅_ndvd hh
          · push_cast
            rw [hi₅_res, he₁_res]; ring
        by_cases hdvd_m : (7 : ℤ) ^ m ∣ e
        · -- ν(e) ≥ m: Lemma 7(ii); the qz(u·e) = 3 carve-out doubles the frame.
          obtain ⟨γ, hγ⟩ := hdvd_m
          have hqz0 : qz m (0 : ℤ) = 0 := by simp [qz]
          have hqz_ve : ∀ (v : ℤ), qz m (v * e) = (v : ZMod 7) * (γ : ZMod 7) := by
            intro v
            rw [hγ, show v * ((7 : ℤ) ^ m * γ) = 0 + (v * γ) * 7 ^ m from by ring,
                qz_add_mul_pow, hqz0, zero_add]
            push_cast; ring
          have hdvd_ve : ∀ (v : ℤ), (7 : ℤ) ^ m ∣ (2 * (v * e₁) - v * d i₅) := by
            intro v
            rw [show 2 * (v * e₁) - v * d i₅ = v * e from by rw [he_def]; ring, hγ]
            exact ⟨v * γ, by ring⟩
          by_cases ht3 : qz m (u_int * e) = 3
          · -- Carve-out: double. qz(2u·e) = 6 and Lemma 7(ii) applies in frame 2u.
            set u₂ : ℤ := 2 * u_int with hu₂_def
            have hu₂_ndvd : ¬ (7 : ℤ) ∣ u₂ := by
              intro hdvd
              rcases hp7.dvd_mul.mp hdvd with hh | hh
              · exact absurd hh (by decide)
              · exact hu_ndvd hh
            obtain ⟨hd_pair, hd'_pair, hr_pair⟩ := hpair u₂ hu₂_ndvd
            have h3 : (u_int : ZMod 7) * (γ : ZMod 7) = 3 := by
              rw [← hqz_ve u_int]; exact ht3
            obtain ⟨lam₁, hlam₁_ndvd, hlam₁_res, hetal⟩ :=
              lemma7_ii m 0 (by omega) (u₂ * e₁) (u₂ * d i₅) hd_pair hd'_pair hr_pair
                ({2, 3} : Finset (ZMod 7)) (hdvd_ve u₂)
                (by
                  rw [show 2 * (u₂ * e₁) - u₂ * d i₅ = u₂ * e from by rw [he_def]; ring,
                      hqz_ve u₂,
                      show ((u₂ : ℤ) : ZMod 7) = 2 * (u_int : ZMod 7) from by
                        rw [hu₂_def]; push_cast; ring,
                      mul_assoc, h3]
                  decide)
            refine finish (lam₁ * u₂) ?_ (Or.inr ?_) ?_
            · intro hdvd
              rcases hp7.dvd_mul.mp hdvd with hh | hh
              · exact hlam₁_ndvd hh
              · exact hu₂_ndvd hh
            · push_cast
              rw [hlam₁_res, hu₂_def]; push_cast; rw [hu_cast]; ring
            · rw [show (lam₁ * u₂) * e₁ = lam₁ * (u₂ * e₁) from by ring,
                  show (lam₁ * u₂) * d i₅ = lam₁ * (u₂ * d i₅) from by ring]
              exact hetal
          · -- qz(u·e) ≠ 3: Lemma 7(ii) directly in frame u.
            obtain ⟨hd_pair, hd'_pair, hr_pair⟩ := hpair u_int hu_ndvd
            obtain ⟨lam₁, hlam₁_ndvd, hlam₁_res, hetal⟩ :=
              lemma7_ii m 0 (by omega) (u_int * e₁) (u_int * d i₅) hd_pair hd'_pair hr_pair
                ({2, 3} : Finset (ZMod 7)) (hdvd_ve u_int)
                (by
                  rw [show 2 * (u_int * e₁) - u_int * d i₅ = u_int * e from by
                    rw [he_def]; ring]
                  intro hmem
                  apply ht3
                  have : qz m (u_int * e) ∈ ({3} : Finset (ZMod 7)) := by
                    revert hmem
                    have : (({2, 3} : Finset (ZMod 7)) ∩
                        (({2, 3} : Finset (ZMod 7)).image (· + 1))) = {3} := by decide
                    rw [this]; exact id
                  simpa using this)
            refine finish (lam₁ * u_int) ?_ (Or.inl ?_) ?_
            · intro hdvd
              rcases hp7.dvd_mul.mp hdvd with hh | hh
              · exact hlam₁_ndvd hh
              · exact hu_ndvd hh
            · push_cast
              rw [hlam₁_res, hu_cast]; ring
            · rw [show (lam₁ * u_int) * e₁ = lam₁ * (u_int * e₁) from by ring,
                  show (lam₁ * u_int) * d i₅ = lam₁ * (u_int * d i₅) from by ring]
              exact hetal
        · -- ν(e) < m: Lemma 7(i) with X = {2,3}.
          have he_ne : e ≠ 0 := fun h0 => hdvd_m (h0 ▸ dvd_zero _)
          set ν := padicValInt 7 e with hν_def
          have hν_lt : ν < m := by
            by_contra hge; push_neg at hge
            exact hdvd_m ((padicValInt_dvd_iff m e).mpr (Or.inr hge))
          have hν_ndvd : ¬ (7 : ℤ) ^ (ν + 1) ∣ e := by
            intro hh
            have hle : ν + 1 ≤ padicValInt 7 e :=
              ((padicValInt_dvd_iff (ν + 1) e).mp hh).resolve_left he_ne
            omega
          obtain ⟨hd_pair, hd'_pair, hr_pair⟩ := hpair u_int hu_ndvd
          obtain ⟨lam₁, hlam₁_ndvd, hlam₁_res, hetal⟩ :=
            lemma7_i m ν hν_lt (u_int * e₁) (u_int * d i₅) hd_pair hd'_pair hr_pair
              ({2, 3} : Finset (ZMod 7)) ⟨2, by decide⟩
              (by
                rw [show 2 * (u_int * e₁) - u_int * d i₅ = u_int * e from by
                  rw [he_def]; ring]
                exact (padicValInt_dvd e).mul_left u_int)
              (by
                rw [show 2 * (u_int * e₁) - u_int * d i₅ = u_int * e from by
                  rw [he_def]; ring]
                exact pow7_ndvd_mul (ν + 1) u_int e hu_ndvd hν_ndvd)
          refine finish (lam₁ * u_int) ?_ (Or.inl ?_) ?_
          · intro hdvd
            rcases hp7.dvd_mul.mp hdvd with hh | hh
            · exact hlam₁_ndvd hh
            · exact hu_ndvd hh
          · push_cast
            rw [hlam₁_res, hu_cast]; ring
          · rw [show (lam₁ * u_int) * e₁ = lam₁ * (u_int * e₁) from by ring,
                show (lam₁ * u_int) * d i₅ = lam₁ * (u_int * d i₅) from by ring]
            exact hetal
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: L9(ii) j=2 (uses only the ratio-2 pair {e₂,e₃,e₁}).
          obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt e₂ e₃ e₁
              (he₂_res.trans he₁_res.symm) (he₃_res.trans he₁_res.symm)
              hd2 hd2' hd3 hd3' hr32
          exact close_fit2 lam₀ hlam₀ a hB_fit
        · -- h > m: all A₁ arcs coincide.
          exact close_hgt
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd3)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd4)

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
      · -- h = m, ratio 4: r⁻¹ normalize → Lemma 7 fixes ẽ(d₄,d₅) ∉ {4,6} → lemma6_501_gen.
        rw [hheq] at hd2 hd2' hd3 hd3' hd4 hd4' hr32 hr4
        -- ── r⁻¹ normalization ────────────────────────────────────────────────
        set r : ZMod 7 := (((e₂ - e₁) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd2
          have hdiv : (e₂ - e₁) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd2' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ)
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by
          simp [u_int, Int.cast_natCast, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          exact hr_ne (inv_eq_zero.mp (hu_cast ▸ h1))
        set a_m : ZMod 7 := qz m (u_int * e₁)
        have hqe2 : qz m (u_int * e₂) = a_m + 1 := by
          rw [qz_top_affine m u_int e₂ e₁ hd2, hu_cast, ← hr_def, inv_mul_cancel₀ hr_ne]
        have hqe3 : qz m (u_int * e₃) = a_m + 2 := by
          rw [qz_top_affine m u_int e₃ e₁ hd3, hu_cast, hr32]
          congr 1
          rw [show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        have hqe4 : qz m (u_int * e₄) = a_m + 4 := by
          rw [qz_top_affine m u_int e₄ e₁ hd4, hu_cast, hr4]
          congr 1
          rw [show r⁻¹ * (4 * r) = 4 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        -- ── e₁ residue + Lemma 7 pair non-divisibility ───────────────────────
        have hb₁_all_1 : ∀ k : Fin 4, (b₁ k : ZMod 7) = 1 := hg₁_res
        have he₁_res : (e₁ : ZMod 7) = 1 := by
          have hmem : (e₁ : ZMod 7) ∈
              ({(b₁ 0 : ZMod 7), (b₁ 1 : ZMod 7), (b₁ 2 : ZMod 7), (b₁ 3 : ZMod 7)} :
                Finset _) := by
            rw [← hperm (fun x => (x : ZMod 7))]; simp
          simp only [hb₁_all_1 0, hb₁_all_1 1, hb₁_all_1 2, hb₁_all_1 3,
                     Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h <;> exact h
        -- Lemma 7 pair: d = u_int*d i₄ (residue 4), d' = u_int*e₁ (residue 1)
        -- hr_L7: r(u_int*e₁) = 2·r(u_int*d i₄) since r⁻¹·1 = 2·r⁻¹·4 (mod 7)
        have hr_L7 : ((u_int * e₁ : ℤ) : ZMod 7) = 2 * ((u_int * d i₄ : ℤ) : ZMod 7) := by
          push_cast; rw [hu_cast, hi₄_res, he₁_res, mul_one,
            mul_comm r⁻¹ 4, ← mul_assoc,
            show (2 : ZMod 7) * 4 = 1 from by decide, one_mul]
        have hd_L7 : ¬ (7 : ℤ) ∣ (u_int * d i₄) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (d i₄ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d i₄) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with h | h
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp h)
          · rw [hi₄_res] at h; exact absurd h (by decide)
        have hd'_L7 : ¬ (7 : ℤ) ∣ (u_int * e₁) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (e₁ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * e₁) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with h | h
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp h)
          · rw [he₁_res] at h; exact absurd h (by decide)
        -- ── Apply Lemma 7 (ii) or (i) based on 7^m ∣ e_L7 ──────────────────
        set e_L7 : ℤ := 2 * (u_int * d i₄) - (u_int * e₁) with he_L7_def
        have he_L7_mod : (e_L7 : ZMod 7) = 0 := by
          simp only [he_L7_def]; push_cast; rw [hu_cast, hi₄_res, he₁_res, mul_one,
            mul_comm r⁻¹ 4, ← mul_assoc,
            show (2 : ZMod 7) * 4 = 1 from by decide, one_mul, sub_self]
        haveI h7p : Fact (Nat.Prime 7) := ⟨by decide⟩
        obtain ⟨lam₁, hl1_ndvd, hl1_res, hetal⟩ :
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
              (2 * qz m (lam * (u_int * d i₄)) - qz m (lam * (u_int * e₁))) ∉
                ({4, 6} : Finset (ZMod 7)) := by
          -- Pre-compute the two finset witnesses explicitly.
          -- image of {4,6} under x↦x+1 in ZMod 7 is {5,0}, disjoint from {4,6}.
          -- Use ZMod.val to reduce to ℕ arithmetic (avoids decide universe issues).
          have hXX46 : qz m (2 * (u_int * d i₄) - (u_int * e₁)) ∉
              (({4, 6} : Finset (ZMod 7)) ∩
               ({4, 6} : Finset (ZMod 7)).image (fun x : ZMod 7 => x + 1)) := by
            intro hmem
            have h1 : qz m (2 * (u_int * d i₄) - u_int * e₁) ∈ ({4, 6} : Finset (ZMod 7)) :=
              (Finset.mem_inter.mp hmem).1
            have h2 : ∃ y ∈ ({4, 6} : Finset (ZMod 7)),
                y + 1 = qz m (2 * (u_int * d i₄) - u_int * e₁) :=
              Finset.mem_image.mp (Finset.mem_inter.mp hmem).2
            obtain ⟨y, hy, hyx⟩ := h2
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1 hy
            rcases hy with rfl | rfl <;> rcases h1 with h | h <;> {
              have heq := congrArg ZMod.val (hyx.trans h)
              simp only [ZMod.val_add, ZMod.val_ofNat, ZMod.val_one] at heq
              omega }
          have hX46 : ∃ a : ZMod 7, fitsInterval ({4, 6} : Finset (ZMod 7)) a 4 :=
            ⟨4, fun x hx => by
              simp only [fitsInterval, Finset.mem_insert, Finset.mem_singleton] at *
              rcases hx with rfl | rfl
              · exact ⟨⟨0, by omega⟩, by norm_num⟩
              · exact ⟨⟨2, by omega⟩, by norm_num⟩⟩
          by_cases hm_dvd : (7 : ℤ) ^ m ∣ e_L7
          · exact lemma7_ii m 0 (by omega) (u_int * d i₄) (u_int * e₁)
                hd_L7 hd'_L7 hr_L7 {4, 6} hm_dvd hXX46
          · have he_ne : e_L7 ≠ 0 := fun heq => hm_dvd (heq ▸ dvd_zero _)
            set ν := padicValInt 7 e_L7 with hν_def
            have hν_lt_m : ν < m := by
              by_contra hge; push_neg at hge
              exact hm_dvd ((padicValInt_dvd_iff m e_L7).mpr (Or.inr hge))
            have hν_ndvd : ¬ (7 : ℤ) ^ (ν + 1) ∣ e_L7 := by
              intro h
              have hle : ν + 1 ≤ padicValInt 7 e_L7 :=
                ((padicValInt_dvd_iff (ν + 1) e_L7).mp h).resolve_left he_ne
              omega
            exact lemma7_i m ν hν_lt_m (u_int * d i₄) (u_int * e₁)
                hd_L7 hd'_L7 hr_L7 {4, 6} hX46
                (padicValInt_dvd e_L7) hν_ndvd
        -- ── Arc structure after lam₁ ─────────────────────────────────────────
        -- lam₁ ≡ 1 (mod 7) so composite (lam₁·u_int) has residue r⁻¹
        have hlu_cast : ((lam₁ * u_int : ℤ) : ZMod 7) = r⁻¹ := by
          push_cast; rw [hl1_res, hu_cast, one_mul]
        set a_m' : ZMod 7 := qz m (lam₁ * (u_int * e₁)) with ha_m'_def
        set q₄' : ZMod 7 := qz m (lam₁ * (u_int * d i₄)) with hq4'_def
        have hqe2' : qz m (lam₁ * (u_int * e₂)) = a_m' + 1 := by
          rw [show lam₁ * (u_int * e₂) = (lam₁ * u_int) * e₂ from by ring,
              qz_top_affine m (lam₁ * u_int) e₂ e₁ hd2,
              show (lam₁ * u_int) * e₁ = lam₁ * (u_int * e₁) from by ring,
              hlu_cast, ← hr_def, inv_mul_cancel₀ hr_ne]
        have hqe3' : qz m (lam₁ * (u_int * e₃)) = a_m' + 2 := by
          rw [show lam₁ * (u_int * e₃) = (lam₁ * u_int) * e₃ from by ring,
              qz_top_affine m (lam₁ * u_int) e₃ e₁ hd3, hlu_cast, hr32,
              show (lam₁ * u_int) * e₁ = lam₁ * (u_int * e₁) from by ring]
          congr 1
          rw [show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        have hqe4' : qz m (lam₁ * (u_int * e₄)) = a_m' + 4 := by
          rw [show lam₁ * (u_int * e₄) = (lam₁ * u_int) * e₄ from by ring,
              qz_top_affine m (lam₁ * u_int) e₄ e₁ hd4, hlu_cast, hr4,
              show (lam₁ * u_int) * e₁ = lam₁ * (u_int * e₁) from by ring]
          congr 1
          rw [show r⁻¹ * (4 * r) = 4 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        -- ── lemma6_501_gen: shift k₀ with interval a_m' ─────────────────────
        -- hetal : 2*q₄' - a_m' ∉ {4,6}
        obtain ⟨k₀, hk₀_A1, hk₀_A4⟩ := lemma6_501_gen a_m' q₄' hetal
        -- ── Compose multipliers: u_int → lam₁ → lambda0_lift(k₀·r) ──────────
        refine five_compress_relabel m d u_int hu_ndvd ?_
        refine five_compress_relabel m (fun i => u_int * d i) lam₁ hl1_ndvd ?_
        refine lambda0_lift m (by omega) (fun i => lam₁ * (u_int * d i)) (k₀ * r) (fun i => ?_)
        -- algebraic: shift (k₀·r) on residue r⁻¹·(d i:ZMod7) simplifies to k₀·(d i:ZMod7)
        have halg : (k₀ * r) * ((lam₁ * (u_int * d i) : ℤ) : ZMod 7) = k₀ * (d i : ZMod 7) := by
          have hcast : ((lam₁ * (u_int * d i) : ℤ) : ZMod 7) = r⁻¹ * (d i : ZMod 7) := by
            push_cast; rw [hl1_res, hu_cast]; ring
          rw [hcast, show (k₀ * r) * (r⁻¹ * (d i : ZMod 7)) =
                k₀ * (r * r⁻¹) * (d i : ZMod 7) from by ring,
              mul_inv_cancel₀ hr_ne]
          ring
        rw [halg]
        rcases hi_dichotomy i with ⟨k₀', hk₀'⟩ | hi
        · -- A₁ element: shift = k₀·1 = k₀; arc ∈ {a_m', a_m'+1, a_m'+2, a_m'+4}
          subst hk₀'; rw [hg₁_res k₀', mul_one]
          show qz m (lam₁ * (u_int * b₁ k₀')) + k₀ ∉ ({0, 6} : Finset (ZMod 7))
          have hmem : qz m (lam₁ * (u_int * b₁ k₀')) ∈
              ({a_m', a_m' + 1, a_m' + 2, a_m' + 4} : Finset (ZMod 7)) := by
            have hmem' : qz m (lam₁ * (u_int * b₁ k₀')) ∈
                ({qz m (lam₁ * (u_int * e₁)), qz m (lam₁ * (u_int * e₂)),
                  qz m (lam₁ * (u_int * e₃)), qz m (lam₁ * (u_int * e₄))} :
                  Finset (ZMod 7)) := by
              rw [hperm (fun x => qz m (lam₁ * (u_int * x)))]; fin_cases k₀' <;> simp
            rwa [← ha_m'_def, hqe2', hqe3', hqe4'] at hmem'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h2 | h3 | h4
          · rw [h1]; have h := hk₀_A1 ⟨0, by omega⟩
            simp only [Fin.val_zero, Nat.cast_zero, add_zero, one_mul] at h; exact h
          · rw [h2]; have h := hk₀_A1 ⟨1, by omega⟩
            simp only [Fin.val_one, Nat.cast_one, one_mul] at h; exact h
          · rw [h3]; have h := hk₀_A1 ⟨2, by omega⟩
            simp only [show (⟨2, by omega⟩ : Fin 5).val = 2 from rfl,
                       Nat.cast_ofNat, one_mul] at h; exact h
          · rw [h4]; have h := hk₀_A1 ⟨4, by omega⟩
            simp only [show (⟨4, by omega⟩ : Fin 5).val = 4 from rfl,
                       Nat.cast_ofNat, one_mul] at h; exact h
        · -- A₄ element: shift = k₀·4; arc = q₄'
          subst hi; rw [hi₄_res]
          have h := hk₀_A4 ⟨0, by omega⟩
          simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h
          rwa [show k₀ * (4 : ZMod 7) = 4 * k₀ from by ring]
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

/-- **A₁ (3-element) extraction + relabeling data.** Shared setup for the `|A₁|=3`
cases (6.3, 6.4, 6.5): enumerate the residue-1 class as `b₁ : Fin 3 → ℤ`, extract
the covering/residue/injectivity facts, and apply Lemma 11 for the labeling. -/
private structure A1three (m : ℕ) (d : Fin 5 → ℤ)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3) where
  g₁ : Fin 3 → Fin 5
  hg₁_res : ∀ k, (d (g₁ k) : ZMod 7) = 1
  hg₁_inj : Function.Injective g₁
  hA₁_cover : ∀ i : Fin 5, (d i : ZMod 7) = 1 → ∃ k : Fin 3, g₁ k = i

/-- Build the `A1three` extraction from the cardinality hypothesis. -/
private def mkA1three (m : ℕ) (d : Fin 5 → ℤ)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3) :
    A1three m d hC₁ :=
  let S₁ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)
  { g₁ := fun k => (S₁.orderIsoOfFin hC₁ k).val
    hg₁_res := fun k => by
      have := (S₁.orderIsoOfFin hC₁ k).prop
      simp only [S₁, mem_filter, mem_univ, true_and] at this; exact this
    hg₁_inj := fun a b h => (S₁.orderIsoOfFin hC₁).injective (Subtype.val_injective h)
    hA₁_cover := fun i hi =>
      ⟨(S₁.orderIsoOfFin hC₁).symm ⟨i, by simp [S₁, hi]⟩,
       congr_arg Subtype.val
         ((S₁.orderIsoOfFin hC₁).right_inv ⟨i, by simp [S₁, hi]⟩)⟩ }

/-- **Case 6.3 `(3,1,1)`** (BS L565). `|A₁|=3, |A₂|=|A₄|=1`. Labeling via Lemma 11;
endgame is `lemma5` on the `(ℓ₁,1,1)` partition (the `(3,1,1)` exception carved by
`ẽ(d₄,d₅) ∉ {2,4}`). Branch map: (i)/(ii.1) `h<m` → `lemma9` gives `ℓ(A₁)≤2`;
`h>m` → arcs coincide (`ℓ=1`); (ii.2.a) `h<m` (`ν(e₄₅)≠h`) → `j3_control`;
(ii.1) `h=m` → `r⁻¹`-frame + Lemma 7; (ii.2.b)/(ii.2) `h=m` → finite tables. -/
private theorem case_63 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  obtain ⟨g₁, hg₁_res, hg₁_inj, hA₁_cover⟩ := mkA1three m d hC₁
  set b₁ : Fin 3 → ℤ := fun k => d (g₁ k) with hb₁_def
  have hb₁_inj : Function.Injective b₁ := fun a b h => hg₁_inj (hinj h)
  -- Extract the unique A₂-element i₄ (residue 2) and A₄-element i₅ (residue 4).
  set S₂ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2) with hS₂_def
  set S₄ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4) with hS₄_def
  obtain ⟨i₄, hS₂sing⟩ := Finset.card_eq_one.mp hC₂
  obtain ⟨i₅, hS₄sing⟩ := Finset.card_eq_one.mp hC₄
  have hi₄_res : (d i₄ : ZMod 7) = 2 := by
    have : i₄ ∈ S₂ := by rw [hS₂sing]; exact mem_singleton_self _
    simp only [hS₂_def, mem_filter, mem_univ, true_and] at this; exact this
  have hi₅_res : (d i₅ : ZMod 7) = 4 := by
    have : i₅ ∈ S₄ := by rw [hS₄sing]; exact mem_singleton_self _
    simp only [hS₄_def, mem_filter, mem_univ, true_and] at this; exact this
  -- Every index is an A₁-element or i₄ or i₅ (the three classes partition Fin 5).
  have hi_tri : ∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i₄ ∨ i = i₅ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h1 | h2 | h4
    · exact Or.inl (hA₁_cover i h1)
    · refine Or.inr (Or.inl ?_)
      have hi_mem : i ∈ S₂ := by simp only [hS₂_def, mem_filter, mem_univ, true_and]; exact h2
      rwa [hS₂sing, Finset.mem_singleton] at hi_mem
    · refine Or.inr (Or.inr ?_)
      have hi_mem : i ∈ S₄ := by simp only [hS₄_def, mem_filter, mem_univ, true_and]; exact h4
      rwa [hS₄sing, Finset.mem_singleton] at hi_mem
  -- ── Endgame: A₁ fits a length-`L` window (L ≤ 3), A₂ at coeff 2, A₄ at coeff 4;
  --    `lemma5` on the `(L,1,1)` partition closes (the `(3,1,1)` carve = ẽ(d₄,d₅)∉{2,4}). ──
  have close_l5 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ (a₁ : ZMod 7) (L : ℕ), 1 ≤ L → L ≤ 3 →
      (∀ k₀ : Fin 3, ∃ j : Fin L, qz m (lam₀ * b₁ k₀) = a₁ + (j.val : ZMod 7)) →
      (L = 3 → (2 * qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅)) ∉ ({2, 4} : Finset (ZMod 7))) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ a₁ L hL1 hL3 hfitA₁ hcarve
    obtain ⟨k, hk1, hk2, hk4⟩ :=
      lemma5 a₁ (qz m (lam₀ * d i₄)) (qz m (lam₀ * d i₅)) L 1 1
        (by omega) (by omega) (by omega) (by omega) (fun h => hcarve h.1)
    refine lift_shift m (by omega) d lam₀ hlam₀ k (fun i => ?_)
    rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
    · subst hk₀; rw [hg₁_res k₀, mul_one]
      obtain ⟨j, hj⟩ := hfitA₁ k₀
      rw [show d (g₁ k₀) = b₁ k₀ from rfl, hj]
      have := hk1 j
      simpa [intervalAvoids, mul_one] using this
    · subst hi; rw [hi₄_res]
      have := hk2 ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
    · subst hi; rw [hi₅_res]
      have := hk4 ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
  -- Bridge: a fitsInterval on the b₁-arc set feeds `close_l5`.
  have fit_of_set : ∀ (lam₀ : ℤ) (a : ZMod 7) (L : ℕ),
      fitsInterval ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)}
        : Finset (ZMod 7)) a L →
      ∀ k₀ : Fin 3, ∃ j : Fin L, qz m (lam₀ * b₁ k₀) = a + (j.val : ZMod 7) := by
    intro lam₀ a L hfit k₀
    exact hfit _ (by fin_cases k₀ <;> simp)
  -- Apply Lemma 11 to label A₁.
  obtain ⟨d₁, d₂, d₃, hperm, h_struct⟩ := lemma11 b₁ hb₁_inj
  have hset_eq : ∀ (lam₀ : ℤ),
      ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)} : Finset (ZMod 7))
      = {qz m (lam₀ * d₁), qz m (lam₀ * d₂), qz m (lam₀ * d₃)} := fun lam₀ =>
    (hperm (fun x => qz m (lam₀ * x))).symm
  -- Closer for the ν(E) > m sub-branch: all A₁ arcs coincide, ℓ(A₁)=1.
  have close_hgt : ∀ (e₁ e₂ e₃ : ℤ),
      (∀ f : ℤ → ZMod 7, ({f e₁, f e₂, f e₃} : Finset (ZMod 7)) = {f (b₁ 0), f (b₁ 1), f (b₁ 2)}) →
      (7 : ℤ) ^ (m + 1) ∣ (e₁ - e₃) → (7 : ℤ) ^ (m + 1) ∣ (e₂ - e₃) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro e₁ e₂ e₃ hperm' hdv1 hdv2
    refine close_l5 1 (by norm_num) (qz m (1 * e₃)) 1 (le_refl 1) (by omega)
      (fun k₀ => ⟨⟨0, by omega⟩, ?_⟩) (fun h => absurd h (by decide))
    simp only [Fin.val_zero, Nat.cast_zero, add_zero]
    have hmem : qz m (1 * b₁ k₀) ∈
        ({qz m (1 * e₁), qz m (1 * e₂), qz m (1 * e₃)} : Finset (ZMod 7)) := by
      rw [hperm' (fun x => qz m (1 * x))]; fin_cases k₀ <;> simp
    rw [qz_eq_of_high_dvd m e₁ e₃ 1 hdv1, qz_eq_of_high_dvd m e₂ e₃ 1 hdv2] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hmem
    exact hmem
  -- Residues of the labels (all ≡ 1).
  have hb₁_all_1 : ∀ k : Fin 3, (b₁ k : ZMod 7) = 1 := hg₁_res
  have he_res_aux : ∀ x : ZMod 7,
      x ∈ ({(b₁ 0 : ZMod 7), (b₁ 1 : ZMod 7), (b₁ 2 : ZMod 7)} : Finset _) → x = 1 := by
    intro x hx
    simp only [hb₁_all_1 0, hb₁_all_1 1, hb₁_all_1 2, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h <;> exact h
  have he₁_res : (d₁ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
  have he₂_res : (d₂ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
  have he₃_res : (d₃ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
  rcases h_struct with
      ⟨h₁, h₂, hlt, hd1, hd1', hd2, hd2'⟩ |
      ⟨h, hd1, hd1', hd2, hd2', hr⟩
  · -- ── (i) distinct valuations: lemma9_i_dispatch → ℓ(A₁) ≤ 2. ──
    obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
      lemma9_i_dispatch m h₁ h₂ d₁ d₂ d₃ (ne_of_lt hlt).symm hd1 hd1' hd2 hd2'
    refine close_l5 lam₀ hlam₀ a 2 (by omega) (by omega) ?_ (fun h => absurd h (by decide))
    exact fit_of_set lam₀ a 2 (by rw [hset_eq lam₀]; exact hB_fit)
  · rcases hr with hr2 | hr3
    · -- ── (ii.1) ratio 2 ──
      by_cases hheq : h = m
      · -- (ii.1) h = m: r⁻¹-frame ℓ(A₁)=3 + Lemma 7 forces ẽ(d₄,d₅)∉{2,4}.
        sorry
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: lemma9_ii_j2 → ℓ(A₁) ≤ 2.
          obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt d₁ d₂ d₃
              (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm) hd1 hd1' hd2 hd2' hr2
          refine close_l5 lam₀ hlam₀ a 2 (by omega) (by omega) ?_ (fun h => absurd h (by decide))
          exact fit_of_set lam₀ a 2 (by rw [hset_eq lam₀]; exact hB_fit)
        · -- h > m: arcs coincide, ℓ(A₁)=1.
          exact close_hgt d₁ d₂ d₃ hperm
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)
    · -- ── (ii.2) ratio 3 ──
      by_cases hheq : h = m
      · -- (ii.2) h = m: eight-bad-pairs (r⁻¹ frame {a,a+1,a+3} + Lemma 7 on (d₃,d₄)).
        sorry
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · -- h < m: split on ν(e₄₅) vs h — (ii.2.a) j3_control / (ii.2.b) ũ-table.
          set e45 : ℤ := 2 * d i₄ - d i₅ with he45_def
          -- carve helper: q(λ·e₄₅) = 6 ⟹ ẽ(d₄,d₅) = 2q(λd₄)−q(λd₅) ∉ {2,4}.
          have carve_of : ∀ (lam : ℤ), qz m (lam * e45) = 6 →
              (2 * qz m (lam * d i₄) - qz m (lam * d i₅)) ∉ ({2, 4} : Finset (ZMod 7)) := by
            intro lam hq
            obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (lam * d i₄) (lam * d i₅)
            rw [show lam * e45 = 2 * (lam * d i₄) - lam * d i₅ from by rw [he45_def]; ring,
                hcarry] at hq
            rw [show 2 * qz m (lam * d i₄) - qz m (lam * d i₅) = 6 - c from by linear_combination hq]
            rcases hc with rfl | rfl | rfl <;> decide
          by_cases he0 : e45 = 0
          · -- e₄₅ = 0: ẽ(d₄,d₅) ∈ {0,1,6} automatically; compress A₁ via lemma9_ii_j3.
            obtain ⟨lam₀, hlam₀, ⟨a, hB_fit⟩, _, _⟩ := lemma9_ii_j3 m h hlt d₁ d₂ d₃
              (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm) hd1 hd1' hd2 hd2' hr3
            refine close_l5 lam₀ hlam₀ a 3 (by omega) (by omega)
              (fit_of_set lam₀ a 3 (by rw [hset_eq lam₀]; exact hB_fit)) (fun _ => ?_)
            obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (lam₀ * d i₄) (lam₀ * d i₅)
            have hqz : qz m (lam₀ * e45) = 0 := by rw [he0, mul_zero]; simp [qz]
            rw [show lam₀ * e45 = 2 * (lam₀ * d i₄) - lam₀ * d i₅ from by rw [he45_def]; ring,
                hcarry] at hqz
            rw [show 2 * qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) = -c from by linear_combination hqz]
            rcases hc with rfl | rfl | rfl <;> decide
          · obtain ⟨ν, hνd, hνd'⟩ := exists_val7 e45 he0
            by_cases hνh : ν = h
            · -- (ii.2.b) ν(e₄₅) = ν(e₁₃) = h: BS ũ-table (L611–635).
              sorry
            · by_cases hνm : ν < m
              · -- (ii.2.a) ν(e₄₅) ≠ h and < m: two-level composition sets q(λ·e₄₅)=6.
                obtain ⟨lam, hlam, ⟨a, hfit⟩, hqe45⟩ :=
                  j3_control m h ν hlt hνm (Ne.symm hνh) d₁ d₂ d₃
                    (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm)
                    hd1 hd1' hd2 hd2' hr3 e45 hνd hνd' 6
                exact close_l5 lam hlam a 3 (by omega) (by omega)
                  (fit_of_set lam a 3 (by rw [hset_eq lam]; exact hfit)) (fun _ => carve_of lam hqe45)
              · -- ν(e₄₅) ≥ m: auto-zero (ν>m) or top-retarget (ν=m), then compress.
                have hmν : m ≤ ν := by omega
                by_cases htop : (7 : ℤ) ^ (m + 1) ∣ e45
                · -- ν(e₄₅) > m: qz(λ·e₄₅) = 0 via inertness ⟹ ẽ ∈ {0,1,6}.
                  obtain ⟨lam₀, hlam₀, ⟨a, hB_fit⟩, _, hinert⟩ := lemma9_ii_j3 m h hlt d₁ d₂ d₃
                    (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm) hd1 hd1' hd2 hd2' hr3
                  refine close_l5 lam₀ hlam₀ a 3 (by omega) (by omega)
                    (fit_of_set lam₀ a 3 (by rw [hset_eq lam₀]; exact hB_fit)) (fun _ => ?_)
                  obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (lam₀ * d i₄) (lam₀ * d i₅)
                  have hqz : qz m (lam₀ * e45) = 0 := by
                    rw [hinert e45 (dvd_trans (pow_dvd_pow 7 (by omega : h + 1 ≤ m + 1)) htop)]
                    obtain ⟨w, hw⟩ := htop
                    have hval : qz m e45 = ((7 * w : ℤ) : ZMod 7) := by
                      simp only [qz, hw,
                        show (7 : ℤ) ^ (m + 1) * w = 7 ^ m * (7 * w) from by rw [pow_succ]; ring]
                      rw [Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
                    rw [hval]; push_cast; rw [seven_eq_zero_z7]; ring
                  rw [show lam₀ * e45 = 2 * (lam₀ * d i₄) - lam₀ * d i₅ from by rw [he45_def]; ring,
                      hcarry] at hqz
                  rw [show 2 * qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) = -c from by
                    linear_combination hqz]
                  rcases hc with rfl | rfl | rfl <;> decide
                · -- ν(e₄₅) = m: `j3_control_top` retargets q(λ·e₄₅)=6, then compresses.
                  have hνeqm : ν = m := by
                    have hνle : ν ≤ m := by
                      by_contra hgt; push_neg at hgt
                      exact htop (dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ ν)) hνd)
                    omega
                  subst hνeqm
                  obtain ⟨lam, hlam, ⟨a, hfit⟩, hqe45⟩ :=
                    j3_control_top m h hlt d₁ d₂ d₃
                      (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm)
                      hd1 hd1' hd2 hd2' hr3 e45 hνd htop 6 (by decide)
                  exact close_l5 lam hlam a 3 (by omega) (by omega)
                    (fit_of_set lam a 3 (by rw [hset_eq lam]; exact hfit)) (fun _ => carve_of lam hqe45)
        · -- h > m: arcs coincide, ℓ(A₁)=1.
          exact close_hgt d₁ d₂ d₃ hperm
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)

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
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  obtain ⟨g₁, hg₁_res, hg₁_inj, hA₁_cover⟩ := mkA1three m d hC₁
  set b₁ : Fin 3 → ℤ := fun k => d (g₁ k) with hb₁_def
  have hb₁_inj : Function.Injective b₁ := fun a b h => hg₁_inj (hinj h)
  -- Extract the two A₂-elements.
  set S₂ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2) with hS₂_def
  obtain ⟨i₄, i₅, hi45_ne, hS₂pair⟩ := Finset.card_eq_two.mp hC₂
  have hi₄_res : (d i₄ : ZMod 7) = 2 := by
    have : i₄ ∈ S₂ := by rw [hS₂pair]; exact mem_insert_self _ _
    simp only [hS₂_def, mem_filter, mem_univ, true_and] at this; exact this
  have hi₅_res : (d i₅ : ZMod 7) = 2 := by
    have : i₅ ∈ S₂ := by rw [hS₂pair]; exact mem_insert_of_mem (mem_singleton_self _)
    simp only [hS₂_def, mem_filter, mem_univ, true_and] at this; exact this
  -- Every index is an A₁-element or i₄ or i₅ (hC₄ = 0 rules out residue 4).
  have hi_tri : ∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i₄ ∨ i = i₅ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h1 | h2 | h4
    · exact Or.inl (hA₁_cover i h1)
    · have hi_mem : i ∈ S₂ := by
        simp only [hS₂_def, mem_filter, mem_univ, true_and]; exact h2
      rw [hS₂pair, Finset.mem_insert, Finset.mem_singleton] at hi_mem
      exact Or.inr hi_mem
    · exfalso
      have hmem : i ∈ univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4) := by simp [h4]
      rw [Finset.card_eq_zero.mp hC₄] at hmem
      exact absurd hmem (Finset.notMem_empty i)
  -- ── Closer: A₁ fits a length-3 window at `a` (after mult by lam₀) ⇒ done ──
  -- lemma12_i gives k good for the 3-window and both A₂ points; lift_shift lifts.
  have close3 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ (a : ZMod 7),
      (∀ k₀ : Fin 3, ∃ j : Fin 3, qz m (lam₀ * b₁ k₀) = a + (j.val : ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ a hfit
    obtain ⟨k, hkA₁, hkα, hkβ⟩ :=
      lemma12_i a (qz m (lam₀ * d i₄)) (qz m (lam₀ * d i₅))
    refine lift_shift m (by omega) d lam₀ hlam₀ k (fun i => ?_)
    rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
    · -- A₁ element: residue 1, arc in the 3-window.
      subst hk₀; rw [hg₁_res k₀, mul_one]
      obtain ⟨j, hj⟩ := hfit k₀
      rw [show d (g₁ k₀) = b₁ k₀ from rfl, hj]
      have := hkA₁ j
      simpa [intervalAvoids, mul_one] using this
    · -- A₂ element i₄: residue 2.
      subst hi; rw [hi₄_res]
      have := hkα ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
    · -- A₂ element i₅: residue 2.
      subst hi; rw [hi₅_res]
      have := hkβ ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
  -- ── Closer for ℓ(A₁)=4 windows (ratio-3 h=m): lemma12_ii, controlling one A₂ pt ──
  -- `iα` (with ẽ-condition) is one A₂ element, `iβ` the other; together they cover A₂.
  have close4 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ (a : ZMod 7) (iα iβ : Fin 5),
      (d iα : ZMod 7) = 2 → (d iβ : ZMod 7) = 2 →
      (∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = iα ∨ i = iβ) →
      (∀ k₀ : Fin 3, ∃ j : Fin 4, qz m (lam₀ * b₁ k₀) = a + (j.val : ZMod 7)) →
      (2 * a - qz m (lam₀ * d iα) ∈ ({0, 1, 6} : Finset (ZMod 7))) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ a iα iβ hαres hβres htri' hfit he
    obtain ⟨k, hkA₁, hkα, hkβ⟩ :=
      lemma12_ii a (qz m (lam₀ * d iα)) (qz m (lam₀ * d iβ)) he
    refine lift_shift m (by omega) d lam₀ hlam₀ k (fun i => ?_)
    rcases htri' i with ⟨k₀, hk₀⟩ | hi | hi
    · subst hk₀; rw [hg₁_res k₀, mul_one]
      obtain ⟨j, hj⟩ := hfit k₀
      rw [show d (g₁ k₀) = b₁ k₀ from rfl, hj]
      have := hkA₁ j
      simpa [intervalAvoids, mul_one] using this
    · subst hi; rw [hαres]
      have := hkα ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
    · subst hi; rw [hβres]
      have := hkβ ⟨0, by omega⟩
      simpa [intervalAvoids, mul_comm] using this
  -- Bridge: a fitsInterval on the b₁-arc set (length ≤ 3) feeds `close3`.
  have fit_of_set : ∀ (lam₀ : ℤ) (a : ZMod 7) (L : ℕ), L ≤ 3 →
      fitsInterval ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)}
        : Finset (ZMod 7)) a L →
      ∀ k₀ : Fin 3, ∃ j : Fin 3, qz m (lam₀ * b₁ k₀) = a + (j.val : ZMod 7) := by
    intro lam₀ a L hL hfit k₀
    have hmem : qz m (lam₀ * b₁ k₀) ∈
        ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)} : Finset (ZMod 7)) := by
      fin_cases k₀ <;> simp
    exact fitsInterval_mono hL hfit _ hmem
  -- Apply Lemma 11 to label A₁.
  obtain ⟨d₁, d₂, d₃, hperm, h_struct⟩ := lemma11 b₁ hb₁_inj
  -- The b₁-arc set equals the {d₁,d₂,d₃}-arc set under any f (hperm).
  have hset_eq : ∀ (lam₀ : ℤ),
      ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)} : Finset (ZMod 7))
      = {qz m (lam₀ * d₁), qz m (lam₀ * d₂), qz m (lam₀ * d₃)} := fun lam₀ =>
    (hperm (fun x => qz m (lam₀ * x))).symm
  -- Closer for the ν(E) > m sub-branch: all A₁ arcs coincide at qz m d₃, ℓ(A₁)=1.
  have close_hgt : ∀ (e₁ e₂ e₃ : ℤ),
      (∀ f : ℤ → ZMod 7, ({f e₁, f e₂, f e₃} : Finset (ZMod 7)) = {f (b₁ 0), f (b₁ 1), f (b₁ 2)}) →
      (7 : ℤ) ^ (m + 1) ∣ (e₁ - e₃) → (7 : ℤ) ^ (m + 1) ∣ (e₂ - e₃) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro e₁ e₂ e₃ hperm' hdv1 hdv2
    refine close3 1 (by norm_num) (qz m (1 * e₃)) (fun k₀ => ⟨⟨0, by omega⟩, ?_⟩)
    simp only [Fin.val_zero, Nat.cast_zero, add_zero]
    have hmem : qz m (1 * b₁ k₀) ∈
        ({qz m (1 * e₁), qz m (1 * e₂), qz m (1 * e₃)} : Finset (ZMod 7)) := by
      rw [hperm' (fun x => qz m (1 * x))]; fin_cases k₀ <;> simp
    rw [qz_eq_of_high_dvd m e₁ e₃ 1 hdv1, qz_eq_of_high_dvd m e₂ e₃ 1 hdv2] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hmem
    exact hmem
  rcases h_struct with
      ⟨h₁, h₂, hlt, hd1, hd1', hd2, hd2'⟩ |
      ⟨h, hd1, hd1', hd2, hd2', hr⟩
  · -- ── (i) distinct valuations: lemma9_i_dispatch compresses to ℓ ≤ 2 ──
    obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
      lemma9_i_dispatch m h₁ h₂ d₁ d₂ d₃ (ne_of_lt hlt).symm hd1 hd1' hd2 hd2'
    refine close3 lam₀ hlam₀ a (fit_of_set lam₀ a 2 (by omega) ?_)
    rw [hset_eq lam₀]; exact hB_fit
  · -- ── (ii) equal level h; ratio 2 or 3 ──
    -- All of d₁,d₂,d₃ have residue 1 (permutation of b₁).
    have hb₁_all_1 : ∀ k : Fin 3, (b₁ k : ZMod 7) = 1 := hg₁_res
    have he_res_aux : ∀ x : ZMod 7,
        x ∈ ({(b₁ 0 : ZMod 7), (b₁ 1 : ZMod 7), (b₁ 2 : ZMod 7)} : Finset _) → x = 1 := by
      intro x hx
      simp only [hb₁_all_1 0, hb₁_all_1 1, hb₁_all_1 2,
                 Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h <;> exact h
    have he₁_res : (d₁ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
    have he₂_res : (d₂ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
    have he₃_res : (d₃ : ZMod 7) = 1 := he_res_aux _ (by rw [← hperm (fun x => (x : ZMod 7))]; simp)
    rcases hr with hr2 | hr3
    · -- ratio 2
      by_cases hheq : h = m
      · -- h = m: r⁻¹-dilation sends A₁ arcs to the 3-window {a_m, a_m+1, a_m+2}.
        rw [hheq] at hd1 hd1' hd2 hr2
        set r : ZMod 7 := (((d₁ - d₃) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd1
          have hdiv : (d₁ - d₃) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd1' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ) with hu_int_def
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by
          simp [hu_int_def, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          exact hr_ne (inv_eq_zero.mp (hu_cast ▸ h1))
        set a_m : ZMod 7 := qz m (u_int * d₃) with ha_m_def
        have hqd1 : qz m (u_int * d₁) = a_m + 1 := by
          rw [ha_m_def, qz_top_affine m u_int d₁ d₃ hd1, hu_cast, ← hr_def, inv_mul_cancel₀ hr_ne]
        have hqd2 : qz m (u_int * d₂) = a_m + 2 := by
          rw [ha_m_def, qz_top_affine m u_int d₂ d₃ hd2, hu_cast, hr2]
          congr 1
          rw [show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
        refine close3 u_int hu_ndvd a_m (fun k₀ => ?_)
        have hmem' : qz m (u_int * b₁ k₀) ∈
            ({qz m (u_int * d₁), qz m (u_int * d₂), qz m (u_int * d₃)} : Finset (ZMod 7)) := by
          rw [← hset_eq u_int]; fin_cases k₀ <;> simp
        rw [hqd1, hqd2, ← ha_m_def] at hmem'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
        rcases hmem' with h' | h' | h'
        · exact ⟨⟨1, by omega⟩, by rw [h']; simp⟩
        · exact ⟨⟨2, by omega⟩, by rw [h']; simp⟩
        · exact ⟨⟨0, by omega⟩, by rw [h']; simp⟩
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · obtain ⟨lam₀, hlam₀, a, hB_fit⟩ :=
            lemma9_ii_j2 m h hlt d₁ d₂ d₃
              (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm) hd1 hd1' hd2 hd2' hr2
          refine close3 lam₀ hlam₀ a (fit_of_set lam₀ a 2 (by omega) ?_)
          rw [hset_eq lam₀]; exact hB_fit
        · -- h > m: all A₁ arcs coincide (7^(m+1) ∣ differences); ℓ(A₁)=1.
          exact close_hgt d₁ d₂ d₃ hperm
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)
    · -- ratio 3
      by_cases hheq : h = m
      · -- h = m: r⁻¹ normalize → A₁ arcs at {a_m, a_m+1, a_m+3} (ℓ=4). Then Lemma 7
        -- controls ẽ(d₃, A₂-element) ∈ {0,1,6} for a suitable A₂ element → lemma12_ii.
        rw [hheq] at hd1 hd1' hd2 hd2' hr3
        -- ── r⁻¹ frame ──
        set r : ZMod 7 := (((d₁ - d₃) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
        have hr_ne : r ≠ 0 := by
          obtain ⟨c, hc⟩ := hd1
          have hdiv : (d₁ - d₃) / (7 : ℤ) ^ m = c := by
            rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
          rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro ⟨w, hw⟩; exact hd1' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
        set u_int : ℤ := ((r⁻¹ : ZMod 7).val : ℤ) with hu_int_def
        have hu_cast : (u_int : ZMod 7) = r⁻¹ := by simp [hu_int_def, ZMod.natCast_val]
        have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
          intro hdvd
          have h1 : (u_int : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr hdvd
          exact hr_ne (inv_eq_zero.mp (hu_cast ▸ h1))
        -- d₃ residue 1.
        -- (already have he₃_res)
        -- ── Lemma 7 pair (d₃, i₄): residue relation 2 = 2·1 ──
        haveI h7p : Fact (Nat.Prime 7) := ⟨by decide⟩
        -- Sub-lemma: applying Lemma 7 to control ẽ(d₃, i_ctrl) ∈ {0,1,6} then close4.
        -- `i_ctrl` is one A₂ element, `i_oth` the other; both cover A₂.
        have close_via_L7 : ∀ (i_ctrl i_oth : Fin 5),
            (d i_ctrl : ZMod 7) = 2 → (d i_oth : ZMod 7) = 2 →
            (∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i_ctrl ∨ i = i_oth) →
            ((7 : ℤ) ^ m ∣ (2 * (u_int * d₃) - u_int * d i_ctrl) →
              qz m (2 * (u_int * d₃) - u_int * d i_ctrl) ∉ (({2,3,4,5} : Finset (ZMod 7)) ∩
                (({2,3,4,5} : Finset (ZMod 7)).image (· + 1)))) →
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
              qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
          intro i_ctrl i_oth hctrl_res hoth_res htri' hXX
          -- residue relation for the pair (u·d₃, u·d i_ctrl): res(u·d i_ctrl) = 2·res(u·d₃)
          have hr_L7 : ((u_int * d i_ctrl : ℤ) : ZMod 7) = 2 * ((u_int * d₃ : ℤ) : ZMod 7) := by
            push_cast; rw [hu_cast, hctrl_res, he₃_res, mul_one]; ring
          have hd_L7 : ¬ (7 : ℤ) ∣ (u_int * d i_ctrl) := by
            intro hdvd
            have h1 : (u_int : ZMod 7) * (d i_ctrl : ZMod 7) = 0 := by
              have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d i_ctrl) 7).mpr hdvd
              push_cast at this; exact this
            rcases mul_eq_zero.mp h1 with hh | hh
            · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
            · rw [hctrl_res] at hh; exact two_ne_zero_z7 hh
          have hd'_L7 : ¬ (7 : ℤ) ∣ (u_int * d₃) := by
            intro hdvd
            have h1 : (u_int : ZMod 7) * (d₃ : ZMod 7) = 0 := by
              have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d₃) 7).mpr hdvd
              push_cast at this; exact this
            rcases mul_eq_zero.mp h1 with hh | hh
            · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
            · rw [he₃_res] at hh; exact one_ne_zero hh
          -- Lemma 7 output: lam₁ ≡ 1, ẽ(lam₁·(u·d₃), lam₁·(u·d i_ctrl)) ∉ {2,3,4,5}.
          set e_L7 : ℤ := 2 * (u_int * d₃) - (u_int * d i_ctrl) with he_L7_def
          obtain ⟨lam₁, hl1_ndvd, hl1_res, hetal⟩ :
              ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
                (2 * qz m (lam * (u_int * d₃)) - qz m (lam * (u_int * d i_ctrl))) ∉
                  ({2, 3, 4, 5} : Finset (ZMod 7)) := by
            have hX46 : ∃ a : ZMod 7, fitsInterval ({2, 3, 4, 5} : Finset (ZMod 7)) a 4 :=
              ⟨2, fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact ⟨⟨0, by omega⟩, by norm_num⟩
                · exact ⟨⟨1, by omega⟩, by norm_num⟩
                · exact ⟨⟨2, by omega⟩, by norm_num⟩
                · exact ⟨⟨3, by omega⟩, by norm_num⟩⟩
            by_cases hm_dvd : (7 : ℤ) ^ m ∣ e_L7
            · exact lemma7_ii m 0 (by omega) (u_int * d₃) (u_int * d i_ctrl)
                hd'_L7 hd_L7 hr_L7 {2,3,4,5} hm_dvd (hXX hm_dvd)
            · have he_ne : e_L7 ≠ 0 := fun heq => hm_dvd (heq ▸ dvd_zero _)
              set ν := padicValInt 7 e_L7 with hν_def
              have hν_lt_m : ν < m := by
                by_contra hge; push_neg at hge
                exact hm_dvd ((padicValInt_dvd_iff m e_L7).mpr (Or.inr hge))
              have hν_ndvd : ¬ (7 : ℤ) ^ (ν + 1) ∣ e_L7 := by
                intro hh
                have hle : ν + 1 ≤ padicValInt 7 e_L7 :=
                  ((padicValInt_dvd_iff (ν + 1) e_L7).mp hh).resolve_left he_ne
                omega
              exact lemma7_i m ν hν_lt_m (u_int * d₃) (u_int * d i_ctrl)
                  hd'_L7 hd_L7 hr_L7 {2,3,4,5} hX46
                  (padicValInt_dvd e_L7) hν_ndvd
          -- ── Arcs after composite lam₁·u_int (residue r⁻¹) ──
          have hlu_cast : ((lam₁ * u_int : ℤ) : ZMod 7) = r⁻¹ := by
            push_cast; rw [hl1_res, hu_cast, one_mul]
          set a_m' : ZMod 7 := qz m (lam₁ * (u_int * d₃)) with ha_m'_def
          have hqd1' : qz m (lam₁ * (u_int * d₁)) = a_m' + 1 := by
            rw [show lam₁ * (u_int * d₁) = (lam₁ * u_int) * d₁ from by ring,
                qz_top_affine m (lam₁ * u_int) d₁ d₃ hd1,
                show (lam₁ * u_int) * d₃ = lam₁ * (u_int * d₃) from by ring,
                hlu_cast, ← hr_def, inv_mul_cancel₀ hr_ne]
          have hqd2' : qz m (lam₁ * (u_int * d₂)) = a_m' + 3 := by
            rw [show lam₁ * (u_int * d₂) = (lam₁ * u_int) * d₂ from by ring,
                qz_top_affine m (lam₁ * u_int) d₂ d₃ hd2, hlu_cast, hr3,
                show (lam₁ * u_int) * d₃ = lam₁ * (u_int * d₃) from by ring]
            congr 1
            rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
          -- A₁ arcs land in the 4-window {a_m', a_m'+1, a_m'+2, a_m'+3}.
          have hfit4 : ∀ k₀ : Fin 3, ∃ j : Fin 4,
              qz m ((lam₁ * u_int) * b₁ k₀) = a_m' + (j.val : ZMod 7) := by
            intro k₀
            have hmem' : qz m ((lam₁ * u_int) * b₁ k₀) ∈
                ({qz m ((lam₁ * u_int) * d₁), qz m ((lam₁ * u_int) * d₂),
                  qz m ((lam₁ * u_int) * d₃)} : Finset (ZMod 7)) := by
              rw [← hset_eq (lam₁ * u_int)]; fin_cases k₀ <;> simp
            rw [show (lam₁ * u_int) * d₁ = lam₁ * (u_int * d₁) from by ring,
                show (lam₁ * u_int) * d₂ = lam₁ * (u_int * d₂) from by ring,
                show (lam₁ * u_int) * d₃ = lam₁ * (u_int * d₃) from by ring,
                hqd1', hqd2', ← ha_m'_def] at hmem'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
            rcases hmem' with h' | h' | h'
            · exact ⟨⟨1, by omega⟩, by rw [h']; simp⟩
            · exact ⟨⟨3, by omega⟩, by rw [h']; simp⟩
            · exact ⟨⟨0, by omega⟩, by rw [h']; simp⟩
          -- ẽ condition: 2·a_m' − qz(lam₁·u·d_ctrl) ∈ {0,1,6} (complement of {2,3,4,5}).
          have he_cond : 2 * a_m' - qz m ((lam₁ * u_int) * d i_ctrl) ∈
              ({0, 1, 6} : Finset (ZMod 7)) := by
            rw [show (lam₁ * u_int) * d i_ctrl = lam₁ * (u_int * d i_ctrl) from by ring]
            exact mem_016_of_notmem_2345 _ hetal
          -- ── close4 with the composite multiplier ──
          exact close4 (lam₁ * u_int)
            (by
              have hp : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
              intro hdvd; rcases hp.dvd_mul.mp hdvd with hh | hh
              · exact hl1_ndvd hh
              · exact hu_ndvd hh)
            a_m' i_ctrl i_oth hctrl_res hoth_res htri' hfit4 he_cond
        -- htri with the two A₂ indices in either order.
        have htri45 : ∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i₄ ∨ i = i₅ := hi_tri
        have htri54 : ∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i₅ ∨ i = i₄ := by
          intro i; rcases hi_tri i with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
        -- e-differences 2·d₃ − d_i₄ / 2·d₃ − d_i₅ (residue 0), and their u-dilated forms.
        set e4 : ℤ := 2 * d₃ - d i₄ with he4_def
        set e5 : ℤ := 2 * d₃ - d i₅ with he5_def
        -- hXX for a controlled index below level m (vacuous antecedent).
        have hXX_vac : ∀ (ic : Fin 5), ¬ (7 : ℤ) ^ m ∣ (2 * d₃ - d ic) →
            ((7 : ℤ) ^ m ∣ (2 * (u_int * d₃) - u_int * d ic) →
              qz m (2 * (u_int * d₃) - u_int * d ic) ∉ (({2,3,4,5} : Finset (ZMod 7)) ∩
                (({2,3,4,5} : Finset (ZMod 7)).image (· + 1)))) := by
          intro ic hnd hdvd
          exact absurd (by
            rwa [show 2 * (u_int * d₃) - u_int * d ic = u_int * (2 * d₃ - d ic) from by ring]
              at hdvd) (pow7_ndvd_mul m u_int (2 * d₃ - d ic) hu_ndvd hnd)
        -- Dispatch: try to control i₄, else i₅, else the ν(e₄)=ν(e₅)=m fallback.
        by_cases hd4 : (7 : ℤ) ^ m ∣ e4
        · by_cases hd5 : (7 : ℤ) ^ m ∣ e5
          · -- Both ẽ-differences at level ≥ m. Try lemma7_ii on i₄, then i₅, else fallback.
            by_cases hq4 : qz m (2 * (u_int * d₃) - u_int * d i₄) ∈ ({3,4,5} : Finset (ZMod 7))
            · by_cases hq5 : qz m (2 * (u_int * d₃) - u_int * d i₅) ∈ ({3,4,5} : Finset (ZMod 7))
              · -- FALLBACK: both qz∈{3,4,5} (BS L693–696). Unified endgame: pick a
                -- frame unit `c` and carry `δ` from `fallback_64_choice`; in the
                -- frame `w' = lam₁·c·u` (with `lam₁ ∈ Λ₁` pinning the doubling
                -- carry of `w'·d₃` to `δ` via `qz_retarget` on `q(7·w·d₃)`), the
                -- A₁ arcs sit at {A₀, A₀+c, A₀+3c} and the A₂ arcs at
                -- {2A₀+δ−c·t₄, 2A₀+δ−c·t₅}; a Λ_m base shift (`lift_shift`) closes.
                set t₄ : ZMod 7 := qz m (2 * (u_int * d₃) - u_int * d i₄) with ht₄_def
                set t₅ : ZMod 7 := qz m (2 * (u_int * d₃) - u_int * d i₅) with ht₅_def
                obtain ⟨c, δ, Atar, hc_ne, hδ, hA, hAc, hA3c, hq₄', hq₅'⟩ :=
                  fallback_64_choice t₄ t₅ hq4 hq5
                have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
                -- Integer lift of the frame unit c.
                set c_int : ℤ := ((c.val : ℕ) : ℤ) with hc_int_def
                have hc_cast : (c_int : ZMod 7) = c := by
                  simp [hc_int_def, ZMod.natCast_val]
                have hc_ndvd : ¬ (7 : ℤ) ∣ c_int := fun hdvd =>
                  hc_ne (hc_cast ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd c_int 7).mpr hdvd)
                set w : ℤ := c_int * u_int with hw_def
                have hw_ndvd : ¬ (7 : ℤ) ∣ w := by
                  intro hdvd
                  rcases hp7.dvd_mul.mp hdvd with hh | hh
                  · exact hc_ndvd hh
                  · exact hu_ndvd hh
                have hd₃_ndvd : ¬ (7 : ℤ) ∣ d₃ := by
                  intro hdvd
                  have h0 : (d₃ : ZMod 7) = 0 :=
                    (ZMod.intCast_zmod_eq_zero_iff_dvd d₃ 7).mpr hdvd
                  rw [he₃_res] at h0; exact one_ne_zero h0
                -- Λ₁ retarget of q(7·w·d₃): target 0 pins carry 0, target 6 pins carry 1.
                have h7wd_dvd : (7 : ℤ) ^ 1 ∣ 7 * (w * d₃) := ⟨w * d₃, by ring⟩
                have h7wd_ndvd : ¬ (7 : ℤ) ^ (1 + 1) ∣ 7 * (w * d₃) := by
                  rintro ⟨cc, hcc⟩
                  have hwd : (7 : ℤ) ∣ w * d₃ := by
                    refine ⟨cc, mul_left_cancel₀ (show (7 : ℤ) ≠ 0 from by norm_num) ?_⟩
                    rw [hcc]; ring
                  rcases hp7.dvd_mul.mp hwd with hh | hh
                  · exact hw_ndvd hh
                  · exact hd₃_ndvd hh
                have h7z : (7 : ZMod 7) = 0 := seven_eq_zero_z7
                have hpin : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
                    qz m (2 * ((lam * w) * d₃)) = 2 * qz m ((lam * w) * d₃) + δ := by
                  rcases hδ with hδ0 | hδ1
                  · obtain ⟨k₁, hqk₁, hk₁u⟩ :=
                      qz_retarget m 1 (by omega) (7 * (w * d₃)) h7wd_dvd h7wd_ndvd 0
                    have hlamres : ((1 + k₁ * 7 ^ (m - 1) : ℤ) : ZMod 7) = 1 := by
                      push_cast
                      rw [h7z, zero_pow (show m - 1 ≠ 0 from by omega), mul_zero, add_zero]
                    refine ⟨1 + k₁ * 7 ^ (m - 1), hk₁u, hlamres, ?_⟩
                    have hq7 : qz m (7 * (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃)) = 0 := by
                      rw [show (7 : ℤ) * (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃)
                          = (1 + k₁ * 7 ^ (m - 1)) * (7 * (w * d₃)) from by ring]
                      exact hqk₁
                    rw [qz_double_no_carry m (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃) hq7,
                      hδ0, add_zero]
                  · obtain ⟨k₁, hqk₁, hk₁u⟩ :=
                      qz_retarget m 1 (by omega) (7 * (w * d₃)) h7wd_dvd h7wd_ndvd 6
                    have hlamres : ((1 + k₁ * 7 ^ (m - 1) : ℤ) : ZMod 7) = 1 := by
                      push_cast
                      rw [h7z, zero_pow (show m - 1 ≠ 0 from by omega), mul_zero, add_zero]
                    refine ⟨1 + k₁ * 7 ^ (m - 1), hk₁u, hlamres, ?_⟩
                    have hq7 : qz m (7 * (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃)) = 6 := by
                      rw [show (7 : ℤ) * (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃)
                          = (1 + k₁ * 7 ^ (m - 1)) * (7 * (w * d₃)) from by ring]
                      exact hqk₁
                    rw [qz_double_carry_one m (by omega) (((1 + k₁ * 7 ^ (m - 1)) * w) * d₃) hq7,
                      hδ1]
                obtain ⟨lam₁, hlam₁_ndvd, hlam₁_res, hdouble₀⟩ := hpin
                set w' : ℤ := lam₁ * w with hw'_def
                have hw'_ndvd : ¬ (7 : ℤ) ∣ w' := by
                  intro hdvd
                  rcases hp7.dvd_mul.mp hdvd with hh | hh
                  · exact hlam₁_ndvd hh
                  · exact hw_ndvd hh
                have hw'_res : (w' : ZMod 7) = c * r⁻¹ := by
                  rw [hw'_def, hw_def]
                  push_cast
                  rw [hlam₁_res, hc_cast, hu_cast]; ring
                set A₀ : ZMod 7 := qz m (w' * d₃) with hA₀_def
                -- A₁ arcs: {A₀, A₀+c, A₀+3c}.
                have harc₁ : qz m (w' * d₁) = A₀ + c := by
                  rw [qz_top_affine m w' d₁ d₃ hd1, ← hr_def, hw'_res,
                    show c * r⁻¹ * r = c * (r⁻¹ * r) from by ring,
                    inv_mul_cancel₀ hr_ne, mul_one]
                have harc₂ : qz m (w' * d₂) = A₀ + 3 * c := by
                  rw [qz_top_affine m w' d₂ d₃ hd2, hr3, hw'_res,
                    show c * r⁻¹ * (3 * r) = 3 * c * (r⁻¹ * r) from by ring,
                    inv_mul_cancel₀ hr_ne, mul_one]
                -- A₂ arcs: {2A₀+δ−c·t₄, 2A₀+δ−c·t₅} via qz_sub_mul_pow + the pinned carry.
                obtain ⟨γ₄, hγ₄⟩ := hd4
                obtain ⟨γ₅, hγ₅⟩ := hd5
                have hqz0 : qz m (0 : ℤ) = 0 := by simp [qz]
                have ht₄γ : t₄ = (u_int : ZMod 7) * (γ₄ : ZMod 7) := by
                  rw [ht₄_def, show 2 * (u_int * d₃) - u_int * d i₄
                      = 0 + (u_int * γ₄) * 7 ^ m from by
                    rw [he4_def] at hγ₄; linear_combination u_int * hγ₄,
                    qz_add_mul_pow, hqz0, zero_add]
                  push_cast; ring
                have ht₅γ : t₅ = (u_int : ZMod 7) * (γ₅ : ZMod 7) := by
                  rw [ht₅_def, show 2 * (u_int * d₃) - u_int * d i₅
                      = 0 + (u_int * γ₅) * 7 ^ m from by
                    rw [he5_def] at hγ₅; linear_combination u_int * hγ₅,
                    qz_add_mul_pow, hqz0, zero_add]
                  push_cast; ring
                have harc₄ : qz m (w' * d i₄) = 2 * A₀ + δ - c * t₄ := by
                  have hsplit : w' * d i₄ = 2 * (w' * d₃) - 7 ^ m * (w' * γ₄) := by
                    rw [he4_def] at hγ₄; linear_combination (-w') * hγ₄
                  rw [hsplit, qz_sub_mul_pow, hdouble₀,
                    show ((w' * γ₄ : ℤ) : ZMod 7) = c * t₄ from by
                      push_cast; rw [hw'_res, ht₄γ, hu_cast]; ring]
                have harc₅ : qz m (w' * d i₅) = 2 * A₀ + δ - c * t₅ := by
                  have hsplit : w' * d i₅ = 2 * (w' * d₃) - 7 ^ m * (w' * γ₅) := by
                    rw [he5_def] at hγ₅; linear_combination (-w') * hγ₅
                  rw [hsplit, qz_sub_mul_pow, hdouble₀,
                    show ((w' * γ₅ : ℤ) : ZMod 7) = c * t₅ from by
                      push_cast; rw [hw'_res, ht₅γ, hu_cast]; ring]
                -- Λ_m base shift to Atar and final assembly.
                refine lift_shift m (by omega) d w' hw'_ndvd (Atar - A₀) (fun i => ?_)
                rcases htri45 i with ⟨k₀, hk₀⟩ | hi | hi
                · subst hk₀
                  rw [hg₁_res k₀, mul_one]
                  have hmem : qz m (w' * b₁ k₀) ∈
                      ({qz m (w' * d₁), qz m (w' * d₂), qz m (w' * d₃)} : Finset (ZMod 7)) := by
                    rw [← hset_eq w']; fin_cases k₀ <;> simp
                  rw [harc₁, harc₂, ← hA₀_def] at hmem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                  rcases hmem with hv | hv | hv
                  · rw [show d (g₁ k₀) = b₁ k₀ from rfl, hv,
                      show A₀ + c + (Atar - A₀) = Atar + c from by ring]
                    exact hAc
                  · rw [show d (g₁ k₀) = b₁ k₀ from rfl, hv,
                      show A₀ + 3 * c + (Atar - A₀) = Atar + 3 * c from by ring]
                    exact hA3c
                  · rw [show d (g₁ k₀) = b₁ k₀ from rfl, hv,
                      show A₀ + (Atar - A₀) = Atar from by ring]
                    exact hA
                · subst hi
                  rw [hi₄_res, harc₄,
                    show 2 * A₀ + δ - c * t₄ + (Atar - A₀) * 2
                      = 2 * Atar + δ - c * t₄ from by ring]
                  exact hq₄'
                · subst hi
                  rw [hi₅_res, harc₅,
                    show 2 * A₀ + δ - c * t₅ + (Atar - A₀) * 2
                      = 2 * Atar + δ - c * t₅ from by ring]
                  exact hq₅'
              · -- Control i₅ via lemma7_ii (qz∉{3,4,5}).
                refine close_via_L7 i₅ i₄ hi₅_res hi₄_res htri54 (fun _ => ?_)
                intro hmem
                exact hq5 (inter_2345_image_subset_345 _ hmem)
            · -- Control i₄ via lemma7_ii (qz∉{3,4,5}).
              refine close_via_L7 i₄ i₅ hi₄_res hi₅_res htri45 (fun _ => ?_)
              intro hmem
              exact hq4 (inter_2345_image_subset_345 _ hmem)
          · -- ν(e₅) < m: control i₅ via lemma7_i (vacuous hXX).
            exact close_via_L7 i₅ i₄ hi₅_res hi₄_res htri54 (hXX_vac i₅ hd5)
        · -- ν(e₄) < m: control i₄ via lemma7_i (vacuous hXX).
          exact close_via_L7 i₄ i₅ hi₄_res hi₅_res htri45 (hXX_vac i₄ hd4)
      · rcases lt_or_gt_of_ne hheq with hlt | hgt
        · obtain ⟨lam₀, hlam₀, hrest⟩ :=
            lemma9_ii_j3 m h hlt d₁ d₂ d₃
              (he₁_res.trans he₃_res.symm) (he₂_res.trans he₃_res.symm) hd1 hd1' hd2 hd2' hr3
          obtain ⟨a, hB_fit⟩ := hrest.1
          refine close3 lam₀ hlam₀ a (fit_of_set lam₀ a 3 (by omega) ?_)
          rw [hset_eq lam₀]; exact hB_fit
        · -- h > m: all A₁ arcs coincide; ℓ(A₁)=1.
          exact close_hgt d₁ d₂ d₃ hperm
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (show m + 1 ≤ h by omega)) hd2)

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
