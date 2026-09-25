import LonelyRunner.LRC.Spec.OrderSevenS5bN
import LonelyRunner.LRC.Spec.OrderSevenLemmasN
import LonelyRunner.LRC.Spec.OrderSevenL79N
import LonelyRunner.LRC.Spec.OrderSevenL1012N
import LonelyRunner.LRC.Spec.OrderSevenA5ZeroN
import LonelyRunner.LRC.Spec.OrderSevenC61N
import LonelyRunner.LRC.Spec.OrderSevenC66N

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

namespace LRC.OrderSevenN

/-- `(2 : ZMod 7) ≠ 0` (hoisted so `decide` runs in a `let`-free context). -/
theorem two_ne_zero_z7 : (2 : ZMod 7) ≠ 0 := by decide

/-- `(7 : ZMod 7) = 0` (hoisted: local `Fact (Nat.Prime 7)` instances block `decide`). -/
theorem seven_eq_zero_z7 : (7 : ZMod 7) = 0 := by decide

/-- `(4 : ZMod 7) ≠ 0` (hoisted so `decide` runs in a `Fact`-free context). -/
theorem four_ne_zero_z7 : (4 : ZMod 7) ≠ 0 := by decide

/-- `(5 : ZMod 7) − 1 = 4` (hoisted: local `Fact (Nat.Prime 7)` blocks `decide`). -/
theorem five_sub_one_z7 : (5 : ZMod 7) - 1 = 4 := by decide

/-- `{2,4} ∩ ({2,4}+1) = ∅` — the empty `ν=m` gap of `lemma7_ii` with the tight
`X = {2,4}`. Since `{2,4}+1 = {3,5}` is disjoint from `{2,4}`, controlling
`ẽ ∉ {2,4}` at the top level needs no doubling fallback. -/
theorem inter24_empty :
    (({2, 4} : Finset (ZMod 7)) ∩ (({2, 4} : Finset (ZMod 7)).image (· + 1))) = ∅ := by decide

/-- The `ν=m` gap of `lemma7_ii` with `X = {2,3,4,5}` is `{3,4,5}`
(`{2,3,4,5} ∩ {3,4,5,6}`). -/
theorem inter2345_eq :
    (({2, 3, 4, 5} : Finset (ZMod 7)) ∩ (({2, 3, 4, 5} : Finset (ZMod 7)).image (· + 1)))
      = {3, 4, 5} := by decide

/-- Complement of `{2,3,4,5}` in `ZMod 7` is `{0,1,6}` (the `ẽ ∈ {0,1,6}` carve-out). -/
theorem mem_016_of_notmem_2345 (w : ZMod 7)
    (hw : w ∉ ({2, 3, 4, 5} : Finset (ZMod 7))) : w ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert hw; revert w; decide

/-- `{2,3,4,5} ∩ ({2,3,4,5}+1) = {3,4,5}` (the `hXX`-set of `lemma7_ii` for `X={2,3,4,5}`). -/
theorem inter_2345_image_subset_345 (w : ZMod 7)
    (hw : w ∈ (({2,3,4,5} : Finset (ZMod 7)) ∩
      (({2,3,4,5} : Finset (ZMod 7)).image (· + 1)))) : w ∈ ({3,4,5} : Finset (ZMod 7)) := by
  revert hw; revert w; decide

/-- `7`-power divisibility transfers off a coprime factor: if `7 ∤ u` and `7^m ∤ X`
then `7^m ∤ u·X`. (Used to make the `hXX` premise of `close_via_L7` vacuous when the
`ẽ`-difference sits below level `m`.) -/
theorem pow7_ndvd_mul (m : ℕ) (u X : ℤ) (hu : ¬ (7 : ℤ) ∣ u)
    (hX : ¬ (7 : ℤ) ^ m ∣ X) : ¬ (7 : ℤ) ^ m ∣ (u * X) := by
  intro hdvd
  have hp : Prime (7 : ℤ) := seven_totient_full_int
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
theorem fallback_64_choice (t₄ t₅ : ZMod 7)
    (h₄ : t₄ ∈ ({3, 4, 5} : Finset (ZMod 7)))
    (h₅ : t₅ ∈ ({3, 4, 5} : Finset (ZMod 7))) :
    ∃ c δ A : ZMod 7, c ≠ 0 ∧ (δ = 0 ∨ δ = 1) ∧
      A ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + c ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 3 * c ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * A + δ - c * t₄ ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * A + δ - c * t₅ ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert h₄ h₅; revert t₄ t₅; decide

/-! **§7 (`m = 1`) is not handled here.** The `|A| = 5, m = 1` case cannot be
stated in this file's `∃ lam, ¬ 7 ∣ lam ∧ qz 1 (lam·dᵢ) ∉ {0,6}` form: three
exceptional 5-sets over `ZMod 49` admit no such multiplier, and `d₆` cannot
rescue them at `N = 49` (a level-1 element only adds a constraint there). BS
resolve them at `N' = 98`, which is not a power of 7.

It is therefore handled jointly with the sixth element, one level up in the §4
reduction, by `five_band_m1` (`OrderSevenS7WireN`) via `m1_six_witness`
(`OrderSevenS7BridgeN`). Accordingly `five_avoid` and `five_band` below require
`2 ≤ m`. See `docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md`. -/

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
theorem mul_res_perm (d : Fin 5 → ℤ)
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
theorem mul_ndvd (d : Fin 5 → ℤ) (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (u : ℤ) (hu : ¬ (7 : ℤ) ∣ u) : ∀ i, ¬ (7 : ℤ) ∣ (u * d i) := by
  intro i h
  have hp : Prime (7 : ℤ) := seven_totient_full_int
  rcases hp.dvd_or_dvd h with h7 | h7
  · exact hu h7
  · exact hndvd i h7

/-- A nonzero dilation preserves injectivity: `dᵢ` distinct ⇒ `u·dᵢ` distinct. -/
theorem mul_inj (d : Fin 5 → ℤ) (hinj : Function.Injective d)
    (u : ℤ) (hu : u ≠ 0) : Function.Injective (fun i => u * d i) :=
  fun _ _ h => hinj (mul_left_cancel₀ hu h)

/-- The residue set `{1,2,4}` is closed under dilation by `2` or `4` (the order-3
subgroup of `(ZMod 7)*`). -/
theorem mul_res_mem (d : Fin 5 → ℤ)
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
theorem lift_shift (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ) (lam₀ : ℤ)
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

theorem case61_nonexception_shift (a p q : ZMod 7)
    (hex : ¬ ((p + (-a - 1) = 2 ∧ q + (-a - 1) = 4) ∨
      (p + (-a - 1) = 4 ∧ q + (-a - 1) = 2))) :
    ∃ t : ZMod 7, ∀ x ∈ ({a, a + 1, p, q} : Finset (ZMod 7)),
      x + t ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert hex; revert a p q; decide

/-! Finite terminal tables for the two remaining Barajas--Serra partitions. -/

/-- **BS (14), first disjunct** (L700): `ℓ(A₁) ≤ 3` and `ℓ(A₄) ≤ 3`. Holds for
ARBITRARY window starts `a₁, a₄` — stronger than BS, which normalizes `A₁` to
`q(A₁) = {1,2,3}` first, so the normalization step is not needed downstream. -/
theorem case65_window_33 (a₁ a₄ : ZMod 7) :
    ∃ k : ZMod 7, intervalAvoids a₁ 3 1 k ∧ intervalAvoids a₄ 3 4 k := by
  revert a₁ a₄; decide

/-- **BS (14), second disjunct** (L700): `ℓ(A₁) ≤ 4` and `ℓ(A₄) ≤ 2`. Again for
arbitrary window starts, generalizing `lemma6_402` (which pins `a₁ = 1`).

`ℓ₁ = 5` admits NO good multiplier for any `ℓ₄ ≥ 1`, so `ℓ(A₁) ≤ 4` is forced;
the full feasibility map is in `docs/n7_bs/AUTOMATION_v2.md` §6. -/
theorem case65_window_42 (a₁ a₄ : ZMod 7) :
    ∃ k : ZMod 7, intervalAvoids a₁ 4 1 k ∧ intervalAvoids a₄ 2 4 k := by
  revert a₁ a₄; decide

theorem case66_window_choice (a₁ a₂ a₄ : ZMod 7) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ 2 1 k ∧ intervalAvoids a₂ 2 2 k ∧
        intervalAvoids a₄ 1 4 k := by
  revert a₁ a₂ a₄
  decide


/-- `q(z) = 0` pins the residue to the bottom arc. -/
theorem lowarc_of_qz0 (m : ℕ) (z : ℤ) (h : qz m z = 0) :
    z % 7 ^ (m + 1) < 7 ^ m := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  obtain ⟨hq0, hq7⟩ := qval_range m z
  have hqv : qval m z = 0 := by
    rw [qz_eq_qval] at h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    omega
  have hdm := Int.mul_ediv_add_emod (z % 7 ^ (m + 1)) (7 ^ m)
  have hlt : (z % 7 ^ (m + 1)) % 7 ^ m < 7 ^ m := Int.emod_lt_of_pos _ hP
  unfold qval at hqv
  rw [hqv] at hdm
  omega

/-- At level exactly `m`, `q(z) = 1` pins the residue to `7^m`. -/
theorem exact_of_qz1 (m : ℕ) (z : ℤ) (hd : (7 : ℤ) ^ m ∣ z) (h : qz m z = 1) :
    z % 7 ^ (m + 1) = 7 ^ m := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  obtain ⟨hq0, hq7⟩ := qval_range m z
  have hqv : qval m z = 1 := by
    rw [qz_eq_qval] at h
    have : ((qval m z - 1 : ℤ) : ZMod 7) = 0 := by push_cast [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    omega
  have hdvd : (7 : ℤ) ^ m ∣ z % 7 ^ (m + 1) := by
    have hN : (7 : ℤ) ^ m ∣ 7 ^ (m + 1) := pow_dvd_pow 7 (by omega)
    have := Int.emod_add_mul_ediv z ((7 : ℤ) ^ (m + 1))
    have h2 : z % 7 ^ (m + 1) = z - 7 ^ (m + 1) * (z / 7 ^ (m + 1)) := by omega
    rw [h2]
    exact dvd_sub hd (Dvd.dvd.mul_right hN _)
  have hmul := Int.ediv_mul_cancel hdvd
  unfold qval at hqv
  rw [hqv] at hmul
  omega

/-- Arc index of `x` from an anchor `t` within one closed `7^m`-window. -/
theorem qz_near (m : ℕ) (x t : ℤ)
    (h : (x - t) % 7 ^ (m + 1) ≤ 7 ^ m) :
    qz m x = qz m t ∨ qz m x = qz m t + 1 := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hlo : 0 ≤ (x - t) % 7 ^ (m + 1) := Int.emod_nonneg _ (by positivity)
  rcases lt_or_eq_of_le h with hlt | heq
  · have h0 : qz m (x - t) = 0 := by
      rw [qz_eq_qval]
      unfold qval
      rw [Int.ediv_eq_zero_of_lt hlo hlt]
      simp
    have hc := qz_add_carry m t (x - t)
    rw [show t + (x - t) = x from by ring, h0, add_zero] at hc
    exact hc
  · -- the residue is exactly `7^m`, so `x = t + (1 + 7k)·7^m`
    have hrep : (x - t) % 7 ^ (m + 1) + 7 ^ (m + 1) * ((x - t) / 7 ^ (m + 1)) = x - t :=
      Int.emod_add_mul_ediv _ _
    have hpow : (7 : ℤ) ^ (m + 1) = 7 ^ m * 7 := by ring
    have hx : x = t + (1 + 7 * ((x - t) / 7 ^ (m + 1))) * 7 ^ m := by
      rw [heq] at hrep
      linear_combination -hrep + ((x - t) / 7 ^ (m + 1)) * hpow
    right
    rw [hx, qz_add_mul_pow]
    push_cast
    rw [show (7 : ZMod 7) = 0 from by decide]
    ring

/-- Tripling multiplies the arc index by `3` up to a `{0,1,2}` carry. -/
theorem qz_triple (m : ℕ) (z : ℤ) :
    ∃ c : ZMod 7, (c = 0 ∨ c = 1 ∨ c = 2) ∧ qz m (3 * z) = 3 * qz m z + c := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  have hz : (7 : ℤ) ^ m * (z / 7 ^ m) + z % 7 ^ m = z := Int.mul_ediv_add_emod z _
  have hr0 : 0 ≤ z % 7 ^ m := Int.emod_nonneg z hPne
  have hrP : z % 7 ^ m < 7 ^ m := Int.emod_lt_of_pos z hP
  obtain ⟨c, hc0, hc2, hdiv⟩ : ∃ c : ℤ, 0 ≤ c ∧ c ≤ 2 ∧
      3 * z / 7 ^ m = 3 * (z / 7 ^ m) + c := by
    refine ⟨3 * (z % 7 ^ m) / 7 ^ m, Int.ediv_nonneg (by omega) (le_of_lt hP), ?_, ?_⟩
    · nlinarith [Int.mul_ediv_add_emod (3 * (z % 7 ^ m)) ((7 : ℤ) ^ m),
        Int.emod_nonneg (3 * (z % 7 ^ m)) hPne, hrP, hP]
    · rw [show 3 * z = 3 * (z % 7 ^ m) + (3 * (z / 7 ^ m)) * 7 ^ m from by
        linear_combination -3 * hz, Int.add_mul_ediv_right _ _ hPne]
      ring
  refine ⟨(c : ZMod 7), ?_, ?_⟩
  · interval_cases c
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl (by norm_num))
    · exact Or.inr (Or.inr (by norm_num))
  · unfold qz
    rw [hdiv]
    push_cast
    ring

/-- Tripled window: an anchor within one closed `7^m`-window becomes a length-4
window after multiplication by `3`. -/
theorem triple_win (m : ℕ) (x t : ℤ)
    (h : (x - t) % 7 ^ (m + 1) ≤ 7 ^ m) :
    (qz m (3 * x) - qz m (3 * t)).val ≤ 3 := by
  have hlo : 0 ≤ (x - t) % 7 ^ (m + 1) := Int.emod_nonneg _ (by positivity)
  rcases lt_or_eq_of_le h with hlt | heq
  · exact rmk8_concl m t (fun _ : Fin 1 => x) (fun _ => hlt) 0
  · have hrep : (x - t) % 7 ^ (m + 1) + 7 ^ (m + 1) * ((x - t) / 7 ^ (m + 1)) = x - t :=
      Int.emod_add_mul_ediv _ _
    have hpow : (7 : ℤ) ^ (m + 1) = 7 ^ m * 7 := by ring
    have hx : 3 * x = 3 * t + (3 + 21 * ((x - t) / 7 ^ (m + 1))) * 7 ^ m := by
      rw [heq] at hrep
      linear_combination -3 * hrep + 3 * ((x - t) / 7 ^ (m + 1)) * hpow
    rw [hx, qz_add_mul_pow]
    have h21 : ((3 + 21 * ((x - t) / 7 ^ (m + 1)) : ℤ) : ZMod 7) = 3 := by
      push_cast
      rw [show (21 : ZMod 7) = 0 from by decide]
      ring
    rw [h21, show qz m (3 * t) + 3 - qz m (3 * t) = (3 : ZMod 7) from by ring]
    decide

/-- One element into the closed bottom window `[0, 7^m]`, at any level. -/
theorem anchor_one (m h : ℕ) (z : ℤ)
    (hz : (7 : ℤ) ^ h ∣ z) (hz' : ¬ (7 : ℤ) ^ (h + 1) ∣ z) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam * z) % 7 ^ (m + 1) ≤ 7 ^ m := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  by_cases htop : (7 : ℤ) ^ (m + 1) ∣ z
  · exact ⟨1, by norm_num, by
      rw [Int.emod_eq_zero_of_dvd (by rw [one_mul]; exact htop)]; omega⟩
  · have hhm : h ≤ m := by
      by_contra hc
      exact htop (dvd_trans (pow_dvd_pow 7 (by omega)) hz)
    rcases lt_or_eq_of_le hhm with hlt | heq
    · obtain ⟨k, hqk, hku⟩ := qz_retarget m h hlt z hz hz' 0
      exact ⟨_, hku, le_of_lt (lowarc_of_qz0 m _ hqk)⟩
    · rw [heq] at hz hz'
      obtain ⟨j, hju, hjq⟩ := qz_retarget_top m z hz hz' 1 (by decide)
      exact ⟨j, hju, le_of_eq (exact_of_qz1 m (j * z) (hz.mul_left j) hjq)⟩

/-- **Anchor for a distinct-valuation pair.** If `x`, `y` have different `7`-adic
valuations then one unit multiplier puts both residues into the closed bottom
window `[0, 7^m]` — i.e. `{0, λx, λy}` lies in one closed `7^m`-window. -/
theorem anchor_pair (m h₁ h₂ : ℕ) (hne : h₁ ≠ h₂) (x y : ℤ)
    (hx : (7 : ℤ) ^ h₁ ∣ x) (hx' : ¬ (7 : ℤ) ^ (h₁ + 1) ∣ x)
    (hy : (7 : ℤ) ^ h₂ ∣ y) (hy' : ¬ (7 : ℤ) ^ (h₂ + 1) ∣ y) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      (lam * x) % 7 ^ (m + 1) ≤ 7 ^ m ∧ (lam * y) % 7 ^ (m + 1) ≤ 7 ^ m := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  by_cases hxtop : (7 : ℤ) ^ (m + 1) ∣ x
  · obtain ⟨lam, hlam, hly⟩ := anchor_one m h₂ y hy hy'
    exact ⟨lam, hlam, by
      rw [Int.emod_eq_zero_of_dvd (hxtop.mul_left lam)]; omega, hly⟩
  · by_cases hytop : (7 : ℤ) ^ (m + 1) ∣ y
    · obtain ⟨lam, hlam, hlx⟩ := anchor_one m h₁ x hx hx'
      exact ⟨lam, hlam, hlx, by
        rw [Int.emod_eq_zero_of_dvd (hytop.mul_left lam)]; omega⟩
    · have h1m : h₁ ≤ m := by
        by_contra hc; exact hxtop (dvd_trans (pow_dvd_pow 7 (by omega)) hx)
      have h2m : h₂ ≤ m := by
        by_contra hc; exact hytop (dvd_trans (pow_dvd_pow 7 (by omega)) hy)
      rcases lt_or_eq_of_le h1m with h1lt | h1eq
      · rcases lt_or_eq_of_le h2m with h2lt | h2eq
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · obtain ⟨lam, hlam, hqy, hqx⟩ :=
              qz_retarget_two m h₂ h₁ h2lt hlt y x hy hy' hx hx' 0 0
            exact ⟨lam, hlam, le_of_lt (lowarc_of_qz0 m _ hqx),
              le_of_lt (lowarc_of_qz0 m _ hqy)⟩
          · obtain ⟨lam, hlam, hqx, hqy⟩ :=
              qz_retarget_two m h₁ h₂ h1lt hgt x y hx hx' hy hy' 0 0
            exact ⟨lam, hlam, le_of_lt (lowarc_of_qz0 m _ hqx),
              le_of_lt (lowarc_of_qz0 m _ hqy)⟩
        · rw [h2eq] at hy hy'
          obtain ⟨lam, hlam, hqy, hqx⟩ :=
            qz_retarget_two_top m h₁ h1lt y x hy hy' hx hx' 1 0 (by decide)
          exact ⟨lam, hlam, le_of_lt (lowarc_of_qz0 m _ hqx),
            le_of_eq (exact_of_qz1 m (lam * y) (hy.mul_left lam) hqy)⟩
      · rw [h1eq] at hx hx'
        have h2lt : h₂ < m := by omega
        obtain ⟨lam, hlam, hqx, hqy⟩ :=
          qz_retarget_two_top m h₂ h2lt x y hx hx' hy hy' 1 0 (by decide)
        exact ⟨lam, hlam,
          le_of_eq (exact_of_qz1 m (lam * x) (hx.mul_left lam) hqx),
          le_of_lt (lowarc_of_qz0 m _ hqy)⟩


/-- The `{p,q} = {2,4}` exception window after tripling. -/
theorem case61_exc_window (a c : ZMod 7) (hc : c.val ≤ 2) :
    ∃ W : ZMod 7, ∀ v : ZMod 7,
      ((v - (3 * a + c)).val ≤ 3 ∨ (v - 3 * (a + 3)).val ≤ 2 ∨
        (v - 3 * (a + 5)).val ≤ 2) → (v - W).val ≤ 4 := by
  revert hc; revert a c; decide

/-- `7^m ∣ z` forces every lower arc index to vanish. -/
theorem qz_zero_of_dvd_pow (m j : ℕ) (hj : j < m) (z : ℤ) (h : (7 : ℤ) ^ m ∣ z) :
    qz j z = 0 := by
  obtain ⟨w, hw⟩ := h
  unfold qz
  rw [hw, show (7 : ℤ) ^ m = 7 ^ j * 7 ^ (m - j) from by rw [← pow_add]; congr 1; omega,
    show (7 : ℤ) ^ j * 7 ^ (m - j) * w = (7 ^ (m - j) * w) * 7 ^ j from by ring,
    Int.mul_ediv_cancel _ (by positivity), ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Dvd.dvd.mul_right (dvd_pow_self 7 (by omega : m - j ≠ 0)) w

/-- Conversely, all lower arc indices vanishing forces `7^m ∣ z`. -/
theorem dvd_pow_of_qz_zero (m : ℕ) (z : ℤ) (h : ∀ j, j < m → qz j z = 0) :
    (7 : ℤ) ^ m ∣ z := by
  by_contra hcon
  have hz : z ≠ 0 := by rintro rfl; exact hcon (dvd_zero _)
  obtain ⟨v, hv, hv'⟩ := exists_val7 z hz
  have hvm : v < m := by
    by_contra hc
    exact hcon (dvd_trans (pow_dvd_pow 7 (by omega)) hv)
  obtain ⟨w, hw⟩ := hv
  have hq := h v hvm
  unfold qz at hq
  rw [hw, show (7 : ℤ) ^ v * w = w * 7 ^ v from by ring,
    Int.mul_ediv_cancel _ (by positivity), ZMod.intCast_zmod_eq_zero_iff_dvd] at hq
  obtain ⟨c, hc⟩ := hq
  exact hv' ⟨c, by rw [hw, hc, pow_succ]; ring⟩

/-- Orientation flip for `q(·) ∈ {0,6}`: the only obstruction is the arc boundary
`z ≡ 6·7^m`, which is excluded once `7^m ∤ z`. -/
theorem qz_neg_mem06 (m : ℕ) (z : ℤ) (hlev : ¬ (7 : ℤ) ^ m ∣ z)
    (hz : qz m z ∈ ({0, 6} : Finset (ZMod 7))) :
    qz m (-z) ∈ ({0, 6} : Finset (ZMod 7)) := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hNval : (7 : ℤ) ^ (m + 1) = 7 * 7 ^ m := by ring
  have hu0 : 0 ≤ z % 7 ^ (m + 1) := Int.emod_nonneg _ (by positivity)
  have huN : z % 7 ^ (m + 1) < 7 ^ (m + 1) := Int.emod_lt_of_pos _ (by positivity)
  have hnd : ¬ ((7 : ℤ) ^ m ∣ z % 7 ^ (m + 1)) := by
    intro hdvd
    refine hlev ?_
    have hrep : z % 7 ^ (m + 1) + 7 ^ (m + 1) * (z / 7 ^ (m + 1)) = z :=
      Int.emod_add_mul_ediv _ _
    have hN : (7 : ℤ) ^ m ∣ 7 ^ (m + 1) * (z / 7 ^ (m + 1)) :=
      Dvd.dvd.mul_right (pow_dvd_pow 7 (by omega)) _
    exact hrep ▸ dvd_add hdvd hN
  have hune : z % 7 ^ (m + 1) ≠ 6 * 7 ^ m := fun he => hnd ⟨6, by rw [he]; ring⟩
  have hneg : (-z) % 7 ^ (m + 1) = (-(z % 7 ^ (m + 1))) % 7 ^ (m + 1) := by
    conv_lhs => rw [show -z = 0 - z from by ring]
    rw [Int.sub_emod]
    simp
  rw [qz_mem06_iff] at hz ⊢
  by_cases h0 : z % 7 ^ (m + 1) = 0
  · rw [hneg, h0]
    simp
  · have hval : (-z) % 7 ^ (m + 1) = 7 ^ (m + 1) - z % 7 ^ (m + 1) := by
      rw [hneg, show -(z % 7 ^ (m + 1))
          = (7 ^ (m + 1) - z % 7 ^ (m + 1)) + 7 ^ (m + 1) * (-1) from by ring,
        Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hval]
    omega

/-- If the leading residue `δ/7^h` is a unit then `7^(h+1) ∤ δ`. -/
theorem ndvd_succ_of_res_ne {δ : ℤ} {h : ℕ} (_hd : (7 : ℤ) ^ h ∣ δ)
    (hne : ((δ / 7 ^ h : ℤ) : ZMod 7) ≠ 0) : ¬ (7 : ℤ) ^ (h + 1) ∣ δ := by
  rintro ⟨c, hc⟩
  refine hne ?_
  have hq : δ / 7 ^ h = 7 * c := by
    rw [hc, pow_succ, show (7 : ℤ) ^ h * 7 * c = (7 * c) * 7 ^ h from by ring]
    exact Int.mul_ediv_cancel _ (by positivity)
  rw [hq]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide]
  ring

set_option maxHeartbeats 1000000 in
/-- **BS Lemma 9 (ii), `j = 2`, difference form.** Same two-stage `Λ`-retarget as
`lemma9_ii_j2`, but exposing the three pairwise arc-index differences
`q(λ·(B−B)) ⊂ {0,6}` that Remark 8(i) consumes — this is what the `3·` remultiply
of BS §6.1 needs, and `fitsInterval` alone does not supply it. -/
theorem ratio2_diffs (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (_hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      qz m (lam * b₁ - lam * b₂) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qz m (lam * b₁ - lam * b₃) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qz m (lam * b₂ - lam * b₃) ∈ ({0, 6} : Finset (ZMod 7)) := by
  -- Two-stage Λ-retarget (the documented `ẽ = 1` gap is closed by the carry implication
  -- `qz_combined_carry`). Set `x = b₁−b₃`, `y = b₂−b₃`, `e = 2x−y`; `r(y)=2r(x)` forces
  -- `ν₇(e) ≥ h+1 > h`. STAGE 1 sets `q(λ₁·e) = se ∈ {0,6}` (a `Λ_{h'}`/`Λ_m` retarget at
  -- the exact level of `e`, or `λ₁=1` if `7^{m+1}∣e`). STAGE 2 applies a `Λ_h` factor on
  -- `λ₁·x` to a target `t = f(se, c₃)`: `ẽ = 2q(λ₁x)−q(λ₁y) = se − c₃` is `Λ_h`-invariant
  -- (Lemma 4(i)) and `e` is inert under `Λ_h` (higher level), so in the final frame all
  -- three pairwise `q`-differences land in `{0,6}` and `remark8_i_int` gives `ℓ ≤ 2`. The
  -- carry implication `c₃=6⇒c₁=6`, `c₃=1⇒c₁=0` (`qz_combined_carry`) is exactly what
  -- rules out the bad `(c₃,c₁)` combos a single retarget cannot avoid.
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  set x : ℤ := b₁ - b₃ with hxdef
  set y : ℤ := b₂ - b₃ with hydef
  set e : ℤ := 2 * x - y with hedef
  -- Step 1: `r(y) = 2·r(x)` forces `7^{h+1} ∣ e` (the level-h terms of `2x−y` cancel).
  have he_lo : (7 : ℤ) ^ (h + 1) ∣ e := by
    have he_dvd : (7 : ℤ) ^ h ∣ e := by
      rw [hedef]; exact dvd_sub (Dvd.dvd.mul_left hx 2) hy
    have hres : (((e) / 7 ^ h : ℤ) : ZMod 7) = 0 := by
      rw [hedef, Int.sub_ediv_of_dvd _ hy, Int.mul_ediv_assoc 2 hx]
      push_cast; rw [hr]; ring
    have h7 : (7 : ℤ) ∣ (e / 7 ^ h) := by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hres
    obtain ⟨c, hc⟩ := h7
    obtain ⟨w, hw⟩ := he_dvd
    refine ⟨c, ?_⟩
    have hwc : w = 7 * c := by
      have : e / 7 ^ h = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by positivity)
      rw [← this, hc]
    rw [hw, hwc, pow_succ]; ring
  -- STAGE 1: a unit `λ₁` and `se ∈ {0,6}` with `q(λ₁·e) = se`; `e` stays at level ≥ h+1.
  obtain ⟨lam₁, se, hlam₁, hse, hse_eq, he_high⟩ :
      ∃ (lam₁ : ℤ) (se : ZMod 7), ¬ (7 : ℤ) ∣ lam₁ ∧ (se = 0 ∨ se = 6) ∧
        qz m (lam₁ * e) = se ∧ (7 : ℤ) ^ (h + 1) ∣ lam₁ * e := by
    by_cases htop : (7 : ℤ) ^ (m + 1) ∣ e
    · -- `e ≡ 0 (mod 7^{m+1})`: `λ₁ = 1`, `q(e) = 0`.
      refine ⟨1, 0, by norm_num, Or.inl rfl, ?_, by rw [one_mul]; exact he_lo⟩
      rw [one_mul]; unfold qz
      obtain ⟨c, hc⟩ := htop
      rw [hc, pow_succ, show (7 : ℤ) ^ m * 7 * c = 7 ^ m * (7 * c) from by ring,
        Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by ring⟩
    · -- extract the exact level `h'` of `e` (`h+1 ≤ h' ≤ m`)
      obtain ⟨h', hh'lo, hh'hi, hh'd, hh'd'⟩ :
          ∃ h' : ℕ, h + 1 ≤ h' ∧ h' ≤ m ∧ (7 : ℤ) ^ h' ∣ e ∧ ¬ (7 : ℤ) ^ (h' + 1) ∣ e := by
        have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ e := ⟨m, htop⟩
        set j₀ := Nat.find hex with hj0
        have hspec : ¬ (7 : ℤ) ^ (j₀ + 1) ∣ e := Nat.find_spec hex
        have hle : j₀ ≤ m := Nat.find_le htop
        have hge : h + 1 ≤ j₀ := by
          by_contra hc; rw [not_le] at hc
          exact hspec (dvd_trans (pow_dvd_pow 7 (by omega)) he_lo)
        have hprev : ¬ ¬ (7 : ℤ) ^ ((j₀ - 1) + 1) ∣ e :=
          Nat.find_min hex (by omega : j₀ - 1 < j₀)
        rw [not_not] at hprev
        exact ⟨j₀, hge, hle, by rwa [show (j₀ - 1) + 1 = j₀ from by omega] at hprev, hspec⟩
      by_cases hh'm : h' < m
      · -- `Λ_{h'}` retarget of `e` to `0`
        obtain ⟨k, hqk, hku⟩ := qz_retarget m h' hh'm e hh'd hh'd' 0
        exact ⟨1 + k * 7 ^ (m - h'), 0, hku, Or.inl rfl, hqk, Dvd.dvd.mul_left he_lo _⟩
      · -- `h' = m`: top-level retarget of `e` to `6` (`0` unreachable at level `m`)
        have hh'eq : h' = m := by omega
        rw [hh'eq] at hh'd hh'd'
        obtain ⟨j, hju, hjq⟩ := qz_retarget_top m e hh'd hh'd' 6 (by decide)
        exact ⟨j, 6, hju, Or.inr rfl, hjq, Dvd.dvd.mul_left he_lo _⟩
  -- `ν(λ₁·x) = h` still (`λ₁` a unit), so STAGE 2's `Λ_h` retarget is available on `λ₁·x`.
  have hl1x_dvd : (7 : ℤ) ^ h ∣ lam₁ * x := Dvd.dvd.mul_left hx lam₁
  have hl1y_dvd : (7 : ℤ) ^ h ∣ lam₁ * y := Dvd.dvd.mul_left hy lam₁
  have hl1x_ndvd : ¬ (7 : ℤ) ^ (h + 1) ∣ lam₁ * x := by
    intro hdvd; refine hx' ?_
    have hcop : IsCoprime ((7 : ℤ) ^ (h + 1)) lam₁ :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hlam₁)
    exact hcop.dvd_of_dvd_mul_left hdvd
  -- carries on the STAGE-1 frame `(λ₁·x, λ₁·y)`, with the `2x−y ⇒ x−y` implication
  obtain ⟨c₃, c₁, hc3, hc1, hcarry3, hcarry1, himp6, himp1⟩ :=
    qz_combined_carry m (lam₁ * x) (lam₁ * y)
  have hle_eq : lam₁ * e = 2 * (lam₁ * x) - lam₁ * y := by rw [hedef]; ring
  -- `ẽ := 2q(λ₁x) − q(λ₁y) = se − c₃` (since `q(λ₁·e) = se` and `e = 2x−y`)
  have hetilde1 : 2 * qz m (lam₁ * x) - qz m (lam₁ * y) = se - c₃ := by
    have := hcarry3; rw [← hle_eq, hse_eq] at this; linear_combination -this
  -- choose the STAGE-2 target `t` so all three final differences land in `{0,6}`
  obtain ⟨t, htA, htB, htC⟩ :
      ∃ t : ZMod 7, t ∈ ({0, 6} : Finset (ZMod 7)) ∧
        (2 * t - (se - c₃)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
        (- t + (se - c₃) + c₁) ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases hse with rfl | rfl <;> rcases hc3 with rfl | rfl | rfl
    · exact ⟨0, by rcases hc1 with rfl | rfl <;> decide⟩
    · have : c₁ = 0 := himp1 rfl; subst this; exact ⟨6, by decide⟩
    · have : c₁ = 6 := himp6 rfl; subst this; exact ⟨0, by decide⟩
    · exact ⟨6, by rcases hc1 with rfl | rfl <;> decide⟩
    · have : c₁ = 0 := himp1 rfl; subst this; exact ⟨6, by decide⟩
    · have : c₁ = 6 := himp6 rfl; subst this; exact ⟨0, by decide⟩
  -- STAGE 2: `Λ_h` factor on `λ₁·x` sending `q(λ·x) = t`; `λ = (1 + k₂·7^{m-h})·λ₁`.
  obtain ⟨k₂, hk₂x, hk₂u⟩ := qz_retarget m h hh (lam₁ * x) hl1x_dvd hl1x_ndvd t
  set lam : ℤ := (1 + k₂ * 7 ^ (m - h)) * lam₁ with hlam_def
  have hlam_u : ¬ (7 : ℤ) ∣ lam := by
    rw [hlam_def]; exact mt (Prime.dvd_mul hp7 |>.mp) (by tauto)
  have e1 : lam * x = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * x) := by rw [hlam_def]; ring
  have e2 : lam * y = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * y) := by rw [hlam_def]; ring
  have e3 : lam * x - lam * y = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * x - lam₁ * y) := by
    rw [hlam_def]; ring
  have hfx : qz m (lam * x) = t := by rw [e1]; exact hk₂x
  -- `ẽ` is `Λ_h`-invariant (Lemma 4(i)) ⇒ `q(λ·y) = 2t − (se − c₃)`
  have hetilde_inv : 2 * qz m (lam * x) - qz m (lam * y)
      = 2 * qz m (lam₁ * x) - qz m (lam₁ * y) := by
    have hr2 : ((lam₁ * y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((lam₁ * x / 7 ^ h : ℤ) : ZMod 7) := by
      rw [Int.mul_ediv_assoc lam₁ hy, Int.mul_ediv_assoc lam₁ hx]; push_cast; rw [hr]; ring
    have hlemma4 := lemma4_i m h (le_of_lt hh) k₂ (lam₁ * x) (lam₁ * y) hl1x_dvd hl1y_dvd hr2
    rw [e1, e2]; exact hlemma4
  have hfy : qz m (lam * y) = 2 * t - (se - c₃) := by
    rw [hetilde1] at hetilde_inv; rw [hfx] at hetilde_inv; linear_combination -hetilde_inv
  -- the `x−y` carry `c₁` is `Λ_h`-invariant ⇒ `q(λ·(x−y)) = q(λ·x) − q(λ·y) + c₁`
  have hcarry1' : qz m (lam * x - lam * y) = qz m (lam * x) - qz m (lam * y) + c₁ := by
    have hl1xy : (7 : ℤ) ^ h ∣ (lam₁ * x - lam₁ * y) := dvd_sub hl1x_dvd hl1y_dvd
    have hgx := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * x) hl1x_dvd
    have hgy := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * y) hl1y_dvd
    have hgxy := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * x - lam₁ * y) hl1xy
    have hslope : (((lam₁ * x - lam₁ * y) / 7 ^ h : ℤ) : ZMod 7)
        = ((lam₁ * x / 7 ^ h : ℤ) : ZMod 7) - ((lam₁ * y / 7 ^ h : ℤ) : ZMod 7) := by
      rw [Int.sub_ediv_of_dvd _ hl1y_dvd]; push_cast; ring
    rw [e3, e1, e2, hgx, hgy, hgxy, hslope, hcarry1]; ring
  -- all three pairwise `q`-differences are in `{0,6}`: Remark 8(i) gives `ℓ ≤ 2`.
  refine ⟨lam, hlam_u, ?_, ?_, ?_⟩
  · rw [show lam * b₁ - lam * b₂ = lam * x - lam * y from by rw [hxdef, hydef]; ring,
      hcarry1', hfx, hfy]
    rw [show t - (2 * t - (se - c₃)) + c₁ = - t + (se - c₃) + c₁ from by ring]; exact htC
  · rw [show lam * b₁ - lam * b₃ = lam * x from by rw [hxdef]; ring, hfx]; exact htA
  · rw [show lam * b₂ - lam * b₃ = lam * y from by rw [hydef]; ring, hfy]; exact htB

/-- **Anchor from the ratio-2 compression (BS §6.1, `ν(E) ≠ {m}`, Lemma 10 (ii)).**
`q(λ·(B−B)) ⊂ {0,6}` (from `ratio2_diffs`) plus the exact level `h < m` of the three
differences — which rules out the arc-boundary `≡ 6·7^m` — gives both orientations,
so `cluster3` produces an integer anchor for `{λb₁, λb₂, λb₃}`. -/
theorem anchor_ratio2 (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam t : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      (lam * b₁ - t) % 7 ^ (m + 1) ≤ 7 ^ m ∧
      (lam * b₂ - t) % 7 ^ (m + 1) ≤ 7 ^ m ∧
      (lam * b₃ - t) % 7 ^ (m + 1) ≤ 7 ^ m := by
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  obtain ⟨lam, hlam, hD12, hD13, hD23⟩ := ratio2_diffs m h hh b₁ b₂ b₃ hx hx' hy hy' hr
  have hxy : (7 : ℤ) ^ h ∣ (b₁ - b₂) := by
    rw [show b₁ - b₂ = (b₁ - b₃) - (b₂ - b₃) from by ring]; exact dvd_sub hx hy
  have hrx : (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7) ≠ 0 := by
    obtain ⟨w, hw⟩ := hx
    rw [res_eq hw]
    exact unit_res hw hx'
  have hxy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₂) := by
    refine ndvd_succ_of_res_ne hxy ?_
    rw [show b₁ - b₂ = (b₁ - b₃) - (b₂ - b₃) from by ring, Int.sub_ediv_of_dvd _ hy]
    push_cast
    rw [hr]
    intro hcon
    exact hrx (by linear_combination -hcon)
  have hlevel : ∀ z : ℤ, ¬ (7 : ℤ) ^ (h + 1) ∣ z → ¬ (7 : ℤ) ^ m ∣ (lam * z) := by
    intro z hz hdvd
    refine hz ?_
    have h1 : (7 : ℤ) ^ (h + 1) ∣ lam * z := dvd_trans (pow_dvd_pow 7 (by omega)) hdvd
    have hcop : IsCoprime ((7 : ℤ) ^ (h + 1)) lam :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hlam)
    exact hcop.dvd_of_dvd_mul_left h1
  have hL12 : ¬ (7 : ℤ) ^ m ∣ (lam * b₁ - lam * b₂) := by
    rw [show lam * b₁ - lam * b₂ = lam * (b₁ - b₂) from by ring]; exact hlevel _ hxy'
  have hL13 : ¬ (7 : ℤ) ^ m ∣ (lam * b₁ - lam * b₃) := by
    rw [show lam * b₁ - lam * b₃ = lam * (b₁ - b₃) from by ring]; exact hlevel _ hx'
  have hL23 : ¬ (7 : ℤ) ^ m ∣ (lam * b₂ - lam * b₃) := by
    rw [show lam * b₂ - lam * b₃ = lam * (b₂ - b₃) from by ring]; exact hlevel _ hy'
  have hrev : ∀ u v : ℤ, ¬ (7 : ℤ) ^ m ∣ (u - v) →
      qz m (u - v) ∈ ({0, 6} : Finset (ZMod 7)) →
      qz m (v - u) ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro u v hl hmem
    rw [show v - u = -(u - v) from by ring]
    exact qz_neg_mem06 m _ hl hmem
  have hzero : ∀ u : ℤ, qz m (u - u) ∈ ({0, 6} : Finset (ZMod 7)) := by
    intro u; rw [sub_self]; simp [qz]
  obtain ⟨k, hk⟩ := cluster3 m ![lam * b₁, lam * b₂, lam * b₃] (by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hzero _
    · exact hD12
    · exact hD13
    · exact hrev _ _ hL12 hD12
    · exact hzero _
    · exact hD23
    · exact hrev _ _ hL13 hD13
    · exact hrev _ _ hL23 hD23
    · exact hzero _)
  exact ⟨lam, ![lam * b₁, lam * b₂, lam * b₃] k, hlam,
    le_of_lt (hk 0), le_of_lt (hk 1), le_of_lt (hk 2)⟩


/-- **Case 6.1 endgame.** `B = {x₁,x₂,x₃}` sits in one closed `7^m`-window (anchor
`t`) after the unit multiplier `lam₀`, and `{z₁,z₂}` are the two remaining
elements. Then `ℓ(A₁) ≤ 5` for `lam₀` or (in BS's `{q(d₄),q(d₅)} = {2,4}`
exception) for `3·lam₀`, and Lemma 5 finishes. -/
theorem case61_endgame (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ)
    (hres1 : ∀ i, (d i : ZMod 7) = 1)
    (x₁ x₂ x₃ z₁ z₂ : ℤ)
    (hcov : ∀ f : ℤ → ZMod 7, ∀ i : Fin 5,
      f (d i) ∈ ({f x₁, f x₂, f x₃, f z₁, f z₂} : Finset (ZMod 7)))
    (lam₀ t : ℤ) (hlam₀ : ¬ (7 : ℤ) ∣ lam₀)
    (hb₁ : (lam₀ * x₁ - t) % 7 ^ (m + 1) ≤ 7 ^ m)
    (hb₂ : (lam₀ * x₂ - t) % 7 ^ (m + 1) ≤ 7 ^ m)
    (hb₃ : (lam₀ * x₃ - t) % 7 ^ (m + 1) ≤ 7 ^ m) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have close_window5 : ∀ lam' : ℤ, ¬ (7 : ℤ) ∣ lam' →
      (∃ a : ZMod 7, ∀ i, (qz m (lam' * d i) - a).val ≤ 4) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam' hlam' hwin
    obtain ⟨u, hu, havoid⟩ := place_window5 m hm (fun i => lam' * d i)
      (lam' : ZMod 7) (by
        intro h0
        exact hlam' ((ZMod.intCast_zmod_eq_zero_iff_dvd lam' 7).mp h0))
      (fun i => by push_cast; rw [hres1 i]; ring) hwin
    refine ⟨u * lam', ?_, ?_⟩
    · intro hdiv
      rcases (seven_totient_full_int).dvd_mul.mp hdiv with h | h
      · exact hu h
      · exact hlam' h
    · intro i
      simpa [mul_assoc] using havoid i
  set a : ZMod 7 := qz m t with ha_def
  set p : ZMod 7 := qz m (lam₀ * z₁) with hp_def
  set q : ZMod 7 := qz m (lam₀ * z₂) with hq_def
  have hmem : ∀ i : Fin 5, qz m (lam₀ * d i) ∈ ({a, a + 1, p, q} : Finset (ZMod 7)) := by
    intro i
    have hco := hcov (fun x => qz m (lam₀ * x)) i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hco ⊢
    rcases hco with h | h | h | h | h
    · rcases qz_near m (lam₀ * x₁) t hb₁ with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (Or.inl (by rw [h, h']))
    · rcases qz_near m (lam₀ * x₂) t hb₂ with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (Or.inl (by rw [h, h']))
    · rcases qz_near m (lam₀ * x₃) t hb₃ with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (Or.inl (by rw [h, h']))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases hex : (p + (-a - 1) = 2 ∧ q + (-a - 1) = 4) ∨
      (p + (-a - 1) = 4 ∧ q + (-a - 1) = 2)
  · -- BS's exception `{q(d₄), q(d₅)} = {2,4}`: re-multiply by `3`.
    have hpq : (p = a + 3 ∧ q = a + 5) ∨ (p = a + 5 ∧ q = a + 3) := by
      rcases hex with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by linear_combination h1, by linear_combination h2⟩
      · exact Or.inr ⟨by linear_combination h1, by linear_combination h2⟩
    obtain ⟨c, hcv, hA⟩ := qz_triple m t
    have hcval : c.val ≤ 2 := by rcases hcv with rfl | rfl | rfl <;> decide
    obtain ⟨W, hW⟩ := case61_exc_window a c hcval
    have h3lam : ¬ (7 : ℤ) ∣ 3 * lam₀ := by
      intro hdiv
      rcases (seven_totient_full_int).dvd_mul.mp hdiv with h | h
      · norm_num at h
      · exact hlam₀ h
    refine close_window5 (3 * lam₀) h3lam ⟨W, fun i => ?_⟩
    rw [show (3 * lam₀) * d i = 3 * (lam₀ * d i) from by ring]
    refine hW _ ?_
    have hco := hcov (fun x => qz m (3 * (lam₀ * x))) i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hco
    have hbase : ∀ w : ℤ, (lam₀ * w - t) % 7 ^ (m + 1) ≤ 7 ^ m →
        (qz m (3 * (lam₀ * w)) - (3 * a + c)).val ≤ 3 := by
      intro w hw
      rw [show 3 * a + c = qz m (3 * t) from hA.symm]
      exact triple_win m (lam₀ * w) t hw
    have hfree : ∀ w : ℤ, (qz m (lam₀ * w) = a + 3 ∨ qz m (lam₀ * w) = a + 5) →
        (qz m (3 * (lam₀ * w)) - 3 * (a + 3)).val ≤ 2 ∨
        (qz m (3 * (lam₀ * w)) - 3 * (a + 5)).val ≤ 2 := by
      intro w hw
      obtain ⟨c', hc', he'⟩ := qz_triple m (lam₀ * w)
      rcases hw with hw | hw
      · left
        rw [he', hw, show 3 * (a + 3) + c' - 3 * (a + 3) = c' from by ring]
        rcases hc' with rfl | rfl | rfl <;> decide
      · right
        rw [he', hw, show 3 * (a + 5) + c' - 3 * (a + 5) = c' from by ring]
        rcases hc' with rfl | rfl | rfl <;> decide
    rcases hco with h | h | h | h | h
    · exact Or.inl (h ▸ hbase x₁ hb₁)
    · exact Or.inl (h ▸ hbase x₂ hb₂)
    · exact Or.inl (h ▸ hbase x₃ hb₃)
    · refine Or.inr (h ▸ hfree z₁ ?_)
      rcases hpq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · refine Or.inr (h ▸ hfree z₂ ?_)
      rcases hpq with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
  · obtain ⟨k, hk⟩ := case61_nonexception_shift a p q hex
    refine lift_shift m hm d lam₀ hlam₀ k (fun i => ?_)
    rw [hres1 i, mul_one]
    exact hk _ (hmem i)



/-- **Case 6.1 `(5,0,0)`** (BS L507). `|A₁| = 5`. Labeling via Lemma 10, then
`ℓ(A₁) ≤ 5` by Lemma 9 / Remark 8(i), closed by `lift_shift`/`place_window5`. -/
theorem case_61 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =5)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have hres1 : ∀ i, (d i : ZMod 7) = 1 := by
    have hS : univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1) = univ := by
      apply Finset.eq_univ_of_card
      simpa using hC₁
    intro i
    have hi : i ∈ univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1) := by
      rw [hS]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  have close_window5 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ →
      (∃ a : ZMod 7, ∀ i,
        (qz m (lam₀ * d i) - a).val ≤ 4) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ hwin
    obtain ⟨u, hu, havoid⟩ := place_window5 m (by omega) (fun i => lam₀ * d i)
      (lam₀ : ZMod 7) (by
        intro h0
        exact hlam₀ ((ZMod.intCast_zmod_eq_zero_iff_dvd lam₀ 7).mp h0))
      (fun i => by push_cast; rw [hres1 i]; ring) hwin
    refine ⟨u * lam₀, ?_, ?_⟩
    · intro hdiv
      rcases (seven_totient_full_int).dvd_mul.mp hdiv with h | h
      · exact hu h
      · exact hlam₀ h
    · intro i
      simpa [mul_assoc] using havoid i
  by_cases htop : ∀ i, (7 : ℤ) ^ m ∣ d i - d 0
  -- `case_61_top_gen` needs no distinctness of the level-`m` coefficients:
  -- `affine_place` only ever uses two missing residues, and a `Fin 5 → ZMod 7`
  -- image always leaves at least two. So the collapsed branch is not a separate
  -- argument, and BS's split here is unnecessary.
  · exact Case61.case_61_top_gen m (by omega) d hres1 htop
  · let b : Fin 4 → ℤ := fun i => d ⟨i.val, by omega⟩
    have hb_inj : Function.Injective b := by
      intro i j hij
      simp only [b] at hij
      have hval : i.val = j.val := by
        exact congrArg (fun k : Fin 5 => k.val) (hinj hij)
      exact Fin.eq_of_val_eq hval
    obtain ⟨e₁, e₂, e₃, e₄, hperm, hstruct⟩ := lemma10 b hb_inj
    have he_res : ∀ e : ℤ, e ∈ ({e₁, e₂, e₃, e₄} : Finset ℤ) → (e : ZMod 7) = 1 := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      all_goals
        have hmem : (e : ZMod 7) ∈
            ({(b 0 : ZMod 7), (b 1 : ZMod 7), (b 2 : ZMod 7), (b 3 : ZMod 7)} : Finset _) := by
          rw [← hperm (fun x : ℤ => (x : ZMod 7))]
          simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h <;> simp [b, hres1] at h
        all_goals exact h
    have he₁_res : (e₁ : ZMod 7) = 1 := he_res e₁ (by simp)
    have he₂_res : (e₂ : ZMod 7) = 1 := he_res e₂ (by simp)
    have he₃_res : (e₃ : ZMod 7) = 1 := he_res e₃ (by simp)
    have he₄_res : (e₄ : ZMod 7) = 1 := he_res e₄ (by simp)
    have hcov : ∀ f : ℤ → ZMod 7, ∀ i : Fin 5,
        f (d i) ∈ ({f e₁, f e₂, f e₃, f e₄, f (d 4)} : Finset (ZMod 7)) := by
      intro f i
      have hsub : ∀ x : ZMod 7, x ∈ ({f e₁, f e₂, f e₃, f e₄} : Finset (ZMod 7)) →
          x ∈ ({f e₁, f e₂, f e₃, f e₄, f (d 4)} : Finset (ZMod 7)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      have hb4 : ∀ j : Fin 4, f (b j) ∈ ({f e₁, f e₂, f e₃, f e₄} : Finset (ZMod 7)) := by
        intro j
        rw [hperm f]
        fin_cases j <;> simp
      fin_cases i
      · exact hsub _ (hb4 0)
      · exact hsub _ (hb4 1)
      · exact hsub _ (hb4 2)
      · exact hsub _ (hb4 3)
      · show f (d 4) ∈ _
        simp
    rcases hstruct with
        ⟨h₁, h₂, hne, hd₁, hd₁', hd₂, hd₂'⟩ |
        ⟨h, hd₁, hd₁', hd₂, hd₂', hd₃, hd₃', hr₂, hr₃₄⟩
    · -- **Lemma 10 (i)**: the two apex differences have distinct valuations, so one
      -- unit multiplier puts `{λe₁, λe₂, λe₃}` inside one closed `7^m`-window.
      obtain ⟨lam₀, hlam₀, hq₂, hq₃⟩ :=
        anchor_pair m h₁ h₂ hne (e₂ - e₁) (e₃ - e₁) hd₁ hd₁' hd₂ hd₂'
      refine case61_endgame m (by omega) d hres1 e₁ e₂ e₃ e₄ (d 4) hcov lam₀ (lam₀ * e₁)
        hlam₀ ?_ ?_ ?_
      · rw [sub_self, Int.zero_emod]; positivity
      · rw [show lam₀ * e₂ - lam₀ * e₁ = lam₀ * (e₂ - e₁) from by ring]; exact hq₂
      · rw [show lam₀ * e₃ - lam₀ * e₁ = lam₀ * (e₃ - e₁) from by ring]; exact hq₃
    · -- **Lemma 10 (ii)**: `e₂₁, e₃₁, e₄₁` share one level `h` with `r(e₃₁) = 2·r(e₂₁)`.
      rcases lt_trichotomy h m with hhm | hhm | hhm
      · -- `h < m`: BS Lemma 9 (ii) with `j = 2` on `B = {d₂, d₃, d₁}` compresses
        -- `q(λ·(B−B)) ⊂ {0,6}`, which is an integer anchor for `B`.
        obtain ⟨lam₀, tt, hlam₀, ha₁, ha₂, ha₃⟩ :=
          anchor_ratio2 m h hhm e₂ e₃ e₁ hd₁ hd₁' hd₂ hd₂' hr₂
        refine case61_endgame m (by omega) d hres1 e₂ e₃ e₁ e₄ (d 4) ?_ lam₀ tt
          hlam₀ ha₁ ha₂ ha₃
        intro f i
        have hco := hcov f i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hco ⊢
        rcases hco with h' | h' | h' | h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
      · -- `h = m`: the four `e`s sit at the top level, so `¬htop` must be witnessed by
        -- `d 4`, whose apex difference has a level `< m` — a distinct-valuation pair.
        rw [hhm] at hd₁ hd₁'
        have hall : ∀ hcon : (7 : ℤ) ^ m ∣ (d 4 - e₁), ∀ i : Fin 5, (7 : ℤ) ^ m ∣ (d i - e₁) := by
          intro hcon i
          refine dvd_pow_of_qz_zero m _ (fun j hj => ?_)
          have hco := hcov (fun x => qz j (x - e₁)) i
          simp only [Finset.mem_insert, Finset.mem_singleton] at hco
          have hz1 : qz j (e₁ - e₁) = 0 := by rw [sub_self]; simp [qz]
          have hz2 : qz j (e₂ - e₁) = 0 := qz_zero_of_dvd_pow m j hj _ hd₁
          have hz3 : qz j (e₃ - e₁) = 0 :=
            qz_zero_of_dvd_pow m j hj _ (by rw [← hhm]; exact hd₂)
          have hz4 : qz j (e₄ - e₁) = 0 :=
            qz_zero_of_dvd_pow m j hj _ (by rw [← hhm]; exact hd₃)
          have hz5 : qz j (d 4 - e₁) = 0 := qz_zero_of_dvd_pow m j hj _ hcon
          rcases hco with h' | h' | h' | h' | h' <;> rw [h'] <;> assumption
        have hd4 : ¬ (7 : ℤ) ^ m ∣ (d 4 - e₁) := by
          intro hcon
          refine htop (fun i => ?_)
          have h1 := hall hcon i
          have h2 := hall hcon 0
          have h3 := dvd_sub h1 h2
          rwa [show d i - e₁ - (d 0 - e₁) = d i - d 0 from by ring] at h3
        have hne4 : d 4 - e₁ ≠ 0 := fun h0 => hd4 (by rw [h0]; exact dvd_zero _)
        obtain ⟨h₅, hv, hv'⟩ := exists_val7 _ hne4
        have h5m : h₅ < m := by
          by_contra hc
          exact hd4 (dvd_trans (pow_dvd_pow 7 (by omega)) hv)
        obtain ⟨lam₀, hlam₀, hqa, hqb⟩ :=
          anchor_pair m m h₅ (by omega) (e₂ - e₁) (d 4 - e₁) hd₁ hd₁' hv hv'
        refine case61_endgame m (by omega) d hres1 e₁ e₂ (d 4) e₃ e₄ ?_ lam₀ (lam₀ * e₁)
          hlam₀ ?_ ?_ ?_
        · intro f i
          have hco := hcov f i
          simp only [Finset.mem_insert, Finset.mem_singleton] at hco ⊢
          rcases hco with h' | h' | h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
          · exact Or.inr (Or.inr (Or.inl h'))
        · rw [sub_self, Int.zero_emod]; positivity
        · rw [show lam₀ * e₂ - lam₀ * e₁ = lam₀ * (e₂ - e₁) from by ring]; exact hqa
        · rw [show lam₀ * d 4 - lam₀ * e₁ = lam₀ * (d 4 - e₁) from by ring]; exact hqb
      · -- `h > m`: `e₂, e₃` are `q`-equivalent to `e₁` under every multiplier.
        refine case61_endgame m (by omega) d hres1 e₁ e₂ e₃ e₄ (d 4) hcov 1 (1 * e₁)
          (by norm_num) ?_ ?_ ?_
        · rw [sub_self, Int.zero_emod]; positivity
        · rw [show (1 : ℤ) * e₂ - 1 * e₁ = e₂ - e₁ from by ring,
            Int.emod_eq_zero_of_dvd (dvd_trans (pow_dvd_pow 7 (by omega)) hd₁)]
          positivity
        · rw [show (1 : ℤ) * e₃ - 1 * e₁ = e₃ - e₁ from by ring,
            Int.emod_eq_zero_of_dvd (dvd_trans (pow_dvd_pow 7 (by omega)) hd₂)]
          positivity

/-- **`(4,1,0)` 2-window endgame.** 2-window `{a,a+1}` (three `A₁` arcs), 4th `A₁`
arc `v₄ ≠ a+4`, and the `A₂` arc `q₅` (shift coefficient `2`). The excluded
antipodal `v₄ = a+4` is BS's `q(d₄) = 3` case, handled by ×2 dilation. -/
theorem avoid_62a_2win (a v₄ q₅ : ZMod 7) (hexc : v₄ ≠ a + 4) :
    ∃ k : ZMod 7,
      a + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      v₄ + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₅ + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert hexc; revert a v₄ q₅; decide

/-- **`(4,1,0)` contiguous 4-window endgame** (`(ii.1)` `h=m`, and the doubled
antipodal case): window `{a,…,a+3}` plus a free `A₂` arc (coeff `2`).
Unconditional. -/
theorem avoid_62a_4win (a q₅ : ZMod 7) :
    ∃ k : ZMod 7,
      a + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 2 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 3 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q₅ + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert a q₅; decide

/-- **`(4,1,0)` holed 5-window endgame** (`(ii.2)` `h=m`): `A₁` arcs
`{A, A+1, A+2, A+4}`, `A₂` arc `q₅` with `ẽ(d₁,d₅) = 2A − q₅ ∉ {2,3}` (Lemma 7). -/
theorem avoid_62a_holewin (A q₅ : ZMod 7)
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
theorem case_62a (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
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
theorem avoid_62b_branch_i (a v₄ q₄ : ZMod 7) :
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
theorem avoid_62b_branch_ii_m (a q₄ : ZMod 7) :
    ∃ k' : ZMod 7,
      (∀ j : Fin 4, a + (j.val : ZMod 7) + k' ∉ ({0, 6} : Finset (ZMod 7))) ∧
      q₄ + 4 * k' ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert a q₄; decide

set_option maxHeartbeats 800000 in
/-- **Case 6.2 `(4,0,1)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₄`. Labeling via Lemma 10;
`ℓ(A₁) ≤ 4` then Lemma 5 with `(4,0,1)` partition. -/
theorem case_62b (hm : 2 ≤ m)
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
    -- In both cases the (4,0,1) Λ₀ assembly closes.
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
        haveI h7p : Fact (Nat.Prime 7) := ⟨seven_totient_full⟩
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
structure A1three (m : ℕ) (d : Fin 5 → ℤ)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3) where
  g₁ : Fin 3 → Fin 5
  hg₁_res : ∀ k, (d (g₁ k) : ZMod 7) = 1
  hg₁_inj : Function.Injective g₁
  hA₁_cover : ∀ i : Fin 5, (d i : ZMod 7) = 1 → ∃ k : Fin 3, g₁ k = i

/-- Build the `A1three` extraction from the cardinality hypothesis. -/
def mkA1three (m : ℕ) (d : Fin 5 → ℤ)
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

set_option maxHeartbeats 1600000 in
/-- **`(3,1,1)` ratio-3 h=m endgame** (BS L643–650). After the `r⁻¹`-frame, `A₁`
arcs sit at `{a, a+1, a+3}`; with `ẽ(d₃,d₄) = 2a − p ∉ {2,3,4,5}` (Lemma 7), the
lone `A₂` arc `p` (coeff 2) and `A₄` arc `q` (coeff 4, uncontrolled) admit a common
`Λ₀` shift avoiding `{0,6}`. Exhaustive `decide`. -/
theorem avoid_63_r3hm (a p q : ZMod 7)
    (he : 2 * a - p ∉ ({2, 3, 4, 5} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      a + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      a + 3 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      p + 2 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      q + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert he; revert a p q; decide

set_option maxHeartbeats 1600000 in
/-- **`(3,1,1)` ratio-3 h=m 2-carry fallback endgame** (BS L656–661). When
`ẽ34 ∈ {2,3,4,5}` and `ν(e₃₄)=ν(e₄₅)=m`, the `Λ₁` pin `q(7·d₃)=4ε₁+2ε₂` controls
BOTH doubling carries (`qz_double_quad_carry`). For any `T34 ∈ {3,4,5}` and any
`T45`, some `(ε₁,ε₂,Atar)` places `A₁` at `{Atar,Atar+1,Atar+3}`, `d₄` at
`2·Atar−(T34−ε₁)` (coeff 2), `d₅` at `4·Atar−2(T34−ε₁)−(T45−ε₂)` (coeff 4), all
avoiding `{0,6}`. Matches BS's eight-bad-pairs table exactly. -/
theorem fallback_63_choice (T34 T45 : ZMod 7)
    (hT34 : T34 ∈ ({3, 4, 5} : Finset (ZMod 7))) :
    ∃ e1 e2 Atar : ZMod 7, (e1 = 0 ∨ e1 = 1) ∧ (e2 = 0 ∨ e2 = 1) ∧
      Atar ∉ ({0, 6} : Finset (ZMod 7)) ∧
      Atar + 1 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      Atar + 3 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * Atar - (T34 - e1) ∉ ({0, 6} : Finset (ZMod 7)) ∧
      4 * Atar - 2 * (T34 - e1) - (T45 - e2) ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert hT34; revert T34 T45; decide

/-- **`(3,1,1)` ratio-3 h=m, `ν(e₄₅)<m` endgame** (BS L652). After the `Λ_{ν(e₄₅)}`
retarget sets `q(e₄₅)=0` (so `q(d₅)=2q(d₄)+cc`, `cc∈{0,1,6}` the carry) and the
single `Λ₁` pin fixes `ẽ34 = T34−ε₁ ∈ {3,4}` (`ε₁=1` iff `T34=5`), a base shift
`Atar` places `A₁` at `{Atar,Atar+1,Atar+3}`, `d₄` at `2·Atar−ẽ34`, `d₅` at
`4·Atar−2·ẽ34+cc`, all avoiding `{0,6}`. Since `ẽ34∈{3,4}≠5`, no bad pair. -/
theorem fallback_63_lo (et34 cc : ZMod 7)
    (het : et34 = 3 ∨ et34 = 4) (hcc : cc = 0 ∨ cc = 1 ∨ cc = 6) :
    ∃ Atar : ZMod 7,
      Atar ∉ ({0, 6} : Finset (ZMod 7)) ∧ Atar + 1 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      Atar + 3 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      2 * Atar - et34 ∉ ({0, 6} : Finset (ZMod 7)) ∧
      4 * Atar - 2 * et34 + cc ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert het hcc; revert et34 cc; decide

set_option maxRecDepth 100000 in
/-- Finset-free core of `fallback_63_l1`. Stating every `{0,6}` membership as
explicit (in)equalities lets `Decidable` instance synthesis go through under the
binders, so the finite check closes by kernel `decide` (~2s) instead of
`native_decide`. -/
theorem fallback_63_l1_core (T34 e0 rho : ZMod 7)
    (hT34 : T34 = 3 ∨ T34 = 4 ∨ T34 = 5) (hrho : rho ≠ 0) :
    ∃ p : ZMod 7, ∀ e1 : ZMod 7, (e1 = 0 ∨ e1 = 1) →
      ((p = 0 ∨ p = 1 ∨ p = 2) → e1 = 0) →
      ((p = 4 ∨ p = 5 ∨ p = 6) → e1 = 1) →
      ∃ Atar : ZMod 7,
        (Atar ≠ 0 ∧ Atar ≠ 6) ∧
        (Atar + 1 ≠ 0 ∧ Atar + 1 ≠ 6) ∧
        (Atar + 3 ≠ 0 ∧ Atar + 3 ≠ 6) ∧
        (2 * Atar + e1 - T34 ≠ 0 ∧ 2 * Atar + e1 - T34 ≠ 6) ∧
        (4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 2 ∨
          4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 3 ∨
          4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 4) := by
  revert hT34 hrho; revert T34 e0 rho; decide

/-- **`(3,1,1)` ratio-3 h=m, `ν(e₄₅)=1` seven-pin endgame** (BS L652–661 edge).
At `ν(e₄₅)=1` the single `Λ₁` knob moves the `d₃`-doubling pin `p = q(7·d₃)`
and `q(e₄₅) = e0 + p·rho` (slope `rho ≠ 0`) in lockstep, so neither can be set
independently. But pins `{0,1,2}` force doubling carry `ε₁ = 0` and pins
`{4,5,6}` force `ε₁ = 1` (`qz_double_pin`); at `p = 3` either carry may occur
and the pin chosen below wins for both. For every `(T34, e0, rho)` some pin `p`
admits a base `Atar` placing `A₁` at `{Atar,Atar+1,Atar+3}`, `d₄` at
`2·Atar+ε₁−T34`, and the `d₅` BASE `4·Atar+2·ε₁−2·T34−(e0+p·rho)` inside
`{2,3,4}` — so the uncontrolled `qz_2xsuby` carry `cc ∈ {0,1,6}` keeps `d₅`
inside `{1,…,5}`. Verified: `experiments/c63_nu1_pin7_decide_v1.py` (126 cfgs),
`experiments/c63_nu1_pin7_intsim_v1.py` (6000 integer cfgs end-to-end). -/
theorem fallback_63_l1 (T34 e0 rho : ZMod 7)
    (hT34 : T34 ∈ ({3, 4, 5} : Finset (ZMod 7))) (hrho : rho ≠ 0) :
    ∃ p : ZMod 7, ∀ e1 : ZMod 7, (e1 = 0 ∨ e1 = 1) →
      ((p = 0 ∨ p = 1 ∨ p = 2) → e1 = 0) →
      ((p = 4 ∨ p = 5 ∨ p = 6) → e1 = 1) →
      ∃ Atar : ZMod 7,
        Atar ∉ ({0, 6} : Finset (ZMod 7)) ∧
        Atar + 1 ∉ ({0, 6} : Finset (ZMod 7)) ∧
        Atar + 3 ∉ ({0, 6} : Finset (ZMod 7)) ∧
        2 * Atar + e1 - T34 ∉ ({0, 6} : Finset (ZMod 7)) ∧
        (4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 2 ∨
          4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 3 ∨
          4 * Atar + 2 * e1 - 2 * T34 - (e0 + p * rho) = 4) := by
  have hT : T34 = 3 ∨ T34 = 4 ∨ T34 = 5 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hT34
  obtain ⟨p, hp⟩ := fallback_63_l1_core T34 e0 rho hT hrho
  refine ⟨p, fun e1 h1 h2 h3 => ?_⟩
  obtain ⟨A, hA1, hA2, hA3, hA4, hA5⟩ := hp e1 h1 h2 h3
  exact ⟨A,
    by simp [Finset.mem_insert, Finset.mem_singleton, hA1.1, hA1.2],
    by simp [Finset.mem_insert, Finset.mem_singleton, hA2.1, hA2.2],
    by simp [Finset.mem_insert, Finset.mem_singleton, hA3.1, hA3.2],
    by simp [Finset.mem_insert, Finset.mem_singleton, hA4.1, hA4.2],
    hA5⟩

theorem reflect_fit_63 (x y z a : ZMod 7) (L : ℕ)
    (hL : L = 2 ∨ L = 3)
    (hfit : fitsInterval ({6 - x, 6 - y, 6 - z} : Finset (ZMod 7)) a L) :
    ∃ b : ZMod 7, fitsInterval ({x, y, z} : Finset (ZMod 7)) b L := by
  rcases hL with rfl | rfl <;> revert x y z a hfit <;> decide

/-- **Case 6.3 `(3,1,1)`** (BS L565). `|A₁|=3, |A₂|=|A₄|=1`. Labeling via Lemma 11;
endgame is `lemma5` on the `(ℓ₁,1,1)` partition (the `(3,1,1)` exception carved by
`ẽ(d₄,d₅) ∉ {2,4}`). Branch map: (i)/(ii.1) `h<m` → `lemma9` gives `ℓ(A₁)≤2`;
`h>m` → arcs coincide (`ℓ=1`); (ii.2.a) `h<m` (`ν(e₄₅)≠h`) → `j3_control`;
(ii.1) `h=m` → `r⁻¹`-frame + Lemma 7; (ii.2.b)/(ii.2) `h=m` → finite tables. -/
theorem case_63 (hm : 2 ≤ m)
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
  -- The alignment target for Lemma 11: `s := r(e₄₅)` where `e₄₅ = 2d₄ − d₅`
  -- (BS §6.3 (ii.2): "r(e₁₃) = 3r(e₂₃) = ±s"), so that case (ii.2.b) may assume
  -- `r(e₄₅) = ±r(d₂−d₃)`. When `e₄₅ = 0` any unit works.
  set e45 : ℤ := 2 * d i₄ - d i₅ with he45_def
  set s : ZMod 7 := if e45 = 0 then 1 else
    ((e45 / 7 ^ padicValInt 7 e45 : ℤ) : ZMod 7) with hs_def
  have hs_ne : s ≠ 0 := by
    rw [hs_def]
    split_ifs with he
    · exact one_ne_zero
    · intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      obtain ⟨c, hc⟩ := h0
      have hd : (7 : ℤ) ^ padicValInt 7 e45 ∣ e45 := padicValInt_dvd e45
      have hd1 : (7 : ℤ) ^ (padicValInt 7 e45 + 1) ∣ e45 :=
        ⟨c, by
          calc
            e45 = (7 : ℤ) ^ padicValInt 7 e45 * (e45 / 7 ^ padicValInt 7 e45) :=
              (Int.mul_ediv_cancel' hd).symm
            _ = (7 : ℤ) ^ padicValInt 7 e45 * (7 * c) :=
              congrArg (fun z : ℤ => (7 : ℤ) ^ padicValInt 7 e45 * z) hc
            _ = (7 : ℤ) ^ (padicValInt 7 e45 + 1) * c := by rw [pow_succ]; ring⟩
      have hle : padicValInt 7 e45 + 1 ≤ padicValInt 7 e45 :=
        ((padicValInt_dvd_iff _ e45).mp hd1).resolve_left he
      omega
  have hs_def_orig : s = if 2 * d i₄ - d i₅ = 0 then 1 else
      (((2 * d i₄ - d i₅) / 7 ^ padicValInt 7 (2 * d i₄ - d i₅) : ℤ) : ZMod 7) := by
    rw [hs_def, he45_def]
  -- Apply Lemma 11 (s-aligned form) to label A₁.
  obtain ⟨d₁, d₂, d₃, hperm, h_struct⟩ := lemma11_s s hs_ne b₁ hb₁_inj
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
  · rcases hr with hr2 | ⟨hr3, hr3s⟩
    · -- ── (ii.1) ratio 2 ──
      by_cases hheq : h = m
      · -- (ii.1) h = m: r⁻¹-frame ℓ(A₁)=3 + Lemma 7 (tight X={2,4}) forces ẽ(d₄,d₅)∉{2,4}.
        rw [hheq] at hd1 hd1' hd2 hr2
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
        haveI h7p : Fact (Nat.Prime 7) := ⟨seven_totient_full⟩
        -- Closer: any frame `w` with residue r⁻¹ places A₁ at {a,a+1,a+2}; carve ⟹ done.
        have close_b5 : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w → (w : ZMod 7) = r⁻¹ →
            (2 * qz m (w * d i₄) - qz m (w * d i₅)) ∉ ({2, 4} : Finset (ZMod 7)) →
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
              qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
          intro w hw hw_res hcarve
          set a_m : ZMod 7 := qz m (w * d₃) with ha_def
          have hqd1 : qz m (w * d₁) = a_m + 1 := by
            rw [ha_def, qz_top_affine m w d₁ d₃ hd1, hw_res, ← hr_def, inv_mul_cancel₀ hr_ne]
          have hqd2 : qz m (w * d₂) = a_m + 2 := by
            rw [ha_def, qz_top_affine m w d₂ d₃ hd2, hw_res, hr2]
            congr 1
            rw [show r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
          refine close_l5 w hw a_m 3 (by omega) (by omega) (fun k₀ => ?_) (fun _ => hcarve)
          have hmem : qz m (w * b₁ k₀) ∈
              ({qz m (w * d₁), qz m (w * d₂), qz m (w * d₃)} : Finset (ZMod 7)) := by
            rw [← hset_eq w]; fin_cases k₀ <;> simp
          rw [hqd1, hqd2, ← ha_def] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h' | h' | h'
          · exact ⟨⟨1, by omega⟩, by rw [h']; simp⟩
          · exact ⟨⟨2, by omega⟩, by rw [h']; simp⟩
          · exact ⟨⟨0, by omega⟩, by rw [h']; simp⟩
        -- Lemma 7 on the pair (u·d₄, u·d₅) with the tight target X = {2,4}.
        have hr_L7 : ((u_int * d i₅ : ℤ) : ZMod 7) = 2 * ((u_int * d i₄ : ℤ) : ZMod 7) := by
          push_cast; rw [hu_cast, hi₄_res, hi₅_res]; ring
        have hd4_nd : ¬ (7 : ℤ) ∣ (u_int * d i₄) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (d i₄ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d i₄) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with hh | hh
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
          · rw [hi₄_res] at hh; exact two_ne_zero_z7 hh
        have hd5_nd : ¬ (7 : ℤ) ∣ (u_int * d i₅) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (d i₅ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d i₅) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with hh | hh
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
          · rw [hi₅_res] at hh; exact four_ne_zero_z7 hh
        set e45u : ℤ := 2 * (u_int * d i₄) - (u_int * d i₅) with he45u_def
        obtain ⟨lam₁, hl1_ndvd, hl1_res, hetal⟩ :
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
              (2 * qz m (lam * (u_int * d i₄)) - qz m (lam * (u_int * d i₅))) ∉
                ({2, 4} : Finset (ZMod 7)) := by
          have hX24 : ∃ a : ZMod 7, fitsInterval ({2, 4} : Finset (ZMod 7)) a 4 :=
            ⟨1, fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact ⟨⟨1, by omega⟩, by norm_num⟩
              · exact ⟨⟨3, by omega⟩, by norm_num⟩⟩
          by_cases hm_dvd : (7 : ℤ) ^ m ∣ e45u
          · exact lemma7_ii m 0 (by omega) (u_int * d i₄) (u_int * d i₅)
              hd4_nd hd5_nd hr_L7 {2, 4} hm_dvd (by rw [inter24_empty]; exact Finset.notMem_empty _)
          · have he_ne : e45u ≠ 0 := fun heq => hm_dvd (heq ▸ dvd_zero _)
            set ν := padicValInt 7 e45u with hν_def
            have hν_lt_m : ν < m := by
              by_contra hge; push_neg at hge
              exact hm_dvd ((padicValInt_dvd_iff m e45u).mpr (Or.inr hge))
            have hν_ndvd : ¬ (7 : ℤ) ^ (ν + 1) ∣ e45u := by
              intro hh
              have hle : ν + 1 ≤ padicValInt 7 e45u :=
                ((padicValInt_dvd_iff (ν + 1) e45u).mp hh).resolve_left he_ne
              omega
            exact lemma7_i m ν hν_lt_m (u_int * d i₄) (u_int * d i₅)
                hd4_nd hd5_nd hr_L7 {2, 4} hX24 (padicValInt_dvd e45u) hν_ndvd
        refine close_b5 (lam₁ * u_int) ?_ ?_ ?_
        · intro hdvd
          rcases (seven_totient_full_int).dvd_mul.mp hdvd with hh | hh
          · exact hl1_ndvd hh
          · exact hu_ndvd hh
        · push_cast; rw [hl1_res, hu_cast, one_mul]
        · rw [show (lam₁ * u_int) * d i₄ = lam₁ * (u_int * d i₄) from by ring,
              show (lam₁ * u_int) * d i₅ = lam₁ * (u_int * d i₅) from by ring]
          exact hetal
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
      · -- (ii.2) h = m: r⁻¹-frame {a,a+1,a+3}; Lemma 7 on (d₃,d₄) gives ẽ34∉{2,3,4,5}.
        rw [hheq] at hd1 hd1' hd2 hd2' hr3
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
        haveI h7p : Fact (Nat.Prime 7) := ⟨seven_totient_full⟩
        -- Closer: any frame `w` (res r⁻¹) with ẽ34∉{2,3,4,5} closes via `avoid_63_r3hm`.
        have close_r3hm : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w → (w : ZMod 7) = r⁻¹ →
            (2 * qz m (w * d₃) - qz m (w * d i₄)) ∉ ({2, 3, 4, 5} : Finset (ZMod 7)) →
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
              qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
          intro w hw hw_res he34
          set a_m : ZMod 7 := qz m (w * d₃) with ha_def
          have hqd1 : qz m (w * d₁) = a_m + 1 := by
            rw [ha_def, qz_top_affine m w d₁ d₃ hd1, hw_res, ← hr_def, inv_mul_cancel₀ hr_ne]
          have hqd2 : qz m (w * d₂) = a_m + 3 := by
            rw [ha_def, qz_top_affine m w d₂ d₃ hd2, hw_res, hr3]
            congr 1
            rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
          obtain ⟨k, hk0, hk1, hk3, hk4, hk5⟩ :=
            avoid_63_r3hm a_m (qz m (w * d i₄)) (qz m (w * d i₅)) he34
          refine lift_shift m (by omega) d w hw k (fun i => ?_)
          rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
          · subst hk₀; rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
            have hmem : qz m (w * b₁ k₀) ∈
                ({qz m (w * d₁), qz m (w * d₂), qz m (w * d₃)} : Finset (ZMod 7)) := by
              rw [← hset_eq w]; fin_cases k₀ <;> simp
            rw [hqd1, hqd2, ← ha_def] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h' | h'
            · rw [h']; exact hk1
            · rw [h']; exact hk3
            · rw [h']; exact hk0
          · subst hi; rw [hi₄_res, mul_comm k (2 : ZMod 7)]; exact hk4
          · subst hi; rw [hi₅_res, mul_comm k (4 : ZMod 7)]; exact hk5
        -- Lemma 7 on (u·d₃, u·d₄), target X = {2,3,4,5}.
        have hr_L7 : ((u_int * d i₄ : ℤ) : ZMod 7) = 2 * ((u_int * d₃ : ℤ) : ZMod 7) := by
          push_cast; rw [hu_cast, hi₄_res, he₃_res]; ring
        have hd3_nd : ¬ (7 : ℤ) ∣ (u_int * d₃) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (d₃ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d₃) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with hh | hh
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
          · rw [he₃_res] at hh; exact one_ne_zero hh
        have hd4_nd : ¬ (7 : ℤ) ∣ (u_int * d i₄) := by
          intro hdvd
          have h1 : (u_int : ZMod 7) * (d i₄ : ZMod 7) = 0 := by
            have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u_int * d i₄) 7).mpr hdvd
            push_cast at this; exact this
          rcases mul_eq_zero.mp h1 with hh | hh
          · exact hu_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mp hh)
          · rw [hi₄_res] at hh; exact two_ne_zero_z7 hh
        set e34u : ℤ := 2 * (u_int * d₃) - (u_int * d i₄) with he34u_def
        -- Assemble ẽ34 control into a composed multiplier `lam₁·u_int`, then `close_r3hm`.
        have finish_L7 : ∀ (lam₁ : ℤ), ¬ (7 : ℤ) ∣ lam₁ → (lam₁ : ZMod 7) = 1 →
            (2 * qz m (lam₁ * (u_int * d₃)) - qz m (lam₁ * (u_int * d i₄))) ∉
              ({2, 3, 4, 5} : Finset (ZMod 7)) →
            ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
              qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
          intro lam₁ hl1nd hl1res hetal
          refine close_r3hm (lam₁ * u_int) ?_ ?_ ?_
          · intro hdvd
            rcases (seven_totient_full_int).dvd_mul.mp hdvd with hh | hh
            · exact hl1nd hh
            · exact hu_ndvd hh
          · push_cast; rw [hl1res, hu_cast, one_mul]
          · rw [show (lam₁ * u_int) * d₃ = lam₁ * (u_int * d₃) from by ring,
                show (lam₁ * u_int) * d i₄ = lam₁ * (u_int * d i₄) from by ring]
            exact hetal
        by_cases hmdvd : (7 : ℤ) ^ m ∣ e34u
        · by_cases hgap : qz m e34u ∈ ({3, 4, 5} : Finset (ZMod 7))
          · -- FALLBACK: ν(e34)=m ∧ qz(e34)∈{3,4,5}. First test if the plain `u`-frame
            -- already has ẽ34∉{2,3,4,5}; else 2-carry pin (ν(e45)≥m) or Lemma 7 (ν(e45)<m).
            by_cases hetil34 :
                (2 * qz m (u_int * d₃) - qz m (u_int * d i₄)) ∈ ({2, 3, 4, 5} : Finset (ZMod 7))
            · -- ẽ34∈{2,3,4,5}: control both carries.
              set e45u : ℤ := u_int * (2 * d i₄ - d i₅) with he45u_def
              by_cases h45 : (7 : ℤ) ^ m ∣ e45u
              · -- ν(e₄₅) ≥ m: the two-carry pin `q(7·d₃)=4ε₁+2ε₂`.
                have hp7 : Prime (7 : ℤ) := seven_totient_full_int
                obtain ⟨e1, e2, Atar, he1, he2, hA0, hA1, hA3, hd4a, hd5a⟩ :=
                  fallback_63_choice (qz m e34u) (qz m e45u) hgap
                obtain ⟨e1n, he1n_le, he1n_cast⟩ : ∃ n : ℕ, n ≤ 1 ∧ ((n : ℕ) : ZMod 7) = e1 := by
                  rcases he1 with rfl | rfl
                  · exact ⟨0, by omega, by simp⟩
                  · exact ⟨1, le_refl _, by simp⟩
                obtain ⟨e2n, he2n_le, he2n_cast⟩ : ∃ n : ℕ, n ≤ 1 ∧ ((n : ℕ) : ZMod 7) = e2 := by
                  rcases he2 with rfl | rfl
                  · exact ⟨0, by omega, by simp⟩
                  · exact ⟨1, le_refl _, by simp⟩
                -- Λ₁ retarget pins q(7·u·d₃) = 4ε₁+2ε₂.
                have h7d3_dvd : (7 : ℤ) ^ 1 ∣ 7 * (u_int * d₃) := ⟨u_int * d₃, by ring⟩
                have h7d3_ndvd : ¬ (7 : ℤ) ^ (1 + 1) ∣ 7 * (u_int * d₃) := by
                  rintro ⟨cc, hcc⟩
                  refine hd3_nd ⟨cc, mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num) ?_⟩
                  rw [hcc]; ring
                obtain ⟨k₂, hqk₂, hk₂u⟩ := qz_retarget m 1 (by omega) (7 * (u_int * d₃))
                  h7d3_dvd h7d3_ndvd ((4 * e1n + 2 * e2n : ℕ) : ZMod 7)
                set w' : ℤ := (1 + k₂ * 7 ^ (m - 1)) * u_int with hw'_def
                have hw'_res : (w' : ZMod 7) = r⁻¹ := by
                  rw [hw'_def]; push_cast
                  rw [seven_eq_zero_z7, zero_pow (show m - 1 ≠ 0 by omega), mul_zero, add_zero,
                    hu_cast, one_mul]
                have hw'_ndvd : ¬ (7 : ℤ) ∣ w' := by
                  rw [hw'_def]; intro hdvd
                  rcases hp7.dvd_mul.mp hdvd with hh | hh
                  · exact hk₂u hh
                  · exact hu_ndvd hh
                set A₀ : ZMod 7 := qz m (w' * d₃) with hA₀_def
                have hpin : qz m (7 * (w' * d₃)) = ((4 * e1n + 2 * e2n : ℕ) : ZMod 7) := by
                  rw [show 7 * (w' * d₃) = (1 + k₂ * 7 ^ (m - 1)) * (7 * (u_int * d₃)) from by
                    rw [hw'_def]; ring]
                  exact hqk₂
                obtain ⟨hdbl, hquad⟩ :=
                  qz_double_quad_carry m (by omega) (w' * d₃) e1n e2n he1n_le he2n_le hpin
                have hlam2_res : ((1 + k₂ * 7 ^ (m - 1) : ℤ) : ZMod 7) = 1 := by
                  push_cast
                  rw [seven_eq_zero_z7, zero_pow (show m - 1 ≠ 0 by omega), mul_zero, add_zero]
                rw [he1n_cast] at hdbl
                have hquad' : qz m (4 * (w' * d₃)) = 4 * qz m (w' * d₃) + (2 * e1 + e2) := by
                  rw [hquad]; push_cast; rw [he1n_cast, he2n_cast]
                -- A₁ arcs {A₀, A₀+1, A₀+3}.
                have harc₁ : qz m (w' * d₁) = A₀ + 1 := by
                  rw [hA₀_def, qz_top_affine m w' d₁ d₃ hd1, hw'_res, ← hr_def,
                    inv_mul_cancel₀ hr_ne]
                have harc₂ : qz m (w' * d₂) = A₀ + 3 := by
                  rw [hA₀_def, qz_top_affine m w' d₂ d₃ hd2, hw'_res, hr3]
                  congr 1
                  rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
                -- d₄ arc = 2A₀+ε₁−T34 via e₃₄ = 2d₃−d₄ at level m.
                obtain ⟨γ, hγ⟩ := hmdvd
                have hkey34 : (7 : ℤ) ^ m * γ = 2 * (u_int * d₃) - u_int * d i₄ :=
                  hγ.symm.trans he34u_def
                have hd4split : w' * d i₄ = 2 * (w' * d₃) - 7 ^ m * ((1 + k₂ * 7 ^ (m - 1)) * γ) := by
                  rw [hw'_def]; linear_combination (1 + k₂ * 7 ^ (m - 1)) * hkey34
                have hqγ : qz m e34u = (γ : ZMod 7) := by
                  rw [hγ]; simp only [qz]
                  rw [Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
                have hT34cast : (((1 + k₂ * 7 ^ (m - 1)) * γ : ℤ) : ZMod 7) = qz m e34u := by
                  rw [Int.cast_mul, hlam2_res, one_mul]; exact hqγ.symm
                have harc₄ : qz m (w' * d i₄) = 2 * A₀ + e1 - qz m e34u := by
                  rw [hd4split, qz_sub_mul_pow, hdbl, hT34cast]
                -- d₅ arc = 4A₀+2ε₁+ε₂−2T34−T45 via e₄₅ = 2d₄−d₅ at level m.
                obtain ⟨δ, hδ⟩ := h45
                have hkey45 : (7 : ℤ) ^ m * δ = u_int * (2 * d i₄ - d i₅) :=
                  hδ.symm.trans he45u_def
                have hd5split : w' * d i₅
                    = 2 * (w' * d i₄) - 7 ^ m * ((1 + k₂ * 7 ^ (m - 1)) * δ) := by
                  rw [hw'_def]; linear_combination (1 + k₂ * 7 ^ (m - 1)) * hkey45
                have hqδ : qz m e45u = (δ : ZMod 7) := by
                  rw [hδ]; simp only [qz]
                  rw [Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
                have hT45cast : (((1 + k₂ * 7 ^ (m - 1)) * δ : ℤ) : ZMod 7) = qz m e45u := by
                  rw [Int.cast_mul, hlam2_res, one_mul]; exact hqδ.symm
                have h2d4 : qz m (2 * (w' * d i₄)) = 4 * A₀ + 2 * e1 + e2 - 2 * qz m e34u := by
                  have hsplit2 : 2 * (w' * d i₄)
                      = 4 * (w' * d₃) - 7 ^ m * (2 * ((1 + k₂ * 7 ^ (m - 1)) * γ)) := by
                    rw [hd4split]; ring
                  rw [hsplit2, qz_sub_mul_pow, hquad',
                    show ((2 * ((1 + k₂ * 7 ^ (m - 1)) * γ) : ℤ) : ZMod 7) = 2 * qz m e34u from by
                      rw [Int.cast_mul, hT34cast]; norm_num]
                  ring
                have harc₅ : qz m (w' * d i₅) = 4 * A₀ + 2 * e1 + e2 - 2 * qz m e34u - qz m e45u := by
                  rw [hd5split, qz_sub_mul_pow, h2d4, hT45cast]
                -- Λ_m base shift to `Atar` and final assembly via `lift_shift`.
                refine lift_shift m (by omega) d w' hw'_ndvd (Atar - A₀) (fun i => ?_)
                rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
                · subst hk₀; rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
                  have hmem : qz m (w' * b₁ k₀) ∈
                      ({qz m (w' * d₁), qz m (w' * d₂), qz m (w' * d₃)} : Finset (ZMod 7)) := by
                    rw [← hset_eq w']; fin_cases k₀ <;> simp
                  rw [harc₁, harc₂, ← hA₀_def] at hmem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                  rcases hmem with h' | h' | h'
                  · rw [h', show A₀ + 1 + (Atar - A₀) = Atar + 1 from by ring]; exact hA1
                  · rw [h', show A₀ + 3 + (Atar - A₀) = Atar + 3 from by ring]; exact hA3
                  · rw [h', show A₀ + (Atar - A₀) = Atar from by ring]; exact hA0
                · subst hi
                  rw [hi₄_res, harc₄,
                    show 2 * A₀ + e1 - qz m e34u + (Atar - A₀) * 2 = 2 * Atar - (qz m e34u - e1)
                      from by ring]
                  exact hd4a
                · subst hi
                  rw [hi₅_res, harc₅,
                    show 4 * A₀ + 2 * e1 + e2 - 2 * qz m e34u - qz m e45u + (Atar - A₀) * 4
                      = 4 * Atar - 2 * (qz m e34u - e1) - (qz m e45u - e2) from by ring]
                  exact hd5a
              · -- ν(e₄₅) < m: retarget e₄₅ (Λ_{ν(e₄₅)}) to q(e₄₅)=0, then a single Λ₁ pin
                -- fixes ẽ34=T34−ε₁∈{3,4}; d₅ follows from `q(e₄₅)=0`.
                have hp7 : Prime (7 : ℤ) := seven_totient_full_int
                have he45_res0 : ((2 * d i₄ - d i₅ : ℤ) : ZMod 7) = 0 := by
                  push_cast; rw [hi₄_res, hi₅_res]; ring
                have h7_e45u : (7 : ℤ) ∣ e45u := by
                  rw [he45u_def, show u_int * (2 * d i₄ - d i₅)
                      = (2 * d i₄ - d i₅) * u_int from by ring]
                  exact Dvd.dvd.mul_right ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp he45_res0) _
                have he45u_ne : e45u ≠ 0 := fun h0 => h45 (by rw [h0]; exact dvd_zero _)
                set ν45 : ℕ := padicValInt 7 e45u with hν45_def
                have hν45_dvd : (7 : ℤ) ^ ν45 ∣ e45u := padicValInt_dvd e45u
                have hν45_lt : ν45 < m := by
                  by_contra hge; push_neg at hge
                  exact h45 (dvd_trans (pow_dvd_pow 7 hge) hν45_dvd)
                have hν45_ndvd : ¬ (7 : ℤ) ^ (ν45 + 1) ∣ e45u := by
                  intro hh
                  have hle : ν45 + 1 ≤ padicValInt 7 e45u :=
                    ((padicValInt_dvd_iff (ν45 + 1) e45u).mp hh).resolve_left he45u_ne
                  omega
                have hν45_ge1 : 1 ≤ ν45 := by
                  rcases Nat.eq_zero_or_pos ν45 with h0 | h; swap; · omega
                  exfalso; rw [h0] at hν45_ndvd; exact hν45_ndvd (by simpa using h7_e45u)
                -- `e₃₄ = 2d₃ − d₄` sits at level `m` (coprime cancel from `hmdvd`).
                have hm_e34 : (7 : ℤ) ^ m ∣ (2 * d₃ - d i₄) := by
                  have hcop : IsCoprime u_int ((7 : ℤ) ^ m) :=
                    hp7.irreducible.coprime_pow_of_not_dvd m hu_ndvd
                  exact hcop.symm.dvd_of_dvd_mul_left
                    (by rw [show u_int * (2 * d₃ - d i₄) = e34u from by rw [he34u_def]; ring]; exact hmdvd)
                obtain ⟨γ', hγ'⟩ := hm_e34
                have hT34γ' : (γ' : ZMod 7) = r * qz m e34u := by
                  have hq : qz m e34u = r⁻¹ * (γ' : ZMod 7) := by
                    rw [he34u_def, show 2 * (u_int * d₃) - u_int * d i₄ = u_int * (2 * d₃ - d i₄)
                        from by ring, hγ']
                    simp only [qz]
                    rw [show u_int * (7 ^ m * γ') = 7 ^ m * (u_int * γ') from by ring,
                      Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
                    push_cast; rw [hu_cast]
                  rw [hq, ← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
                -- Placement closer (any frame `w` of residue r⁻¹, with the d₃-doubling carry
                -- `e1c` pinned and `q(w·e₄₅)=0`): place A₁/d₄/d₅ and shift to `Atar`.
                have close_placement : ∀ (w : ℤ) (e1c et34 : ZMod 7), ¬ (7 : ℤ) ∣ w →
                    (w : ZMod 7) = r⁻¹ →
                    qz m (2 * (w * d₃)) = 2 * qz m (w * d₃) + e1c →
                    qz m (w * (2 * d i₄ - d i₅)) = 0 →
                    qz m e34u - e1c = et34 → (et34 = 3 ∨ et34 = 4) →
                    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
                      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
                  intro w e1c et34 hw_nd hw_res hdbl hqe45w het34eq het34mem
                  set A₀ : ZMod 7 := qz m (w * d₃) with hA₀_def
                  have harc₁ : qz m (w * d₁) = A₀ + 1 := by
                    rw [hA₀_def, qz_top_affine m w d₁ d₃ hd1, hw_res, ← hr_def, inv_mul_cancel₀ hr_ne]
                  have harc₂ : qz m (w * d₂) = A₀ + 3 := by
                    rw [hA₀_def, qz_top_affine m w d₂ d₃ hd2, hw_res, hr3]
                    congr 1
                    rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring, inv_mul_cancel₀ hr_ne, mul_one]
                  have hd4split : w * d i₄ = 2 * (w * d₃) - 7 ^ m * (w * γ') := by
                    linear_combination -w * hγ'
                  have hqγ' : ((w * γ' : ℤ) : ZMod 7) = qz m e34u := by
                    push_cast; rw [hw_res, hT34γ', ← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
                  have harc₄ : qz m (w * d i₄) = 2 * A₀ + e1c - qz m e34u := by
                    rw [hd4split, qz_sub_mul_pow, hdbl, hqγ']
                  -- d₅ arc = 2·(d₄ arc) + cc, cc∈{0,1,6}, from q(w·e₄₅)=0.
                  obtain ⟨cc, hcc, hccarry⟩ := qz_2xsuby_carry m (w * d i₄) (w * d i₅)
                  rw [show 2 * (w * d i₄) - w * d i₅ = w * (2 * d i₄ - d i₅) from by ring,
                      hqe45w] at hccarry
                  have hd5eq : qz m (w * d i₅) = 2 * qz m (w * d i₄) + cc := by
                    linear_combination hccarry
                  have harc₅ : qz m (w * d i₅) = 4 * A₀ + 2 * e1c - 2 * qz m e34u + cc := by
                    rw [hd5eq, harc₄]; ring
                  obtain ⟨Atar, hA0, hA1, hA3, hd4a, hd5a⟩ := fallback_63_lo et34 cc het34mem hcc
                  refine lift_shift m (by omega) d w hw_nd (Atar - A₀) (fun i => ?_)
                  rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
                  · subst hk₀; rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
                    have hmem : qz m (w * b₁ k₀) ∈
                        ({qz m (w * d₁), qz m (w * d₂), qz m (w * d₃)} : Finset (ZMod 7)) := by
                      rw [← hset_eq w]; fin_cases k₀ <;> simp
                    rw [harc₁, harc₂, ← hA₀_def] at hmem
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                    rcases hmem with h' | h' | h'
                    · rw [h', show A₀ + 1 + (Atar - A₀) = Atar + 1 from by ring]; exact hA1
                    · rw [h', show A₀ + 3 + (Atar - A₀) = Atar + 3 from by ring]; exact hA3
                    · rw [h', show A₀ + (Atar - A₀) = Atar from by ring]; exact hA0
                  · subst hi
                    rw [hi₄_res, harc₄,
                      show 2 * A₀ + e1c - qz m e34u + (Atar - A₀) * 2 = 2 * Atar - et34 from by
                        rw [← het34eq]; ring]
                    exact hd4a
                  · subst hi
                    rw [hi₅_res, harc₅,
                      show 4 * A₀ + 2 * e1c - 2 * qz m e34u + cc + (Atar - A₀) * 4
                        = 4 * Atar - 2 * et34 + cc from by rw [← het34eq]; ring]
                    exact hd5a
                by_cases hν1 : ν45 = 1
                · -- ν(e₄₅)=1: e₄₅ and the d₃-doubling share the single Λ₁ knob. The
                  -- knob moves the pin p := q(7·w·d₃) and q(w·e₄₅) = e0p + p·rho in
                  -- lockstep; `qz_double_pin` reads the doubling carry off SIX of the
                  -- seven pin values (only p = 3 is ambiguous, and there either carry
                  -- wins), and `fallback_63_l1` picks a winning pin.
                  have hpow : (7 : ℤ) ^ (m - 1) * 7 = 7 ^ m := by
                    rw [← pow_succ]; congr 1; omega
                  obtain ⟨se, hse⟩ := h7_e45u
                  have hse_ne : ((se : ℤ) : ZMod 7) ≠ 0 := by
                    intro h0
                    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd se 7).mp h0
                    refine hν45_ndvd ?_
                    rw [hν1]
                    exact ⟨t, by rw [hse, ht]; ring⟩
                  set rho : ZMod 7 := r * ((se : ℤ) : ZMod 7) with hrho_def
                  have hrho_ne : rho ≠ 0 := mul_ne_zero hr_ne hse_ne
                  set P0 : ZMod 7 := qz m (7 * (u_int * d₃)) with hP0_def
                  set e0p : ZMod 7 := qz m e45u - P0 * rho with he0p_def
                  obtain ⟨p, hp_prop⟩ := fallback_63_l1 (qz m e34u) e0p rho hgap hrho_ne
                  -- Λ₁ retarget realizing the chosen pin: q(7·w·d₃) = p.
                  have h7d3_dvd : (7 : ℤ) ^ 1 ∣ 7 * (u_int * d₃) := ⟨u_int * d₃, by ring⟩
                  have h7d3_ndvd : ¬ (7 : ℤ) ^ (1 + 1) ∣ 7 * (u_int * d₃) := by
                    rintro ⟨c2, hc2⟩
                    refine hd3_nd ⟨c2, mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num) ?_⟩
                    rw [hc2]; ring
                  obtain ⟨k₂, hqk₂, hk₂u⟩ :=
                    qz_retarget m 1 (by omega) (7 * (u_int * d₃)) h7d3_dvd h7d3_ndvd p
                  set w : ℤ := (1 + k₂ * 7 ^ (m - 1)) * u_int with hw_def
                  have hw_res : (w : ZMod 7) = r⁻¹ := by
                    rw [hw_def]; push_cast
                    rw [seven_eq_zero_z7, zero_pow (show m - 1 ≠ 0 by omega), mul_zero,
                      add_zero, hu_cast, one_mul]
                  have hw_ndvd : ¬ (7 : ℤ) ∣ w := by
                    rw [hw_def]; intro hdvd
                    rcases hp7.dvd_mul.mp hdvd with hh | hh
                    · exact hk₂u hh
                    · exact hu_ndvd hh
                  have hpin : qz m (7 * (w * d₃)) = p := by
                    rw [show 7 * (w * d₃) = (1 + k₂ * 7 ^ (m - 1)) * (7 * (u_int * d₃)) from by
                      rw [hw_def]; ring]
                    exact hqk₂
                  -- Knob residue: κ·r⁻¹ = p − P0 (exact level-m shift, no carry).
                  have hP0p : P0 = p - (k₂ : ZMod 7) * r⁻¹ := by
                    have hsplit7 : 7 * (u_int * d₃)
                        = 7 * (w * d₃) - 7 ^ m * (k₂ * (u_int * d₃)) := by
                      rw [hw_def, ← hpow]; ring
                    rw [hP0_def, hsplit7, qz_sub_mul_pow, hpin]
                    push_cast
                    rw [hu_cast, he₃_res]; ring
                  -- q(w·e₄₅) = e0p + p·rho (the lockstep shift of the level-1 e₄₅).
                  have hEval : qz m (w * (2 * d i₄ - d i₅)) = e0p + p * rho := by
                    have hsplit : e45u = w * (2 * d i₄ - d i₅) - 7 ^ m * (k₂ * se) := by
                      have h1 : w * (2 * d i₄ - d i₅) = e45u + k₂ * 7 ^ (m - 1) * e45u := by
                        rw [hw_def, he45u_def]; ring
                      rw [h1, hse, ← hpow]; ring
                    have h2 := qz_sub_mul_pow m (w * (2 * d i₄ - d i₅)) (k₂ * se)
                    rw [← hsplit] at h2
                    have hκ : (k₂ : ZMod 7) = (p - P0) * r := by
                      have h3 : (k₂ : ZMod 7) * r⁻¹ = p - P0 := by rw [hP0p]; ring
                      calc (k₂ : ZMod 7) = (k₂ : ZMod 7) * r⁻¹ * r := by
                            rw [mul_assoc, inv_mul_cancel₀ hr_ne, mul_one]
                        _ = (p - P0) * r := by rw [h3]
                    rw [he0p_def, hrho_def]
                    push_cast at h2
                    rw [hκ] at h2
                    linear_combination -h2
                  -- Doubling carry of w·d₃, pinned one-sidedly by p.
                  obtain ⟨ε, hε01, hdbl, hεlow, hεhigh⟩ := qz_double_pin m (by omega) (w * d₃)
                  obtain ⟨Atar, hA0, hA1, hA3, hd4a, hd5base⟩ :=
                    hp_prop ε hε01
                      (fun hp => hεlow (by rw [hpin]; exact hp))
                      (fun hp => hεhigh (by rw [hpin]; exact hp))
                  -- A₁ arcs {A₀, A₀+1, A₀+3}; d₄ via e₃₄ (level m); d₅ via the carry.
                  set A₀ : ZMod 7 := qz m (w * d₃) with hA₀_def
                  have harc₁ : qz m (w * d₁) = A₀ + 1 := by
                    rw [hA₀_def, qz_top_affine m w d₁ d₃ hd1, hw_res, ← hr_def,
                      inv_mul_cancel₀ hr_ne]
                  have harc₂ : qz m (w * d₂) = A₀ + 3 := by
                    rw [hA₀_def, qz_top_affine m w d₂ d₃ hd2, hw_res, hr3]
                    congr 1
                    rw [show r⁻¹ * (3 * r) = 3 * (r⁻¹ * r) from by ring,
                      inv_mul_cancel₀ hr_ne, mul_one]
                  have hd4split : w * d i₄ = 2 * (w * d₃) - 7 ^ m * (w * γ') := by
                    linear_combination -w * hγ'
                  have hqγ' : ((w * γ' : ℤ) : ZMod 7) = qz m e34u := by
                    push_cast; rw [hw_res, hT34γ', ← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
                  have harc₄ : qz m (w * d i₄) = 2 * A₀ + ε - qz m e34u := by
                    rw [hd4split, qz_sub_mul_pow, hdbl, hqγ']
                  obtain ⟨cc, hcc, hccarry⟩ := qz_2xsuby_carry m (w * d i₄) (w * d i₅)
                  rw [show 2 * (w * d i₄) - w * d i₅ = w * (2 * d i₄ - d i₅) from by ring,
                    hEval] at hccarry
                  have harc₅ : qz m (w * d i₅)
                      = 4 * A₀ + 2 * ε - 2 * qz m e34u - (e0p + p * rho) + cc := by
                    rw [harc₄] at hccarry
                    linear_combination hccarry
                  -- Λ_m base shift to Atar and final assembly.
                  refine lift_shift m (by omega) d w hw_ndvd (Atar - A₀) (fun i => ?_)
                  rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
                  · subst hk₀; rw [hg₁_res k₀, mul_one, show d (g₁ k₀) = b₁ k₀ from rfl]
                    have hmem : qz m (w * b₁ k₀) ∈
                        ({qz m (w * d₁), qz m (w * d₂), qz m (w * d₃)} : Finset (ZMod 7)) := by
                      rw [← hset_eq w]; fin_cases k₀ <;> simp
                    rw [harc₁, harc₂, ← hA₀_def] at hmem
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
                    rcases hmem with h' | h' | h'
                    · rw [h', show A₀ + 1 + (Atar - A₀) = Atar + 1 from by ring]; exact hA1
                    · rw [h', show A₀ + 3 + (Atar - A₀) = Atar + 3 from by ring]; exact hA3
                    · rw [h', show A₀ + (Atar - A₀) = Atar from by ring]; exact hA0
                  · subst hi
                    rw [hi₄_res, harc₄,
                      show 2 * A₀ + ε - qz m e34u + (Atar - A₀) * 2
                        = 2 * Atar + ε - qz m e34u from by ring]
                    exact hd4a
                  · subst hi
                    rw [hi₅_res, harc₅,
                      show 4 * A₀ + 2 * ε - 2 * qz m e34u - (e0p + p * rho) + cc + (Atar - A₀) * 4
                        = (4 * Atar + 2 * ε - 2 * qz m e34u - (e0p + p * rho)) + cc from by ring]
                    rcases hd5base with hb | hb | hb <;> rw [hb] <;>
                      rcases hcc with rfl | rfl | rfl <;> decide
                · have hν45_ge2 : 2 ≤ ν45 := by omega
                  obtain ⟨k_r, hqr, hk_ru⟩ :=
                    qz_retarget m ν45 hν45_lt e45u hν45_dvd hν45_ndvd 0
                  set v : ℤ := (1 + k_r * 7 ^ (m - ν45)) * u_int with hv_def
                  have hv_res : (v : ZMod 7) = r⁻¹ := by
                    rw [hv_def]; push_cast
                    rw [seven_eq_zero_z7, zero_pow (show m - ν45 ≠ 0 by omega), mul_zero, add_zero,
                      hu_cast, one_mul]
                  have hv_nd : ¬ (7 : ℤ) ∣ v := by
                    rw [hv_def]; intro hdvd
                    rcases hp7.dvd_mul.mp hdvd with hh | hh
                    · exact hk_ru hh
                    · exact hu_ndvd hh
                  have hqe45v : qz m (v * (2 * d i₄ - d i₅)) = 0 := by
                    rw [show v * (2 * d i₄ - d i₅) = (1 + k_r * 7 ^ (m - ν45)) * e45u from by
                      rw [hv_def, he45u_def]; ring]
                    exact hqr
                  have hvd3_nd : ¬ (7 : ℤ) ∣ (v * d₃) := by
                    intro hdvd
                    rw [hv_def, show (1 + k_r * 7 ^ (m - ν45)) * u_int * d₃
                        = (1 + k_r * 7 ^ (m - ν45)) * (u_int * d₃) from by ring] at hdvd
                    rcases hp7.dvd_mul.mp hdvd with hh | hh
                    · exact hk_ru hh
                    · exact hd3_nd hh
                  -- `Λ₁` pin builder: realize `q(7·w·d₃)=ptgt∈{0,6}` while keeping `q(w·e₄₅)=0`.
                  have mkw : ∀ (ptgt : ZMod 7), ∃ w : ℤ, ¬ (7 : ℤ) ∣ w ∧ (w : ZMod 7) = r⁻¹ ∧
                      qz m (7 * (w * d₃)) = ptgt ∧ qz m (w * (2 * d i₄ - d i₅)) = 0 := by
                    intro ptgt
                    have h7vd : (7 : ℤ) ^ 1 ∣ 7 * (v * d₃) := ⟨v * d₃, by ring⟩
                    have h7vd' : ¬ (7 : ℤ) ^ (1 + 1) ∣ 7 * (v * d₃) := by
                      rintro ⟨cc, hcc⟩
                      refine hvd3_nd ⟨cc, mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num) ?_⟩
                      rw [hcc]; ring
                    obtain ⟨k_p, hqp, hk_pu⟩ := qz_retarget m 1 (by omega) (7 * (v * d₃)) h7vd h7vd' ptgt
                    have hdvd_ν45 : (7 : ℤ) ^ ν45 ∣ v * (2 * d i₄ - d i₅) := by
                      rw [show v * (2 * d i₄ - d i₅) = (1 + k_r * 7 ^ (m - ν45)) * e45u from by
                        rw [hv_def, he45u_def]; ring]
                      exact hν45_dvd.mul_left _
                    refine ⟨(1 + k_p * 7 ^ (m - 1)) * v, ?_, ?_, ?_, ?_⟩
                    · intro hdvd; rcases hp7.dvd_mul.mp hdvd with hh | hh
                      · exact hk_pu hh
                      · exact hv_nd hh
                    · push_cast
                      rw [seven_eq_zero_z7, zero_pow (show m - 1 ≠ 0 by omega), mul_zero, add_zero,
                        one_mul, hv_res]
                    · rw [show 7 * ((1 + k_p * 7 ^ (m - 1)) * v * d₃)
                          = (1 + k_p * 7 ^ (m - 1)) * (7 * (v * d₃)) from by ring]
                      exact hqp
                    · rw [show (1 + k_p * 7 ^ (m - 1)) * v * (2 * d i₄ - d i₅)
                          = (1 + k_p * 7 ^ (m - 1)) * (v * (2 * d i₄ - d i₅)) from by ring]
                      rw [qz_higher_inert m 1 (by omega) k_p (v * (2 * d i₄ - d i₅))
                        (dvd_trans (pow_dvd_pow 7 (by omega)) hdvd_ν45)]
                      exact hqe45v
                  by_cases h5 : qz m e34u = 5
                  · obtain ⟨w, hw_nd, hw_res, hq7, hqe45w⟩ := mkw 6
                    exact close_placement w 1 4 hw_nd hw_res
                      (by rw [qz_double_carry_one m (by omega) (w * d₃) hq7]) hqe45w
                      (by rw [h5]; exact five_sub_one_z7) (Or.inr rfl)
                  · obtain ⟨w, hw_nd, hw_res, hq7, hqe45w⟩ := mkw 0
                    have het34mem : qz m e34u = 3 ∨ qz m e34u = 4 := by
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
                      rcases hgap with h | h | h
                      · exact Or.inl h
                      · exact Or.inr h
                      · exact absurd h h5
                    exact close_placement w 0 (qz m e34u) hw_nd hw_res
                      (by rw [qz_double_no_carry m (w * d₃) hq7]; ring) hqe45w (by ring) het34mem
            · exact close_r3hm u_int hu_ndvd hu_cast hetil34
          · obtain ⟨lam₁, hl1nd, hl1res, hetal⟩ :=
              lemma7_ii m 0 (by omega) (u_int * d₃) (u_int * d i₄) hd3_nd hd4_nd hr_L7
                {2, 3, 4, 5} hmdvd (by rw [inter2345_eq]; exact hgap)
            exact finish_L7 lam₁ hl1nd hl1res hetal
        · have he_ne : e34u ≠ 0 := fun heq => hmdvd (heq ▸ dvd_zero _)
          set ν := padicValInt 7 e34u with hν_def
          have hν_lt_m : ν < m := by
            by_contra hge; push_neg at hge
            exact hmdvd ((padicValInt_dvd_iff m e34u).mpr (Or.inr hge))
          have hν_ndvd : ¬ (7 : ℤ) ^ (ν + 1) ∣ e34u := by
            intro hh
            have hle : ν + 1 ≤ padicValInt 7 e34u :=
              ((padicValInt_dvd_iff (ν + 1) e34u).mp hh).resolve_left he_ne
            omega
          have hX46 : ∃ a : ZMod 7, fitsInterval ({2, 3, 4, 5} : Finset (ZMod 7)) a 4 :=
            ⟨2, fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl | rfl
              · exact ⟨⟨0, by omega⟩, by norm_num⟩
              · exact ⟨⟨1, by omega⟩, by norm_num⟩
              · exact ⟨⟨2, by omega⟩, by norm_num⟩
              · exact ⟨⟨3, by omega⟩, by norm_num⟩⟩
          obtain ⟨lam₁, hl1nd, hl1res, hetal⟩ :=
            lemma7_i m ν hν_lt_m (u_int * d₃) (u_int * d i₄) hd3_nd hd4_nd hr_L7
              {2, 3, 4, 5} hX46 (padicValInt_dvd e34u) hν_ndvd
          exact finish_L7 lam₁ hl1nd hl1res hetal
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
              rcases hr3s with hrEpos | hrEneg
              · have hν_eq : padicValInt 7 e45 = ν := by
                  apply Nat.le_antisymm
                  · by_contra hlt
                    have hle : ν + 1 ≤ padicValInt 7 e45 := by omega
                    have : (7 : ℤ) ^ (ν + 1) ∣ e45 :=
                      (padicValInt_dvd_iff (ν + 1) e45).mpr (Or.inr hle)
                    exact hνd' this
                  · exact ((padicValInt_dvd_iff ν e45).mp hνd).resolve_left he0
                have hEd : (7 : ℤ) ^ h ∣ e45 := by simpa [hνh] using hνd
                have hs_eq : s = ((e45 / 7 ^ h : ℤ) : ZMod 7) := by
                  have he0' : 2 * d i₄ - d i₅ ≠ 0 := by simpa [he45_def] using he0
                  have hν_eq' : padicValInt 7 (2 * d i₄ - d i₅) = ν := by
                    simpa [he45_def] using hν_eq
                  rw [hs_def_orig, if_neg he0']
                  rw [hν_eq', hνh, he45_def]
                have hEres : ((e45 / 7 ^ h : ℤ) : ZMod 7) =
                    (((d₂ - d₃) / 7 ^ h : ℤ) : ZMod 7) := by
                  calc
                    ((e45 / 7 ^ h : ℤ) : ZMod 7) = s := hs_eq.symm
                    _ = (((d₂ - d₃) / 7 ^ h : ℤ) : ZMod 7) := hrEpos.symm
                obtain ⟨lam, hlam, hctrl⟩ := ii2b_control m h hlt d₁ d₂ d₃ e45
                  hd1 hd1' hd2 hr3 hEd hEres
                have carve_mem : ∀ (l : ℤ), qz m (l * e45) ∈ ({0, 6} : Finset (ZMod 7)) →
                    (2 * qz m (l * d i₄) - qz m (l * d i₅)) ∉ ({2, 4} : Finset (ZMod 7)) := by
                  intro l hq
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                  rcases hq with hq | hq
                  · obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (l * d i₄) (l * d i₅)
                    rw [show l * e45 = 2 * (l * d i₄) - l * d i₅ from by
                      rw [he45_def]; ring, hcarry] at hq
                    rw [show 2 * qz m (l * d i₄) - qz m (l * d i₅) = -c from by
                      linear_combination hq]
                    rcases hc with rfl | rfl | rfl <;> decide
                  · exact carve_of l hq
                by_cases hsmall : ∃ a : ZMod 7, fitsInterval
                    ({qz m (lam * d₁), qz m (lam * d₂), qz m (lam * d₃)} : Finset (ZMod 7)) a 2
                · obtain ⟨a, hfit⟩ := hsmall
                  exact close_l5 lam hlam a 2 (by omega) (by omega)
                    (fit_of_set lam a 2 (by rw [hset_eq lam]; exact hfit)) (fun h => by omega)
                · have hlarge := hctrl.resolve_left hsmall
                  obtain ⟨⟨a, hfit⟩, hqE⟩ := hlarge
                  exact close_l5 lam hlam a 3 (by omega) (by omega)
                    (fit_of_set lam a 3 (by rw [hset_eq lam]; exact hfit))
                    (fun _ => carve_mem lam hqE)
              · have hEd : (7 : ℤ) ^ h ∣ e45 := by simpa [hνh] using hνd
                have hν_eq : padicValInt 7 e45 = ν := by
                  apply Nat.le_antisymm
                  · by_contra hlt'
                    have hle : ν + 1 ≤ padicValInt 7 e45 := by omega
                    exact hνd' ((padicValInt_dvd_iff (ν + 1) e45).mpr (Or.inr hle))
                  · exact ((padicValInt_dvd_iff ν e45).mp hνd).resolve_left he0
                have hs_eq : s = ((e45 / 7 ^ h : ℤ) : ZMod 7) := by
                  have he0' : 2 * d i₄ - d i₅ ≠ 0 := by simpa [he45_def] using he0
                  have hν_eq' : padicValInt 7 (2 * d i₄ - d i₅) = ν := by
                    simpa [he45_def] using hν_eq
                  rw [hs_def_orig, if_neg he0']
                  rw [hν_eq', hνh, he45_def]
                have hEres : ((e45 / 7 ^ h : ℤ) : ZMod 7) =
                    (((-d₂ - -d₃) / 7 ^ h : ℤ) : ZMod 7) := by
                  rw [show -d₂ - -d₃ = -(d₂ - d₃) by ring,
                    Int.neg_ediv_of_dvd hd2]
                  push_cast
                  simpa [hs_eq, neg_neg] using congrArg Neg.neg hrEneg.symm
                have hneg1 : (7 : ℤ) ^ h ∣ -d₁ - -d₃ := by
                  rw [show -d₁ - -d₃ = -(d₁ - d₃) by ring]; exact dvd_neg.mpr hd1
                have hneg1' : ¬ (7 : ℤ) ^ (h + 1) ∣ -d₁ - -d₃ := by
                  intro hh
                  apply hd1'
                  have hh' : (7 : ℤ) ^ (h + 1) ∣ -(d₁ - d₃) := by
                    simpa [show -d₁ - -d₃ = -(d₁ - d₃) by ring] using hh
                  exact dvd_neg.mp hh'
                have hneg2 : (7 : ℤ) ^ h ∣ -d₂ - -d₃ := by
                  rw [show -d₂ - -d₃ = -(d₂ - d₃) by ring]; exact dvd_neg.mpr hd2
                have hnegEbase : ¬ (7 : ℤ) ^ m ∣ e45 := by
                  intro hh
                  apply hνd'
                  exact dvd_trans (pow_dvd_pow 7 (by omega : ν + 1 ≤ m)) hh
                have hcarve_mem : ∀ (l : ℤ), qz m (l * e45) ∈ ({0, 6} : Finset (ZMod 7)) →
                    (2 * qz m (l * d i₄) - qz m (l * d i₅)) ∉ ({2, 4} : Finset (ZMod 7)) := by
                  intro l hq
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                  rcases hq with hq | hq
                  · obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (l * d i₄) (l * d i₅)
                    rw [show l * e45 = 2 * (l * d i₄) - l * d i₅ from by
                      rw [he45_def]; ring, hcarry] at hq
                    rw [show 2 * qz m (l * d i₄) - qz m (l * d i₅) = -c from by
                      linear_combination hq]
                    rcases hc with rfl | rfl | rfl <;> decide
                  · exact carve_of l hq
                have hneg_r : (((-d₂ - -d₃) / 7 ^ h : ℤ) : ZMod 7) =
                    3 * (((-d₁ - -d₃) / 7 ^ h : ℤ) : ZMod 7) := by
                  rw [show -d₂ - -d₃ = -(d₂ - d₃) by ring, Int.neg_ediv_of_dvd hd2,
                    show -d₁ - -d₃ = -(d₁ - d₃) by ring, Int.neg_ediv_of_dvd hd1]
                  push_cast
                  rw [hr3]
                  ring
                obtain ⟨lam, hlam, hctrl⟩ := ii2b_control m h hlt (-d₁) (-d₂) (-d₃) e45
                  hneg1 hneg1' hneg2 hneg_r hEd hEres
                have hnd1 : ¬ (7 : ℤ) ^ m ∣ lam * d₁ := by
                  intro hh
                  have h7 : (7 : ℤ) ∣ lam * d₁ := dvd_trans (dvd_pow_self 7 (by omega : m ≠ 0)) hh
                  rcases (seven_totient_full_int).dvd_mul.mp h7 with h7 | h7
                  · exact hlam h7
                  · have : (d₁ : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d₁ 7).mpr h7
                    exact one_ne_zero (he₁_res ▸ this)
                have hnd2 : ¬ (7 : ℤ) ^ m ∣ lam * d₂ := by
                  intro hh
                  have h7 : (7 : ℤ) ∣ lam * d₂ := dvd_trans (dvd_pow_self 7 (by omega : m ≠ 0)) hh
                  rcases (seven_totient_full_int).dvd_mul.mp h7 with h7 | h7
                  · exact hlam h7
                  · have : (d₂ : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d₂ 7).mpr h7
                    exact one_ne_zero (he₂_res ▸ this)
                have hnd3 : ¬ (7 : ℤ) ^ m ∣ lam * d₃ := by
                  intro hh
                  have h7 : (7 : ℤ) ∣ lam * d₃ := dvd_trans (dvd_pow_self 7 (by omega : m ≠ 0)) hh
                  rcases (seven_totient_full_int).dvd_mul.mp h7 with h7 | h7
                  · exact hlam h7
                  · have : (d₃ : ZMod 7) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d₃ 7).mpr h7
                    exact one_ne_zero (he₃_res ▸ this)
                have hndE : ¬ (7 : ℤ) ^ m ∣ lam * e45 := pow7_ndvd_mul m lam e45 hlam hnegEbase
                have hreflect : ∀ L : ℕ, (L = 2 ∨ L = 3) →
                    (∃ a : ZMod 7, fitsInterval
                      ({qz m (lam * -d₁), qz m (lam * -d₂), qz m (lam * -d₃)} : Finset (ZMod 7)) a L) →
                    ∃ a : ZMod 7, fitsInterval
                      ({qz m (lam * d₁), qz m (lam * d₂), qz m (lam * d₃)} : Finset (ZMod 7)) a L := by
                  intro L hL hfit
                  obtain ⟨a, hfit⟩ := hfit
                  have hn1 : qz m (lam * -d₁) = 6 - qz m (lam * d₁) := by
                    rw [show lam * -d₁ = -(lam * d₁) by ring, qz_neg m (lam * d₁) hnd1]
                  have hn2 : qz m (lam * -d₂) = 6 - qz m (lam * d₂) := by
                    rw [show lam * -d₂ = -(lam * d₂) by ring, qz_neg m (lam * d₂) hnd2]
                  have hn3 : qz m (lam * -d₃) = 6 - qz m (lam * d₃) := by
                    rw [show lam * -d₃ = -(lam * d₃) by ring, qz_neg m (lam * d₃) hnd3]
                  rw [hn1, hn2, hn3] at hfit
                  exact reflect_fit_63 _ _ _ a L hL hfit
                by_cases hsmall : ∃ a : ZMod 7, fitsInterval
                    ({qz m (lam * -d₁), qz m (lam * -d₂), qz m (lam * -d₃)} : Finset (ZMod 7)) a 2
                · obtain ⟨a, hfit⟩ := hreflect 2 (Or.inl rfl) hsmall
                  exact close_l5 lam hlam a 2 (by omega) (by omega)
                    (fit_of_set lam a 2 (by rw [hset_eq lam]; exact hfit)) (fun h => by omega)
                · have hlarge := hctrl.resolve_left hsmall
                  obtain ⟨⟨a, hfit⟩, hqE⟩ := hlarge
                  obtain ⟨a', hfit'⟩ := hreflect 3 (Or.inr rfl) ⟨a, hfit⟩
                  exact close_l5 lam hlam a' 3 (by omega) (by omega)
                    (fit_of_set lam a' 3 (by rw [hset_eq lam]; exact hfit'))
                    (fun _ => hcarve_mem lam hqE)
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
                  rw [hνeqm] at hνd
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
theorem case_64 (hm : 2 ≤ m)
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
        haveI h7p : Fact (Nat.Prime 7) := ⟨seven_totient_full⟩
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
              have hp : Prime (7 : ℤ) := seven_totient_full_int
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
                have hp7 : Prime (7 : ℤ) := seven_totient_full_int
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

/-! ### §6.5 front-half toolkit (BS L698–731)

BS (14) asks, up to a multiplier, for `ℓ(A₁) ≤ 3 ∧ ℓ(A₄) ≤ 3` or
`ℓ(A₁) ≤ 4 ∧ ℓ(A₄) ≤ 2`; those two disjuncts are `case65_window_33` /
`case65_window_42` above. The lemmas here are the "compress, then double or
triple" engine of BS's branch `(i) or (ii.1) with h < m` (L706–709), restated so
that no real-metric (`|e|_N ≥ 5N/14`) reasoning is needed. The hypothesis
replacing BS's metric statement is that all three `A₁` points sit AHEAD of one
common apex by at most `7^m` — which is exactly what a two-target `Λ`-retarget
(`qz_retarget_two` with targets `0,0`) delivers. -/

/-- Adding a nonnegative `s ≤ c·7^m` raises the arc index by some `j ≤ c`:
`q(B + s) = q(B) + j`. (Euclidean: `B % 7^m + s < (c+1)·7^m`.) -/
theorem qz_add_small (m : ℕ) (B s : ℤ) (c : ℕ) (hs0 : 0 ≤ s)
    (hs : s ≤ (c : ℤ) * (7 : ℤ) ^ m) :
    ∃ j : ℕ, j ≤ c ∧ qz m (B + s) = qz m B + (j : ZMod 7) := by
  have hP : (0 : ℤ) < (7 : ℤ) ^ m := by positivity
  have hR0 : 0 ≤ B % (7 : ℤ) ^ m := Int.emod_nonneg B (ne_of_gt hP)
  have hRP : B % (7 : ℤ) ^ m < (7 : ℤ) ^ m := Int.emod_lt_of_pos B hP
  have hBd : (7 : ℤ) ^ m * (B / (7 : ℤ) ^ m) + B % (7 : ℤ) ^ m = B := Int.mul_ediv_add_emod B _
  have hdiv : (B + s) / (7 : ℤ) ^ m
      = B / (7 : ℤ) ^ m + (B % (7 : ℤ) ^ m + s) / (7 : ℤ) ^ m := by
    rw [show B + s = (B % (7 : ℤ) ^ m + s) + (7 : ℤ) ^ m * (B / (7 : ℤ) ^ m) by omega,
      Int.add_mul_ediv_left _ _ (ne_of_gt hP)]
    ring
  have hj0 : 0 ≤ (B % (7 : ℤ) ^ m + s) / (7 : ℤ) ^ m := Int.ediv_nonneg (by omega) (le_of_lt hP)
  have hjc : (B % (7 : ℤ) ^ m + s) / (7 : ℤ) ^ m ≤ (c : ℤ) := by
    have h1 : (B % (7 : ℤ) ^ m + s) / (7 : ℤ) ^ m < (c : ℤ) + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hP]; nlinarith
    omega
  refine ⟨((B % (7 : ℤ) ^ m + s) / (7 : ℤ) ^ m).toNat, by omega, ?_⟩
  simp only [qz, hdiv]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hj0]
  push_cast; ring

/-- `7^{m+1}`-multiples are invisible to `q` (they shift the quotient by `7·w`). -/
theorem qz_add_high (m : ℕ) (B w : ℤ) :
    qz m (B + (7 : ℤ) ^ (m + 1) * w) = qz m B := by
  have hP : ((7 : ℤ) ^ m) ≠ 0 := by positivity
  simp only [qz]
  rw [show B + (7 : ℤ) ^ (m + 1) * w = B + (7 : ℤ) ^ m * (7 * w) by ring, mul_comm ((7 : ℤ) ^ m),
    Int.add_mul_ediv_right _ _ hP]
  push_cast
  rw [seven_eq_zero_z7]; ring

/-- **Ahead-shift.** If `x ≡ ρ (mod 7^{m+1})` with `0 ≤ ρ ≤ 7^m` (BS: `x` sits ahead
of the origin by at most `N/7`), then multiplying by `c` moves the arc index up by
at most `c`: `q(B + c·x) = q(B) + j`, `j ≤ c`. This is the whole content of BS's
`ℓ(2·A₁) ≤ 3` / `ℓ(3·A₁) ≤ 4` (L707–709), with no real-metric argument. -/
theorem qz_ahead_shift (m : ℕ) (B x ρ : ℤ) (c : ℕ)
    (hρ0 : 0 ≤ ρ) (hρP : ρ ≤ (7 : ℤ) ^ m) (hdvd : (7 : ℤ) ^ (m + 1) ∣ (x - ρ)) :
    ∃ j : ℕ, j ≤ c ∧ qz m (B + (c : ℤ) * x) = qz m B + (j : ZMod 7) := by
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨j, hj, hje⟩ := qz_add_small m B ((c : ℤ) * ρ) c (by positivity)
    (mul_le_mul_of_nonneg_left hρP (by positivity))
  refine ⟨j, hj, ?_⟩
  rw [show B + (c : ℤ) * x = (B + (c : ℤ) * ρ) + (7 : ℤ) ^ (m + 1) * ((c : ℤ) * w) by
    have hx : x = ρ + (7 : ℤ) ^ (m + 1) * w := by omega
    rw [hx]; ring, qz_add_high, hje]

/-- **Doubling and tripling carries with the one-sided links.** `q(2x) = 2q(x)+ε₂`,
`q(3x) = 3q(x)+ε₃`, and `ε₂ = 0 ⇒ ε₃ ≤ 1`, `ε₂ = 1 ⇒ ε₃ ≥ 1` (from `2ρ < 7^m ⇒
3ρ < 2·7^m` and `2ρ ≥ 7^m ⇒ 3ρ ≥ 7^m` on the shared low part `ρ = x % 7^m`).
These links are what make BS's `5N/14` threshold unnecessary. -/
theorem qz_23_carry (m : ℕ) (x : ℤ) :
    ∃ e2 e3 : ℕ, e2 ≤ 1 ∧ e3 ≤ 2 ∧
      qz m (2 * x) = 2 * qz m x + (e2 : ZMod 7) ∧
      qz m (3 * x) = 3 * qz m x + (e3 : ZMod 7) ∧
      (e2 = 0 → e3 ≤ 1) ∧ (e2 = 1 → 1 ≤ e3) := by
  have hP : (0 : ℤ) < (7 : ℤ) ^ m := by positivity
  set R : ℤ := x % (7 : ℤ) ^ m with hRdef
  have hR0 : 0 ≤ R := Int.emod_nonneg x (ne_of_gt hP)
  have hRP : R < (7 : ℤ) ^ m := Int.emod_lt_of_pos x hP
  have hBd : (7 : ℤ) ^ m * (x / (7 : ℤ) ^ m) + R = x := Int.mul_ediv_add_emod x _
  have h2 : (2 * x) / (7 : ℤ) ^ m = 2 * (x / (7 : ℤ) ^ m) + (2 * R) / (7 : ℤ) ^ m := by
    rw [show 2 * x = 2 * R + (7 : ℤ) ^ m * (2 * (x / (7 : ℤ) ^ m)) by linear_combination -2 * hBd,
      Int.add_mul_ediv_left _ _ (ne_of_gt hP)]; ring
  have h3 : (3 * x) / (7 : ℤ) ^ m = 3 * (x / (7 : ℤ) ^ m) + (3 * R) / (7 : ℤ) ^ m := by
    rw [show 3 * x = 3 * R + (7 : ℤ) ^ m * (3 * (x / (7 : ℤ) ^ m)) by linear_combination -3 * hBd,
      Int.add_mul_ediv_left _ _ (ne_of_gt hP)]; ring
  have he20 : 0 ≤ (2 * R) / (7 : ℤ) ^ m := Int.ediv_nonneg (by omega) (le_of_lt hP)
  have he21 : (2 * R) / (7 : ℤ) ^ m ≤ 1 := by
    have : (2 * R) / (7 : ℤ) ^ m < 2 := by rw [Int.ediv_lt_iff_lt_mul hP]; omega
    omega
  have he30 : 0 ≤ (3 * R) / (7 : ℤ) ^ m := Int.ediv_nonneg (by omega) (le_of_lt hP)
  have he32 : (3 * R) / (7 : ℤ) ^ m ≤ 2 := by
    have : (3 * R) / (7 : ℤ) ^ m < 3 := by rw [Int.ediv_lt_iff_lt_mul hP]; omega
    omega
  refine ⟨((2 * R) / (7 : ℤ) ^ m).toNat, ((3 * R) / (7 : ℤ) ^ m).toNat, by omega, by omega,
    ?_, ?_, ?_, ?_⟩
  · simp only [qz, h2]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg he20]; push_cast; ring
  · simp only [qz, h3]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg he30]; push_cast; ring
  · intro h
    have hlt : 2 * R < (7 : ℤ) ^ m := by
      by_contra hc
      have : 1 ≤ (2 * R) / (7 : ℤ) ^ m := by rw [Int.le_ediv_iff_mul_le hP]; omega
      omega
    have : (3 * R) / (7 : ℤ) ^ m < 2 := by rw [Int.ediv_lt_iff_lt_mul hP]; omega
    omega
  · intro h
    have hge : 1 ≤ (2 * R) / (7 : ℤ) ^ m := by omega
    rw [Int.le_ediv_iff_mul_le hP] at hge
    have : 1 ≤ (3 * R) / (7 : ℤ) ^ m := by rw [Int.le_ediv_iff_mul_le hP]; omega
    omega

/-- Two `ZMod 7` points at circular distance `≤ 2` fit a common length-3 window. -/
theorem pair_fits3 (α β : ZMod 7) (h : β - α ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, (∃ j : Fin 3, α = a + (j.val : ZMod 7)) ∧
      (∃ j : Fin 3, β = a + (j.val : ZMod 7)) := by
  revert h; revert α β; decide

/-- Two `ZMod 7` points at circular distance `≤ 1` fit a common length-2 window. -/
theorem pair_fits2 (α β : ZMod 7) (h : β - α ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, (∃ j : Fin 2, α = a + (j.val : ZMod 7)) ∧
      (∃ j : Fin 2, β = a + (j.val : ZMod 7)) := by
  revert h; revert α β; decide

/-- `{0,1,5,6}` and its `+1` translate both sit inside `{0,1,2,5,6}` (the `ℓ₄ ≤ 3`
band): one carry cannot push a distance-`≤1` `q` value out of the good band. -/
theorem shift_0156 (D : ZMod 7) (h : D ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    D ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) ∧
      D + 1 ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  revert h; revert D; decide

/-- The complement of `{0,1,5,6}` in `ZMod 7` (BS's bad band `q(e₄₅) ∈ {2,3,4}`). -/
theorem z7_not_0156 (D : ZMod 7) (h : D ∉ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    D = 2 ∨ D = 3 ∨ D = 4 := by
  revert h; revert D; decide

/-- `x` sits AHEAD of the origin by at most `N/7`: `x ≡ ρ (mod 7^{m+1})` with
`0 ≤ ρ ≤ 7^m`. This is BS's `|x|_N ≤ N/7` in a form that only mentions `ediv`. -/
def AheadArc (m : ℕ) (x : ℤ) : Prop :=
  ∃ ρ : ℤ, 0 ≤ ρ ∧ ρ ≤ (7 : ℤ) ^ m ∧ (7 : ℤ) ^ (m + 1) ∣ (x - ρ)

/-- `q(x) = 0` (BS's `Λ_h`-retarget target) gives `AheadArc`, with `ρ = x % 7^m`. -/
theorem aheadArc_of_qz_zero (m : ℕ) (x : ℤ) (h : qz m x = 0) : AheadArc m x := by
  have hP : (0 : ℤ) < (7 : ℤ) ^ m := by positivity
  refine ⟨x % (7 : ℤ) ^ m, Int.emod_nonneg x (ne_of_gt hP),
    le_of_lt (Int.emod_lt_of_pos x hP), ?_⟩
  have h7 : (7 : ℤ) ∣ x / (7 : ℤ) ^ m := by
    have hz : ((x / (7 : ℤ) ^ m : ℤ) : ZMod 7) = 0 := h
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
  obtain ⟨k, hk⟩ := h7
  have hd := Int.mul_ediv_add_emod x ((7 : ℤ) ^ m)
  exact ⟨k, by rw [hk] at hd; linear_combination -hd⟩

/-- `7^m ∣ x` with `q(x) = 1` (the `Λ_m` retarget target) gives `AheadArc`, `ρ = 7^m`. -/
theorem aheadArc_of_top_one (m : ℕ) (x : ℤ) (hd : (7 : ℤ) ^ m ∣ x)
    (h : qz m x = 1) : AheadArc m x := by
  obtain ⟨Q, hQ⟩ := hd
  have hdivQ : x / (7 : ℤ) ^ m = Q := by
    rw [hQ]; exact Int.mul_ediv_cancel_left Q (by positivity)
  have hq : ((Q : ℤ) : ZMod 7) = 1 := by rw [← hdivQ]; exact h
  have h7 : (7 : ℤ) ∣ (Q - 1) := by
    have hz : ((Q - 1 : ℤ) : ZMod 7) = 0 := by push_cast [hq]; ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
  obtain ⟨k, hk⟩ := h7
  exact ⟨(7 : ℤ) ^ m, by positivity, le_refl _, ⟨k, by rw [hQ]; linear_combination (7 : ℤ) ^ m * hk⟩⟩

/-- `ν(x) > m` gives `AheadArc` with `ρ = 0` (all such arcs coincide). -/
theorem aheadArc_of_high (m : ℕ) (x : ℤ) (h : (7 : ℤ) ^ (m + 1) ∣ x) :
    AheadArc m x :=
  ⟨0, le_refl _, by positivity, by simpa using h⟩

/-- **BS's "Lemma 9(i) ⟹ ℓ(A₁) ≤ 2" in the ahead form.** Two elements with DISTINCT
`7`-adic valuations admit a unit multiplier putting BOTH ahead of the origin by at
most `N/7`. Dispatches over the position of the levels relative to `m`: above `m`
nothing is needed, at `m` the target is `q = 1` (`Λ_m`, `0` unreachable), below `m`
the target is `q = 0`, and mixed pairs use `qz_retarget_two(_top)`. -/
theorem ahead_pair (m : ℕ) (hm : 0 < m) (X Y : ℤ) (h₁ h₂ : ℕ) (hne : h₁ ≠ h₂)
    (hX : (7 : ℤ) ^ h₁ ∣ X) (hX' : ¬ (7 : ℤ) ^ (h₁ + 1) ∣ X)
    (hY : (7 : ℤ) ^ h₂ ∣ Y) (hY' : ¬ (7 : ℤ) ^ (h₂ + 1) ∣ Y) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ AheadArc m (lam * X) ∧ AheadArc m (lam * Y) := by
  -- single-element retarget, used when the partner is already above level `m`
  have single : ∀ W : ℤ, ∀ h : ℕ, h ≤ m → (7 : ℤ) ^ h ∣ W → ¬ (7 : ℤ) ^ (h + 1) ∣ W →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ AheadArc m (lam * W) := by
    intro W h hhm hW hW'
    rcases eq_or_lt_of_le hhm with rfl | hlt
    · obtain ⟨j, hju, hjW⟩ := qz_retarget_top _ W hW hW' 1 (by decide)
      exact ⟨j, hju, aheadArc_of_top_one _ _ (Dvd.dvd.mul_left hW j) hjW⟩
    · obtain ⟨k, hqk, hku⟩ := qz_retarget m h hlt W hW hW' 0
      exact ⟨1 + k * 7 ^ (m - h), hku, aheadArc_of_qz_zero m _ hqk⟩
  by_cases hh1 : h₁ ≤ m
  · by_cases hh2 : h₂ ≤ m
    · rcases lt_trichotomy h₁ h₂ with hlt | heq | hgt
      · rcases eq_or_lt_of_le hh2 with rfl | h2lt
        · obtain ⟨lam, hu, hqY, hqX⟩ :=
            qz_retarget_two_top _ h₁ (by omega) Y X hY hY' hX hX' 1 0 (by decide)
          exact ⟨lam, hu, aheadArc_of_qz_zero _ _ hqX,
            aheadArc_of_top_one _ _ (Dvd.dvd.mul_left hY lam) hqY⟩
        · obtain ⟨lam, hu, hqY, hqX⟩ :=
            qz_retarget_two m h₂ h₁ h2lt hlt Y X hY hY' hX hX' 0 0
          exact ⟨lam, hu, aheadArc_of_qz_zero m _ hqX, aheadArc_of_qz_zero m _ hqY⟩
      · exact absurd heq hne
      · rcases eq_or_lt_of_le hh1 with rfl | h1lt
        · obtain ⟨lam, hu, hqX, hqY⟩ :=
            qz_retarget_two_top _ h₂ (by omega) X Y hX hX' hY hY' 1 0 (by decide)
          exact ⟨lam, hu, aheadArc_of_top_one _ _ (Dvd.dvd.mul_left hX lam) hqX,
            aheadArc_of_qz_zero _ _ hqY⟩
        · obtain ⟨lam, hu, hqX, hqY⟩ :=
            qz_retarget_two m h₁ h₂ h1lt hgt X Y hX hX' hY hY' 0 0
          exact ⟨lam, hu, aheadArc_of_qz_zero m _ hqX, aheadArc_of_qz_zero m _ hqY⟩
    · obtain ⟨lam, hu, hA⟩ := single X h₁ hh1 hX hX'
      exact ⟨lam, hu, hA, aheadArc_of_high m _
        (Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hY) lam)⟩
  · by_cases hh2 : h₂ ≤ m
    · obtain ⟨lam, hu, hA⟩ := single Y h₂ hh2 hY hY'
      exact ⟨lam, hu, aheadArc_of_high m _
        (Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hX) lam), hA⟩
    · exact ⟨1, by norm_num,
        aheadArc_of_high m _ (Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hX) 1),
        aheadArc_of_high m _ (Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hY) 1)⟩

/-- `q(x) = 0` pins `x` to its low part modulo `7^{m+1}`. -/
theorem qz_zero_mod (m : ℕ) (x : ℤ) (h : qz m x = 0) :
    (7 : ℤ) ^ (m + 1) ∣ (x - x % (7 : ℤ) ^ m) := by
  have h7 : (7 : ℤ) ∣ x / (7 : ℤ) ^ m := by
    have hz : ((x / (7 : ℤ) ^ m : ℤ) : ZMod 7) = 0 := h
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
  obtain ⟨k, hk⟩ := h7
  have hd := Int.mul_ediv_add_emod x ((7 : ℤ) ^ m)
  exact ⟨k, by rw [hk] at hd; linear_combination -hd⟩

/-- `AheadArc` only depends on the value modulo `7^{m+1}`. -/
theorem aheadArc_congr (m : ℕ) (a b : ℤ) (h : (7 : ℤ) ^ (m + 1) ∣ (a - b))
    (ha : AheadArc m a) : AheadArc m b := by
  obtain ⟨ρ, h0, h1, ⟨c, hc⟩⟩ := ha
  obtain ⟨e, he⟩ := h
  exact ⟨ρ, h0, h1, ⟨c - e, by linear_combination hc - he⟩⟩

/-- **Ratio-2 apex selection (BS §6.5, branch `(ii.1)` with `h < m`).** In a frame
where `q(X) = 0` (so `X` sits ahead of the apex `0` by `ρ < 7^m`) and `W` is ahead
by at most `7^m`, the third point `Y = 2X − W` may fall outside the window `[0,7^m]`.
Exactly one of three placements works: apex `0` (`Y` inside), apex `Y` (`Y` behind),
or apex `Y'` after the `Λ_h` cell shift `X ↦ X − 7^m` (`Y` beyond `7^m`).  Purely
Euclidean: with `ρ = X % 7^m` and `ρ_W ≤ 7^m` one has `V = 2ρ − ρ_W ∈ (−7^m, 2·7^m)`
and the three cases are `0 ≤ V ≤ 7^m`, `V < 0`, `V > 7^m`. -/
theorem ratio2_ahead_core (m : ℕ) (X W : ℤ)
    (hX : qz m X = 0) (hW : AheadArc m W) :
    (AheadArc m X ∧ AheadArc m (2 * X - W))
  ∨ (AheadArc m (-(2 * X - W)) ∧ AheadArc m (W - X))
  ∨ (AheadArc m (-(2 * (X - (7 : ℤ) ^ m) - W)) ∧ AheadArc m (W - (X - (7 : ℤ) ^ m))) := by
  have hP : (0 : ℤ) < (7 : ℤ) ^ m := by positivity
  obtain ⟨c₁, hc₁⟩ := qz_zero_mod m X hX
  obtain ⟨ρW, hW0, hWP, ⟨c₂, hc₂⟩⟩ := hW
  have hρ0 : 0 ≤ X % (7 : ℤ) ^ m := Int.emod_nonneg X (ne_of_gt hP)
  have hρP : X % (7 : ℤ) ^ m < (7 : ℤ) ^ m := Int.emod_lt_of_pos X hP
  set ρ : ℤ := X % (7 : ℤ) ^ m with hρdef
  clear_value ρ
  rcases lt_trichotomy (2 * ρ - ρW) 0 with hV | hV | hV
  · -- `V < 0`: apex is the third point `Y = 2X − W`.
    refine Or.inr (Or.inl ⟨⟨ρW - 2 * ρ, by omega, by omega, ⟨-(2 * c₁) + c₂, by
      linear_combination -2 * hc₁ + hc₂⟩⟩,
      ⟨ρW - ρ, by omega, by omega, ⟨c₂ - c₁, by linear_combination hc₂ - hc₁⟩⟩⟩)
  · -- `V = 0`: apex `0`.
    exact Or.inl ⟨⟨ρ, by omega, by omega, ⟨c₁, by linear_combination hc₁⟩⟩,
      ⟨2 * ρ - ρW, by omega, by omega, ⟨2 * c₁ - c₂, by linear_combination 2 * hc₁ - hc₂⟩⟩⟩
  · rcases le_or_gt (2 * ρ - ρW) ((7 : ℤ) ^ m) with hV2 | hV2
    · -- `0 < V ≤ 7^m`: apex `0`.
      exact Or.inl ⟨⟨ρ, by omega, by omega, ⟨c₁, by linear_combination hc₁⟩⟩,
        ⟨2 * ρ - ρW, by omega, by omega, ⟨2 * c₁ - c₂, by linear_combination 2 * hc₁ - hc₂⟩⟩⟩
    · -- `V > 7^m`: shift the `X`-cell down by one and take the shifted third point.
      refine Or.inr (Or.inr ⟨⟨2 * (7 : ℤ) ^ m - (2 * ρ - ρW), by omega, by omega,
        ⟨-(2 * c₁) + c₂, by linear_combination -2 * hc₁ + hc₂⟩⟩,
        ⟨ρW - ρ + (7 : ℤ) ^ m, by omega, by omega, ⟨c₂ - c₁, by linear_combination hc₂ - hc₁⟩⟩⟩)

/-- **BS §6.5, branch `(ii.1)` with `h < m`: the "ahead" compression.** A ratio-`2`
triple at a common level `h < m` admits a unit multiplier and an apex among its
three members putting all three points ahead of the apex by at most `7^m` — the
metric strengthening of `ℓ(A₁) ≤ 2` that BS's doubling/tripling step (L707–709)
actually consumes.  Construction: with `x = e₁−e₃`, `y = e₂−e₃` and `E = 2x−y`
(level `> h` because the leading residues cancel), a two-level retarget sets
`q(λx) = 0` and puts `λE` ahead; `ratio2_ahead_core` then picks the apex, using a
`Λ_h` cell shift of `x` in the one case where the third point overshoots. -/
theorem ahead_ratio2 (m h : ℕ) (hh : h < m) (e₁ e₂ e₃ : ℤ)
    (hd1 : (7 : ℤ) ^ h ∣ (e₁ - e₃)) (hd1' : ¬ (7 : ℤ) ^ (h + 1) ∣ (e₁ - e₃))
    (hd2 : (7 : ℤ) ^ h ∣ (e₂ - e₃))
    (hr : (((e₂ - e₃) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((e₁ - e₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ℤ,
      AheadArc m (lam * (e₁ - a)) ∧ AheadArc m (lam * (e₂ - a)) ∧
      AheadArc m (lam * (e₃ - a)) := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  set x : ℤ := e₁ - e₃ with hxdef
  set y : ℤ := e₂ - e₃ with hydef
  set E : ℤ := 2 * x - y with hEdef
  -- `r(y) = 2·r(x)` cancels the level-`h` term of `E`.
  have hE_lo : (7 : ℤ) ^ (h + 1) ∣ E := by
    have hE_dvd : (7 : ℤ) ^ h ∣ E := by
      rw [hEdef]; exact dvd_sub (Dvd.dvd.mul_left hd1 2) hd2
    have hres : (((E) / 7 ^ h : ℤ) : ZMod 7) = 0 := by
      rw [hEdef, Int.sub_ediv_of_dvd _ hd2, Int.mul_ediv_assoc 2 hd1]
      push_cast; rw [hr]; ring
    have h7 : (7 : ℤ) ∣ (E / 7 ^ h) := by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hres
    obtain ⟨c, hc⟩ := h7
    obtain ⟨w, hw⟩ := hE_dvd
    refine ⟨c, ?_⟩
    have hwc : w = 7 * c := by
      have hq : E / 7 ^ h = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by positivity)
      rw [← hq, hc]
    rw [hw, hwc, pow_succ]; ring
  -- STAGE 1: `q(λ·x) = 0` and `λ·E` ahead.
  obtain ⟨lam, hlam, hqx, hEahead⟩ :
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ qz m (lam * x) = 0 ∧ AheadArc m (lam * E) := by
    by_cases htop : (7 : ℤ) ^ (m + 1) ∣ E
    · obtain ⟨k, hqk, hku⟩ := qz_retarget m h hh x hd1 hd1' 0
      exact ⟨1 + k * 7 ^ (m - h), hku, hqk,
        aheadArc_of_high m _ (Dvd.dvd.mul_left htop _)⟩
    · obtain ⟨h', hh'lo, hh'hi, hh'd, hh'd'⟩ :
          ∃ h' : ℕ, h + 1 ≤ h' ∧ h' ≤ m ∧ (7 : ℤ) ^ h' ∣ E ∧ ¬ (7 : ℤ) ^ (h' + 1) ∣ E := by
        have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ E := ⟨m, htop⟩
        have hspec : ¬ (7 : ℤ) ^ (Nat.find hex + 1) ∣ E := Nat.find_spec hex
        have hle : Nat.find hex ≤ m := Nat.find_le htop
        have hge : h + 1 ≤ Nat.find hex := by
          by_contra hc; rw [not_le] at hc
          exact hspec (dvd_trans (pow_dvd_pow 7 (by omega)) hE_lo)
        have hprev : ¬ ¬ (7 : ℤ) ^ ((Nat.find hex - 1) + 1) ∣ E :=
          Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex)
        rw [not_not] at hprev
        exact ⟨Nat.find hex, hge, hle,
          by rwa [show (Nat.find hex - 1) + 1 = Nat.find hex from by omega] at hprev, hspec⟩
      by_cases hh'm : h' < m
      · obtain ⟨lam, hu, hqE, hqx⟩ :=
          qz_retarget_two m h' h hh'm (by omega) E x hh'd hh'd' hd1 hd1' 0 0
        exact ⟨lam, hu, hqx, aheadArc_of_qz_zero m _ hqE⟩
      · have hh'eq : h' = m := by omega
        rw [hh'eq] at hh'd hh'd'
        obtain ⟨lam, hu, hqE, hqx⟩ :=
          qz_retarget_two_top m h hh E x hh'd hh'd' hd1 hd1' 1 0 (by decide)
        exact ⟨lam, hu, hqx, aheadArc_of_top_one m _ (Dvd.dvd.mul_left hh'd lam) hqE⟩
  -- `λ·y = 2·(λ·x) − (λ·E)`.
  have hy_eq : lam * y = 2 * (lam * x) - lam * E := by rw [hEdef]; ring
  rcases ratio2_ahead_core m (lam * x) (lam * E) hqx hEahead with
      ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · -- apex `e₃`
    refine ⟨lam, hlam, e₃, ?_, ?_, ?_⟩
    · rw [show lam * (e₁ - e₃) = lam * x from by rw [hxdef]]; exact hA
    · rw [show lam * (e₂ - e₃) = lam * y from by rw [hydef], hy_eq]; exact hB
    · exact aheadArc_of_high m _ ⟨0, by ring⟩
  · -- apex `e₂`
    refine ⟨lam, hlam, e₂, ?_, ?_, ?_⟩
    · rw [show lam * (e₁ - e₂) = lam * E - lam * x from by rw [hEdef, hxdef, hydef]; ring]
      exact hB
    · exact aheadArc_of_high m _ ⟨0, by ring⟩
    · rw [show lam * (e₃ - e₂) = -(2 * (lam * x) - lam * E) from by
        rw [hEdef, hxdef, hydef]; ring]
      exact hA
  · -- apex `e₂` after the `Λ_h` cell shift on `x`
    have hlx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (lam * x) := fun hdvd =>
      hd1' ((hp7.irreducible.coprime_pow_of_not_dvd (h + 1) hlam).symm.dvd_of_dvd_mul_left hdvd)
    obtain ⟨k, hqk, hku⟩ :=
      qz_retarget m h hh (lam * x) (Dvd.dvd.mul_left hd1 lam) hlx' 6
    set μ : ℤ := 1 + k * 7 ^ (m - h) with hμdef
    have hlam' : ¬ (7 : ℤ) ∣ (μ * lam) := by
      intro hdvd; rcases hp7.dvd_mul.mp hdvd with hc | hc
      · exact hku hc
      · exact hlam hc
    -- `μ` is inert on `λ·E` (level `≥ h+1`).
    have hpowE : (7 : ℤ) ^ (m - h) * 7 ^ (h + 1) = 7 ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    have hpowx : (7 : ℤ) ^ (m - h) * 7 ^ h = 7 ^ m := by
      rw [← pow_add]; congr 1; omega
    -- `μ` is inert on `λ·E` (level `≥ h+1`).
    have hEinert : (7 : ℤ) ^ (m + 1) ∣ (μ * (lam * E) - lam * E) := by
      obtain ⟨w, hw⟩ := id hE_lo
      refine ⟨k * (lam * w), ?_⟩
      rw [hμdef, hw]
      linear_combination (k * lam * w) * hpowE
    -- the cell of `μ·λ·x` drops by exactly one `7^m`
    have hshift : (7 : ℤ) ^ (m + 1) ∣ (μ * (lam * x) - (lam * x - (7 : ℤ) ^ m)) := by
      obtain ⟨w, hw⟩ := id hd1
      have hlow : (7 : ℤ) ^ m ∣ (μ * (lam * x) - lam * x) := by
        refine ⟨k * (lam * w), ?_⟩
        rw [hμdef, hw]
        linear_combination (k * lam * w) * hpowx
      obtain ⟨c, hc⟩ := hlow
      have hqdiff : ((c : ℤ) : ZMod 7) = 6 := by
        have h1 : qz m (μ * (lam * x)) = qz m (lam * x) + (c : ZMod 7) := by
          rw [show μ * (lam * x) = lam * x + c * 7 ^ m from by linarith [hc], qz_add_mul_pow]
        rw [hqk, hqx] at h1
        simpa using h1.symm
      have h7c : (7 : ℤ) ∣ (c + 1) := by
        have hz : ((c + 1 : ℤ) : ZMod 7) = 0 := by push_cast [hqdiff]; decide
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
      obtain ⟨t, ht⟩ := h7c
      exact ⟨t, by rw [pow_succ]; linear_combination hc + (7 : ℤ) ^ m * ht⟩
    refine ⟨μ * lam, hlam', e₂, ?_, ?_, ?_⟩
    · refine aheadArc_congr m (lam * E - (lam * x - (7 : ℤ) ^ m)) _ ?_ hB
      obtain ⟨u₁, hu₁⟩ := hEinert
      obtain ⟨u₂, hu₂⟩ := hshift
      refine ⟨-u₁ + u₂, ?_⟩
      have hexp : (μ * lam) * (e₁ - e₂) = μ * (lam * E) - μ * (lam * x) := by
        rw [hEdef, hxdef, hydef]; ring
      rw [hexp]
      linear_combination -hu₁ + hu₂
    · exact aheadArc_of_high m _ ⟨0, by ring⟩
    · refine aheadArc_congr m (-(2 * (lam * x - (7 : ℤ) ^ m) - lam * E)) _ ?_ hA
      obtain ⟨u₁, hu₁⟩ := hEinert
      obtain ⟨u₂, hu₂⟩ := hshift
      refine ⟨-u₁ + 2 * u₂, ?_⟩
      have hexp : (μ * lam) * (e₃ - e₂) = μ * (lam * E) - 2 * (μ * (lam * x)) := by
        rw [hEdef, hxdef, hydef]; ring
      rw [hexp]
      linear_combination -hu₁ + 2 * hu₂

set_option maxHeartbeats 800000 in
/-- **BS §6.5, branch `(i) or (ii.1) with h < m` endgame (L706–709).** Given a unit
`lam₀` under which the three `A₁` points sit ahead of a common apex `a` by at most
`7^m`, the multiplier `c·lam₀` for a suitable `c ∈ {1,2,3}` realises one of the two
disjuncts of BS (14) and hence a `Λ₀` shift `k` avoiding `{0,6}` on all five points.

Dispatch on `D = q(lam₀·(z₄−z₅))`: `D ∈ {0,1,5,6}` needs no scaling; `D = 3`, or
`D = 2` with doubling carry `1`, or `D = 4` with doubling carry `0`, close after
doubling (`ℓ₁ ≤ 3, ℓ₄ ≤ 3`); the two survivors `D = 2, ε₂ = 0` and `D = 4, ε₂ = 1`
close after tripling (`ℓ₁ ≤ 4, ℓ₄ ≤ 2`), using the carry links of `qz_23_carry`. -/
theorem case65_doubling_close (m : ℕ) (b : Fin 3 → ℤ) (a z₄ z₅ : ℤ)
    (lam₀ : ℤ) (hlam₀ : ¬ (7 : ℤ) ∣ lam₀)
    (hahead : ∀ i : Fin 3, AheadArc m (lam₀ * (b i - a))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ k : ZMod 7,
      (∀ i : Fin 3, qz m (lam * b i) + k ∉ ({0, 6} : Finset (ZMod 7))) ∧
      qz m (lam * z₄) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      qz m (lam * z₅) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  set e : ℤ := lam₀ * (z₄ - z₅) with he_def
  -- `c·lam₀` is a unit for `c ∈ {1,2,3}`.
  have hcu : ∀ c : ℕ, 0 < c → c ≤ 3 → ¬ (7 : ℤ) ∣ ((c : ℤ) * lam₀) := by
    intro c hc0 hc3 hdvd
    rcases hp7.dvd_mul.mp hdvd with h | h
    · interval_cases c <;> omega
    · exact hlam₀ h
  -- `A₁` sits in a window of length `c+1` at `q(c·lam₀·a)`.
  have hA1 : ∀ c : ℕ, ∀ i : Fin 3, ∃ j : ℕ, j ≤ c ∧
      qz m (((c : ℤ) * lam₀) * b i) = qz m ((c : ℤ) * (lam₀ * a)) + (j : ZMod 7) := by
    intro c i
    obtain ⟨ρ, hρ0, hρP, hdvd⟩ := hahead i
    obtain ⟨j, hj, hje⟩ :=
      qz_ahead_shift m ((c : ℤ) * (lam₀ * a)) (lam₀ * (b i - a)) ρ c hρ0 hρP hdvd
    refine ⟨j, hj, ?_⟩
    rw [show ((c : ℤ) * lam₀) * b i = (c : ℤ) * (lam₀ * a) + (c : ℤ) * (lam₀ * (b i - a)) by ring]
    exact hje
  -- The `A₄` arc difference is `q(c·e)` up to one carry.
  have hA4 : ∀ c : ℕ,
      qz m (((c : ℤ) * lam₀) * z₄) - qz m (((c : ℤ) * lam₀) * z₅) = qz m ((c : ℤ) * e) ∨
      qz m (((c : ℤ) * lam₀) * z₄) - qz m (((c : ℤ) * lam₀) * z₅) = qz m ((c : ℤ) * e) + 1 := by
    intro c
    have hsplit : ((c : ℤ) * lam₀) * z₄ = ((c : ℤ) * lam₀) * z₅ + (c : ℤ) * e := by
      rw [he_def]; ring
    rcases qz_add_carry m (((c : ℤ) * lam₀) * z₅) ((c : ℤ) * e) with h | h
    · left; rw [hsplit, h]; ring
    · right; rw [hsplit, h]; ring
  -- Closer with `(ℓ₁,ℓ₄) = (3,3)`.
  have finish33 : ∀ c : ℕ, 0 < c → c ≤ 2 →
      qz m (((c : ℤ) * lam₀) * z₄) - qz m (((c : ℤ) * lam₀) * z₅)
        ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ k : ZMod 7,
        (∀ i : Fin 3, qz m (lam * b i) + k ∉ ({0, 6} : Finset (ZMod 7))) ∧
        qz m (lam * z₄) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
        qz m (lam * z₅) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
    intro c hc0 hc2 hΔ
    obtain ⟨a₄, ⟨j₅, hj₅⟩, ⟨j₄, hj₄⟩⟩ := pair_fits3 _ _ hΔ
    obtain ⟨k, hk1, hk4⟩ := case65_window_33 (qz m ((c : ℤ) * (lam₀ * a))) a₄
    refine ⟨(c : ℤ) * lam₀, hcu c hc0 (by omega), k, fun i => ?_, ?_, ?_⟩
    · obtain ⟨j, hj, hje⟩ := hA1 c i
      rw [hje]
      have := hk1 ⟨j, by omega⟩
      simpa [intervalAvoids, one_mul] using this
    · rw [hj₄]; exact hk4 j₄
    · rw [hj₅]; exact hk4 j₅
  -- Closer with `(ℓ₁,ℓ₄) = (4,2)`.
  have finish42 : ∀ c : ℕ, 0 < c → c ≤ 3 →
      qz m (((c : ℤ) * lam₀) * z₄) - qz m (((c : ℤ) * lam₀) * z₅)
        ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ k : ZMod 7,
        (∀ i : Fin 3, qz m (lam * b i) + k ∉ ({0, 6} : Finset (ZMod 7))) ∧
        qz m (lam * z₄) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
        qz m (lam * z₅) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
    intro c hc0 hc3 hΔ
    obtain ⟨a₄, ⟨j₅, hj₅⟩, ⟨j₄, hj₄⟩⟩ := pair_fits2 _ _ hΔ
    obtain ⟨k, hk1, hk4⟩ := case65_window_42 (qz m ((c : ℤ) * (lam₀ * a))) a₄
    refine ⟨(c : ℤ) * lam₀, hcu c hc0 hc3, k, fun i => ?_, ?_, ?_⟩
    · obtain ⟨j, hj, hje⟩ := hA1 c i
      rw [hje]
      have := hk1 ⟨j, by omega⟩
      simpa [intervalAvoids, one_mul] using this
    · rw [hj₄]; exact hk4 j₄
    · rw [hj₅]; exact hk4 j₅
  -- Dispatch on `D = q(e)`.
  obtain ⟨e2, e3, he2, he3, hq2, hq3, hlink0, hlink1⟩ := qz_23_carry m e
  by_cases hD : qz m e ∈ ({0, 1, 5, 6} : Finset (ZMod 7))
  · obtain ⟨hgood, hgood'⟩ := shift_0156 _ hD
    refine finish33 1 (by omega) (by omega) ?_
    have h1 : ((1 : ℕ) : ℤ) * e = e := by push_cast; ring
    rcases hA4 1 with h | h
    · rw [h, h1]; exact hgood
    · rw [h, h1]; exact hgood'
  · rcases z7_not_0156 _ hD with hD3 | hD3 | hD3
    · -- D = 2
      rcases Nat.lt_or_ge e2 1 with he | he
      · -- ε₂ = 0 : triple
        have he0 : e2 = 0 := by omega
        have he3' : e3 ≤ 1 := hlink0 he0
        refine finish42 3 (by omega) (by omega) ?_
        have h3 : ((3 : ℕ) : ℤ) * e = 3 * e := by push_cast; ring
        have hval : qz m (3 * e) = 6 + (e3 : ZMod 7) := by rw [hq3, hD3]; ring
        rcases hA4 3 with h | h <;> rw [h, h3, hval] <;> interval_cases e3 <;> decide
      · -- ε₂ = 1 : double
        have he1 : e2 = 1 := by omega
        refine finish33 2 (by omega) (by omega) ?_
        have h2 : ((2 : ℕ) : ℤ) * e = 2 * e := by push_cast; ring
        have hval : qz m (2 * e) = 5 := by rw [hq2, hD3, he1]; decide
        rcases hA4 2 with h | h <;> rw [h, h2, hval] <;> decide
    · -- D = 3 : double
      refine finish33 2 (by omega) (by omega) ?_
      have h2 : ((2 : ℕ) : ℤ) * e = 2 * e := by push_cast; ring
      have hval : qz m (2 * e) = 6 + (e2 : ZMod 7) := by rw [hq2, hD3]; ring
      rcases hA4 2 with h | h <;> rw [h, h2, hval] <;> interval_cases e2 <;> decide
    · -- D = 4
      rcases Nat.lt_or_ge e2 1 with he | he
      · -- ε₂ = 0 : double
        have he0 : e2 = 0 := by omega
        refine finish33 2 (by omega) (by omega) ?_
        have h2 : ((2 : ℕ) : ℤ) * e = 2 * e := by push_cast; ring
        have hval : qz m (2 * e) = 1 := by rw [hq2, hD3, he0]; decide
        rcases hA4 2 with h | h <;> rw [h, h2, hval] <;> decide
      · -- ε₂ = 1 : triple
        have he1 : e2 = 1 := by omega
        have he3' : 1 ≤ e3 := hlink1 he1
        refine finish42 3 (by omega) (by omega) ?_
        have h3 : ((3 : ℕ) : ℤ) * e = 3 * e := by push_cast; ring
        have hval : qz m (3 * e) = 5 + (e3 : ZMod 7) := by
          rw [hq3, hD3, show (3 : ZMod 7) * 4 = 5 from by decide]
        rcases hA4 3 with h | h <;> rw [h, h3, hval] <;> interval_cases e3 <;> decide

/-- **The `r⁻¹` frame.** For a difference at exactly level `m` with leading residue
`r`, a constant unit multiplier `u ≡ r⁻¹ (mod 7)` exists; `qz_top_affine` then reads
every level-`m` difference off as its leading residue divided by `r`. -/
theorem inv_frame (m : ℕ) (X Y : ℤ) (hd : (7 : ℤ) ^ m ∣ (X - Y))
    (hd' : ¬ (7 : ℤ) ^ (m + 1) ∣ (X - Y)) :
    ∃ u : ℤ, ¬ (7 : ℤ) ∣ u ∧
      (u : ZMod 7) * (((X - Y) / 7 ^ m : ℤ) : ZMod 7) = 1 := by
  obtain ⟨c, hc⟩ := id hd
  have hdiv : (X - Y) / (7 : ℤ) ^ m = c := by
    rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
  set r : ZMod 7 := (((X - Y) / (7 : ℤ) ^ m : ℤ) : ZMod 7) with hr_def
  have hr_ne : r ≠ 0 := by
    rw [hr_def, hdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro ⟨w, hw⟩; exact hd' ⟨w, by rw [hc, hw, pow_succ]; ring⟩
  refine ⟨((r⁻¹ : ZMod 7).val : ℤ), ?_, ?_⟩
  · intro hdvd
    have h1 : ((((r⁻¹ : ZMod 7).val : ℕ) : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdvd
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id] at h1
    exact hr_ne (inv_eq_zero.mp h1)
  · rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel₀ hr_ne]


/-- **`ℓ(A₁) ≤ 4` unconditionally.** Every three-element class with a common residue
admits a unit multiplier compressing its arcs into a length-4 window: Lemma 9(i)
gives `≤ 2` for distinct difference valuations, Lemma 9(ii) gives `≤ 2` / `≤ 3` for
the ratio-`2` / ratio-`3` cases below level `m`, the `r⁻¹` frame gives the exact
offsets `{0,1,2}` / `{0,1,3}` at level `m`, and above level `m` all three arcs
coincide. Used for the `ν(e₄₅) > m` branch of §6.5, where `ℓ(A₄) = 1` and only the
`(4,2)` disjunct of BS (14) is needed. -/
theorem a1_le4 (m : ℕ) (b : Fin 3 → ℤ) (hb_inj : Function.Injective b)
    (c : ZMod 7) (hres : ∀ k, ((b k : ℤ) : ZMod 7) = c) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b 0), qz m (lam * b 1), qz m (lam * b 2)}
        : Finset (ZMod 7)) a 4 := by
  classical
  obtain ⟨e₁, e₂, e₃, hperm, hstruct⟩ := lemma11 b hb_inj
  have hset : ∀ lam : ℤ,
      ({qz m (lam * b 0), qz m (lam * b 1), qz m (lam * b 2)} : Finset (ZMod 7))
      = {qz m (lam * e₁), qz m (lam * e₂), qz m (lam * e₃)} :=
    fun lam => (hperm (fun x => qz m (lam * x))).symm
  have haux : ∀ x : ZMod 7,
      x ∈ ({(e₁ : ZMod 7), (e₂ : ZMod 7), (e₃ : ZMod 7)} : Finset (ZMod 7)) → x = c := by
    intro x hx
    rw [hperm (fun t => ((t : ℤ) : ZMod 7))] at hx
    simp only [hres 0, hres 1, hres 2, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h <;> exact h
  have he₁ : ((e₁ : ℤ) : ZMod 7) = c := haux _ (by simp)
  have he₂ : ((e₂ : ℤ) : ZMod 7) = c := haux _ (by simp)
  have he₃ : ((e₃ : ℤ) : ZMod 7) = c := haux _ (by simp)
  rcases hstruct with ⟨h₁, h₂, hlt, hd1, hd1', hd2, hd2'⟩ | ⟨h, hd1, hd1', hd2, hd2', hr⟩
  · obtain ⟨lam, hlam, a, hfit⟩ :=
      lemma9_i_dispatch m h₁ h₂ e₁ e₂ e₃ (ne_of_lt hlt).symm hd1 hd1' hd2 hd2'
    exact ⟨lam, hlam, a, by rw [hset lam]; exact fitsInterval_mono (by omega) hfit⟩
  · rcases lt_trichotomy h m with hlt | heq | hgt
    · rcases hr with hr2 | hr3
      · obtain ⟨lam, hlam, a, hfit⟩ :=
          lemma9_ii_j2 m h hlt e₁ e₂ e₃ (he₁.trans he₃.symm) (he₂.trans he₃.symm)
            hd1 hd1' hd2 hd2' hr2
        exact ⟨lam, hlam, a, by rw [hset lam]; exact fitsInterval_mono (by omega) hfit⟩
      · obtain ⟨lam, hlam, ⟨a, hfit⟩, -, -⟩ :=
          lemma9_ii_j3 m h hlt e₁ e₂ e₃ (he₁.trans he₃.symm) (he₂.trans he₃.symm)
            hd1 hd1' hd2 hd2' hr3
        exact ⟨lam, hlam, a, by rw [hset lam]; exact fitsInterval_mono (by omega) hfit⟩
    · -- `h = m`: the `r⁻¹` frame gives exact offsets `{0, 1, j}` with `j ∈ {2,3}`.
      rw [heq] at hd1 hd1' hd2 hr
      obtain ⟨u, hu, hu1⟩ := inv_frame m e₁ e₃ hd1 hd1'
      have ha1 : qz m (u * e₁) = qz m (u * e₃) + 1 := by
        rw [qz_top_affine m u e₁ e₃ hd1, hu1]
      refine ⟨u, hu, qz m (u * e₃), ?_⟩
      rw [hset u]
      have hmain : ∀ (j : ℕ), j < 4 → qz m (u * e₂) = qz m (u * e₃) + (j : ZMod 7) →
          fitsInterval ({qz m (u * e₁), qz m (u * e₂), qz m (u * e₃)} : Finset (ZMod 7))
            (qz m (u * e₃)) 4 := by
        intro j hj ha2 v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact ⟨⟨1, by omega⟩, by rw [ha1]; simp⟩
        · exact ⟨⟨j, hj⟩, by rw [ha2]⟩
        · exact ⟨⟨0, by omega⟩, by simp⟩
      rcases hr with hr2 | hr3
      · refine hmain 2 (by omega) ?_
        rw [qz_top_affine m u e₂ e₃ hd2, hr2,
          show (u : ZMod 7) * (2 * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))
            = 2 * ((u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7)) from by ring, hu1]
        norm_num
      · refine hmain 3 (by omega) ?_
        rw [qz_top_affine m u e₂ e₃ hd2, hr3,
          show (u : ZMod 7) * (3 * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))
            = 3 * ((u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7)) from by ring, hu1]
        norm_num
    · -- `h > m`: all three arcs coincide.
      refine ⟨1, by norm_num, qz m (1 * e₃), ?_⟩
      rw [hset 1]
      have hq1 : qz m (1 * e₁) = qz m (1 * e₃) :=
        qz_eq_of_high_dvd m e₁ e₃ 1 (dvd_trans (pow_dvd_pow 7 (by omega)) hd1)
      have hq2 : qz m (1 * e₂) = qz m (1 * e₃) :=
        qz_eq_of_high_dvd m e₂ e₃ 1 (dvd_trans (pow_dvd_pow 7 (by omega)) hd2)
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [Nat.cast_zero, add_zero]
      rcases hv with rfl | rfl | rfl
      · exact hq1
      · exact hq2
      · rfl

set_option maxRecDepth 20000 in
/-- **Lemma 9(ii), `j = 3`, with BS's sharp bound on the BIG difference (BS L491).**
`lemma9_ii_j3` exposes `q(λ·e) ∈ {0,1,5,6}` for all three pairwise differences; BS's
own statement is sharper on the `3r` difference: `q(λ·(b₂−b₃)) ∈ {0,5,6}`. That
sharpening is what §6.5's branch `(ii.2)` with `ν(e₄₅) = h` consumes — with
`q(λ·f) = 0` (resp. `= 1` at level `m`) the `A₄` difference is `q(λ·(b₂−b₃))` plus at
most one carry, and only `{0,5,6}` (not `{0,1,5,6}`) keeps it inside the `ℓ(A₄) ≤ 3`
band `{0,1,5,6}`. Same proof as `lemma9_ii_j3` with the target table tightened; the
table is still total (`decide`). -/
theorem j3_big056 (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 3) ∧
      qz m (lam * b₂ - lam * b₃) ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
      (∀ e : ℤ, (7 : ℤ) ^ (h + 1) ∣ e → qz m (lam * e) = qz m e) := by
  set x : ℤ := b₁ - b₃ with hx_def
  set y : ℤ := b₂ - b₃ with hy_def
  set rx : ZMod 7 := ((x / 7 ^ h : ℤ) : ZMod 7) with hrx_def
  have hry : ((y / 7 ^ h : ℤ) : ZMod 7) = 3 * rx := hr
  have hxy_dvd : (7 : ℤ) ^ h ∣ (x - y) := dvd_sub hx hy
  have hrxy : (((x - y) / 7 ^ h : ℤ) : ZMod 7) = rx - 3 * rx := by
    rw [Int.sub_ediv_of_dvd _ hy]; push_cast; rw [← hrx_def, hry]
  obtain ⟨c, hc, hcarry⟩ := qz_subxy_carry m x y
  obtain ⟨t, htA, htB, htC⟩ :
      ∃ t : ZMod 7, t ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        (qz m y + 3 * (t - qz m x)) ∈ ({0, 5, 6} : Finset (ZMod 7)) ∧
        ((qz m x - qz m y + c) - 2 * (t - qz m x)) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    clear hcarry hrxy hxy_dvd hry hr hrx_def
    generalize qz m x = p
    generalize qz m y = s
    rcases hc with rfl | rfl <;> revert p s <;> decide
  obtain ⟨k, hqx, hk⟩ := qz_retarget m h hh x hx hx' t
  set lam : ℤ := 1 + k * 7 ^ (m - h) with hlam_def
  have hkrx : (k : ZMod 7) * rx = t - qz m x := by
    have hl := qz_lambda m h (le_of_lt hh) k x hx
    rw [← hrx_def] at hl; rw [hqx] at hl; linear_combination -hl
  have h12 : qz m (lam * b₁ - lam * b₂) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₁ - lam * b₂ = lam * (x - y) from by rw [hx_def, hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k (x - y) hxy_dvd, hrxy]
    have hh2 : qz m (x - y) + (k : ZMod 7) * (rx - 3 * rx)
        = (qz m x - qz m y + c) - 2 * (t - qz m x) := by
      rw [hcarry]; linear_combination (-2 : ZMod 7) * hkrx
    rw [hh2]; exact htC
  have h13 : qz m (lam * b₁ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₁ - lam * b₃ = lam * x from by rw [hx_def]; ring, hqx]; exact htA
  have h23 : qz m (lam * b₂ - lam * b₃) ∈ ({0, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₂ - lam * b₃ = lam * y from by rw [hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k y hy, hry]
    have hh3 : qz m y + (k : ZMod 7) * (3 * rx) = qz m y + 3 * (t - qz m x) := by
      linear_combination (3 : ZMod 7) * hkrx
    rw [hh3]; exact htB
  have h23' : qz m (lam * b₂ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    revert h23; generalize qz m (lam * b₂ - lam * b₃) = v; revert v; decide
  exact ⟨lam, hk, remark8_ii_int m (lam * b₁) (lam * b₂) (lam * b₃) h12 h13 h23',
    h23, fun e he => qz_higher_inert m h (le_of_lt hh) k e he⟩

/-! ### §6.5 branch `(ii.1)` with `h = ν(e₄₅) = m`: the `Λ₀` obstruction tables

With `q(A₁) = {A, A+c, A+2c}` and `q(A₄) = {P₅, P₅+cτ}` (both exact — every
difference sits at level `m`), a `Λ₀` shift `k` avoiding `{0,6}` on all five points
exists precisely when `ẽ = 2P₅ − A` (a `Λ₀` invariant) misses a small set depending
on the frame scale `c`.  For `c = 1` that set is `{−τ, 1−τ}`; for the DOUBLED frame
`c = 2` it is `{4, 6, τ−2}`, which — unlike the `c = 1` set — has empty overlap with
its own translate, so Lemma 7(ii) is unobstructed there. -/

theorem z7_not34 (x : ZMod 7) (h : ¬ (x = 3 ∨ x = 4)) :
    x ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  revert h; revert x; decide

set_option maxRecDepth 40000 in
theorem c65_top_lo (A P5 t : ZMod 7) (ht : t = 3 ∨ t = 4)
    (he : 2 * P5 - A ∉ ({-t, 1 - t} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      A + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 1 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 2 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      P5 + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      P5 + t + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert ht he; revert A P5 t; decide

set_option maxRecDepth 40000 in
theorem c65_top_hi (A P5 t : ZMod 7) (ht : t = 3 ∨ t = 4)
    (he : 2 * P5 - A ∉ ({4, 6, t - 2} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      A + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 2 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      A + 4 + k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      P5 + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) ∧
      P5 + 2 * t + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) := by
  revert ht he; revert A P5 t; decide

theorem c65_gap_empty (t : ZMod 7) (ht : t = 3 ∨ t = 4) :
    (({4, 6, t - 2} : Finset (ZMod 7)) ∩ (({4, 6, t - 2} : Finset (ZMod 7)).image (· + 1)))
      = ∅ := by
  rcases ht with h | h <;> rw [h] <;> decide

set_option maxHeartbeats 1000000 in
/-- **Case 6.5 `(3,0,2)`** (BS L698). `|A₁|=3, |A₄|=2`. Labeling via Lemma 11;
`lemma6_402` endpoint (symmetric to 6.4). -/
theorem case_65 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 2) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  obtain ⟨g₁, hg₁_res, hg₁_inj, hA₁_cover⟩ := mkA1three m d hC₁
  set b₁ : Fin 3 → ℤ := fun k => d (g₁ k) with hb₁_def
  have hb₁_inj : Function.Injective b₁ := fun a b h => hg₁_inj (hinj h)
  set S₄ := univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4) with hS₄_def
  obtain ⟨i₄, i₅, hi45_ne, hS₄pair⟩ := Finset.card_eq_two.mp hC₄
  have hi₄_res : (d i₄ : ZMod 7) = 4 := by
    have hmem : i₄ ∈ S₄ := by rw [hS₄pair]; exact mem_insert_self _ _
    simp only [hS₄_def, mem_filter, mem_univ, true_and] at hmem; exact hmem
  have hi₅_res : (d i₅ : ZMod 7) = 4 := by
    have hmem : i₅ ∈ S₄ := by rw [hS₄pair]; exact mem_insert_of_mem (mem_singleton_self _)
    simp only [hS₄_def, mem_filter, mem_univ, true_and] at hmem; exact hmem
  have hi_tri : ∀ i : Fin 5, (∃ k₀ : Fin 3, g₁ k₀ = i) ∨ i = i₄ ∨ i = i₅ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h1 | h2 | h4
    · exact Or.inl (hA₁_cover i h1)
    · exfalso
      have hmem : i ∈ univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2) := by simp [h2]
      rw [Finset.card_eq_zero.mp hC₂] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    · have hi_mem : i ∈ S₄ := by
        simp only [hS₄_def, mem_filter, mem_univ, true_and]; exact h4
      rw [hS₄pair, Finset.mem_insert, Finset.mem_singleton] at hi_mem
      exact Or.inr hi_mem
  set E45 : ℤ := d i₄ - d i₅ with hE45_def
  -- ── generic closer: a `Λ₀` shift `k` good on all five points ──
  have close_gen : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ → ∀ (k : ZMod 7),
      (∀ k₀ : Fin 3, qz m (lam₀ * b₁ k₀) + k ∉ ({0, 6} : Finset (ZMod 7))) →
      qz m (lam₀ * d i₄) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (lam₀ * d i₅) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ k h1 h4 h5
    refine lift_shift m (by omega) d lam₀ hlam₀ k (fun i => ?_)
    rcases hi_tri i with ⟨k₀, hk₀⟩ | hi | hi
    · subst hk₀; rw [hg₁_res k₀, mul_one]; exact h1 k₀
    · subst hi; rw [hi₄_res, mul_comm k 4]; exact h4
    · subst hi; rw [hi₅_res, mul_comm k 4]; exact h5
  -- ── the `A₄` arc difference, with the one-carry slop of `q(e₄₅)` ──
  have hA4diff : ∀ lam₀ : ℤ,
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) = qz m (lam₀ * E45) ∨
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) = qz m (lam₀ * E45) + 1 := by
    intro lam₀
    have hsplit : lam₀ * d i₄ = lam₀ * d i₅ + lam₀ * E45 := by rw [hE45_def]; ring
    rcases qz_add_carry m (lam₀ * d i₅) (lam₀ * E45) with h | h
    · left; rw [hsplit, h]; ring
    · right; rw [hsplit, h]; ring
  -- at level exactly `m` the `A₄` shift is a whole number of cells: no carry
  have hA4exact : ∀ lam₀ : ℤ, (7 : ℤ) ^ m ∣ E45 →
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) = qz m (lam₀ * E45) := by
    intro lam₀ hdvd
    obtain ⟨c, hc⟩ := hdvd
    have h1 : qz m (lam₀ * d i₄) = qz m (lam₀ * d i₅) + ((lam₀ * c : ℤ) : ZMod 7) := by
      rw [show lam₀ * d i₄ = lam₀ * d i₅ + (lam₀ * c) * 7 ^ m from by
        rw [hE45_def] at hc; linear_combination lam₀ * hc, qz_add_mul_pow]
    have h2 : qz m (lam₀ * E45) = ((lam₀ * c : ℤ) : ZMod 7) := by
      rw [show lam₀ * E45 = 0 + (lam₀ * c) * 7 ^ m from by rw [hc]; ring, qz_add_mul_pow,
        show qz m (0 : ℤ) = 0 from by simp [qz], zero_add]
    rw [h1, h2]; ring
  -- ── the two BS (14) endgames ──
  have close_33 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ →
      (∃ a : ZMod 7, fitsInterval ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)}
        : Finset (ZMod 7)) a 3) →
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ hfitA1 hD
    obtain ⟨a₁, hfit⟩ := hfitA1
    obtain ⟨a₄, ⟨j₅, hj₅⟩, ⟨j₄, hj₄⟩⟩ :=
      pair_fits3 (qz m (lam₀ * d i₅)) (qz m (lam₀ * d i₄)) hD
    obtain ⟨k, hk1, hk4⟩ := case65_window_33 a₁ a₄
    refine close_gen lam₀ hlam₀ k (fun k₀ => ?_) ?_ ?_
    · obtain ⟨j, hj⟩ := hfit (qz m (lam₀ * b₁ k₀)) (by fin_cases k₀ <;> simp)
      rw [hj]
      have := hk1 j
      simpa [intervalAvoids, one_mul] using this
    · rw [hj₄]; exact hk4 j₄
    · rw [hj₅]; exact hk4 j₅
  have close_42 : ∀ (lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ →
      (∃ a : ZMod 7, fitsInterval ({qz m (lam₀ * b₁ 0), qz m (lam₀ * b₁ 1), qz m (lam₀ * b₁ 2)}
        : Finset (ZMod 7)) a 4) →
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro lam₀ hlam₀ hfitA1 hD
    obtain ⟨a₁, hfit⟩ := hfitA1
    obtain ⟨a₄, ⟨j₅, hj₅⟩, ⟨j₄, hj₄⟩⟩ :=
      pair_fits2 (qz m (lam₀ * d i₅)) (qz m (lam₀ * d i₄)) hD
    obtain ⟨k, hk1, hk4⟩ := case65_window_42 a₁ a₄
    refine close_gen lam₀ hlam₀ k (fun k₀ => ?_) ?_ ?_
    · obtain ⟨j, hj⟩ := hfit (qz m (lam₀ * b₁ k₀)) (by fin_cases k₀ <;> simp)
      rw [hj]
      have := hk1 j
      simpa [intervalAvoids, one_mul] using this
    · rw [hj₄]; exact hk4 j₄
    · rw [hj₅]; exact hk4 j₅
  -- `q(λ·e₄₅) ∈ {0,1,5,6}` ⇒ the `A₄` arc pair fits a length-3 window
  have band33 : ∀ lam₀ : ℤ, qz m (lam₀ * E45) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) →
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
    intro lam₀ hD
    obtain ⟨hg, hg'⟩ := shift_0156 _ hD
    rcases hA4diff lam₀ with h | h
    · rw [h]; exact hg
    · rw [h]; exact hg'
  -- the same, for either orientation of the `A₄` pair (`ℓ(A₄) ≤ 3` is sign-symmetric)
  have hAdgen : ∀ (lam₀ z z' : ℤ),
      qz m (lam₀ * z) - qz m (lam₀ * z') = qz m (lam₀ * (z - z')) ∨
      qz m (lam₀ * z) - qz m (lam₀ * z') = qz m (lam₀ * (z - z')) + 1 := by
    intro lam₀ z z'
    have hsplit : lam₀ * z = lam₀ * z' + lam₀ * (z - z') := by ring
    rcases qz_add_carry m (lam₀ * z') (lam₀ * (z - z')) with hcc | hcc
    · left; rw [hsplit, hcc]; ring
    · right; rw [hsplit, hcc]; ring
  have bandF : ∀ (lam₀ F : ℤ), (F = E45 ∨ F = -E45) →
      qz m (lam₀ * F) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) →
      qz m (lam₀ * d i₄) - qz m (lam₀ * d i₅) ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
    intro lam₀ F hFor hq
    obtain ⟨hg, hg'⟩ := shift_0156 _ hq
    rcases hFor with rfl | rfl
    · rcases hAdgen lam₀ (d i₄) (d i₅) with hcc | hcc
      · rw [hcc]; exact hg
      · rw [hcc]; exact hg'
    · have hnegset : ∀ v : ZMod 7, v ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) →
          -v ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by decide
      have key : qz m (lam₀ * d i₅) - qz m (lam₀ * d i₄)
          ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
        rcases hAdgen lam₀ (d i₅) (d i₄) with hcc | hcc
        · rw [hcc, show d i₅ - d i₄ = -E45 from by rw [hE45_def]; ring]; exact hg
        · rw [hcc, show d i₅ - d i₄ = -E45 from by rw [hE45_def]; ring]; exact hg'
      have hfin := hnegset _ key
      rwa [neg_sub] at hfin
  -- ── the BS doubling/tripling endgame, wrapped for the `A₁` labeling ──
  have close_ahead : ∀ (x₁ x₂ x₃ : ℤ),
      (∀ f : ℤ → ZMod 7,
        ({f x₁, f x₂, f x₃} : Finset (ZMod 7)) = {f (b₁ 0), f (b₁ 1), f (b₁ 2)}) →
      ∀ (a lam₀ : ℤ), ¬ (7 : ℤ) ∣ lam₀ →
      AheadArc m (lam₀ * (x₁ - a)) → AheadArc m (lam₀ * (x₂ - a)) →
      AheadArc m (lam₀ * (x₃ - a)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro x₁ x₂ x₃ hperm' a lam₀ hlam₀ h1 h2 h3
    obtain ⟨lam, hlam, k, hk1, hk4, hk5⟩ :=
      case65_doubling_close m ![x₁, x₂, x₃] a (d i₄) (d i₅) lam₀ hlam₀
        (by intro i; fin_cases i <;> simpa using ‹_›)
    refine close_gen lam hlam k (fun k₀ => ?_) hk4 hk5
    have hmem : qz m (lam * b₁ k₀) ∈
        ({qz m (lam * x₁), qz m (lam * x₂), qz m (lam * x₃)} : Finset (ZMod 7)) := by
      rw [hperm' (fun t => qz m (lam * t))]; fin_cases k₀ <;> simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h]; simpa using hk1 0
    · rw [h]; simpa using hk1 1
    · rw [h]; simpa using hk1 2
  -- ── dispatch on the level of `e₄₅` ──
  by_cases hEhigh : (7 : ℤ) ^ (m + 1) ∣ E45
  · -- `ν(e₄₅) > m`: the two `A₄` arcs coincide; only `ℓ(A₁) ≤ 4` is needed.
    obtain ⟨lam₀, hlam₀, a, hfit⟩ := a1_le4 m b₁ hb₁_inj 1 hg₁_res
    refine close_42 lam₀ hlam₀ ⟨a, hfit⟩ ?_
    have h0 : qz m (lam₀ * E45) = 0 := by
      have h := qz_eq_of_high_dvd m E45 0 lam₀ (by simpa using hEhigh)
      rw [mul_zero] at h
      rw [h]; simp [qz]
    rcases hA4diff lam₀ with h | h <;> rw [h, h0] <;> decide
  · -- `ν(e₄₅) = μ ≤ m`
    obtain ⟨μ, hμm, hμd, hμd'⟩ :
        ∃ μ : ℕ, μ ≤ m ∧ (7 : ℤ) ^ μ ∣ E45 ∧ ¬ (7 : ℤ) ^ (μ + 1) ∣ E45 := by
      have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ E45 := ⟨m, hEhigh⟩
      refine ⟨Nat.find hex, Nat.find_le hEhigh, ?_, Nat.find_spec hex⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; simp
      · have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [not_not] at hprev
        rwa [show Nat.find hex - 1 + 1 = Nat.find hex from by omega] at hprev
    obtain ⟨cE, hcE⟩ := id hμd
    set s : ZMod 7 := ((E45 / 7 ^ μ : ℤ) : ZMod 7) with hs_def
    have hs_ne : s ≠ 0 := by
      have hdiv : E45 / (7 : ℤ) ^ μ = cE := by
        rw [hcE]; exact Int.mul_ediv_cancel_left cE (by positivity)
      rw [hs_def, hdiv]
      exact unit_res hcE hμd'
    obtain ⟨e₁, e₂, e₃, hperm, hstruct⟩ := lemma11_s s hs_ne b₁ hb₁_inj
    have hset : ∀ lam : ℤ,
        ({qz m (lam * b₁ 0), qz m (lam * b₁ 1), qz m (lam * b₁ 2)} : Finset (ZMod 7))
        = {qz m (lam * e₁), qz m (lam * e₂), qz m (lam * e₃)} :=
      fun lam => (hperm (fun x => qz m (lam * x))).symm
    have haux : ∀ x : ZMod 7,
        x ∈ ({(e₁ : ZMod 7), (e₂ : ZMod 7), (e₃ : ZMod 7)} : Finset (ZMod 7)) → x = 1 := by
      intro x hx
      rw [hperm (fun t => ((t : ℤ) : ZMod 7))] at hx
      have hb1res : ∀ k : Fin 3, ((b₁ k : ℤ) : ZMod 7) = 1 := hg₁_res
      simp only [hb1res 0, hb1res 1, hb1res 2, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h <;> exact h
    have he₁ : ((e₁ : ℤ) : ZMod 7) = 1 := haux _ (by simp)
    have he₂ : ((e₂ : ℤ) : ZMod 7) = 1 := haux _ (by simp)
    have he₃ : ((e₃ : ℤ) : ZMod 7) = 1 := haux _ (by simp)
    -- `A₁` arcs coincide whenever both differences sit above level `m`
    have flat : ∀ lam : ℤ, (7 : ℤ) ^ (m + 1) ∣ (e₁ - e₃) → (7 : ℤ) ^ (m + 1) ∣ (e₂ - e₃) →
        ∃ a : ZMod 7, fitsInterval ({qz m (lam * b₁ 0), qz m (lam * b₁ 1), qz m (lam * b₁ 2)}
          : Finset (ZMod 7)) a 1 := by
      intro lam hdv1 hdv2
      refine ⟨qz m (lam * e₃), ?_⟩
      rw [hset lam]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [Nat.cast_zero, add_zero]
      rcases hv with rfl | rfl | rfl
      · exact qz_eq_of_high_dvd m e₁ e₃ lam hdv1
      · exact qz_eq_of_high_dvd m e₂ e₃ lam hdv2
      · rfl
    -- five-point closer stated on the Lemma-11 labels
    have closeK : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w → ∀ (k : ZMod 7),
        qz m (w * e₁) + k ∉ ({0, 6} : Finset (ZMod 7)) →
        qz m (w * e₂) + k ∉ ({0, 6} : Finset (ZMod 7)) →
        qz m (w * e₃) + k ∉ ({0, 6} : Finset (ZMod 7)) →
        qz m (w * d i₄) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) →
        qz m (w * d i₅) + 4 * k ∉ ({0, 6} : Finset (ZMod 7)) →
        ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
          qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
      intro w hw k h1 h2 h3 h4 h5
      refine close_gen w hw k (fun k₀ => ?_) h4 h5
      have hmem : qz m (w * b₁ k₀) ∈
          ({qz m (w * e₁), qz m (w * e₂), qz m (w * e₃)} : Finset (ZMod 7)) := by
        rw [← hset w]; fin_cases k₀ <;> simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hq | hq | hq
      · rw [hq]; exact h1
      · rw [hq]; exact h2
      · rw [hq]; exact h3
    -- `ν(A₁-differences) > m`: the arcs coincide, so only `e₄₅` needs a retarget.
    have close_hgt : (7 : ℤ) ^ (m + 1) ∣ (e₁ - e₃) → (7 : ℤ) ^ (m + 1) ∣ (e₂ - e₃) →
        ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
          qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
      intro hdv1 hdv2
      by_cases hμlt : μ < m
      · obtain ⟨k, hqk, hku⟩ := qz_retarget m μ hμlt E45 hμd hμd' 0
        obtain ⟨a, hfa⟩ := flat (1 + k * 7 ^ (m - μ)) hdv1 hdv2
        exact close_33 _ hku ⟨a, fitsInterval_mono (by omega) hfa⟩
          (band33 _ (by rw [hqk]; decide))
      · have hμeq : μ = m := by omega
        rw [hμeq] at hμd hμd'
        obtain ⟨j, hju, hqj⟩ := qz_retarget_top m E45 hμd hμd' 1 (by decide)
        obtain ⟨a, hfa⟩ := flat j hdv1 hdv2
        exact close_42 j hju ⟨a, fitsInterval_mono (by omega) hfa⟩
          (by rw [hA4exact j hμd, hqj]; decide)
    -- `Λ_μ` / `Λ_m` retarget of `e₄₅` composed with a residue-preserving frame
    rcases hstruct with ⟨h₁, h₂, hlt, hd1, hd1', hd2, hd2'⟩ | ⟨h, hd1, hd1', hd2, hd2', hr⟩
    · -- ── (i) distinct valuations: BS's doubling engine ──
      obtain ⟨lam₀, hlam₀, hX, hY⟩ :=
        ahead_pair m (by omega) (e₁ - e₃) (e₂ - e₃) h₁ h₂ (ne_of_lt hlt).symm hd1 hd1' hd2 hd2'
      exact close_ahead e₁ e₂ e₃ hperm e₃ lam₀ hlam₀ hX hY
        (aheadArc_of_high m _ ⟨0, by ring⟩)
    · rcases hr with hr2 | ⟨hr3, hsalign⟩
      · -- ── (ii.1) ratio 2 ──
        rcases lt_trichotomy h m with hlt | heq | hgt
        · -- `h < m`: the ahead compression, then BS's doubling/tripling
          obtain ⟨lam₀, hlam₀, a, hA1, hA2, hA3⟩ :=
            ahead_ratio2 m h hlt e₁ e₂ e₃ hd1 hd1' hd2 hr2
          exact close_ahead e₁ e₂ e₃ hperm a lam₀ hlam₀ hA1 hA2 hA3
        · -- `h = m`: the `r⁻¹` frame puts `A₁` at `{A, A+1, A+2}`
          rw [heq] at hd1 hd1' hd2 hr2
          obtain ⟨u, hu, hu1⟩ := inv_frame m e₁ e₃ hd1 hd1'
          by_cases hμlt : μ < m
          · -- retarget `e₄₅` to `q = 0` with a `Λ_μ` factor (inert on the level-`m` arcs)
            obtain ⟨k, hqk, hku⟩ := qz_retarget m μ hμlt (u * E45)
              (Dvd.dvd.mul_left hμd u)
              (fun hdvd => hμd'
                ((hp7.irreducible.coprime_pow_of_not_dvd (μ + 1) hu).symm.dvd_of_dvd_mul_left hdvd))
              0
            set w : ℤ := (1 + k * 7 ^ (m - μ)) * u with hw_def
            have hwu : ¬ (7 : ℤ) ∣ w := by
              intro hdvd; rcases hp7.dvd_mul.mp hdvd with hc | hc
              · exact hku hc
              · exact hu hc
            have hwres : (w : ZMod 7) = (u : ZMod 7) := by
              rw [hw_def]; push_cast
              rw [seven_eq_zero_z7, zero_pow (show m - μ ≠ 0 from by omega), mul_zero, add_zero,
                one_mul]
            have hqE : qz m (w * E45) = 0 := by
              rw [hw_def, show (1 + k * 7 ^ (m - μ)) * u * E45 = (1 + k * 7 ^ (m - μ)) * (u * E45)
                from by ring]
              exact hqk
            refine close_33 w hwu ⟨qz m (w * e₃), ?_⟩ (band33 w (by rw [hqE]; decide))
            rw [hset w]
            have ha1 : qz m (w * e₁) = qz m (w * e₃) + 1 := by
              rw [qz_top_affine m w e₁ e₃ hd1, hwres, hu1]
            have ha2 : qz m (w * e₂) = qz m (w * e₃) + 2 := by
              rw [qz_top_affine m w e₂ e₃ hd2, hr2, hwres,
                show (u : ZMod 7) * (2 * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))
                  = 2 * ((u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7)) from by ring, hu1]
              norm_num
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact ⟨⟨1, by omega⟩, by rw [ha1]; simp⟩
            · exact ⟨⟨2, by omega⟩, by rw [ha2]; simp⟩
            · exact ⟨⟨0, by omega⟩, by simp⟩
          · -- `μ = m` (BS L727–731).  `q(A₁) = {A, A+1, A+2}` and the `A₄` gap is
            -- `τ = q(u·e₄₅)` (exact: `ν(e₄₅) = m`).  `τ ∉ {3,4}` gives `ℓ(A₄) ≤ 3` at
            -- once.  For `τ ∈ {3,4}` BS controls `ẽ(d₅,d₃) = 2q(λd₅) − q(λd₃)` by
            -- Lemma 7.  The exhaustive `Λ₀` tables record the exact obstruction: in the
            -- `u`-frame it is `ẽ ∈ {−τ, 1−τ}` (`c65_top_lo`), avoidable by Lemma 7(i)
            -- when `ν(2d₅−d₃) < m`; in the DOUBLED frame `2u` — where `q(A₁)` is
            -- `{A, A+2, A+4}` and the `A₄` gap is `2τ` — it is `{4, 6, τ−2}`
            -- (`c65_top_hi`), whose self-overlap `X ∩ (X+1)` is EMPTY
            -- (`c65_gap_empty`), so Lemma 7(ii) applies with no gap and discharges the
            -- `ν(2d₅−d₃) = m` edge that the `u`-frame cannot reach.  (BS's own text
            -- here — L732, "unless `e₄₅ = 5N/2`" — is corrupted in the source: `N` is
            -- odd, so `N/2` is not a lattice point, and the follow-up claim
            -- `ℓ(2·A₄) = 1` needs `2e₄₅ ≡ 0 (mod N)`, impossible for odd `N`.  The
            -- doubled-frame argument below replaces that paragraph.)
            have hμeq : μ = m := by omega
            rw [hμeq] at hμd hμd' hs_def
            set τ : ZMod 7 := ((u : ℤ) : ZMod 7) * s with hτ_def
            have arcs : ∀ (w : ℤ) (cc : ZMod 7), ((w : ℤ) : ZMod 7) = cc * ((u : ℤ) : ZMod 7) →
                qz m (w * e₁) = qz m (w * e₃) + cc ∧
                qz m (w * e₂) = qz m (w * e₃) + 2 * cc ∧
                qz m (w * d i₄) = qz m (w * d i₅) + cc * τ := by
              intro w cc hw
              refine ⟨?_, ?_, ?_⟩
              · rw [qz_top_affine m w e₁ e₃ hd1, hw, mul_assoc, hu1, mul_one]
              · rw [qz_top_affine m w e₂ e₃ hd2, hr2, hw]
                congr 1
                rw [show cc * ((u : ℤ) : ZMod 7) * (2 * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))
                    = 2 * cc * (((u : ℤ) : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))
                  from by ring, hu1, mul_one]
              · have hq : qz m (w * E45) = cc * τ := by
                  rw [qz_top_affine m w E45 0 (by simpa using hμd), mul_zero,
                    show qz m (0 : ℤ) = 0 from by simp [qz], zero_add, sub_zero, ← hs_def, hw,
                    hτ_def]
                  ring
                have hex := hA4exact w hμd
                rw [hq] at hex
                linear_combination hex
            by_cases hτ34 : τ = 3 ∨ τ = 4
            · -- BS's Lemma 7 route, in the `u`- or the doubled `2u`-frame
              have hz₅nd : ¬ (7 : ℤ) ∣ (u * d i₅) := by
                intro hdvd
                have h1 : ((u : ℤ) : ZMod 7) * ((d i₅ : ℤ) : ZMod 7) = 0 := by
                  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (u * d i₅) 7).mpr hdvd
                  push_cast at hz; exact hz
                rcases mul_eq_zero.mp h1 with hh | hh
                · exact hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u 7).mp hh)
                · rw [hi₅_res] at hh; exact four_ne_zero_z7 hh
              have he₃nd : ¬ (7 : ℤ) ∣ (u * e₃) := by
                intro hdvd
                have h1 : ((u : ℤ) : ZMod 7) * ((e₃ : ℤ) : ZMod 7) = 0 := by
                  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (u * e₃) 7).mpr hdvd
                  push_cast at hz; exact hz
                rcases mul_eq_zero.mp h1 with hh | hh
                · exact hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u 7).mp hh)
                · rw [he₃] at hh; exact one_ne_zero hh
              by_cases hgm : (7 : ℤ) ^ m ∣ (2 * (u * d i₅) - u * e₃)
              · -- `ν(2d₅−d₃) = m` (or higher): the doubled frame, where the gap is empty
                have hz₅nd2 : ¬ (7 : ℤ) ∣ (2 * u * d i₅) := by
                  intro hdvd
                  refine hz₅nd ?_
                  rcases hp7.dvd_mul.mp (show (7 : ℤ) ∣ 2 * (u * d i₅) from by
                    rwa [show 2 * (u * d i₅) = 2 * u * d i₅ from by ring]) with hh | hh
                  · exact absurd hh (by decide)
                  · exact hh
                have he₃nd2 : ¬ (7 : ℤ) ∣ (2 * u * e₃) := by
                  intro hdvd
                  refine he₃nd ?_
                  rcases hp7.dvd_mul.mp (show (7 : ℤ) ∣ 2 * (u * e₃) from by
                    rwa [show 2 * (u * e₃) = 2 * u * e₃ from by ring]) with hh | hh
                  · exact absurd hh (by decide)
                  · exact hh
                have hrel2 : ((2 * u * e₃ : ℤ) : ZMod 7) = 2 * ((2 * u * d i₅ : ℤ) : ZMod 7) := by
                  push_cast
                  rw [he₃, hi₅_res]
                  linear_combination (-(2 * ((u : ℤ) : ZMod 7))) * seven_eq_zero_z7
                have hdv2 : (7 : ℤ) ^ m ∣ (2 * (2 * u * d i₅) - 2 * u * e₃) := by
                  rw [show 2 * (2 * u * d i₅) - 2 * u * e₃
                      = 2 * (2 * (u * d i₅) - u * e₃) from by ring]
                  exact hgm.mul_left 2
                obtain ⟨lam, hlamu, hlamres, hout⟩ :=
                  lemma7_ii m 0 (by omega) (2 * u * d i₅) (2 * u * e₃) hz₅nd2 he₃nd2 hrel2
                    ({4, 6, τ - 2} : Finset (ZMod 7)) hdv2
                    (by rw [c65_gap_empty τ hτ34]; exact Finset.notMem_empty _)
                have hwu : ¬ (7 : ℤ) ∣ (lam * (2 * u)) := by
                  intro hdvd
                  rcases hp7.dvd_mul.mp hdvd with hh | hh
                  · exact hlamu hh
                  · rcases hp7.dvd_mul.mp hh with hh' | hh'
                    · exact absurd hh' (by decide)
                    · exact hu hh'
                obtain ⟨ha1, ha2, ha4⟩ := arcs (lam * (2 * u)) 2 (by push_cast [hlamres]; ring)
                have hout' : 2 * qz m (lam * (2 * u) * d i₅) - qz m (lam * (2 * u) * e₃)
                    ∉ ({4, 6, τ - 2} : Finset (ZMod 7)) := by
                  rwa [show lam * (2 * u) * d i₅ = lam * (2 * u * d i₅) from by ring,
                    show lam * (2 * u) * e₃ = lam * (2 * u * e₃) from by ring]
                obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ :=
                  c65_top_hi (qz m (lam * (2 * u) * e₃)) (qz m (lam * (2 * u) * d i₅)) τ hτ34
                    hout'
                refine closeK (lam * (2 * u)) hwu k ?_ ?_ hk1 ?_ hk4
                · rw [ha1]; exact hk2
                · rw [ha2, show (2 : ZMod 7) * 2 = 4 from by decide]; exact hk3
                · rw [ha4]; exact hk5
              · -- `ν(2d₅−d₃) < m`: Lemma 7(i) in the `u`-frame
                have hrel : ((u * e₃ : ℤ) : ZMod 7) = 2 * ((u * d i₅ : ℤ) : ZMod 7) := by
                  push_cast
                  rw [he₃, hi₅_res]
                  linear_combination (-(((u : ℤ) : ZMod 7))) * seven_eq_zero_z7
                have hgne : (2 * (u * d i₅) - u * e₃) ≠ 0 := fun hq => hgm (hq ▸ dvd_zero _)
                set νg : ℕ := padicValInt 7 (2 * (u * d i₅) - u * e₃) with hνg_def
                have hν_lt : νg < m := by
                  by_contra hge
                  push_neg at hge
                  exact hgm ((padicValInt_dvd_iff m (2 * (u * d i₅) - u * e₃)).mpr (Or.inr hge))
                have hν_nd : ¬ (7 : ℤ) ^ (νg + 1) ∣ (2 * (u * d i₅) - u * e₃) := by
                  intro hh2
                  have hle := ((padicValInt_dvd_iff (νg + 1)
                    (2 * (u * d i₅) - u * e₃)).mp hh2).resolve_left hgne
                  rw [← hνg_def] at hle
                  omega
                have hX : ∃ a : ZMod 7, fitsInterval ({-τ, 1 - τ} : Finset (ZMod 7)) a 4 := by
                  refine ⟨-τ, ?_⟩
                  rcases hτ34 with h34 | h34 <;> rw [h34] <;> decide
                obtain ⟨lam, hlamu, hlamres, hout⟩ :=
                  lemma7_i m νg hν_lt
                    (u * d i₅) (u * e₃) hz₅nd he₃nd hrel ({-τ, 1 - τ} : Finset (ZMod 7)) hX
                    (padicValInt_dvd (2 * (u * d i₅) - u * e₃)) hν_nd
                have hwu : ¬ (7 : ℤ) ∣ (lam * u) := by
                  intro hdvd
                  rcases hp7.dvd_mul.mp hdvd with hh | hh
                  · exact hlamu hh
                  · exact hu hh
                obtain ⟨ha1, ha2, ha4⟩ := arcs (lam * u) 1 (by push_cast [hlamres]; ring)
                have hout' : 2 * qz m (lam * u * d i₅) - qz m (lam * u * e₃)
                    ∉ ({-τ, 1 - τ} : Finset (ZMod 7)) := by
                  rwa [show lam * u * d i₅ = lam * (u * d i₅) from by ring,
                    show lam * u * e₃ = lam * (u * e₃) from by ring]
                obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ :=
                  c65_top_lo (qz m (lam * u * e₃)) (qz m (lam * u * d i₅)) τ hτ34 hout'
                refine closeK (lam * u) hwu k ?_ ?_ hk1 ?_ hk4
                · rw [ha1]; exact hk2
                · rw [ha2, mul_one]; exact hk3
                · rw [ha4, one_mul]; exact hk5
            · -- `τ ∉ {3,4}`: `ℓ(A₄) ≤ 3` and `ℓ(A₁) = 3`
              obtain ⟨ha1, ha2, ha4⟩ := arcs u 1 (by rw [one_mul])
              refine close_33 u hu ⟨qz m (u * e₃), ?_⟩ ?_
              · rw [hset u]
                intro v hv
                simp only [Finset.mem_insert, Finset.mem_singleton] at hv
                rcases hv with rfl | rfl | rfl
                · exact ⟨⟨1, by omega⟩, by rw [ha1]; simp⟩
                · exact ⟨⟨2, by omega⟩, by rw [ha2, mul_one]; simp⟩
                · exact ⟨⟨0, by omega⟩, by simp⟩
              · rw [ha4, one_mul, add_sub_cancel_left]
                exact z7_not34 τ hτ34
        · -- `h > m`: all `A₁` arcs coincide; retarget `e₄₅`
          exact close_hgt (dvd_trans (pow_dvd_pow 7 (by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (by omega)) hd2)
      · -- ── (ii.2) ratio 3 ──
        rcases lt_trichotomy h m with hlt | heq | hgt
        · by_cases hμh : μ = h
          · -- `ν(e₄₅) = h` (BS L713–717). Align the `A₄` difference `F` with `e₂₃`
            -- (`r(F) = r(e₂₃)`, flipping the `A₄` pair if `r(e₂₃) = −s`), so that
            -- `f = F − e₂₃` sits above level `h`; retarget `q(λ·f)` and use the sharp
            -- Lemma 9(ii) bound `q(λ·e₂₃) ∈ {0,5,6}`.
            rw [hμh] at hμd hμd' hs_def
            obtain ⟨F, hFor, hFd, hFr⟩ :
                ∃ F : ℤ, (F = E45 ∨ F = -E45) ∧ (7 : ℤ) ^ h ∣ F ∧
                  ((F / 7 ^ h : ℤ) : ZMod 7) = (((e₂ - e₃) / 7 ^ h : ℤ) : ZMod 7) := by
              obtain ⟨cc, hcc⟩ := id hμd
              have hq1 : E45 / (7 : ℤ) ^ h = cc := by
                rw [hcc]; exact Int.mul_ediv_cancel_left cc (by positivity)
              rcases hsalign with hsg | hsg
              · exact ⟨E45, Or.inl rfl, hμd, by rw [hs_def] at hsg; exact hsg.symm⟩
              · refine ⟨-E45, Or.inr rfl, (dvd_neg).mpr hμd, ?_⟩
                have hq2 : (-E45) / (7 : ℤ) ^ h = -cc := by
                  rw [show -E45 = 7 ^ h * (-cc) from by rw [hcc]; ring]
                  exact Int.mul_ediv_cancel_left (-cc) (by positivity)
                rw [hq2, hsg, hs_def, hq1]; push_cast; ring
            set f : ℤ := F - (e₂ - e₃) with hf_def
            have hf_lo : (7 : ℤ) ^ (h + 1) ∣ f := by
              have hfd : (7 : ℤ) ^ h ∣ f := by rw [hf_def]; exact dvd_sub hFd hd2
              have hres0 : ((f / 7 ^ h : ℤ) : ZMod 7) = 0 := by
                rw [hf_def, Int.sub_ediv_of_dvd _ hd2]
                push_cast; rw [hFr]; ring
              have h7 : (7 : ℤ) ∣ (f / 7 ^ h) := by
                rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hres0
              obtain ⟨cq, hcq⟩ := h7
              obtain ⟨wq, hwq⟩ := hfd
              refine ⟨cq, ?_⟩
              have hqq : f / 7 ^ h = wq := by
                rw [hwq]; exact Int.mul_ediv_cancel_left wq (by positivity)
              rw [hwq, show wq = 7 * cq from by rw [← hqq, hcq], pow_succ]; ring
            -- the ratio-3 structure survives any unit dilation
            have transfer : ∀ w : ℤ, ¬ (7 : ℤ) ∣ w →
                (7 : ℤ) ^ h ∣ (w * e₁ - w * e₃) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (w * e₁ - w * e₃) ∧
                (7 : ℤ) ^ h ∣ (w * e₂ - w * e₃) ∧
                (((w * e₂ - w * e₃) / 7 ^ h : ℤ) : ZMod 7)
                  = 3 * (((w * e₁ - w * e₃) / 7 ^ h : ℤ) : ZMod 7) := by
              intro w hw
              have hE1 : w * e₁ - w * e₃ = w * (e₁ - e₃) := by ring
              have hE2 : w * e₂ - w * e₃ = w * (e₂ - e₃) := by ring
              refine ⟨by rw [hE1]; exact hd1.mul_left w, ?_, by rw [hE2]; exact hd2.mul_left w, ?_⟩
              · rw [hE1]
                exact fun hdvd => hd1'
                  ((hp7.irreducible.coprime_pow_of_not_dvd (h + 1) hw).symm.dvd_of_dvd_mul_left
                    hdvd)
              · rw [hE1, hE2, Int.mul_ediv_assoc w hd2, Int.mul_ediv_assoc w hd1]
                push_cast; rw [hr3]; ring
            by_cases hfhigh : (7 : ℤ) ^ (m + 1) ∣ f
            · -- `ν(f) > m`: `q(λ·F) = q(λ·e₂₃)` exactly
              obtain ⟨lam, hlam, hfit, hbig, -⟩ := j3_big056 m h hlt e₁ e₂ e₃ hd1 hd1' hd2 hr3
              refine close_33 lam hlam ?_ (bandF lam F hFor ?_)
              · obtain ⟨a, hfa⟩ := hfit
                exact ⟨a, by rw [hset lam]; exact hfa⟩
              · rw [qz_eq_of_high_dvd m F (e₂ - e₃) lam (by rw [← hf_def]; exact hfhigh),
                  show lam * (e₂ - e₃) = lam * e₂ - lam * e₃ from by ring]
                revert hbig; generalize qz m (lam * e₂ - lam * e₃) = v; revert v; decide
            · obtain ⟨μ', hμ'lo, hμ'hi, hμ'd, hμ'd'⟩ :
                  ∃ μ' : ℕ, h + 1 ≤ μ' ∧ μ' ≤ m ∧ (7 : ℤ) ^ μ' ∣ f ∧ ¬ (7 : ℤ) ^ (μ' + 1) ∣ f := by
                have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ f := ⟨m, hfhigh⟩
                have hspec := Nat.find_spec hex
                have hle : Nat.find hex ≤ m := Nat.find_le hfhigh
                have hge : h + 1 ≤ Nat.find hex := by
                  by_contra hcon; rw [not_le] at hcon
                  exact hspec (dvd_trans (pow_dvd_pow 7 (by omega)) hf_lo)
                have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
                rw [not_not] at hprev
                exact ⟨Nat.find hex, hge, hle,
                  by rwa [show Nat.find hex - 1 + 1 = Nat.find hex from by omega] at hprev, hspec⟩
              by_cases hμ'lt : μ' < m
              · -- `h < ν(f) < m`: set `q(λ·f) = 0`, then compress (`Λ_h` is inert on `f`)
                obtain ⟨k, hqk, hku⟩ := qz_retarget m μ' hμ'lt f hμ'd hμ'd' 0
                obtain ⟨ht1, ht1', ht2, ht3⟩ := transfer (1 + k * 7 ^ (m - μ')) hku
                obtain ⟨lam, hlam, hfit, hbig, hinert⟩ :=
                  j3_big056 m h hlt ((1 + k * 7 ^ (m - μ')) * e₁) ((1 + k * 7 ^ (m - μ')) * e₂)
                    ((1 + k * 7 ^ (m - μ')) * e₃) ht1 ht1' ht2 ht3
                have hqf : qz m (lam * ((1 + k * 7 ^ (m - μ')) * f)) = 0 := by
                  rw [hinert ((1 + k * 7 ^ (m - μ')) * f)
                    (Dvd.dvd.mul_left hf_lo (1 + k * 7 ^ (m - μ')))]
                  exact hqk
                have hcompu : ¬ (7 : ℤ) ∣ (lam * (1 + k * 7 ^ (m - μ'))) := by
                  intro hdvd; rcases hp7.dvd_mul.mp hdvd with hc | hc
                  · exact hlam hc
                  · exact hku hc
                refine close_33 (lam * (1 + k * 7 ^ (m - μ'))) hcompu ?_
                  (bandF (lam * (1 + k * 7 ^ (m - μ'))) F hFor ?_)
                · obtain ⟨a, hfa⟩ := hfit
                  refine ⟨a, ?_⟩
                  rw [hset (lam * (1 + k * 7 ^ (m - μ')))]
                  simp only [mul_assoc]
                  exact hfa
                · have hsplit : lam * (1 + k * 7 ^ (m - μ')) * F
                      = (lam * ((1 + k * 7 ^ (m - μ')) * e₂)
                          - lam * ((1 + k * 7 ^ (m - μ')) * e₃))
                        + lam * ((1 + k * 7 ^ (m - μ')) * f) := by
                    rw [hf_def]; ring
                  rcases qz_add_carry m (lam * ((1 + k * 7 ^ (m - μ')) * e₂)
                      - lam * ((1 + k * 7 ^ (m - μ')) * e₃))
                      (lam * ((1 + k * 7 ^ (m - μ')) * f)) with hcc | hcc
                  · rw [hsplit, hcc, hqf, add_zero]
                    revert hbig
                    generalize qz m (lam * ((1 + k * 7 ^ (m - μ')) * e₂)
                      - lam * ((1 + k * 7 ^ (m - μ')) * e₃)) = v
                    revert v; decide
                  · rw [hsplit, hcc, hqf, add_zero]
                    revert hbig
                    generalize qz m (lam * ((1 + k * 7 ^ (m - μ')) * e₂)
                      - lam * ((1 + k * 7 ^ (m - μ')) * e₃)) = v
                    revert v; decide
              · -- `ν(f) = m`: `q(λ·f) = 1` and the level-`m` shift carries no rounding
                have hμ'eq : μ' = m := by omega
                rw [hμ'eq] at hμ'd hμ'd'
                obtain ⟨jj, hju, hqj⟩ := qz_retarget_top m f hμ'd hμ'd' 1 (by decide)
                obtain ⟨ht1, ht1', ht2, ht3⟩ := transfer jj hju
                obtain ⟨lam, hlam, hfit, hbig, hinert⟩ :=
                  j3_big056 m h hlt (jj * e₁) (jj * e₂) (jj * e₃) ht1 ht1' ht2 ht3
                have hqf : qz m (lam * (jj * f)) = 1 := by
                  rw [hinert (jj * f) (Dvd.dvd.mul_left hf_lo jj)]; exact hqj
                obtain ⟨cf, hcf⟩ := id hμ'd
                have hcast : ((lam * jj * cf : ℤ) : ZMod 7) = 1 := by
                  rw [show lam * (jj * f) = 0 + (lam * jj * cf) * 7 ^ m from by
                    rw [hcf]; ring, qz_add_mul_pow,
                    show qz m (0 : ℤ) = 0 from by simp [qz], zero_add] at hqf
                  exact hqf
                have hcompu : ¬ (7 : ℤ) ∣ (lam * jj) := by
                  intro hdvd; rcases hp7.dvd_mul.mp hdvd with hc | hc
                  · exact hlam hc
                  · exact hju hc
                refine close_33 (lam * jj) hcompu ?_ (bandF (lam * jj) F hFor ?_)
                · obtain ⟨a, hfa⟩ := hfit
                  refine ⟨a, ?_⟩
                  rw [hset (lam * jj)]
                  simp only [mul_assoc]
                  exact hfa
                · have hsplit : lam * jj * F
                      = (lam * (jj * e₂) - lam * (jj * e₃)) + (lam * jj * cf) * 7 ^ m := by
                    rw [hf_def] at hcf; linear_combination lam * jj * hcf
                  rw [hsplit, qz_add_mul_pow, hcast]
                  revert hbig
                  generalize qz m (lam * (jj * e₂) - lam * (jj * e₃)) = v
                  revert v; decide
          · by_cases hμlt : μ < m
            · obtain ⟨lam₀, hlam₀, hfit, hqE⟩ :=
                j3_control m h μ hlt hμlt (Ne.symm hμh) e₁ e₂ e₃ (he₁.trans he₃.symm)
                  (he₂.trans he₃.symm) hd1 hd1' hd2 hd2' hr3 E45 hμd hμd' 0
              refine close_33 lam₀ hlam₀ ?_ (band33 lam₀ (by rw [hqE]; decide))
              obtain ⟨a, hfa⟩ := hfit
              exact ⟨a, by rw [hset lam₀]; exact hfa⟩
            · have hμeq : μ = m := by omega
              rw [hμeq] at hμd hμd'
              obtain ⟨lam₀, hlam₀, hfit, hqE⟩ :=
                j3_control_top m h hlt e₁ e₂ e₃ (he₁.trans he₃.symm) (he₂.trans he₃.symm)
                  hd1 hd1' hd2 hd2' hr3 E45 hμd hμd' 1 (by decide)
              refine close_33 lam₀ hlam₀ ?_ ?_
              · obtain ⟨a, hfa⟩ := hfit
                exact ⟨a, by rw [hset lam₀]; exact hfa⟩
              · rw [hA4exact lam₀ hμd, hqE]; decide
        · -- `h = m`: the `r(e₂₃)⁻¹` frame puts `A₁` at `{A+5, A+1, A}` (`ℓ = 4`)
          rw [heq] at hd1 hd2 hd2' hr3 hsalign
          obtain ⟨u, hu, hu1⟩ := inv_frame m e₂ e₃ hd2 hd2'
          have hu5 : (u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7) = 5 := by
            have hh := hu1
            rw [hr3] at hh
            calc (u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7)
                = (15 : ZMod 7) * ((u : ZMod 7) * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7)) := by
                  rw [show (15 : ZMod 7) = 1 from by decide, one_mul]
              _ = 5 * ((u : ZMod 7) * (3 * (((e₁ - e₃) / 7 ^ m : ℤ) : ZMod 7))) := by ring
              _ = 5 * 1 := by rw [hh]
              _ = 5 := by ring
          have hnum1 : (5 : ZMod 7) + ((2 : ℕ) : ZMod 7) = 0 := by decide
          have hnum2 : (5 : ZMod 7) + ((3 : ℕ) : ZMod 7) = 1 := by decide
          have arcs : ∀ w : ℤ, ((w : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) →
              ∃ a : ZMod 7,
                fitsInterval ({qz m (w * b₁ 0), qz m (w * b₁ 1), qz m (w * b₁ 2)}
                  : Finset (ZMod 7)) a 4 := by
            intro w hwres
            refine ⟨qz m (w * e₃) + 5, ?_⟩
            rw [hset w]
            have ha1 : qz m (w * e₁) = qz m (w * e₃) + 5 := by
              rw [qz_top_affine m w e₁ e₃ hd1, hwres, hu5]
            have ha2 : qz m (w * e₂) = qz m (w * e₃) + 1 := by
              rw [qz_top_affine m w e₂ e₃ hd2, hwres, hu1]
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact ⟨⟨0, by omega⟩, by rw [ha1]; simp⟩
            · refine ⟨⟨3, by omega⟩, ?_⟩
              rw [ha2, add_assoc, hnum2]
            · refine ⟨⟨2, by omega⟩, ?_⟩
              rw [add_assoc, hnum1, add_zero]
          by_cases hμlt : μ < m
          · obtain ⟨k, hqk, hku⟩ := qz_retarget m μ hμlt (u * E45)
              (Dvd.dvd.mul_left hμd u)
              (fun hdvd => hμd'
                ((hp7.irreducible.coprime_pow_of_not_dvd (μ + 1) hu).symm.dvd_of_dvd_mul_left hdvd))
              0
            have hwu : ¬ (7 : ℤ) ∣ ((1 + k * 7 ^ (m - μ)) * u) := by
              intro hdvd; rcases hp7.dvd_mul.mp hdvd with hc | hc
              · exact hku hc
              · exact hu hc
            have hwres : (((1 + k * 7 ^ (m - μ)) * u : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) := by
              push_cast
              rw [seven_eq_zero_z7, zero_pow (show m - μ ≠ 0 from by omega), mul_zero, add_zero,
                one_mul]
            have hqE : qz m ((1 + k * 7 ^ (m - μ)) * u * E45) = 0 := by
              rw [show (1 + k * 7 ^ (m - μ)) * u * E45 = (1 + k * 7 ^ (m - μ)) * (u * E45)
                from by ring]
              exact hqk
            exact close_42 _ hwu (arcs _ hwres)
              (by rcases hA4diff ((1 + k * 7 ^ (m - μ)) * u) with hcc | hcc <;>
                rw [hcc, hqE] <;> decide)
          · have hμeq : μ = m := by omega
            rw [hμeq] at hμd hμd' hs_def
            have hqE : qz m (u * E45) = (u : ZMod 7) * s := by
              rw [qz_top_affine m u E45 0 (by simpa using hμd), mul_zero,
                show qz m (0 : ℤ) = 0 from by simp [qz], zero_add, sub_zero, hs_def]
            refine close_42 u hu (arcs u rfl) ?_
            rw [hA4exact u hμd, hqE]
            rcases hsalign with hsg | hsg
            · rw [← hsg, hu1]; decide
            · have hs2 : s = -(((e₂ - e₃) / 7 ^ m : ℤ) : ZMod 7) := by rw [hsg]; ring
              rw [hs2, mul_neg, hu1]; decide
        · -- `h > m`
          exact close_hgt (dvd_trans (pow_dvd_pow 7 (by omega)) hd1)
            (dvd_trans (pow_dvd_pow 7 (by omega)) hd2)

/-- **Ratio-2 pair compression into `{0,6}` (BS Lemma 9 (ii), `j = 2`, sharpened).**
Two integers `x, y` at the same level `h < m` with `r(y) = 2·r(x)` admit a unit
multiplier putting BOTH arc indices in `{0,6}`. This is the engine behind BS's
"if `ν(e₁₂) < m` the desired multiplier exists by Lemma 9" step of §6.6 (L749).

`lemma9_ii_j2` packages the same two-stage retarget as `ℓ(λ·B) ≤ 2`, which is
strictly weaker than the `{0,6}` statement its own proof establishes (a length-2
window through `0` may be `{0,1}`), so the argument is redone here in the form
§6.6 needs. STAGE 1 puts `q(λ₁·e) = se ∈ {0,6}` for `e = 2x − y` (level `> h`);
STAGE 2 uses the `Λ_h`-invariance of `ẽ = 2q(x) − q(y)` (Lemma 4 (i)) to place
`q(λ·x)` at a target `t` chosen from `(se, c)` by the six-row table below. -/
theorem ratio2_both06 (m h : ℕ) (hh : h < m) (x y : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ x)
    (hy : (7 : ℤ) ^ h ∣ y)
    (hr : ((y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((x / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      qz m (lam * x) ∈ ({0, 6} : Finset (ZMod 7)) ∧
      qz m (lam * y) ∈ ({0, 6} : Finset (ZMod 7)) := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  set e : ℤ := 2 * x - y with hedef
  -- `r(y) = 2 r(x)` cancels the level-`h` term of `2x − y`.
  have he_lo : (7 : ℤ) ^ (h + 1) ∣ e := by
    have he_dvd : (7 : ℤ) ^ h ∣ e := by
      rw [hedef]; exact dvd_sub (Dvd.dvd.mul_left hx 2) hy
    have hres : ((e / 7 ^ h : ℤ) : ZMod 7) = 0 := by
      rw [hedef, Int.sub_ediv_of_dvd _ hy, Int.mul_ediv_assoc 2 hx]
      push_cast; rw [hr]; ring
    have h7 : (7 : ℤ) ∣ (e / 7 ^ h) := by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hres
    obtain ⟨c, hc⟩ := h7
    obtain ⟨w, hw⟩ := he_dvd
    refine ⟨c, ?_⟩
    have hwc : w = 7 * c := by
      have hq : e / 7 ^ h = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by positivity)
      rw [← hq, hc]
    rw [hw, hwc, pow_succ]; ring
  -- STAGE 1: `q(λ₁·e) = se ∈ {0,6}` (`λ₁ = 1` when `ν(e) > m`).
  obtain ⟨lam₁, se, hlam₁, hse, hse_eq⟩ :
      ∃ (lam₁ : ℤ) (se : ZMod 7), ¬ (7 : ℤ) ∣ lam₁ ∧ (se = 0 ∨ se = 6) ∧
        qz m (lam₁ * e) = se := by
    by_cases htop : (7 : ℤ) ^ (m + 1) ∣ e
    · refine ⟨1, 0, by norm_num, Or.inl rfl, ?_⟩
      rw [one_mul]; unfold qz
      obtain ⟨c, hc⟩ := htop
      rw [hc, pow_succ, show (7 : ℤ) ^ m * 7 * c = 7 ^ m * (7 * c) from by ring,
        Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0)),
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨c, by ring⟩
    · obtain ⟨h', hh'lo, hh'hi, hh'd, hh'd'⟩ :
          ∃ h' : ℕ, h + 1 ≤ h' ∧ h' ≤ m ∧ (7 : ℤ) ^ h' ∣ e ∧ ¬ (7 : ℤ) ^ (h' + 1) ∣ e := by
        have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ e := ⟨m, htop⟩
        have hspec : ¬ (7 : ℤ) ^ (Nat.find hex + 1) ∣ e := Nat.find_spec hex
        have hle : Nat.find hex ≤ m := Nat.find_le htop
        have hge : h + 1 ≤ Nat.find hex := by
          by_contra hcon; rw [not_le] at hcon
          exact hspec (dvd_trans (pow_dvd_pow 7 (by omega)) he_lo)
        have hprev : ¬ ¬ (7 : ℤ) ^ ((Nat.find hex - 1) + 1) ∣ e :=
          Nat.find_min hex (by omega)
        rw [not_not] at hprev
        exact ⟨Nat.find hex, hge, hle,
          by rwa [show (Nat.find hex - 1) + 1 = Nat.find hex from by omega] at hprev, hspec⟩
      by_cases hh'm : h' < m
      · obtain ⟨k, hqk, hku⟩ := qz_retarget m h' hh'm e hh'd hh'd' 0
        exact ⟨1 + k * 7 ^ (m - h'), 0, hku, Or.inl rfl, hqk⟩
      · have hh'eq : h' = m := by omega
        rw [hh'eq] at hh'd hh'd'
        obtain ⟨j, hju, hjq⟩ := qz_retarget_top m e hh'd hh'd' 6 (by decide)
        exact ⟨j, 6, hju, Or.inr rfl, hjq⟩
  have hl1x_dvd : (7 : ℤ) ^ h ∣ lam₁ * x := Dvd.dvd.mul_left hx lam₁
  have hl1y_dvd : (7 : ℤ) ^ h ∣ lam₁ * y := Dvd.dvd.mul_left hy lam₁
  have hl1x_ndvd : ¬ (7 : ℤ) ^ (h + 1) ∣ lam₁ * x := by
    intro hdvd; refine hx' ?_
    have hcop : IsCoprime ((7 : ℤ) ^ (h + 1)) lam₁ :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hlam₁)
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (lam₁ * x) (lam₁ * y)
  have hle_eq : lam₁ * e = 2 * (lam₁ * x) - lam₁ * y := by rw [hedef]; ring
  have hetilde1 : 2 * qz m (lam₁ * x) - qz m (lam₁ * y) = se - c := by
    rw [← hle_eq, hse_eq] at hcarry; linear_combination -hcarry
  -- the six `(se, c)` rows: a target `t ∈ {0,6}` with `2t − ẽ ∈ {0,6}` always exists
  obtain ⟨t, htA, htB⟩ :
      ∃ t : ZMod 7, t ∈ ({0, 6} : Finset (ZMod 7)) ∧
        (2 * t - (se - c)) ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases hse with rfl | rfl <;> rcases hc with rfl | rfl | rfl
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨6, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨6, by decide, by decide⟩
    · exact ⟨6, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  -- STAGE 2: a `Λ_h` factor on `λ₁·x`, with `ẽ` invariant by Lemma 4 (i)
  obtain ⟨k₂, hk₂x, hk₂u⟩ := qz_retarget m h hh (lam₁ * x) hl1x_dvd hl1x_ndvd t
  refine ⟨(1 + k₂ * 7 ^ (m - h)) * lam₁, ?_, ?_, ?_⟩
  · exact mt (Prime.dvd_mul hp7 |>.mp) (by tauto)
  · rw [show (1 + k₂ * 7 ^ (m - h)) * lam₁ * x = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * x) from by
      ring, hk₂x]
    exact htA
  · have hr2 : ((lam₁ * y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((lam₁ * x / 7 ^ h : ℤ) : ZMod 7) := by
      rw [Int.mul_ediv_assoc lam₁ hy, Int.mul_ediv_assoc lam₁ hx]; push_cast; rw [hr]; ring
    have hl4 := lemma4_i m h (le_of_lt hh) k₂ (lam₁ * x) (lam₁ * y) hl1x_dvd hl1y_dvd hr2
    rw [hk₂x, hetilde1] at hl4
    rw [show (1 + k₂ * 7 ^ (m - h)) * lam₁ * y = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * y) from by ring,
      show qz m ((1 + k₂ * 7 ^ (m - h)) * (lam₁ * y)) = 2 * t - (se - c) from by
        linear_combination -hl4]
    exact htB

/-- **BS §6.6 (b) table, corrected fifth arc** (L771–780). `e₁₂ = N/7`,
`e₃₄ = 2N/7`; `λk ∈ Λ₀` chosen so `q(λk d₄) = k`. The five arcs are `k`, `k+2`
(that is `A₂`), `4ẽ₂₄ + 4k`, `4ẽ₂₄ + 4k + 1` (that is `A₁`), and `2k − ẽ₄₅`
(that is `d₅`).

BS write the fifth arc as `ẽ(d₂,d₄) − ẽ(d₂,d₅) + k` with
`ẽ(d₂,d₅) = 2q(d₂) − q(d₅)`. That quantity is **not** `Λ₀`-invariant: `d₅` has
residue `4 = 2·2 = 2·r(d₄)`, not `2·r(d₂) = 2`, so the ratio-2 partner of `d₅`
in this frame is `d₄`, and the governing invariant is `ẽ(d₄,d₅) = 2q(d₄) − q(d₅)`.
Solving `q(λk d₅)` in the `k`-frame gives `2k − ẽ(d₄,d₅)`, which is what appears
below. (`avoid_66b` in `OrderSevenC66N` is stated with BS's non-invariant version;
its exclusion set `{0,2,4,6}` is an artefact of that substitution.)

With the invariant fifth arc the bad set is `{(2,4),(2,5),(4,4),(4,5)}`, so the
exclusion needed is only `ẽ₂₄ ∉ {2,4}` — an interval-fitting set (`ℓ = 3 ≤ 4`,
Lemma 7 (i)) with empty self-overlap (`inter24_empty`, Lemma 7 (ii)). Sub-case
(b) therefore closes at every valuation of `2d₂ − d₄`. -/
theorem avoid_66b_Q (t24 t45 : ZMod 7) (h : t24 ≠ 2 ∧ t24 ≠ 4) :
    ∃ k : ZMod 7, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      (k ≠ 0 ∧ k ≠ 6) ∧
      (k + 2 ≠ 0 ∧ k + 2 ≠ 6) ∧
      (4 * t24 + 4 * k ≠ 0 ∧ 4 * t24 + 4 * k ≠ 6) ∧
      (4 * t24 + 4 * k + 1 ≠ 0 ∧ 4 * t24 + 4 * k + 1 ≠ 6) ∧
      (2 * k - t45 ≠ 0 ∧ 2 * k - t45 ≠ 6) := by
  revert h; revert t24 t45; decide

/-- **`{4,6} ∩ ({4,6}+1) = ∅`** — the second empty `ν=m` gap used in §6.6 (a). -/
theorem inter46_empty :
    (({4, 6} : Finset (ZMod 7)) ∩ (({4, 6} : Finset (ZMod 7)).image (· + 1))) = ∅ := by decide

/-- `{2,4}` and `{4,6}` fit length-4 windows (`ℓ = 3`), the Lemma 7 (i) hypothesis. -/
theorem fits24 : ∃ a : ZMod 7, fitsInterval ({2, 4} : Finset (ZMod 7)) a 4 :=
  ⟨2, by decide⟩

theorem fits46 : ∃ a : ZMod 7, fitsInterval ({4, 6} : Finset (ZMod 7)) a 4 :=
  ⟨4, by decide⟩

/-- `{4,5,6}` fits a length-4 window — the Lemma 7 (i) hypothesis for §6.6 (a). -/
theorem fits456 : ∃ a : ZMod 7, fitsInterval ({4, 5, 6} : Finset (ZMod 7)) a 4 :=
  ⟨4, by decide⟩

/-- **§6.6 (a), `ν(e₂₄) ≥ m`: the exclusion combiner.** At the top level the
doubling carry pins `ẽ₂₄ ∈ {ρ, ρ−1}` where `ρ = q(λ·(2d₂−d₄))` is frame-invariant
(only two values, not the three of the generic `2x−y` carry). Over that pair the
bad `ẽ₅₂` values of BS's list (16) are `{4,6}` when `ρ ∈ {0,6}` and `{2,4}`
otherwise — both `ℓ = 3` and both with empty self-overlap, so Lemma 7 applies at
every valuation of `2d₅ − d₂`. -/
theorem c66a_exc (rho t24 t25 : ZMod 7) (hP : t24 = rho ∨ t24 = rho - 1)
    (hR0 : (rho = 0 ∨ rho = 6) → (t25 ≠ 4 ∧ t25 ≠ 6))
    (hR1 : ¬ (rho = 0 ∨ rho = 6) → (t25 ≠ 2 ∧ t25 ≠ 4)) :
    ¬ ((t24 = 4 ∧ t25 = 2) ∨ (t24 = 4 ∧ t25 = 4) ∨ (t24 = 5 ∧ t25 = 4) ∨
       (t24 = 6 ∧ t25 = 4) ∨ (t24 = 6 ∧ t25 = 6)) := by
  revert hP hR0 hR1; revert rho t24 t25; decide

/-- Every ratio of two nonzero `ZMod 7` residues is, after flipping the sign of the
second, one of `1, 2, 4` — BS's "up to renaming the elements of `A` we may assume
`r(e₁₂), r(e₃₄) ∈ {1,2,4}`" (L745), in the only form §6.6 uses it. -/
theorem ratio_normalize (s₁ s₂ : ZMod 7) (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    s₂ = s₁ ∨ s₂ = 2 * s₁ ∨ s₂ = 4 * s₁ ∨
      -s₂ = s₁ ∨ -s₂ = 2 * s₁ ∨ -s₂ = 4 * s₁ := by
  revert h₁ h₂; revert s₁ s₂; decide

/-- `{0,1,6}` (circular distance `≤ 1`) is closed under negation. -/
theorem neg016 (v : ZMod 7) (h : v ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    -v ∈ ({0, 1, 6} : Finset (ZMod 7)) := by revert h; revert v; decide

/-- One carry cannot push a `{0,6}` arc difference out of the `ℓ ≤ 2` band. -/
theorem shift_06 (D : ZMod 7) (h : D ∈ ({0, 6} : Finset (ZMod 7))) :
    D ∈ ({0, 1, 6} : Finset (ZMod 7)) ∧ D + 1 ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  revert h; revert D; decide

/-- **Case 6.6 `(2,2,1)`** (BS L743). `|A₁|=2, |A₂|=2, |A₄|=1`. Self-contained:
Lemma 2 / Lemma 9(i)/(ii) compress `A₁,A₂` to `ℓ ≤ 2`, then Lemma 5; ν=m subcases
use the explicit `(a)/(b)` q-tables. -/
theorem case_66 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d)
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card =2)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 2)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  classical
  have hp7 : Prime (7 : ℤ) := seven_totient_full_int
  -- ── the five indices ──
  obtain ⟨i₁, i₂, h12ne, hP₁⟩ := Finset.card_eq_two.mp hC₁
  obtain ⟨i₃, i₄, h34ne, hP₂⟩ := Finset.card_eq_two.mp hC₂
  obtain ⟨i₅, hP₄⟩ := Finset.card_eq_one.mp hC₄
  have hmem₁ : ∀ i : Fin 5, (d i : ZMod 7) = 1 → i = i₁ ∨ i = i₂ := by
    intro i hi
    have hmm : i ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 1) := by simp [hi]
    rw [hP₁, Finset.mem_insert, Finset.mem_singleton] at hmm; exact hmm
  have hmem₂ : ∀ i : Fin 5, (d i : ZMod 7) = 2 → i = i₃ ∨ i = i₄ := by
    intro i hi
    have hmm : i ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 2) := by simp [hi]
    rw [hP₂, Finset.mem_insert, Finset.mem_singleton] at hmm; exact hmm
  have hmem₄ : ∀ i : Fin 5, (d i : ZMod 7) = 4 → i = i₅ := by
    intro i hi
    have hmm : i ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 4) := by simp [hi]
    rw [hP₄, Finset.mem_singleton] at hmm; exact hmm
  have hr₁ : (d i₁ : ZMod 7) = 1 := by
    have hmm : i₁ ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 1) := by
      rw [hP₁]; exact mem_insert_self _ _
    simpa using hmm
  have hr₂ : (d i₂ : ZMod 7) = 1 := by
    have hmm : i₂ ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 1) := by
      rw [hP₁]; exact mem_insert_of_mem (mem_singleton_self _)
    simpa using hmm
  have hr₃ : (d i₃ : ZMod 7) = 2 := by
    have hmm : i₃ ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 2) := by
      rw [hP₂]; exact mem_insert_self _ _
    simpa using hmm
  have hr₄ : (d i₄ : ZMod 7) = 2 := by
    have hmm : i₄ ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 2) := by
      rw [hP₂]; exact mem_insert_of_mem (mem_singleton_self _)
    simpa using hmm
  have hr₅ : (d i₅ : ZMod 7) = 4 := by
    have hmm : i₅ ∈ univ.filter (fun j : Fin 5 => (d j : ZMod 7) = 4) := by
      rw [hP₄]; exact mem_singleton_self _
    simpa using hmm
  have hcover : ∀ i : Fin 5, i = i₁ ∨ i = i₂ ∨ i = i₃ ∨ i = i₄ ∨ i = i₅ := by
    intro i
    have hri := hres i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hri
    rcases hri with h | h | h
    · rcases hmem₁ i h with h' | h' <;> tauto
    · rcases hmem₂ i h with h' | h' <;> tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hmem₄ i h))))
  have notmem06 : ∀ v : ZMod 7, v ≠ 0 → v ≠ 6 → v ∉ ({0, 6} : Finset (ZMod 7)) := by
    intro v h0 h6 hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact h0 h
    · exact h6 h
  have hnd_u : ∀ (u : ℤ), ¬ (7 : ℤ) ∣ u → ∀ i : Fin 5, ¬ (7 : ℤ) ∣ (u * d i) := by
    intro u hu i hdvd
    rcases hp7.dvd_mul.mp hdvd with h | h
    · exact hu h
    · exact hndvd i h
  -- ── the five-point closer, and its label-permuted form ──
  have close5 : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w → ∀ κ : ZMod 7,
      qz m (w * d i₁) + κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d i₂) + κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d i₃) + 2 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d i₄) + 2 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d i₅) + 4 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro w hw κ h1 h2 h3 h4 h5
    refine lift_shift m (by omega) d w hw κ (fun i => ?_)
    rcases hcover i with rfl | rfl | rfl | rfl | rfl
    · rw [hr₁, mul_one]; exact h1
    · rw [hr₂, mul_one]; exact h2
    · rw [hr₃, mul_comm κ 2]; exact h3
    · rw [hr₄, mul_comm κ 2]; exact h4
    · rw [hr₅, mul_comm κ 4]; exact h5
  have close5' : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w → ∀ (q₁ q₂ p₃ p₄ : Fin 5) (κ : ZMod 7),
      ((q₁ = i₁ ∧ q₂ = i₂) ∨ (q₁ = i₂ ∧ q₂ = i₁)) →
      ((p₃ = i₃ ∧ p₄ = i₄) ∨ (p₃ = i₄ ∧ p₄ = i₃)) →
      qz m (w * d q₁) + κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d q₂) + κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d p₃) + 2 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d p₄) + 2 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * d i₅) + 4 * κ ∉ ({0, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro w hw q₁ q₂ p₃ p₄ κ hq hp h1 h2 h3 h4 h5
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact close5 w hw κ h1 h2 h3 h4 h5
    · exact close5 w hw κ h1 h2 h4 h3 h5
    · exact close5 w hw κ h2 h1 h3 h4 h5
    · exact close5 w hw κ h2 h1 h4 h3 h5
  -- ── BS (15): `ℓ(A₁) ≤ 2` and `ℓ(A₂) ≤ 2`, closed by Lemma 5 ──
  have close_222 : ∀ (w : ℤ), ¬ (7 : ℤ) ∣ w →
      qz m (w * d i₁) - qz m (w * d i₂) ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      qz m (w * d i₃) - qz m (w * d i₄) ∈ ({0, 1, 6} : Finset (ZMod 7)) →
      ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
        qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
    intro w hw hD₁ hD₂
    obtain ⟨a₁, ⟨j₂, hj₂⟩, ⟨j₁, hj₁⟩⟩ := pair_fits2 (qz m (w * d i₂)) (qz m (w * d i₁)) hD₁
    obtain ⟨a₂, ⟨j₄, hj₄⟩, ⟨j₃, hj₃⟩⟩ := pair_fits2 (qz m (w * d i₄)) (qz m (w * d i₃)) hD₂
    obtain ⟨k, hk1, hk2, hk4⟩ := case66_window_choice a₁ a₂ (qz m (w * d i₅))
    refine close5 w hw k ?_ ?_ ?_ ?_ ?_
    · rw [hj₁]; simpa [one_mul] using hk1 j₁
    · rw [hj₂]; simpa [one_mul] using hk1 j₂
    · rw [hj₃]; simpa using hk2 j₃
    · rw [hj₄]; simpa using hk2 j₄
    · simpa using hk4 0
  -- ── from `q(λ·e) ∈ {0,6}` to `ℓ ≤ 2` (one carry of slop) ──
  have band : ∀ (w x y : ℤ), qz m (w * (x - y)) ∈ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * x) - qz m (w * y) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro w x y hq
    obtain ⟨hg, hg'⟩ := shift_06 _ hq
    have hsplit : w * x = w * y + w * (x - y) := by ring
    rcases qz_add_carry m (w * y) (w * (x - y)) with hcc | hcc
    · rw [hsplit, hcc, show qz m (w * y) + qz m (w * (x - y)) - qz m (w * y)
        = qz m (w * (x - y)) from by ring]
      exact hg
    · rw [hsplit, hcc, show qz m (w * y) + qz m (w * (x - y)) + 1 - qz m (w * y)
        = qz m (w * (x - y)) + 1 from by ring]
      exact hg'
  have bandF : ∀ (w x y F : ℤ), (F = x - y ∨ F = y - x) →
      qz m (w * F) ∈ ({0, 6} : Finset (ZMod 7)) →
      qz m (w * x) - qz m (w * y) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro w x y F hor hq
    rcases hor with rfl | rfl
    · exact band w x y hq
    · have hkey := neg016 _ (band w y x hq)
      rwa [neg_sub] at hkey
  have bandhigh : ∀ (w x y : ℤ), (7 : ℤ) ^ (m + 1) ∣ (x - y) →
      qz m (w * x) - qz m (w * y) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    intro w x y hdv
    rw [qz_eq_of_high_dvd m x y w hdv, sub_self]; decide
  -- ── exact 7-adic level extraction ──
  have lev : ∀ X : ℤ, ¬ (7 : ℤ) ^ (m + 1) ∣ X →
      ∃ μ : ℕ, μ ≤ m ∧ (7 : ℤ) ^ μ ∣ X ∧ ¬ (7 : ℤ) ^ (μ + 1) ∣ X := by
    intro X hX
    have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ X := ⟨m, hX⟩
    refine ⟨Nat.find hex, Nat.find_le hX, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [not_not] at hprev
      rwa [show Nat.find hex - 1 + 1 = Nat.find hex from by omega] at hprev
  have lev_lt : ∀ X : ℤ, ¬ (7 : ℤ) ^ m ∣ X →
      ∃ ν : ℕ, ν < m ∧ (7 : ℤ) ^ ν ∣ X ∧ ¬ (7 : ℤ) ^ (ν + 1) ∣ X := by
    intro X hX
    obtain ⟨ν, hνm, hd1, hd2⟩ := lev X (fun hh => hX (dvd_trans (pow_dvd_pow 7 (by omega)) hh))
    rcases lt_or_eq_of_le hνm with h | h
    · exact ⟨ν, h, hd1, hd2⟩
    · exact absurd (h ▸ hd1) hX
  -- **Lemma 2**: any element at a level `≤ m` can be sent to `q = 6`
  have ret6 : ∀ (X : ℤ) (μ : ℕ), μ ≤ m → (7 : ℤ) ^ μ ∣ X → ¬ (7 : ℤ) ^ (μ + 1) ∣ X →
      ∃ w : ℤ, ¬ (7 : ℤ) ∣ w ∧ qz m (w * X) = 6 := by
    intro X μ hμ hd1 hd2
    rcases lt_or_eq_of_le hμ with hlt | heq
    · obtain ⟨k, hqk, hku⟩ := qz_retarget m μ hlt X hd1 hd2 6
      exact ⟨1 + k * 7 ^ (m - μ), hku, hqk⟩
    · rw [heq] at hd1 hd2
      obtain ⟨j, hju, hjq⟩ := qz_retarget_top m X hd1 hd2 6 (by decide)
      exact ⟨j, hju, hjq⟩
  -- ── dispatch on `ν(e₁₂)` versus `ν(e₃₄)` ──
  by_cases hH12 : (7 : ℤ) ^ (m + 1) ∣ (d i₁ - d i₂)
  · by_cases hH34 : (7 : ℤ) ^ (m + 1) ∣ (d i₃ - d i₄)
    · exact close_222 1 (by norm_num) (bandhigh 1 _ _ hH12) (bandhigh 1 _ _ hH34)
    · obtain ⟨μ, hμm, hd1, hd2⟩ := lev _ hH34
      obtain ⟨w, hw, hq⟩ := ret6 _ μ hμm hd1 hd2
      exact close_222 w hw (bandhigh w _ _ hH12) (band w (d i₃) (d i₄) (by rw [hq]; decide))
  · by_cases hH34 : (7 : ℤ) ^ (m + 1) ∣ (d i₃ - d i₄)
    · obtain ⟨μ, hμm, hd1, hd2⟩ := lev _ hH12
      obtain ⟨w, hw, hq⟩ := ret6 _ μ hμm hd1 hd2
      exact close_222 w hw (band w (d i₁) (d i₂) (by rw [hq]; decide)) (bandhigh w _ _ hH34)
    · obtain ⟨μ₁, hμ₁m, hd12, hd12'⟩ := lev _ hH12
      obtain ⟨μ₂, hμ₂m, hd34, hd34'⟩ := lev _ hH34
      rcases lt_trichotomy μ₁ μ₂ with hlt | heqμ | hgt
      · -- **distinct valuations** (BS L747): Lemma 2 on both differences
        obtain ⟨w, hw, hqA, hqB⟩ : ∃ w : ℤ, ¬ (7 : ℤ) ∣ w ∧
            qz m (w * (d i₃ - d i₄)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
            qz m (w * (d i₁ - d i₂)) ∈ ({0, 6} : Finset (ZMod 7)) := by
          rcases lt_or_eq_of_le hμ₂m with h2m | h2m
          · obtain ⟨w, hu, hA, hB⟩ := qz_retarget_two m μ₂ μ₁ h2m hlt _ _ hd34 hd34' hd12 hd12' 0 0
            exact ⟨w, hu, by rw [hA]; decide, by rw [hB]; decide⟩
          · rw [h2m] at hd34 hd34'
            obtain ⟨w, hu, hA, hB⟩ :=
              qz_retarget_two_top m μ₁ (by omega) _ _ hd34 hd34' hd12 hd12' 6 0 (by decide)
            exact ⟨w, hu, by rw [hA]; decide, by rw [hB]; decide⟩
        exact close_222 w hw (band w (d i₁) (d i₂) hqB) (band w (d i₃) (d i₄) hqA)
      · -- **equal valuations** (BS L749) — the substance of §6.6
        rw [← heqμ] at hd34 hd34'
        obtain ⟨c₁, hc₁⟩ := id hd12
        obtain ⟨c₂, hc₂⟩ := id hd34
        have hs₁ : ((c₁ : ℤ) : ZMod 7) ≠ 0 := unit_res hc₁ hd12'
        have hs₂ : ((c₂ : ℤ) : ZMod 7) ≠ 0 := unit_res hc₂ hd34'
        have hres₁ : (((d i₁ - d i₂) / 7 ^ μ₁ : ℤ) : ZMod 7) = ((c₁ : ℤ) : ZMod 7) := res_eq hc₁
        -- BS's "up to renaming we may assume `r(e₁₂), r(e₃₄) ∈ {1,2,4}`": orient `A₂`
        obtain ⟨p₃, p₄, hGperm, hGd, hGd', hGr⟩ :
            ∃ p₃ p₄ : Fin 5,
              ((p₃ = i₃ ∧ p₄ = i₄) ∨ (p₃ = i₄ ∧ p₄ = i₃)) ∧
              (7 : ℤ) ^ μ₁ ∣ (d p₃ - d p₄) ∧ ¬ (7 : ℤ) ^ (μ₁ + 1) ∣ (d p₃ - d p₄) ∧
              ((((d p₃ - d p₄) / 7 ^ μ₁ : ℤ) : ZMod 7) = ((c₁ : ℤ) : ZMod 7) ∨
               (((d p₃ - d p₄) / 7 ^ μ₁ : ℤ) : ZMod 7) = 2 * ((c₁ : ℤ) : ZMod 7) ∨
               (((d p₃ - d p₄) / 7 ^ μ₁ : ℤ) : ZMod 7) = 4 * ((c₁ : ℤ) : ZMod 7)) := by
          have hflip_d : (7 : ℤ) ^ μ₁ ∣ (d i₄ - d i₃) := by
            rw [show d i₄ - d i₃ = -(d i₃ - d i₄) from by ring]; exact hd34.neg_right
          have hflip_d' : ¬ (7 : ℤ) ^ (μ₁ + 1) ∣ (d i₄ - d i₃) := by
            intro hh; refine hd34' ?_
            rw [show d i₄ - d i₃ = -(d i₃ - d i₄) from by ring, dvd_neg] at hh; exact hh
          have hflip_r : (((d i₄ - d i₃) / 7 ^ μ₁ : ℤ) : ZMod 7) = -((c₂ : ℤ) : ZMod 7) := by
            rw [res_eq (show d i₄ - d i₃ = 7 ^ μ₁ * (-c₂) from by linear_combination -hc₂)]
            push_cast; ring
          have hres₂ : (((d i₃ - d i₄) / 7 ^ μ₁ : ℤ) : ZMod 7) = ((c₂ : ℤ) : ZMod 7) := res_eq hc₂
          rcases ratio_normalize _ _ hs₁ hs₂ with h | h | h | h | h | h
          · exact ⟨i₃, i₄, Or.inl ⟨rfl, rfl⟩, hd34, hd34', Or.inl (by rw [hres₂, h])⟩
          · exact ⟨i₃, i₄, Or.inl ⟨rfl, rfl⟩, hd34, hd34', Or.inr (Or.inl (by rw [hres₂, h]))⟩
          · exact ⟨i₃, i₄, Or.inl ⟨rfl, rfl⟩, hd34, hd34', Or.inr (Or.inr (by rw [hres₂, h]))⟩
          · exact ⟨i₄, i₃, Or.inr ⟨rfl, rfl⟩, hflip_d, hflip_d', Or.inl (by rw [hflip_r, h])⟩
          · exact ⟨i₄, i₃, Or.inr ⟨rfl, rfl⟩, hflip_d, hflip_d',
              Or.inr (Or.inl (by rw [hflip_r, h]))⟩
          · exact ⟨i₄, i₃, Or.inr ⟨rfl, rfl⟩, hflip_d, hflip_d',
              Or.inr (Or.inr (by rw [hflip_r, h]))⟩
        have hband34 : ∀ w : ℤ, qz m (w * (d p₃ - d p₄)) ∈ ({0, 6} : Finset (ZMod 7)) →
            qz m (w * d i₃) - qz m (w * d i₄) ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
          intro w hq
          rcases hGperm with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] at hq
          · exact band w (d i₃) (d i₄) hq
          · exact bandF w (d i₃) (d i₄) (d i₄ - d i₃) (Or.inr rfl) hq
        have hrp₃ : (d p₃ : ZMod 7) = 2 := by
          rcases hGperm with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> assumption
        have hrp₄ : (d p₄ : ZMod 7) = 2 := by
          rcases hGperm with ⟨_, h4⟩ | ⟨_, h4⟩ <;> rw [h4] <;> assumption
        rcases hGr with hEq | hR2 | hR4
        · -- **`r(e₁₂) = r(e₃₄)`** (BS L750): `f = e₁₂ − e₃₄` sits above the common level
          have hf_lo : (7 : ℤ) ^ (μ₁ + 1) ∣ ((d i₁ - d i₂) - (d p₃ - d p₄)) := by
            have hfd : (7 : ℤ) ^ μ₁ ∣ ((d i₁ - d i₂) - (d p₃ - d p₄)) := dvd_sub hd12 hGd
            have hz : ((((d i₁ - d i₂) - (d p₃ - d p₄)) / 7 ^ μ₁ : ℤ) : ZMod 7) = 0 := by
              rw [Int.sub_ediv_of_dvd _ hGd]
              push_cast
              rw [hres₁, hEq]; ring
            have h7 : (7 : ℤ) ∣ ((d i₁ - d i₂) - (d p₃ - d p₄)) / 7 ^ μ₁ := by
              rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
            obtain ⟨cq, hcq⟩ := h7
            obtain ⟨wq, hwq⟩ := hfd
            refine ⟨cq, ?_⟩
            have hqq : ((d i₁ - d i₂) - (d p₃ - d p₄)) / 7 ^ μ₁ = wq := by
              rw [hwq]; exact Int.mul_ediv_cancel_left wq (by positivity)
            rw [hwq, show wq = 7 * cq from by rw [← hqq, hcq], pow_succ]; ring
          -- Lemma 2 on `f` and `e₃₄`: `q(f) + q(e₃₄) = 6` with `q(e₃₄) ∈ {0,6}`
          obtain ⟨w, hw, hqG, hsum⟩ : ∃ w : ℤ, ¬ (7 : ℤ) ∣ w ∧
              qz m (w * (d p₃ - d p₄)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
              qz m (w * (d p₃ - d p₄)) + qz m (w * ((d i₁ - d i₂) - (d p₃ - d p₄))) = 6 := by
            by_cases hfhigh : (7 : ℤ) ^ (m + 1) ∣ ((d i₁ - d i₂) - (d p₃ - d p₄))
            · obtain ⟨w, hw, hq⟩ := ret6 _ μ₁ hμ₁m hGd hGd'
              have hf0 : qz m (w * ((d i₁ - d i₂) - (d p₃ - d p₄))) = 0 := by
                rw [qz_eq_of_high_dvd m _ 0 w (by simpa using hfhigh), mul_zero]
                simp [qz]
              exact ⟨w, hw, by rw [hq]; decide, by rw [hq, hf0]; decide⟩
            · obtain ⟨μ', hμ'm, hfd, hfd'⟩ := lev _ hfhigh
              have hμ'gt : μ₁ < μ' := by
                by_contra hcon
                push_neg at hcon
                exact hfd' (dvd_trans (pow_dvd_pow 7 (by omega)) hf_lo)
              rcases lt_or_eq_of_le hμ'm with h'lt | h'eq
              · obtain ⟨w, hu, hA, hB⟩ :=
                  qz_retarget_two m μ' μ₁ h'lt hμ'gt _ _ hfd hfd' hGd hGd' 6 0
                exact ⟨w, hu, by rw [hB]; decide, by rw [hA, hB]; decide⟩
              · rw [h'eq] at hfd hfd'
                obtain ⟨w, hu, hA, hB⟩ :=
                  qz_retarget_two_top m μ₁ (by omega) _ _ hfd hfd' hGd hGd' 6 0 (by decide)
                exact ⟨w, hu, by rw [hB]; decide, by rw [hA, hB]; decide⟩
          refine close_222 w hw ?_ (hband34 w hqG)
          refine band w (d i₁) (d i₂) ?_
          have hsp : w * (d i₁ - d i₂)
              = w * (d p₃ - d p₄) + w * ((d i₁ - d i₂) - (d p₃ - d p₄)) := by ring
          rcases qz_add_carry m (w * (d p₃ - d p₄)) (w * ((d i₁ - d i₂) - (d p₃ - d p₄)))
            with h | h
          · rw [hsp, h, hsum]; decide
          · rw [hsp, h, hsum]; decide
        · -- **`r(e₃₄) = 2·r(e₁₂)`** — that is `r(e₁₂) = 4·r(e₃₄)`, BS's sub-case (b) (L771)
          rcases lt_or_eq_of_le hμ₁m with hμlt | hμeq
          · -- `ν(e₁₂) < m` (BS L751): Lemma 9 (ii), `j = 2`
            obtain ⟨w, hw, hqA, hqB⟩ :=
              ratio2_both06 m μ₁ hμlt (d i₁ - d i₂) (d p₃ - d p₄) hd12 hd12' hGd
                (by rw [hres₁, hR2])
            exact close_222 w hw (band w (d i₁) (d i₂) hqA) (hband34 w hqB)
          · -- `ν(e₁₂) = ν(e₃₄) = m`: the `(b)` frame `q(u·e₁₂) = 1`, `q(u·e₃₄) = 2`
            rw [hμeq] at hd12 hd12' hGd hGd' hres₁ hR2
            obtain ⟨u, hu, hu1⟩ := inv_frame m (d i₁) (d i₂) hd12 hd12'
            have hu1' : ((u : ℤ) : ZMod 7) * ((c₁ : ℤ) : ZMod 7) = 1 := by rw [← hres₁]; exact hu1
            have hu2 : ((u : ℤ) : ZMod 7) * (((d p₃ - d p₄) / 7 ^ m : ℤ) : ZMod 7) = 2 := by
              rw [hR2]; linear_combination 2 * hu1'
            have harcs : ∀ w : ℤ, ((w : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) →
                qz m (w * d i₁) = qz m (w * d i₂) + 1 ∧
                qz m (w * d p₃) = qz m (w * d p₄) + 2 := by
              intro w hw
              refine ⟨?_, ?_⟩
              · rw [qz_top_affine m w (d i₁) (d i₂) hd12, hw, hres₁, hu1']
              · rw [qz_top_affine m w (d p₃) (d p₄) hGd, hw, hu2]
            have hnd2 : ¬ (7 : ℤ) ∣ (u * d i₂) := hnd_u u hu i₂
            have hnd4 : ¬ (7 : ℤ) ∣ (u * d p₄) := hnd_u u hu p₄
            have hrel24 : ((u * d p₄ : ℤ) : ZMod 7) = 2 * ((u * d i₂ : ℤ) : ZMod 7) := by
              push_cast; rw [hr₂, hrp₄]; ring
            -- Lemma 7 on `(d₂,d₄)` with the tight exclusion `ẽ₂₄ ∉ {2,4}`: `ℓ = 3 ≤ 4`
            -- for 7 (i), and `{2,4} ∩ ({2,4}+1) = ∅` for 7 (ii), so every valuation of
            -- `2d₂ − d₄` is covered.
            obtain ⟨lam, hlamu, hlamres, hout⟩ : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
                ((lam : ℤ) : ZMod 7) = 1 ∧
                (2 * qz m (lam * (u * d i₂)) - qz m (lam * (u * d p₄)))
                  ∉ ({2, 4} : Finset (ZMod 7)) := by
              by_cases hT : (7 : ℤ) ^ m ∣ (2 * (u * d i₂) - u * d p₄)
              · exact lemma7_ii m 0 (by omega) (u * d i₂) (u * d p₄) hnd2 hnd4 hrel24
                  ({2, 4} : Finset (ZMod 7)) hT
                  (by rw [inter24_empty]; exact Finset.notMem_empty _)
              · obtain ⟨ν, hνlt, hνd, hνd'⟩ := lev_lt _ hT
                exact lemma7_i m ν hνlt (u * d i₂) (u * d p₄) hnd2 hnd4 hrel24
                  ({2, 4} : Finset (ZMod 7)) fits24 hνd hνd'
            have hwres : ((lam * u : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) := by
              push_cast [hlamres]; ring
            have hwu : ¬ (7 : ℤ) ∣ (lam * u) := by
              intro hdvd; rcases hp7.dvd_mul.mp hdvd with h | h
              · exact hlamu h
              · exact hu h
            obtain ⟨ha1, ha2⟩ := harcs (lam * u) hwres
            have hout' : (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄))
                ∉ ({2, 4} : Finset (ZMod 7)) := by
              rwa [show lam * u * d i₂ = lam * (u * d i₂) from by ring,
                show lam * u * d p₄ = lam * (u * d p₄) from by ring]
            obtain ⟨k, hk123, hkA, hkB, hkC, hkD, hkE⟩ :=
              avoid_66b_Q (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄))
                (2 * qz m (lam * u * d p₄) - qz m (lam * u * d i₅))
                ⟨fun hcon => hout' (by rw [hcon]; decide),
                 fun hcon => hout' (by rw [hcon]; decide)⟩
            refine close5' (lam * u) hwu i₁ i₂ p₃ p₄ (4 * (k - qz m (lam * u * d p₄)))
              (Or.inl ⟨rfl, rfl⟩) hGperm ?_ ?_ ?_ ?_ ?_
            · rw [ha1, show qz m (lam * u * d i₂) + 1 + 4 * (k - qz m (lam * u * d p₄))
                  = 4 * (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) + 4 * k + 1 from by
                linear_combination (-(qz m (lam * u * d i₂))) * seven_eq_zero_z7]
              exact notmem06 _ hkD.1 hkD.2
            · rw [show qz m (lam * u * d i₂) + 4 * (k - qz m (lam * u * d p₄))
                  = 4 * (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) + 4 * k from by
                linear_combination (-(qz m (lam * u * d i₂))) * seven_eq_zero_z7]
              exact notmem06 _ hkC.1 hkC.2
            · rw [ha2, show qz m (lam * u * d p₄) + 2 + 2 * (4 * (k - qz m (lam * u * d p₄)))
                  = k + 2 from by
                linear_combination (k - qz m (lam * u * d p₄)) * seven_eq_zero_z7]
              exact notmem06 _ hkB.1 hkB.2
            · rw [show qz m (lam * u * d p₄) + 2 * (4 * (k - qz m (lam * u * d p₄))) = k from by
                linear_combination (k - qz m (lam * u * d p₄)) * seven_eq_zero_z7]
              exact notmem06 _ hkA.1 hkA.2
            · rw [show qz m (lam * u * d i₅) + 4 * (4 * (k - qz m (lam * u * d p₄)))
                  = 2 * k - (2 * qz m (lam * u * d p₄) - qz m (lam * u * d i₅)) from by
                linear_combination (2 * (k - qz m (lam * u * d p₄))) * seven_eq_zero_z7]
              exact notmem06 _ hkE.1 hkE.2
        · -- **`r(e₃₄) = 4·r(e₁₂)`** — that is `r(e₁₂) = 2·r(e₃₄)`, BS's sub-case (a) (L760)
          rcases lt_or_eq_of_le hμ₁m with hμlt | hμeq
          · -- `ν(e₁₂) < m` (BS L751): Lemma 9 (ii), `j = 2`, with the roles swapped
            obtain ⟨w, hw, hqA, hqB⟩ :=
              ratio2_both06 m μ₁ hμlt (d p₃ - d p₄) (d i₁ - d i₂) hGd hGd' hd12
                (by rw [hres₁, hR4]; linear_combination (-((c₁ : ℤ) : ZMod 7)) * seven_eq_zero_z7)
            exact close_222 w hw (band w (d i₁) (d i₂) hqB) (hband34 w hqA)
          · -- `ν(e₁₂) = ν(e₃₄) = m`: the `(a)` frame `q(u·e₃₄) = 1`, `q(u·e₁₂) = 2`
            rw [hμeq] at hd12 hd12' hGd hGd' hres₁ hR4
            obtain ⟨u, hu, hu1⟩ := inv_frame m (d p₃) (d p₄) hGd hGd'
            have hu4 : ((u : ℤ) : ZMod 7) * (4 * ((c₁ : ℤ) : ZMod 7)) = 1 := by
              rw [← hR4]; exact hu1
            have huc1 : ((u : ℤ) : ZMod 7) * ((c₁ : ℤ) : ZMod 7) = 2 := by
              have key : ∀ a b : ZMod 7, a * (4 * b) = 1 → a * b = 2 := by decide
              exact key _ _ hu4
            have harcs : ∀ w : ℤ, ((w : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) →
                qz m (w * d i₁) = qz m (w * d i₂) + 2 ∧
                qz m (w * d p₃) = qz m (w * d p₄) + 1 := by
              intro w hw
              refine ⟨?_, ?_⟩
              · rw [qz_top_affine m w (d i₁) (d i₂) hd12, hw, hres₁, huc1]
              · rw [qz_top_affine m w (d p₃) (d p₄) hGd, hw, hu1]
            have hnd2 : ¬ (7 : ℤ) ∣ (u * d i₂) := hnd_u u hu i₂
            have hnd4 : ¬ (7 : ℤ) ∣ (u * d p₄) := hnd_u u hu p₄
            have hnd5 : ¬ (7 : ℤ) ∣ (u * d i₅) := hnd_u u hu i₅
            have hrel24 : ((u * d p₄ : ℤ) : ZMod 7) = 2 * ((u * d i₂ : ℤ) : ZMod 7) := by
              push_cast; rw [hr₂, hrp₄]; ring
            have hrel52 : ((u * d i₂ : ℤ) : ZMod 7) = 2 * ((u * d i₅ : ℤ) : ZMod 7) := by
              push_cast; rw [hr₂, hr₅]
              linear_combination (-(((u : ℤ) : ZMod 7))) * seven_eq_zero_z7
            -- the `Λ₀` endgame, once BS's exceptional list (16) has been excluded
            have finish_a : ∀ (lam : ℤ), ¬ (7 : ℤ) ∣ lam → ((lam : ℤ) : ZMod 7) = 1 →
                ¬ (((2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) = 4 ∧
                      (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) = 2) ∨
                   ((2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) = 4 ∧
                      (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) = 4) ∨
                   ((2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) = 5 ∧
                      (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) = 4) ∨
                   ((2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) = 6 ∧
                      (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) = 4) ∨
                   ((2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) = 6 ∧
                      (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) = 6)) →
                ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
                  qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
              intro lam hlamu hlamres hexc
              have hwres : ((lam * u : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) := by
                push_cast [hlamres]; ring
              have hwu : ¬ (7 : ℤ) ∣ (lam * u) := by
                intro hdvd; rcases hp7.dvd_mul.mp hdvd with h | h
                · exact hlamu h
                · exact hu h
              obtain ⟨ha1, ha2⟩ := harcs (lam * u) hwres
              obtain ⟨k, hk123, hkA, hkB, hkC, hkD, hkE⟩ :=
                Case66.avoid_66a (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄))
                  (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) hexc
              refine close5' (lam * u) hwu i₁ i₂ p₃ p₄ (k - qz m (lam * u * d i₂))
                (Or.inl ⟨rfl, rfl⟩) hGperm ?_ ?_ ?_ ?_ ?_
              · rw [ha1, show qz m (lam * u * d i₂) + 2 + (k - qz m (lam * u * d i₂)) = k + 2 from
                  by ring]
                exact notmem06 _ hkB.1 hkB.2
              · rw [show qz m (lam * u * d i₂) + (k - qz m (lam * u * d i₂)) = k from by ring]
                exact notmem06 _ hkA.1 hkA.2
              · rw [ha2, show qz m (lam * u * d p₄) + 1 + 2 * (k - qz m (lam * u * d i₂))
                    = 2 * k - (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) + 1 from by ring]
                exact notmem06 _ hkD.1 hkD.2
              · rw [show qz m (lam * u * d p₄) + 2 * (k - qz m (lam * u * d i₂))
                    = 2 * k - (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄)) from by ring]
                exact notmem06 _ hkC.1 hkC.2
              · rw [show qz m (lam * u * d i₅) + 4 * (k - qz m (lam * u * d i₂))
                    = 4 * (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) + 4 * k from by
                  linear_combination (-(qz m (lam * u * d i₅))) * seven_eq_zero_z7]
                exact notmem06 _ hkE.1 hkE.2
            by_cases hT : (7 : ℤ) ^ m ∣ (2 * d i₂ - d p₄)
            · -- `ν(e₂₄) ≥ m` (BS L767).  `ρ = q(u·e₂₄)` is invariant under every frame
              -- with residue `u`, and the DOUBLING carry pins `ẽ₂₄ ∈ {ρ, ρ−1}` — two
              -- values, not the three a generic `2x−y` carry would give.  Over that pair
              -- the bad `ẽ₅₂` values of (16) are `{4,6}` for `ρ ∈ {0,6}` and `{2,4}`
              -- otherwise: both have `ℓ = 3 ≤ 4` and EMPTY self-overlap, so Lemma 7 (i) /
              -- (ii) on `(d₅,d₂)` applies at every valuation of `2d₅ − d₂`.
              set ρ : ZMod 7 := qz m (u * (2 * d i₂ - d p₄)) with hρ_def
              have hqE : ∀ v : ℤ, ((v : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) →
                  qz m (v * (2 * d i₂ - d p₄)) = ρ := by
                intro v hv
                rw [qz_top_affine m v (2 * d i₂ - d p₄) 0 (by simpa using hT), hρ_def,
                  qz_top_affine m u (2 * d i₂ - d p₄) 0 (by simpa using hT), hv]
                simp only [mul_zero]
              obtain ⟨X, hXfit, hXgap, hXexc⟩ :
                  ∃ X : Finset (ZMod 7), (∃ a, fitsInterval X a 4) ∧
                    (∀ v : ZMod 7, v ∉ X ∩ (X.image (· + 1))) ∧
                    (∀ t24 t25 : ZMod 7, (t24 = ρ ∨ t24 = ρ - 1) → t25 ∉ X →
                      ¬ ((t24 = 4 ∧ t25 = 2) ∨ (t24 = 4 ∧ t25 = 4) ∨ (t24 = 5 ∧ t25 = 4) ∨
                         (t24 = 6 ∧ t25 = 4) ∨ (t24 = 6 ∧ t25 = 6))) := by
                by_cases hρ06 : ρ = 0 ∨ ρ = 6
                · refine ⟨{4, 6}, fits46, ?_, ?_⟩
                  · rw [inter46_empty]; exact fun v => Finset.notMem_empty v
                  · intro t24 t25 h24 h25
                    refine c66a_exc ρ t24 t25 h24 (fun _ => ?_) (fun hc => absurd hρ06 hc)
                    exact ⟨fun hcon => h25 (by rw [hcon]; decide),
                           fun hcon => h25 (by rw [hcon]; decide)⟩
                · refine ⟨{2, 4}, fits24, ?_, ?_⟩
                  · rw [inter24_empty]; exact fun v => Finset.notMem_empty v
                  · intro t24 t25 h24 h25
                    refine c66a_exc ρ t24 t25 h24 (fun hc => absurd hc hρ06) (fun _ => ?_)
                    exact ⟨fun hcon => h25 (by rw [hcon]; decide),
                           fun hcon => h25 (by rw [hcon]; decide)⟩
              obtain ⟨lam, hlamu, hlamres, hout⟩ : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
                  ((lam : ℤ) : ZMod 7) = 1 ∧
                  (2 * qz m (lam * (u * d i₅)) - qz m (lam * (u * d i₂))) ∉ X := by
                by_cases hT2 : (7 : ℤ) ^ m ∣ (2 * (u * d i₅) - u * d i₂)
                · exact lemma7_ii m 0 (by omega) (u * d i₅) (u * d i₂) hnd5 hnd2 hrel52 X hT2
                    (hXgap _)
                · obtain ⟨ν, hνlt, hνd, hνd'⟩ := lev_lt _ hT2
                  exact lemma7_i m ν hνlt (u * d i₅) (u * d i₂) hnd5 hnd2 hrel52 X hXfit hνd hνd'
              have hwres : ((lam * u : ℤ) : ZMod 7) = ((u : ℤ) : ZMod 7) := by
                push_cast [hlamres]; ring
              have ht25 : (2 * qz m (lam * u * d i₅) - qz m (lam * u * d i₂)) ∉ X := by
                rwa [show lam * u * d i₅ = lam * (u * d i₅) from by ring,
                  show lam * u * d i₂ = lam * (u * d i₂) from by ring]
              -- the doubling carry: `ẽ₂₄ = ρ − ε`, `ε ∈ {0,1}`
              have hP : (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄) = ρ) ∨
                  (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄) = ρ - 1) := by
                obtain ⟨tq, htq⟩ : (7 : ℤ) ^ m ∣ (lam * u * (2 * d i₂ - d p₄)) := hT.mul_left _
                have hqt : ((tq : ℤ) : ZMod 7) = ρ := by
                  rw [← hqE (lam * u) hwres]
                  unfold qz
                  rw [htq, Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
                have hsplit : 2 * (lam * u * d i₂) = lam * u * d p₄ + tq * 7 ^ m := by
                  linear_combination htq
                obtain ⟨e2, e3, he2, he3, hd2c, -, -, -⟩ := qz_23_carry m (lam * u * d i₂)
                have hkey : 2 * qz m (lam * u * d i₂) + (e2 : ZMod 7)
                    = qz m (lam * u * d p₄) + ρ := by
                  rw [← hd2c, hsplit, qz_add_mul_pow, hqt]
                interval_cases e2
                · left; push_cast at hkey; linear_combination hkey
                · right; push_cast at hkey; linear_combination hkey
              exact finish_a lam hlamu hlamres (hXexc _ _ hP ht25)
            · -- `ν(e₂₄) < m` (BS L766): Lemma 7 (i) with `X = {4,5,6}` (`ℓ = 3 ≤ 4`)
              have hTu : ¬ (7 : ℤ) ^ m ∣ (2 * (u * d i₂) - u * d p₄) := by
                intro hdv
                refine hT ?_
                rw [show 2 * (u * d i₂) - u * d p₄ = u * (2 * d i₂ - d p₄) from by ring] at hdv
                exact (hp7.irreducible.coprime_pow_of_not_dvd m hu).symm.dvd_of_dvd_mul_left hdv
              obtain ⟨ν, hνlt, hνd, hνd'⟩ := lev_lt _ hTu
              obtain ⟨lam, hlamu, hlamres, hout⟩ :=
                lemma7_i m ν hνlt (u * d i₂) (u * d p₄) hnd2 hnd4 hrel24
                  ({4, 5, 6} : Finset (ZMod 7)) fits456 hνd hνd'
              have hout' : (2 * qz m (lam * u * d i₂) - qz m (lam * u * d p₄))
                  ∉ ({4, 5, 6} : Finset (ZMod 7)) := by
                rwa [show lam * u * d i₂ = lam * (u * d i₂) from by ring,
                  show lam * u * d p₄ = lam * (u * d p₄) from by ring]
              refine finish_a lam hlamu hlamres ?_
              rintro (⟨h24, -⟩ | ⟨h24, -⟩ | ⟨h24, -⟩ | ⟨h24, -⟩ | ⟨h24, -⟩) <;>
                exact hout' (by rw [h24]; decide)
      · -- `ν(e₃₄) < ν(e₁₂)`: mirror of the first branch
        obtain ⟨w, hw, hqA, hqB⟩ : ∃ w : ℤ, ¬ (7 : ℤ) ∣ w ∧
            qz m (w * (d i₁ - d i₂)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
            qz m (w * (d i₃ - d i₄)) ∈ ({0, 6} : Finset (ZMod 7)) := by
          rcases lt_or_eq_of_le hμ₁m with h1m | h1m
          · obtain ⟨w, hu, hA, hB⟩ := qz_retarget_two m μ₁ μ₂ h1m hgt _ _ hd12 hd12' hd34 hd34' 0 0
            exact ⟨w, hu, by rw [hA]; decide, by rw [hB]; decide⟩
          · rw [h1m] at hd12 hd12'
            obtain ⟨w, hu, hA, hB⟩ :=
              qz_retarget_two_top m μ₂ (by omega) _ _ hd12 hd12' hd34 hd34' 6 0 (by decide)
            exact ⟨w, hu, by rw [hA]; decide, by rw [hB]; decide⟩
        exact close_222 w hw (band w (d i₁) (d i₂) hqA) (band w (d i₃) (d i₄) hqB)

end Repr

/-- **§6 representative dispatch (`m ≥ 2`, `A₁` most popular).** After WLOG dilation,
`n₁ ≥ n₂` and `n₁ ≥ n₄`; exactly 7 partitions `(n₁,n₂,n₄)` survive, each routed to
its BS §6 case theorem (`case_61` … `case_66`). The other 14 partitions are killed
by `hpop₂/hpop₄`. -/
theorem five_compress_repr (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
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
(BS §6). `m = 1` is §7 and is handled in the §4 reduction instead, jointly with
the sixth element — see the note above. The Λ₀ bridge is `lambda0_lift`. -/
theorem five_avoid (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hinj : Function.Injective d) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  exact five_compress m hm d hndvd hres hinj

/-- **Master `|A| = 5` theorem (5-element analogue of `four_band`).** Five integers
coprime to 7 admit a unit multiplier `lam` placing every residue `(lam·dᵢ)_N` in
the central band `[7^m, 6·7^m]`. Proved by normalizing to residues `{1,2,4}` and
applying `band_of_qz_ne` to `five_avoid`. The single level-`m` element of `D₇` is
handled separately by `band_top` (any unit `lam` keeps it in band). -/
theorem five_band (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
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


end LRC.OrderSevenN
