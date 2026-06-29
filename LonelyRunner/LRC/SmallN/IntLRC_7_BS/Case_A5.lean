import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5b
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas7_9
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
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
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
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 5)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.2 `(4,1,0)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₂`. Labeling via Lemma 10;
`ℓ(A₁) ≤ 4` then Lemma 6(i) `lemma6_510` with `ẽ(d₄,d₅) ∉ {2,3}` from Lemma 7. -/
private theorem case_62a (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.2 `(4,0,1)`** (BS L547). `|A₁| = 4`, `d₅ ∈ A₄`. Labeling via Lemma 10;
`ℓ(A₁) ≤ 4` then Lemma 6(i) `lemma6_501` with `ẽ(d₄,d₅) ∉ {4,6}` from Lemma 7. -/
private theorem case_62b (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 4)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 0)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.3 `(3,1,1)`** (BS L565). `|A₁|=3, |A₂|=|A₄|=1`. Labeling via Lemma 11
(6 subcases + q-tables), Lemma 7(i) securing the `(3,1,1)` `ẽ ∉ {2,4}` carve-out
of Lemma 5. -/
private theorem case_63 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 1)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 1) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.4 `(3,2,0)`** (BS L665). `|A₁|=3, |A₂|=2`. Labeling via Lemma 11 +
Lemma 12; `lemma6_330` endpoint. -/
private theorem case_64 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3)
    (hC₂ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 2)).card = 2)
    (hC₄ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 4)).card = 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := sorry

/-- **Case 6.5 `(3,0,2)`** (BS L698). `|A₁|=3, |A₄|=2`. Labeling via Lemma 11;
`lemma6_402` endpoint (symmetric to 6.4). -/
private theorem case_65 (hm : 2 ≤ m)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 3)
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
    (hC₁ : (univ.filter (fun i : Fin 5 => (d i : ZMod 7) = 1)).card = 2)
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
    | exact case_61 m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_62a m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_62b m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_63 m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_64 m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_65 m d hm hndvd hres hC₁ hC₂ hC₄
    | exact case_66 m d hm hndvd hres hC₁ hC₂ hC₄
    -- `(2,1,2)` ties C₁=C₄ at max; a max-preserving ×2 dilation sends it to the
    -- canonical `(2,2,1)` (BS Case 6.6). new (C₁,C₂,C₄) = old (C₄,C₁,C₂) = (2,2,1).
    | (apply five_compress_relabel m d 2 (by decide)
       exact case_66 m _ hm (mul_ndvd d hndvd 2 (by decide)) (mul_res_mem d hres 2 (Or.inl rfl))
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
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
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
  -- WLOG: dilate to make C₁ the most popular class.
  -- ×2: (n₁,n₂,n₄) → (n₄,n₁,n₂);  ×4: (n₁,n₂,n₄) → (n₂,n₄,n₁)
  by_cases h₁₂ : C₂.card ≤ C₁.card <;> by_cases h₁₄ : C₄.card ≤ C₁.card
  · -- C₁ dominant: no dilation
    exact five_compress_repr m hm d hndvd hres C₁.card C₂.card C₄.card hpart h₁₂ h₁₄ rfl rfl rfl
  · -- C₄ > C₁ ≥ C₂: dilate by 2
    push_neg at h₁₄
    apply five_compress_relabel m d 2 (by decide)
    exact five_compress_repr m hm _ (hndvd_u 2 (by decide)) (hres_u 2 (Or.inl rfl))
      C₄.card C₁.card C₂.card (by omega) (by omega) (by omega)
      (mul_res_perm d hres 2 1 4 (by decide))
      (mul_res_perm d hres 2 2 1 (by decide))
      (mul_res_perm d hres 2 4 2 (by decide))
  · -- C₂ > C₁ ≥ C₄: dilate by 4
    push_neg at h₁₂
    apply five_compress_relabel m d 4 (by decide)
    exact five_compress_repr m hm _ (hndvd_u 4 (by decide)) (hres_u 4 (Or.inr rfl))
      C₂.card C₄.card C₁.card (by omega) (by omega) (by omega)
      (mul_res_perm d hres 4 1 2 (by decide))
      (mul_res_perm d hres 4 2 4 (by decide))
      (mul_res_perm d hres 4 4 1 (by decide))
  · -- Both C₂ > C₁ and C₄ > C₁: pick the larger
    push_neg at h₁₂ h₁₄
    by_cases h₂₄ : C₄.card ≤ C₂.card
    · -- C₂ ≥ C₄ > C₁: dilate by 4
      apply five_compress_relabel m d 4 (by decide)
      exact five_compress_repr m hm _ (hndvd_u 4 (by decide)) (hres_u 4 (Or.inr rfl))
        C₂.card C₄.card C₁.card (by omega) h₂₄ (by omega)
        (mul_res_perm d hres 4 1 2 (by decide))
        (mul_res_perm d hres 4 2 4 (by decide))
        (mul_res_perm d hres 4 4 1 (by decide))
    · -- C₄ > C₂ > C₁: dilate by 2
      push_neg at h₂₄
      apply five_compress_relabel m d 2 (by decide)
      exact five_compress_repr m hm _ (hndvd_u 2 (by decide)) (hres_u 2 (Or.inl rfl))
        C₄.card C₁.card C₂.card (by omega) (by omega) (by omega)
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
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  · exact five_compress m (by omega) d hndvd hres
  · interval_cases m
    · exact five_avoid_m1 d hndvd hres

/-- **Master `|A| = 5` theorem (5-element analogue of `four_band`).** Five integers
coprime to 7 admit a unit multiplier `lam` placing every residue `(lam·dᵢ)_N` in
the central band `[7^m, 6·7^m]`. Proved by normalizing to residues `{1,2,4}` and
applying `band_of_qz_ne` to `five_avoid`. The single level-`m` element of `D₇` is
handled separately by `band_top` (any unit `lam` keeps it in band). -/
theorem five_band (m : ℕ) (hm : 1 ≤ m) (d : Fin 5 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m := by
  set d' : Fin 5 → ℤ := fun i => normalize7 (d i) with hd'_def
  have hd'_ndvd : ∀ i, ¬ (7 : ℤ) ∣ d' i := fun i => normalize7_ndvd _ (hnotdvd i)
  -- It suffices to band the normalized elements (normalize7_band transports back).
  suffices h : ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d' i) % 7 ^ (m + 1) ∧
      (lam * d' i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m by
    obtain ⟨lam, hlam, hband⟩ := h
    exact ⟨lam, hlam, fun i => normalize7_band m lam (d i) (hband i)⟩
  have hd'_res : ∀ i, (d' i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) :=
    fun i => normalize7_res _ (hnotdvd i)
  obtain ⟨lam, hlam, havoid⟩ := five_avoid m hm d' hd'_ndvd hd'_res
  exact ⟨lam, hlam, fun i => band_of_qz_ne m (lam * d' i) (havoid i).1 (havoid i).2⟩

end IntLRC7BS
