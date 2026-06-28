import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5b
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas

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

/-- **§6/§7 core (q-avoidance form).** Five integers coprime to 7, already
normalized to residues `{1,2,4}`, admit a unit multiplier `lam` sending every
arc index `q(lam·dᵢ)` outside `{0,6}`. This is the entire `|A|=5` case analysis
(BS §6 for `m ≥ 2`, §7 for `m = 1`). **Open.** -/
theorem five_avoid (m : ℕ) (hm : 1 ≤ m) (d : Fin 5 → ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  sorry

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
