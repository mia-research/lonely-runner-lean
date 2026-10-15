import LonelyRunner.LRC.Spec.OrderSixN

/-!
# Order six at a divisible largest flank: residue pinning and the cell reduction

Framework objects only: the free-flank shift condition of `LRC.OrderSixN.FreeFlank` and the
residue criterion at an integer flank. No BHK lemma is used.

* `all_shifts_blocked_iff` — the six coarse shifts are all blocked by a residue set `R ⊆ {1,…,5}`
  exactly when `1, 3, 5 ∈ R` and `2 ∈ R ∨ 4 ∈ R` (finite check).
* `cell_criterion` — at the flank `e = 6E`, for `d = 6q + s` with `1 ≤ s ≤ 5` and `d < e`, and the
  opening `j = u·E + i` (`u < 6`, `i < E`): `d` reads in `[e, 5e]` modulo `6e` exactly when the cell
  `(a + s·u) mod 6` lies in `{1,2,3,4}`, where `a = ((d·i + q) mod 6E) / E`.
-/

namespace SixCells

/-- Residue `r` blocks coarse shift `k` when `r·k mod 6 ∈ {0, 5}`. -/
def Blocks (r k : ℕ) : Prop := (r * k) % 6 = 0 ∨ (r * k) % 6 = 5

instance (r k : ℕ) : Decidable (Blocks r k) := by unfold Blocks; infer_instance

/-- **Residue pinning.** Over residue sets inside `{1,…,5}`, every shift `k < 6` is blocked exactly
when `1, 3, 5` are present together with `2` or `4`. -/
theorem all_shifts_blocked_iff :
    ∀ R ∈ (Finset.Icc 1 5).powerset,
      (∀ k < 6, ∃ r ∈ R, Blocks r k) ↔ (1 ∈ R ∧ 3 ∈ R ∧ 5 ∈ R ∧ (2 ∈ R ∨ 4 ∈ R)) := by
  decide

/-- Uniqueness of the remainder: `n = m·K + r`, `r < m` gives `n % m = r`. -/
theorem mod_of_decomp {n m K r : ℕ} (h : n = m * K + r) (hr : r < m) : n % m = r := by
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- **The cell criterion** (natural-number form). -/
theorem cell_criterion {E q s u i d j : ℕ} (hE : 0 < E) (hs1 : 1 ≤ s) (hs5 : s ≤ 5)
    (hdq : d = 6 * q + s) (hd : d < 6 * E) (hu : u < 6) (hi : i < E) (hj : j = u * E + i) :
    (6 * E ≤ (d * (6 * j + 1)) % (36 * E) ∧ (d * (6 * j + 1)) % (36 * E) ≤ 30 * E) ↔
      (1 ≤ ((d * i + q) % (6 * E) / E + s * u) % 6 ∧
        ((d * i + q) % (6 * E) / E + s * u) % 6 ≤ 4) := by
  -- names for the pieces
  obtain ⟨y, hy⟩ : ∃ y, y = (d * i + q) % (6 * E) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = y / E := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = y % E := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (a + s * u) % 6 := ⟨_, rfl⟩
  rw [← hy, ← ha, ← hc]
  have hbE : b < E := hb ▸ Nat.mod_lt _ hE
  have hc6 : c < 6 := hc ▸ Nat.mod_lt _ (by norm_num)
  have hyab : y = E * a + b := by rw [ha, hb]; exact (Nat.div_add_mod y E).symm
  have hyQ : d * i + q = 6 * E * ((d * i + q) / (6 * E)) + y := by
    rw [hy]; exact (Nat.div_add_mod _ _).symm
  have hsu : s * u = 6 * ((s * u) / 6) + (s * u) % 6 := (Nat.div_add_mod _ _).symm
  have hcdef : a + s * u = 6 * ((a + s * u) / 6) + c := by rw [hc]; exact (Nat.div_add_mod _ _).symm
  -- the residue: d·(6j+1) mod 36E = 6·(E·c + b) + s
  have hres : (d * (6 * j + 1)) % (36 * E) = 6 * (E * c + b) + s := by
    apply mod_of_decomp (K := q * u + (d * i + q) / (6 * E) + (a + s * u) / 6)
    · subst hdq hj
      -- 6·(d·j + q) + s with d·j = d·u·E + d·i, d·u = 6qu + su
      have e1 : (6 * q + s) * (6 * (u * E + i) + 1)
          = 6 * (E * (6 * (q * u)) + E * (s * u) + ((6 * q + s) * i + q)) + s := by ring
      rw [e1]
      -- substitute the decompositions (linear once the quotients are atoms)
      generalize ((6 * q + s) * i + q) / (6 * E) = Q at hyQ ⊢
      generalize (a + s * u) / 6 = W at hcdef ⊢
      zify at hyQ hyab hcdef ⊢
      linear_combination 6 * hyQ + 6 * hyab + 6 * (E : ℤ) * hcdef
    · nlinarith
  rw [hres]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    · by_contra hcon
      have hc5 : c = 5 := by omega
      rw [hc5] at h2; omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith

end SixCells

#print axioms SixCells.all_shifts_blocked_iff
#print axioms SixCells.cell_criterion
