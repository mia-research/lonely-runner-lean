import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs

/-!
# n = 7 (Barajas–Serra) — the band criterion at an arbitrary modulus

`circDist_ge_of_residue` (in `Defs.lean`) states BS's "good" criterion
`|x|_N ≥ N/7` for `N = 7^(m+1)`. Its proof never uses that `N/7` is a power of
7 — only that `N = 7·P` with `P > 0`. This file records the general form.

That matters for BS §7, which resolves the `|A| = 5, m = 1` case at
`N' = 2·49 = 98`. `98 = 7·14` is not a power of 7, so `circDist_ge_of_residue`
does not apply to it and the §7 argument cannot be transcribed without this
generalization. See `docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md`.
-/

namespace IntLRC7BS

/-- **Band criterion at an arbitrary modulus `N = 7·P`.** A residue in the
inclusive band `[P, 6P]` mod `7P` is at circle distance at least `1/7`.

Generalizes `circDist_ge_of_residue`, which is the case `P = 7^m`. The band is
inclusive at both ends: `P` and `6P` give `|x|_N = N/7` exactly. -/
theorem circDist_ge_of_band (P : ℕ) (hP : 0 < P) (x : ℤ)
    (hlo : (P : ℤ) ≤ x % (7 * P : ℤ))
    (hhi : x % (7 * P : ℤ) ≤ 6 * P) :
    (1 : ℝ) / 7 ≤ circDist ((x : ℝ) / ((7 * P : ℕ) : ℝ)) := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hNRpos : (0 : ℝ) < ((7 * P : ℕ) : ℝ) := by push_cast; linarith
  have hNval : ((7 * P : ℕ) : ℝ) = 7 * (P : ℝ) := by push_cast; ring
  have hRlo' : ((P : ℤ) : ℝ) ≤ ((x % (7 * P : ℤ) : ℤ) : ℝ) := by exact_mod_cast hlo
  have hRhi' : ((x % (7 * P : ℤ) : ℤ) : ℝ) ≤ 6 * (P : ℝ) := by exact_mod_cast hhi
  have hRlo : (P : ℝ) ≤ ((x % (7 * P : ℤ) : ℤ) : ℝ) := by push_cast at hRlo' ⊢; linarith
  have hfract : Int.fract ((x : ℝ) / ((7 * P : ℕ) : ℝ))
      = ((x % (7 * P : ℤ) : ℤ) : ℝ) / ((7 * P : ℕ) : ℝ) := by
    have h := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := x) (n := (7 * P : ℕ))
    rw [h]; push_cast; ring_nf
  unfold circDist
  rw [hfract]
  have hub : ((x % (7 * P : ℤ) : ℤ) : ℝ) / ((7 * P : ℕ) : ℝ) ≤ 6 / 7 := by
    rw [div_le_iff₀ hNRpos, hNval]; nlinarith [hRhi']
  apply le_min
  · rw [le_div_iff₀ hNRpos, hNval]; nlinarith [hRlo]
  · linarith [hub]

/-- `circDist_ge_of_residue` is the `P = 7^m` instance of `circDist_ge_of_band`. -/
theorem circDist_ge_of_residue' (m : ℕ) (x : ℤ)
    (hlo : (7 ^ m : ℤ) ≤ x % (7 ^ (m + 1) : ℤ))
    (hhi : x % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m) :
    (1 : ℝ) / 7 ≤ circDist ((x : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ)) := by
  have hP : 0 < 7 ^ m := by positivity
  have hNeq : (7 * 7 ^ m : ℕ) = 7 ^ (m + 1) := by ring
  have hZ : (7 * ((7 ^ m : ℕ) : ℤ)) = (7 ^ (m + 1) : ℤ) := by push_cast; ring
  have := circDist_ge_of_band (7 ^ m) hP x (by rw [hZ]; exact_mod_cast hlo)
    (by rw [hZ]; exact_mod_cast hhi)
  rwa [hNeq] at this

end IntLRC7BS
