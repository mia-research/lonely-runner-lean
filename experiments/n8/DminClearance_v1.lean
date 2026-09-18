import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # When does a subject clear at its own `d_min`, with no cascade at all?

Audit finding.  I reported "63.8% / 66.7% clear at scale `d_min` with zero cascade moves" several
times without ever giving a criterion — and separately refuted a parallel session's proposed
theorem for exactly this case (`FILTER_ASSESSMENT_AND_CROSSCHECK_v1` B.3) without supplying the
correct one.  A deterministic arithmetic fact was left as a percentage.  Here it is.

At scale `D = d_min` the reading of disparity `d` is `s = d/d_min`.  In reduced units `d = a·g`
and `d_min = c·g`, so `s = a/c` and the blocking condition `|s − 8M| < 1` becomes `|a − 8Mc| < c`.
Hence, with the threshold counting as clear:

> **clear at `d_min`  ⟺  every disparity satisfies  `c ≤ a mod 8c ≤ 7c`**,  where `c = d_min/g`.

Verified against the cascade on 32,000 subject-instances: **32,000 / 32,000**
(`dmin_criterion_v1.py`).  The parallel session's predicate ("unique residue", which is the
criterion at scale `g`, not at scale `d_min`) agrees only 57.2%.

Sanity: `a = c` (the minimum itself) gives `c mod 8c = c`, on the boundary, clear — as it must be,
since `d_min` is what defines the scale. -/

namespace DminClearance

/-- The blocking condition, reduced to the residue.  With `0 ≤ r < 8c`, some multiple of `8c` lands
within `c` of `r` exactly when `r` is in one of the two end zones. -/
theorem bad_iff {c r : ℤ} (hc : 0 < c) (h0 : 0 ≤ r) (h1 : r < 8 * c) :
    (∃ k : ℤ, |8 * c * k + r| < c) ↔ (r < c ∨ 7 * c < r) := by
  constructor
  · rintro ⟨k, hk⟩
    rw [abs_lt] at hk
    obtain ⟨hlo, hhi⟩ := hk
    rcases lt_trichotomy k 0 with h | h | h
    · right
      have hk1 : k ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by linarith : (0:ℤ) < 8 * c))]
    · subst h; left; simpa using hhi
    · exfalso
      have hk1 : 1 ≤ k := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by linarith : (0:ℤ) < 8 * c))]
  · rintro (h | h)
    · exact ⟨0, by rw [abs_lt]; constructor <;> omega⟩
    · exact ⟨-1, by rw [abs_lt]; constructor <;> nlinarith⟩

/-- **The criterion.**  Disparity `a` (in reduced units) leaves the subject clear at scale `c`
exactly when `a`'s residue mod `8c` lies in the central band `[c, 7c]`. -/
theorem clear_iff {a c : ℤ} (hc : 0 < c) :
    (∀ M : ℤ, c ≤ |a - 8 * M * c|) ↔ (c ≤ a % (8 * c) ∧ a % (8 * c) ≤ 7 * c) := by
  have h8c : (0:ℤ) < 8 * c := by linarith
  set r := a % (8 * c) with hr
  have h0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have h1 : r < 8 * c := Int.emod_lt_of_pos _ h8c
  have hsplit : 8 * c * (a / (8 * c)) + r = a := Int.mul_ediv_add_emod a (8 * c)
  have hbij : (∃ M : ℤ, |a - 8 * M * c| < c) ↔ (∃ k : ℤ, |8 * c * k + r| < c) := by
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨a / (8 * c) - M, ?_⟩
      have : 8 * c * (a / (8 * c) - M) + r = a - 8 * M * c := by linarith [hsplit]
      rwa [this]
    · rintro ⟨k, hk⟩
      refine ⟨a / (8 * c) - k, ?_⟩
      have : a - 8 * (a / (8 * c) - k) * c = 8 * c * k + r := by linarith [hsplit]
      rwa [this]
  have hbad := (hbij.trans (bad_iff hc h0 h1))
  constructor
  · intro h
    by_contra hcon
    have : r < c ∨ 7 * c < r := by omega
    obtain ⟨M, hM⟩ := hbad.mpr this
    exact absurd (h M) (by omega)
  · rintro ⟨hlo, hhi⟩ M
    by_contra hM
    have : r < c ∨ 7 * c < r := hbad.mp ⟨M, by omega⟩
    omega

end DminClearance
