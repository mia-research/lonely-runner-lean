import LonelyRunner.LRC.Cascade.Flanks

/-!
# The cascade as a residue walk, and runner 2 at runner 3's openings in BHK §6

Observed exactly on 17,135 order-six residual sets (`six_later_moves_v1.out`, `six_s6_by_c_v1.out`).

* `later_move_blocking`: at an opening `(k + 1/n)/x` of a whole-number flank `x`, a whole-number
  difference `d` is in the way exactly when its residue `d(nk+1) mod nx` leaves the band `[x, (n−1)x]`.
  (Negation of `Flanks.clear_at_int_flank_iff_emod`.)
* `s6_runner2_at_runner3`: with `v₂ = (c−1)D`, `v₃ = cD` (BHK §6), runner 2 is clear at runner 3's opening
  `k < c` exactly when `2c − 1 ≤ 6k`.
-/

namespace CascadeResidueWalk

open MomentIterationN

theorem later_move_blocking {n : ℕ} [Fact (2 ≤ n)] {d x : ℤ} (hx : 0 < x) (k : ℕ) :
    inWay n (d : ℝ) (Flanks.flankOpening n (x : ℝ) k) ↔
      ¬ (x ≤ d * ((n : ℤ) * k + 1) % ((n : ℤ) * x) ∧
          d * ((n : ℤ) * k + 1) % ((n : ℤ) * x) ≤ (n : ℤ) * x - x) := by
  unfold inWay
  rw [← Flanks.clear_at_int_flank_iff_emod hx k, not_le]

/-- Runner 2 at runner 3's openings, BHK §6. -/
theorem s6_runner2_at_runner3 {c k D : ℤ} (hc : 2 ≤ c) (hk0 : 0 ≤ k) (hk : k < c) (hD : 0 < D) :
    (c * D ≤ ((c - 1) * D) * (6 * k + 1) % (6 * (c * D)) ∧
      ((c - 1) * D) * (6 * k + 1) % (6 * (c * D)) ≤ 6 * (c * D) - c * D) ↔ 2 * c - 1 ≤ 6 * k := by
  have hM : 0 < 6 * (c * D) := by positivity
  have hsplit : ((c - 1) * D) * (6 * k + 1) = D * (c - 1 - 6 * k) + 6 * (c * D) * k := by ring
  rw [hsplit, Int.add_mul_emod_self_left]
  by_cases hsmall : 6 * k ≤ c - 1
  · -- residue D·(c−1−6k) < c·D: blocked; and 2c − 1 > 6k
    have h0 : 0 ≤ D * (c - 1 - 6 * k) := by nlinarith
    have hlt : D * (c - 1 - 6 * k) < 6 * (c * D) := by nlinarith
    rw [Int.emod_eq_of_lt h0 hlt]
    constructor
    · rintro ⟨h1, -⟩; nlinarith
    · intro h; omega
  · -- residue D·(7c−1−6k)
    push Not at hsmall
    have hr : D * (c - 1 - 6 * k) % (6 * (c * D)) = D * (7 * c - 1 - 6 * k) := by
      have e : D * (c - 1 - 6 * k) = D * (7 * c - 1 - 6 * k) + 6 * (c * D) * (-1) := by ring
      rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by nlinarith) (by nlinarith)]
    rw [hr]
    constructor
    · rintro ⟨-, h2⟩
      by_contra h; push Not at h
      nlinarith
    · intro h; constructor <;> nlinarith

end CascadeResidueWalk

#print axioms CascadeResidueWalk.later_move_blocking
#print axioms CascadeResidueWalk.s6_runner2_at_runner3
