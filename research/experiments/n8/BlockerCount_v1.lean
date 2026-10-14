import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Who can block a candidate

At a candidate `A/sₖ` with `A ≡ 1 (mod 8)`, reading `sᵢ` is *in the way* when
`(sᵢ·A) mod 8sₖ` lies within `sₖ` of `0`. Two readings can never be in the way, so at order `n` the
blocker count at any candidate is at most `n − 3`, not `n − 1`.

* **The generating reading itself.** `(sₖ·A) mod 8sₖ = sₖ` exactly, on the boundary. Checked for
  every `sₖ < 400` and every admissible `A`: 0 blocking cases.
* **The unit reading `1`.** `A mod 8sₖ = A ∈ [sₖ, 7sₖ]`. Checked likewise: 0 cases.

**What is NOT true, recorded so it is not re-derived:** even readings are *not* excluded. Over 3,000
profiles they perform **49.7%** of all blocking — `sᵢ = 4` blocks `u = 9/5`, since `4·9/5 = 7.2` and
`dist(7.2, 8ℤ) = 0.8 < 1`. The cage (`even_offset_caged`) does not apply here: it is a statement
about **grid instants**, and `(8m+1)/sₖ` is a grid instant only when `sₖ ∣ (8m+1)`. The blocking
condition lives mod `8sₖ`; reducing mod `8` discards what decides it. -/

namespace BlockerCount

/-- Reading `sᵢ` is in the way at the candidate `A/sₖ`. -/
def blocks (si A sk : ℤ) : Prop :=
  min ((si * A) % (8 * sk)) (8 * sk - (si * A) % (8 * sk)) < sk

/-- **The generating reading sits exactly on the boundary.** -/
theorem self_residue {sk A : ℤ} (hk : 0 < sk) (q : ℤ) (hA : A = 8 * q + 1) :
    (sk * A) % (8 * sk) = sk := by
  subst hA
  have : sk * (8 * q + 1) = sk + (8 * sk) * q := by ring
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hk.le (by linarith)]

/-- **A reading never blocks its own candidates.** -/
theorem self_never_blocks {sk A : ℤ} (hk : 0 < sk) (q : ℤ) (hA : A = 8 * q + 1) :
    ¬ blocks sk A sk := by
  unfold blocks
  rw [self_residue hk q hA]
  exact not_lt.2 (le_min (le_refl sk) (by linarith))

/-- **The unit reading never blocks any candidate.**  `d_min`'s reading is clear throughout. -/
theorem unit_never_blocks {sk A : ℤ} (hk : 0 < sk) (h1 : sk ≤ A) (h7 : A ≤ 7 * sk) :
    ¬ blocks 1 A sk := by
  unfold blocks
  rw [one_mul, Int.emod_eq_of_lt (by linarith) (by linarith)]
  exact not_lt.2 (le_min h1 (by linarith))

end BlockerCount
