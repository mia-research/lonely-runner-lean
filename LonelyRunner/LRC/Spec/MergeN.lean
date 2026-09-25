import LonelyRunner.LRC.Spec.FastRunnerN
import LonelyRunner.LRC.Cascade.Together

/-!
# The merge rule: a runner sitting with another costs nothing

2026-09-24.  Isolation is a two-neighbour condition (Theorem 1), so a runner that sits close to
another adds no new obstacle.  If a set is clear at the threshold of the order below, `1/(n−1)`,
and one more runner `y` sits within `1/(n−1) − 1/n` of a member `s` of the set, then `y` is at
least `1/n` from the subject: the set with `y` is clear at `1/n`.  Four runners with a merged
pair are three runners, which the order below already settles with room to spare.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.SpecN

open MomentIterationN

/-- **The merge rule.**  If every member of `S` is clear at `1/(n − 1)` and `y` sits within
`1/(n − 1) − 1/n` of a member `s`, then every member of `S` together with `y` is clear at `1/n`. -/
theorem clear_of_merge {n : ℕ} (hn : 2 ≤ n) {S : Finset ℝ} {t y s : ℝ} (hs : s ∈ S)
    (hS : ∀ d ∈ S, ((n : ℝ) - 1)⁻¹ ≤ circDist (d * t))
    (hy : circDist ((y - s) * t) ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) :
    ∀ d ∈ insert y S, (n : ℝ)⁻¹ ≤ circDist (d * t) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlt : (n : ℝ)⁻¹ ≤ ((n : ℝ) - 1)⁻¹ := inv_anti₀ hn1 (by linarith)
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hdS
  · -- the merged runner: `circDist (s t) ≤ circDist (d t) + circDist ((d − s) t)`
    have htri := Together.circDist_sub_le (d * t) ((d - s) * t)
    rw [show d * t - (d - s) * t = s * t by ring] at htri
    have := hS s hs
    linarith
  · exact le_trans hlt (hS d hdS)

end LRC.SpecN
