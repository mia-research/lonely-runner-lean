import LonelyRunner.LRC.ConstructionN.Sorted

/-!

**RING-FENCE.**  This tree is the general-`n` line and is **not** the artefact of
`docs/n8/MANUSCRIPT_v1.md`.  That paper cites `LonelyRunner/LRC/Construction8/`, which is
**frozen**: nothing here may change it, and `scripts/n8/gate.sh` gates it independently.
This file began as a copy of its `Construction8` counterpart with the namespace renamed;
divergence from that starting point is the point of the tree, and is recorded per file as
it happens.
# The regular `n`-gon, explicitly

`docs/n8/PROOF_PLAN_v1.md` §2 — the structural heart of the converse of part 6(c).

`Sorted.lean` gives that all cyclic gaps are exactly `1/n`.  This file turns that into the
explicit statement: in sorted order the positions are an arithmetic progression of step
`1/n`.  The induction is one line once the gap hypothesis is in the right shape.

**What this completes and what it does not.**  The chain
*pairwise separations → equal gaps → arithmetic progression* is now closed.  What the
converse of 6(c) still needs on top is the step from "the positions are `α + j/n`" to
"each `x_k` is an integer", where `x_k = k r + e_k r / d`.  That step uses the
normalisation `e₀ = 0`: the position of runner 0 pins `n·α` to an integer, after which
every `x_k` is one.  Formalising it means carrying the common rotation `v₀ t` and the
`frac` relation between a position and `x_k / n`, and is not done here.

Nothing here states or attempts part 7.
-/

namespace ConstructionN

/-- Equal cyclic gaps force the sorted positions into an arithmetic progression of step
`1/n`. -/
theorem sorted_eq_grid {n : ℕ} (p : ℕ → ℝ)
    (hgap : ∀ i, i + 1 < n → p (i + 1) - p i = (n : ℝ)⁻¹)
    (i : ℕ) (hi : i < n) : p i = p 0 + (i : ℝ) * (n : ℝ)⁻¹ := by
  induction i with
  | zero => simp
  | succ k ih =>
    have hk : k < n := by omega
    have hstep := hgap k (by omega)
    have hprev := ih hk
    push_cast
    linarith

/-- The interior cyclic gaps are the consecutive differences, which is the shape
`sorted_eq_grid` wants. -/
theorem cycGap_interior {n : ℕ} (p : ℕ → ℝ) (i : ℕ) (hi : i + 1 < n) :
    cycGap n p ⟨i, by omega⟩ = p (i + 1) - p i := by
  unfold cycGap
  simp [hi]

/-- **The regular `n`-gon.**  `n` positions in `[0,1)`, pairwise at circle distance at
least `1/n`, are in sorted order an arithmetic progression of step `1/n`. -/
theorem grid_of_pairwise {n : ℕ} (hn : 1 < n) (q : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ q k) (h1 : ∀ k, q k < 1)
    (hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (q a - q b))
    (i : ℕ) (hi : i < n) :
    sortedPos q i = sortedPos q 0 + (i : ℝ) * (n : ℝ)⁻¹ := by
  refine sorted_eq_grid (sortedPos q) ?_ i hi
  intro j hj
  rw [← cycGap_interior (sortedPos q) j hj]
  exact equally_spaced_of_pairwise hn q h0 h1 hsep ⟨j, by omega⟩

end ConstructionN
