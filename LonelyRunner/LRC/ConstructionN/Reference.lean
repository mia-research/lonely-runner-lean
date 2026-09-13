import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!

**RING-FENCE.**  This tree is the general-`n` line and is **not** the artefact of
`docs/n8/MANUSCRIPT_v1.md`.  That paper cites `LonelyRunner/LRC/Construction8/`, which is
**frozen**: nothing here may change it, and `scripts/n8/gate.sh` gates it independently.
This file began as a copy of its `Construction8` counterpart with the namespace renamed;
divergence from that starting point is the point of the tree, and is recorded per file as
it happens.
# Part 6 — the reference instant, and what a deviation does to it

`docs/n8/PROOF_CANDIDATE_v3.md` parts 6(a) and 6(c); `docs/n8/PROOF_PLAN_v1.md` §2
targets 1 and 2, which the handover of 2026-09-13 §7 item 2 orders first after the
cheap batch.

Part 6(b) — the displacement algebra — is `ConstructionN.displacement` in `Parts.lean`.

**What these do not claim.**  Neither says anyone is lonely: that is part 1's two-gap
criterion, and the composition is deliberately left out rather than restating part 1
here.  Neither says the instant is the first.  Nothing here states or attempts part 7.

**Of 6(c), the constructive direction only.**  `survives_of` gives: whole-eighth
displacements with a non-divisible index difference ⟹ the pair is separated.  The
converse — all pairs separated ⟹ the displacements are whole eighths and the map is a
bijection — routes through `gaps_all_eq` and the cyclic gap order, and is not done here.
-/

namespace ConstructionN

/-! ## 6(a) — the AP puts the runners on distinct eighths -/

/-- The AP's pairwise separation at a reference instant reduces to an index gap over `n`. -/
theorem ap_separation (n : ℕ) (v₀ d r : ℝ) (hd : d ≠ 0) (hn : (n : ℝ) ≠ 0) (k k' : ℤ) :
    ((v₀ + (k : ℝ) * d) - (v₀ + (k' : ℝ) * d)) * (r / (n * d))
      = ((k : ℝ) - (k' : ℝ)) * r / n := by
  field_simp
  ring

/-- **Part 6(a).**  At the reference instant `t = r/(n d)` with `r` a unit mod `n`, any two
distinct runners of the AP `A_k = v₀ + k d` are at circle distance at least `1/n` — and the
bound holds for every pair at once, which is why the reference serves every runner
simultaneously and no runner need be held still. -/
theorem ap_reference {n : ℕ} (hn : 0 < n) (v₀ d : ℝ) (hd : d ≠ 0) {r : ℤ}
    (hcop : IsCoprime (n : ℤ) r) {k k' : ℤ} (hne : k ≠ k') (hlt : (k - k').natAbs < n) :
    (n : ℝ)⁻¹ ≤ circDist (((v₀ + (k : ℝ) * d) - (v₀ + (k' : ℝ) * d)) * ((r : ℝ) / (n * d))) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [ap_separation n v₀ d r hd hn' k k']
  have hcast : ((k : ℝ) - (k' : ℝ)) * (r : ℝ) / n = (((k - k') * r : ℤ) : ℝ) / n := by
    push_cast; ring
  rw [hcast]
  exact ap_pair_clear hn (sub_ne_zero.mpr hne) hlt hcop

/-! ## 6(c) — when the reference instant survives a deviation -/

/-- Write `V_k = v₀ + k d + e_k` and suppose each displacement `e_k · r / d` is a whole
number of eighths `w_k`.  Then at `t = r/(n d)` the separation of runners `k` and `k'` is
exactly `(x_k - x_k')/n` with `x_k = k r + w_k`.  This is part 6(b) carried through to a
pair. -/
theorem deviation_separation {n : ℕ} (v₀ d : ℝ) (hd : d ≠ 0) (hn : (n : ℝ) ≠ 0) (r : ℤ)
    (k k' : ℤ) (ek ek' : ℝ) (wk wk' : ℤ)
    (hw : ek * (r : ℝ) / d = (wk : ℝ)) (hw' : ek' * (r : ℝ) / d = (wk' : ℝ)) :
    ((v₀ + (k : ℝ) * d + ek) - (v₀ + (k' : ℝ) * d + ek')) * ((r : ℝ) / (n * d))
      = ((((k * r + wk) - (k' * r + wk')) : ℤ) : ℝ) / n := by
  have h : ((v₀ + (k : ℝ) * d + ek) - (v₀ + (k' : ℝ) * d + ek')) * ((r : ℝ) / (n * d))
      = (((k : ℝ) - k') * r + (ek * r / d - ek' * r / d)) / n := by
    field_simp
    ring
  rw [h, hw, hw']
  push_cast
  ring

/-- **Part 6(c), the constructive direction.**  Whole-eighth displacements with
`n ∤ (x_k - x_k')` put the pair at distance at least `1/n`.  The converse is not proved
here; see the module docstring. -/
theorem survives_of {n : ℕ} (hn : 0 < n) (v₀ d : ℝ) (hd : d ≠ 0) (r : ℤ)
    (k k' : ℤ) (ek ek' : ℝ) (wk wk' : ℤ)
    (hw : ek * (r : ℝ) / d = (wk : ℝ)) (hw' : ek' * (r : ℝ) / d = (wk' : ℝ))
    (hdvd : ¬ ((n : ℤ) ∣ ((k * r + wk) - (k' * r + wk')))) :
    (n : ℝ)⁻¹ ≤ circDist (((v₀ + (k : ℝ) * d + ek) - (v₀ + (k' : ℝ) * d + ek'))
                            * ((r : ℝ) / (n * d))) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [deviation_separation v₀ d hd hn' r k k' ek ek' wk wk' hw hw']
  exact circDist_int_div hn hdvd

end ConstructionN
