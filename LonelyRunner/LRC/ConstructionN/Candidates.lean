import LonelyRunner.LRC.ConstructionN.Band

/-!
# §7.2 and §6.3 of the manuscript, at general `n`

**RING-FENCE.** General-`n` line. `LRC/Construction8/` is the `n = 8` paper's frozen
artefact and is untouched by this module.

`MANUSCRIPT_v5.md` §7.2 states Proposition 7.1 — *if the subject is lonely at any instant of
its window, it is lonely at one of the integer candidates* — and proves it from §1.2's
boundary discipline. That proposition is what makes the integer procedure of §7.1 lossless
against the window, so it is the load-bearing new statement of v5. It is proved here.

`exists_clear_candidate` is its finite core and needs **no topology**: the witness is the
largest zone right endpoint already passed. Everything else follows by instantiating the
zones as the lap zones of the runner's own differences.

`two_sigma_zone_inside` is §6.3's sharpening: a single reading at `s = 2σ` has a zone strictly
inside **every** clear interval of `σ`, so no argument bounding how many gaps one reading can
reach will work. **It needs `3 < n`** — at `n = 3` the two ends coincide — one more threshold
of the kind recorded in `Coords.clear_width_pos`.

Part 7 is not stated here and is not approached.
-/

open Finset

namespace ConstructionN

/-- **Proposition 7.1 (W1), the finite form.**  If some point of `[lo, hi]` lies outside every
open zone, then so does `lo` itself or the right endpoint of one of the zones.  No topology:
the witness is the largest right endpoint that has been passed. -/
theorem exists_clear_candidate {Z : Finset (ℝ × ℝ)} {lo hi x : ℝ}
    (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hx : ∀ p ∈ Z, ¬(p.1 < x ∧ x < p.2)) :
    ∃ y, lo ≤ y ∧ y ≤ hi ∧ (y = lo ∨ ∃ p ∈ Z, p.2 = y) ∧
      (∀ p ∈ Z, ¬(p.1 < y ∧ y < p.2)) := by
  classical
  set T : Finset ℝ :=
    insert lo ((Z.filter (fun p => p.1 < x ∧ lo ≤ p.2)).image Prod.snd) with hT
  have hne : T.Nonempty := ⟨lo, by simp [hT]⟩
  set y := T.max' hne with hy
  have hyT : y ∈ T := T.max'_mem hne
  -- every member of T is at most x
  have hle : ∀ z ∈ T, z ≤ x := by
    intro z hz
    rw [hT] at hz
    rcases mem_insert.mp hz with h | h
    · exact h ▸ hlo
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp h
      obtain ⟨hp1, _⟩ := (mem_filter.mp hp).2
      by_contra hc
      exact hx p (mem_filter.mp hp).1 ⟨hp1, lt_of_not_ge hc⟩
  have hyx : y ≤ x := hle y hyT
  have hloy : lo ≤ y := T.le_max' lo (by simp [hT])
  refine ⟨y, hloy, le_trans hyx hhi, ?_, ?_⟩
  · rcases mem_insert.mp (hT ▸ hyT) with h | h
    · exact Or.inl h
    · obtain ⟨p, hp, hpy⟩ := mem_image.mp h
      exact Or.inr ⟨p, (mem_filter.mp hp).1, hpy⟩
  · rintro p hp ⟨h1, h2⟩
    have hpx : p.1 < x := lt_of_lt_of_le h1 hyx
    have hplo : lo ≤ p.2 := le_trans hloy (le_of_lt h2)
    have : p.2 ∈ T := by
      rw [hT]
      exact mem_insert_of_mem (mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hpx, hplo⟩, rfl⟩)
    exact absurd (T.le_max' _ this) (not_le.mpr h2)

/-- §6.3 sharpened, general `n`: for `s = 2σ` the lap-`(2k+1)` zone sits strictly inside the
`k`-th clear interval of `σ`.  Needs `3 < n`; at `n = 3` the two ends coincide. -/
theorem two_sigma_zone_inside (n : ℕ) (hn : 3 < n) (sig : ℝ) (hsig : 0 < sig) (k : ℕ) :
    ((n : ℝ) * k + 1) / (n * sig) < (2 * (n : ℝ) * k + n - 1) / (2 * n * sig) ∧
    (2 * (n : ℝ) * k + n + 1) / (2 * n * sig) < ((n : ℝ) * k + n - 1) / (n * sig) := by
  have hn3 : (3 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have key : 0 < (n : ℝ) * sig * ((n : ℝ) - 3) :=
    mul_pos (mul_pos hn0 hsig) (by linarith)
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [key]
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [key]

/-- At `n = 8`, `k`-th clear interval `((8k+1)/(8σ), (8k+7)/(8σ))` and the `2σ` zone
`((16k+7)/(16σ), (16k+9)/(16σ))`. -/
theorem n8_two_sigma_zone_inside (sig : ℝ) (hsig : 0 < sig) (k : ℕ) :
    (8 * (k : ℝ) + 1) / (8 * sig) < (16 * (k : ℝ) + 7) / (16 * sig) ∧
    (16 * (k : ℝ) + 9) / (16 * sig) < (8 * (k : ℝ) + 7) / (8 * sig) := by
  constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> nlinarith

/-- The band identity at **any** spine point `u = r/n`, not only `r = 1`. -/
theorem band_identity_spine (n : ℕ) (hn : 0 < n) (s : ℝ) (r : ℕ) :
    ((n : ℝ)⁻¹ ≤ circDist (s * r / n)) ↔ (∀ k : ℤ, 1 ≤ |s * r - (n : ℝ) * k|) :=
  band_identity n hn (s * r)

/-- **The four-candidate row.**  If no reading times `r` lies within `1` of a multiple of `n`,
the spine point `u = r/n` clears every one of them. -/
theorem returns_at_spine {ι : Type*} (n : ℕ) (hn : 0 < n) (s : ι → ℝ) (r : ℕ)
    (h : ∀ j, ∀ k : ℤ, 1 ≤ |s j * r - (n : ℝ) * k|) :
    ∀ j, (n : ℝ)⁻¹ ≤ circDist (s j * ((r : ℝ) / n)) := by
  intro j
  have hrw : s j * ((r : ℝ) / n) = s j * r / n := by ring
  rw [hrw]
  exact (band_identity_spine n hn (s j) r).mpr (h j)

end ConstructionN
