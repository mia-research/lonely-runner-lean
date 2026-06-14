import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Lemma4

/-!
# BHK §5 — Proposition 11 (the long core, pp. 17–40)

This file is the **skeleton** for BHK's Proposition 11, the deepest single
result in *Six Lonely Runners*. The §5 dispatcher (`bhk_s5_main`, PROVED in
`IntLRC_6_BHK_Section5.lean`) reduces the case `{v₁t₀} = 0` to it.

## Statement (integer-speed form)

For integer speeds `w₀ < w₁ < w₂ < w₃ < w₄` with `w₀ + w₁ = w₂`:

* **part 1** (`3 w₀ < w₂`, i.e. `v₁ < 1/3`): some time has every runner
  `≥ 1/6` from the origin (`circDist (wᵢ t) ≥ 1/6`).
* **part 2** (`6 w₀ < w₂`, i.e. `v₁ < 1/6`): additionally `{w₀ t} ∉ (5/12, 7/12)`.

BHK normalise `v₃ = 1`, `v₁ = p/q`, `v₂ = (q-p)/q`; clearing denominators by
`q` gives `w₀ = p`, `w₁ = q - p`, `w₂ = q`, `w₃ = r` (`= q v₄`), `w₄ = s`. So
**`q ↔ w₂`** and **`p ↔ w₀`** in this file.

## Proof architecture (BHK Parts 1–6; Figure 2 road-map)

The proof is *indirect*: assume the runners cover all of `ℝ⁺` (`B₀ = ℝ⁺`,
formalised here as `hcover`/`hcover2`) and derive `False`.

* **Part 1 — Notation.** `B₀ = ℝ⁺`, `v₁ = p/q < 1/3`. For part 2 (`v₁ < 1/6`)
  introduce a *fictional runner 0* of speed `2 v₁`: it sits in `(-1/6, 1/6)`
  exactly when runner 1 is in `(5/12, 7/12)`. Hence `B₀ = B ∪ ½B₁` and
  `{w₀t} ∉ (5/12,7/12)` ⟺ `circDist (2 w₀ t) ≥ 1/6` (given runner 1 safe).
  This is why `bhk_prop11_core2` may be reduced to a 6-runner instance of the
  Part-2–6 machinery (the fictional runner 0 prepended).
* **Part 2 — Preliminary observations** (Lemmas 12–18, Table 1):
  - **Lemma 12**: a 0123-gap `I` satisfies `I ⊆ B₄ ∨ I ⊆ B₅ ∨ (v₄ = r/q ∧
    v₅ = s/q)` (denominators divide `q`; finite-equidistribution of
    `{vⱼ(u+iq)}`).
  - **Lemma 13**: `q ≥ 5` (rule out `v₁ = 1/4`, i.e. `w₂ = 4`, via the explicit
    123-gaps `I₁=[2/3,5/6]`, `I₂=[13/6,44/18]` and Lemma 4).
  - **Lemma 14 / Cor 15**: existence of a 0123-gap of length `≥ 1/3 + ρ`
    (runner 1 near `[1/6+ρv₁, 1/3-ρv₂]` at a half-integer time `t = l + 1/2`).
  - **Cor 16**: `v₄ < 2` (i.e. `w₃ < 2 w₂`).
  - **Lemma 17**: `v₄ = r/q`, `v₅ = s/q` unconditionally (Cor 15 + Lemma 12).
  - **Lemma 18 / Table 1**: sharper `v₄ ≤ 3/2` for `q ≥ 12`, with per-`(p,q)`
    bounds for `q ≤ 17`.
* **Part 3 — Application of the main lemma** ((36)–(50), Figure 3): the set
  `S = {({v₄(l+½)}, {v₁(l+½)})}` avoids the `1/3 × 1/6` rectangle `R`. Apply
  `bhk_main_lemma` / `bhk_corollary_6` (ALREADY PROVED in
  `IntLRC_6_BHK_MainLemma.lean`) to the polygon `P`, leaving a finite list of
  *exceptional generator pairs* `(i,j)` (Table 2, eq. (49)).
* **Part 4 — Pre-processing exceptional groups** (Table 2): express `v₄` in
  terms of `v₁` for each exceptional pair.
* **Part 5 — Cases 5.2.1–5.2.11** (Tables 3–8): every exceptional pair except
  `(1,1)` is shown to intersect `R`, contradiction. Combinatorial casework
  closely parallel to the closed `Section7` Table-9 argument.
* **Part 6 — Case 5.2.12** (`v₄ = (q+p)/q`, the pair `(1,1)`): a separate
  two-part argument (Claim 19, times `t = x₁(k+1/6)`).

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001) R3,
§5 (pp. 17–40).
-/

open MeasureTheory Set

namespace BHK

/-- **BHK §5 Part 1 — the fictional runner 0.** A runner of speed `2 v₁` sits
    within `1/6` of the origin whenever runner 1 is in the window `(5/12, 7/12)`
    (i.e. near the half-way point). This is the inclusion `½B₁ ⊆ B₀` that lets
    the part-2 core (`bhk_prop11_core2`) fold its `{w₀t} ∈ (5/12,7/12)` window
    into an ordinary covering by the six runners `2w₀, w₀, w₁, w₂, w₃, w₄`. -/
lemma bhk_prop11_fict_window {x : ℝ}
    (hx : Int.fract x ∈ Set.Ioo (5 / 12 : ℝ) (7 / 12)) :
    circDist (2 * x) < 1 / 6 := by
  rw [← mem_bhkB_iff]
  refine ⟨2 * ⌊x⌋ + 1, ?_⟩
  obtain ⟨h1, h2⟩ := hx
  have hrw : 2 * x - ((2 * ⌊x⌋ + 1 : ℤ) : ℝ) = 2 * Int.fract x - 1 := by
    rw [Int.fract]; push_cast; ring
  rw [hrw, abs_lt]
  constructor <;> linarith

/-- **No-wrap helper.** If `Int.fract x + b ∈ [0, 1)` then
    `Int.fract (x + b) = Int.fract x + b` — advancing a fractional position by a
    small nonnegative amount that does not cross the next integer. -/
lemma bhk_prop11_fract_add {x b : ℝ} (hlo : 0 ≤ Int.fract x + b)
    (hhi : Int.fract x + b < 1) : Int.fract (x + b) = Int.fract x + b := by
  have hxe : x + b = (⌊x⌋ : ℝ) + (Int.fract x + b) := by rw [Int.fract]; ring
  rw [hxe, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hlo, hhi⟩]

/-- **BHK §5 Part 2 — Lemma 14 (the 0123-gap construction, `ρ = 0`).** At a time
    `t` where runner 3 is at the half-way point (`{w₂t} = 1/2`) and runner 1 is
    in `[1/6, 1/3]`, the forward interval `[t, t + 1/(3 w₂)]` is a 123-gap:
    runners 1, 2, 3 are all `≥ 1/6` from the origin throughout. (Runner 2 sits at
    `1/2 - {w₁t}` since `w₀ + w₁ = w₂`.) This is the geometric input to the
    `block_containment` arguments of Corollaries 15–16 and Lemma 18. -/
lemma bhk_prop11_gap123 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3) :
    ∀ s ∈ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hw0R : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1R : (0 : ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2R : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsmallR : 3 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
  have hw1cast : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by
    have : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    linarith
  -- runner 2 sits at 1/2 - {w₁t}
  have hf1 : Int.fract ((w ⟨1, by omega⟩ : ℝ) * t)
      = 1 / 2 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) := by
    have h0 : (w ⟨1, by omega⟩ : ℝ) * t
        = ((⌊(w ⟨2, by omega⟩ : ℝ) * t⌋ - ⌊(w ⟨0, by omega⟩ : ℝ) * t⌋ : ℤ) : ℝ)
          + (1 / 2 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)) := by
      have e2 := Int.floor_add_fract ((w ⟨2, by omega⟩ : ℝ) * t)
      have e0 := Int.floor_add_fract ((w ⟨0, by omega⟩ : ℝ) * t)
      rw [h3] at e2
      rw [hw1cast, sub_mul, Int.cast_sub]; linarith [e2, e0]
    rw [h0, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  intro s hs i
  obtain ⟨hsl, hsu⟩ := hs
  have hd0 : 0 ≤ s - t := by linarith
  have hdu : s - t ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by linarith
  fin_cases i
  · -- runner 1 (w₀): {w₀s} = {w₀t} + w₀(s-t) ∈ [1/6, 4/9]
    have hbnn : 0 ≤ (w ⟨0, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw0R.le hd0
    have hb : (w ⟨0, by omega⟩ : ℝ) * (s - t) < 1 / 9 := by
      have h1 : (w ⟨0, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hdu hw0R.le
      have h2 : (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) < 1 / 9 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hsmallR]
      linarith
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith) (by linarith)]
    simp only [circDist]; rw [hfs]; exact le_min (by linarith) (by linarith)
  · -- runner 2 (w₁): {w₁s} = (1/2 - {w₀t}) + w₁(s-t) ∈ [1/6, 5/6]
    have hbnn : 0 ≤ (w ⟨1, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw1R.le hd0
    have hb : (w ⟨1, by omega⟩ : ℝ) * (s - t) < 1 / 3 := by
      have h1 : (w ⟨1, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨1, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hdu hw1R.le
      have h2 : (w ⟨1, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) < 1 / 3 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hw0R, hw1cast]
      linarith
    have hfs : Int.fract ((w ⟨1, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨1, by omega⟩ : ℝ) * t) + (w ⟨1, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨1, by omega⟩ : ℝ) * s
            = (w ⟨1, by omega⟩ : ℝ) * t + (w ⟨1, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by rw [hf1]; linarith) (by rw [hf1]; linarith)]
    simp only [circDist]; rw [hfs, hf1]; exact le_min (by linarith) (by linarith)
  · -- runner 3 (w₂): {w₂s} = 1/2 + w₂(s-t) ∈ [1/2, 5/6]
    have hbnn : 0 ≤ (w ⟨2, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw2R.le hd0
    have hb : (w ⟨2, by omega⟩ : ℝ) * (s - t) ≤ 1 / 3 := by
      have h1 : (w ⟨2, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨2, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hdu hw2R.le
      rw [mul_one_div] at h1
      rw [show (w ⟨2, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) = 1 / 3 from by
        field_simp] at h1
      linarith
    have hfs : Int.fract ((w ⟨2, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) + (w ⟨2, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨2, by omega⟩ : ℝ) * s
            = (w ⟨2, by omega⟩ : ℝ) * t + (w ⟨2, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by rw [h3]; linarith) (by rw [h3]; linarith)]
    simp only [circDist]; rw [hfs, h3]; exact le_min (by linarith) (by linarith)

/-- **Proposition 11 — indirect core (part 1).** The `B₀ = ℝ⁺` contradiction:
    for integer speeds `w₀ < ⋯ < w₄` with `w₀ + w₁ = w₂` and `3 w₀ < w₂`, the
    runners cannot cover every time within `1/6` of the origin. This is BHK's
    Parts 1–6 (`v₁ < 1/3`, no fictional runner 0). OPEN — see the module
    docstring for the Part decomposition. -/
theorem bhk_prop11_core (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6) : False := by
  sorry

/-- **Proposition 11 — indirect core (part 2).** As `bhk_prop11_core`, but with
    the stronger `6 w₀ < w₂` (`v₁ < 1/6`) and the fictional-runner-0 window:
    no time is simultaneously runner-safe *and* outside `(5/12, 7/12)` for
    runner 1. Equivalently (Part 1's `B₀ = B ∪ ½B₁`), the six runners
    `2w₀, w₀, w₁, w₂, w₃, w₄` cover every time. OPEN. -/
theorem bhk_prop11_core2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, (∃ i, circDist ((w i : ℝ) * t) < 1 / 6) ∨
        Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ∈ Set.Ioo (5 / 12 : ℝ) (7 / 12)) :
    False := by
  sorry

end BHK
