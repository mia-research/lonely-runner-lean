import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Lemma4
import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_MainLemma

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

/-- `circDist` is invariant under integer shifts. -/
lemma bhk_prop11_circDist_add_int (x : ℝ) (n : ℤ) :
    circDist (x + (n : ℝ)) = circDist x := by
  unfold circDist; rw [Int.fract_add_intCast]

/-- **BHK §5 Part 2 — periodicity (the engine of Lemma 12).** A runner whose
    speed `v` is divisible by `g` has period `1/g`: its circle position repeats
    after `1/g`. With `g = gcd(w₀, w₂)` this applies to runners 1, 2, 3 (since
    `g ∣ w₀, w₁, w₂`), so every 0123-gap `I` translates to a 0123-gap `I + 1/g`
    — BHK's "`I + iq` is again a 0123-gap". -/
lemma bhk_prop11_period (v g : ℕ) (hg : 0 < g) (hdvd : g ∣ v) (t : ℝ) :
    circDist ((v : ℝ) * (t + 1 / g)) = circDist ((v : ℝ) * t) := by
  obtain ⟨c, hc⟩ := hdvd
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have heq : (v : ℝ) * (t + 1 / (g : ℝ)) = (v : ℝ) * t + ((c : ℤ) : ℝ) := by
    rw [hc]; push_cast; field_simp
  rw [heq, bhk_prop11_circDist_add_int]

/-- **0123-gap translation.** If `g` divides the speeds of runners 1, 2, 3 then
    any 123-gap `[a, b]` translates to the 123-gap `[a + 1/g, b + 1/g]`. With
    `g = gcd(w₀, w₂)` this is BHK's "`I + iq` is again a 0123-gap". -/
lemma bhk_prop11_gap123_translate (w : Fin 5 → ℕ) (g : ℕ) (hg : 0 < g)
    (hdvd : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s)) :
    ∀ s ∈ Set.Icc (a + 1 / g) (b + 1 / g), ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
  intro s hs i
  obtain ⟨hsl, hsu⟩ := hs
  have hkey := hgap (s - 1 / g) ⟨by linarith, by linarith⟩ i
  have hper := bhk_prop11_period (w ⟨i.val, by omega⟩) g hg (hdvd i) (s - 1 / g)
  rw [show s - 1 / (g : ℝ) + 1 / (g : ℝ) = s from by ring] at hper
  rw [hper]; exact hkey

/-- **A long interval is in no single runner block.** A closed interval longer
    than `1/(3 wᵢ)` (the width of one `Bᵢ` block) cannot be contained in
    `unsafeOf wᵢ`: `block_containment` would force its length `< 1/(3 wᵢ)`. -/
lemma bhk_prop11_not_subset_unsafeOf (w : Fin 5 → ℕ) (i : Fin 5) (hi : 0 < w i)
    {a b : ℝ} (hab : a ≤ b) (hlong : 1 / (3 * (w i : ℝ)) < b - a) :
    ¬ Set.Icc a b ⊆ unsafeOf w i := by
  intro hsub
  have hwi : (0 : ℝ) < (w i : ℝ) := by exact_mod_cast hi
  obtain ⟨k, hk1, hk2⟩ := block_containment w i hi a b hab hsub
  have hkey : (w i : ℝ) * (b - a) < 1 / 3 := by rw [mul_sub]; linarith
  rw [div_lt_iff₀ (by positivity)] at hlong
  nlinarith [hkey, hlong, hwi]

/-- `unsafeOf` is open (preimage of the open set `bhkB` under `t ↦ wᵢ·t`). -/
lemma bhk_prop11_isOpen_unsafeOf (w : Fin 5 → ℕ) (i : Fin 5) :
    IsOpen (unsafeOf w i) := by
  have hbo : IsOpen bhkB := by
    rw [bhkB_eq_iUnion_Ioo]; exact isOpen_iUnion fun _ => isOpen_Ioo
  exact hbo.preimage (continuous_const.mul continuous_id)

/-- **BHK §5 Part 2 — the overlap point of Lemma 12.** A 123-gap `[a,b]` that is
    covered by runners 4, 5 but contained in *neither* `B₄` nor `B₅` must, being
    connected, contain a time `u` covered by *both* runners 4 and 5. (This is
    BHK's `u ∈ I ∩ B₄ ∩ B₅`, the start of the equidistribution argument.) -/
lemma bhk_prop11_overlap (w : Fin 5 → ℕ) {a b : ℝ}
    (hsub : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩)
    (hn4 : ¬ Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩)
    (hn5 : ¬ Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩) :
    ∃ u ∈ Set.Icc a b, u ∈ unsafeOf w ⟨3, by omega⟩ ∧ u ∈ unsafeOf w ⟨4, by omega⟩ := by
  have hne4 : (Set.Icc a b ∩ unsafeOf w ⟨3, by omega⟩).Nonempty := by
    rw [Set.not_subset] at hn5; obtain ⟨p, hpJ, hpn5⟩ := hn5
    exact ⟨p, hpJ, (hsub hpJ).resolve_right hpn5⟩
  have hne5 : (Set.Icc a b ∩ unsafeOf w ⟨4, by omega⟩).Nonempty := by
    rw [Set.not_subset] at hn4; obtain ⟨p, hpJ, hpn4⟩ := hn4
    exact ⟨p, hpJ, (hsub hpJ).resolve_left hpn4⟩
  obtain ⟨u, huJ, hu4, hu5⟩ :=
    isPreconnected_Icc _ _ (bhk_prop11_isOpen_unsafeOf w _)
      (bhk_prop11_isOpen_unsafeOf w _) hsub hne4 hne5
  exact ⟨u, huJ, hu4, hu5⟩

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

/-- **Covering of a 123-gap.** Under the indirect covering assumption, every
    123-gap (runners 1, 2, 3 safe) must be covered by runners 4 and 5. -/
lemma bhk_prop11_gap_covered (w : Fin 5 → ℕ)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s)) :
    Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩ := by
  intro s hs
  obtain ⟨i, hi⟩ := hcover s
  fin_cases i
  · exact absurd hi (not_lt.mpr (hgap s hs 0))
  · exact absurd hi (not_lt.mpr (hgap s hs 1))
  · exact absurd hi (not_lt.mpr (hgap s hs 2))
  · exact Or.inl ((mem_unsafeOf_iff w _ s).mpr hi)
  · exact Or.inr ((mem_unsafeOf_iff w _ s).mpr hi)

/-- **Residue hit (the equidistribution kernel).** For coprime `a, b` with
    `3a < b` and `b ≥ 5`, some odd-multiple time `(2m+1)/(2b)` puts `a` in the
    window `[1/6, 1/3]` mod 1. Witness: `k = (b - 3a + 5)/6` (so `b ≤ 6k+3a < 2b`)
    and `m` solving `a m ≡ k (mod b)` via the `ZMod` unit inverse of `a`. -/
lemma bhk_prop11_residue_hit (a b : ℕ) (ha : 0 < a) (h3a : 3 * a < b) (hb5 : 5 ≤ b)
    (hcop : Nat.Coprime a b) :
    ∃ m : ℕ, Int.fract ((a : ℝ) * ((2 * (m : ℝ) + 1) / (2 * b)))
      ∈ Set.Icc (1 / 6 : ℝ) (1 / 3) := by
  have hb0 : 0 < b := by omega
  haveI : NeZero b := ⟨by omega⟩
  set k : ℕ := (b - 3 * a + 5) / 6 with hk
  have hklo : b ≤ 6 * k + 3 * a := by omega
  have hkhi : 6 * k + 3 * a < b + 6 := by omega
  have hkn : k < b := by omega
  obtain ⟨m, hm_mod⟩ : ∃ m : ℕ, (a * m) % b = k % b := by
    set u := ZMod.unitOfCoprime a hcop with hu
    refine ⟨(((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (k : ZMod b)).val, ?_⟩
    have hcast : ((a * (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (k : ZMod b)).val : ℕ) : ZMod b)
        = ((k : ℕ) : ZMod b) := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, ← ZMod.coe_unitOfCoprime a hcop, ← hu,
        ← mul_assoc]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hmk : (a * m) % b = k := by rw [hm_mod, Nat.mod_eq_of_lt hkn]
  set j : ℕ := (a * m) / b with hj
  have hamj : a * m = b * j + k := by
    rw [hj, ← hmk]; exact (Nat.div_add_mod (a * m) b).symm
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
  have hcast2b : (6 : ℝ) * k + 3 * a < 2 * b := by
    have : 6 * k + 3 * a < 2 * b := by omega
    exact_mod_cast this
  have hcastlo : (b : ℝ) ≤ 6 * k + 3 * a := by exact_mod_cast hklo
  refine ⟨m, Set.mem_Icc.mpr ?_⟩
  have hfr : Int.fract ((a : ℝ) * ((2 * (m : ℝ) + 1) / (2 * b)))
      = (2 * (k : ℝ) + a) / (2 * b) := by
    have hamR : (a : ℝ) * (m : ℝ) = (b : ℝ) * j + k := by exact_mod_cast hamj
    have hae : (a : ℝ) * (2 * (m : ℝ) + 1) = 2 * b * j + (2 * k + a) := by
      linear_combination 2 * hamR
    have hstep : (a : ℝ) * ((2 * (m : ℝ) + 1) / (2 * b))
        = (j : ℝ) + (2 * (k : ℝ) + a) / (2 * b) := by
      rw [← mul_div_assoc, hae]; field_simp
    rw [hstep, show (j : ℝ) = ((j : ℤ) : ℝ) from by push_cast; ring,
      Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by positivity, ?_⟩]
    rw [div_lt_one (by positivity)]; linarith
  rw [hfr]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [div_le_iff₀ (by positivity)]; linarith

/-- **BHK §5 Part 2 — Corollary 15 (witness half-integer time).** Let
    `q = w₂ / gcd(w₀, w₂)` be the reduced denominator of `v₁ = w₀/w₂`. If `q ≥ 5`
    there is a time `t` at which runner 3 sits at the half-way point
    (`{w₂t} = 1/2`) and runner 1 lies in `[1/6, 1/3]`. The `{w₀ t_m}` over the
    candidate times `t_m = (2m+1)/(2w₂)` form `q` points spaced `1/q`; for
    `q ≥ 5` (`q = 5` forces `a' = 1`, hitting `3/10`)
    one lands in `[1/6, 1/3]` (reduces to `bhk_prop11_residue_hit` on the coprime
    pair `w₀/g, w₂/g`). -/
lemma bhk_prop11_witness_time (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) :
    ∃ t : ℝ, Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2 ∧
      1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ∧
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3 := by
  set a := w ⟨0, by omega⟩ with ha
  set n := w ⟨2, by omega⟩ with hn
  have ha0 : 0 < a := hpos _
  have hn0 : 0 < n := by omega
  set g : ℕ := Nat.gcd a n with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a n
  have hgn : g ∣ n := Nat.gcd_dvd_right a n
  have ha'0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hg0
  have h3a' : 3 * (a / g) < n / g := by
    have hmul : 3 * (a / g) * g < n / g * g := by
      calc 3 * (a / g) * g = 3 * a := by rw [mul_assoc, Nat.div_mul_cancel hga]
        _ < n := hsmall
        _ = n / g * g := (Nat.div_mul_cancel hgn).symm
    exact lt_of_mul_lt_mul_right hmul (Nat.zero_le g)
  have hcop' : Nat.Coprime (a / g) (n / g) := Nat.coprime_div_gcd_div_gcd hg0
  obtain ⟨m, hm⟩ := bhk_prop11_residue_hit (a / g) (n / g) ha'0 h3a' hq5 hcop'
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hb'R : (0 : ℝ) < ((n / g : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n / g)
  have haf : (a : ℝ) = (g : ℝ) * ((a / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hga]
  have hnf : (n : ℝ) = (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hgn]
  have heq : (a : ℝ) * ((2 * (m : ℝ) + 1) / (2 * n))
      = ((a / g : ℕ) : ℝ) * ((2 * (m : ℝ) + 1) / (2 * ((n / g : ℕ) : ℝ))) := by
    rw [haf, hnf]; field_simp
  refine ⟨(2 * (m : ℝ) + 1) / (2 * n), ?_, ?_, ?_⟩
  · have hhalf : (n : ℝ) * ((2 * (m : ℝ) + 1) / (2 * n)) = (m : ℝ) + 1 / 2 := by
      field_simp
    rw [hhalf, show (m : ℝ) + 1 / 2 = ((m : ℤ) : ℝ) + 1 / 2 from by push_cast; ring,
      Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  · rw [heq]; exact (Set.mem_Icc.mp hm).1
  · rw [heq]; exact (Set.mem_Icc.mp hm).2

/-- **BHK §5 Part 2 — Corollary 16 (`v₄ < 2`), conditional on a witness time.**
    Given a half-integer time `t` (runner 3 at `1/2`) with runner 1 in
    `[1/6, 1/3]`, the indirect covering assumption forces `w₃ < 2 w₂`
    (`v₄ < 2 v₃`). The witness-time existence (BHK Corollary 15, via finite
    equidistribution of the `w₂` half-integer positions of runner 1) is the
    remaining ingredient. Proof: `bhk_prop11_gap123` gives a 123-gap of length
    `1/(3 w₂)`; `bhk_lemma_4` bounds that length by `2/(3 w₃)`. -/
lemma bhk_prop11_v4_lt_2v3_of_time (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3) :
    (w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ) := by
  have hw2R : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hcov := bhk_prop11_gap_covered w hcover
    (bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi)
  have hab : t ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have : (0 : ℝ) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) hab hcov
  have hkey : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by
    linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hkey
  linarith

/-- **BHK §5 Part 2 — Corollary 16 (`v₄ < 2`).** Combining the witness-time
    existence (`bhk_prop11_witness_time`) with the conditional bound: under the
    covering assumption, `q = w₂/gcd(w₀,w₂) ≥ 5` forces `w₃ < 2 w₂`. This `q ≥ 5`
    is exactly BHK Lemma 13 — the only remaining structural fact for Cor 16. -/
lemma bhk_prop11_v4_lt_2v3 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) :
    (w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ) := by
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  exact bhk_prop11_v4_lt_2v3_of_time w hmono hpos hsum hsmall hcover t h3 h1lo h1hi

/-- **Residue realization.** For coprime `w'` and `n > 0`, every residue class mod
    `n` is hit by some multiple `w' · i`. (The `ZMod` unit-inverse construction of
    `bhk_prop11_residue_hit`, extracted for reuse in the orbit argument.) -/
lemma bhk_prop11_residue_solve (w' n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime w' n)
    (r : ℕ) : ∃ i : ℕ, (w' * i) % n = r % n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set u := ZMod.unitOfCoprime w' hcop with hu
  refine ⟨(((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n)).val, ?_⟩
  have hcast : ((w' * (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n)).val : ℕ) : ZMod n)
      = ((r : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ← ZMod.coe_unitOfCoprime w' hcop, ← hu,
      ← mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

/-- **BHK §5 Part 2 — orbit escape (the kernel of Lemma 12, bound (34)).** If
    `g ∤ w` then the orbit of runner `w` under the period-`1/g` translation cannot
    stay within `1/6` of the origin: some translate `x₀ + i·(w/g)` has
    `circDist ≥ 1/6`. Equivalently, a cyclic orbit of order `≥ 2` on the circle
    escapes the bad arc `(−1/6, 1/6)`. This is the contrapositive of BHK's "the
    positions … are equidistributed, so there can be only one [if all are
    covered]": if every translate of a `0123a`-gap point were covered by runner
    `b`, then `b`'s orbit would lie in the bad arc, forcing `g ∣ w_b`. -/
lemma bhk_prop11_orbit_escape (w g : ℕ) (hg : 0 < g) (hndvd : ¬ g ∣ w) (x₀ : ℝ) :
    ∃ i : ℕ, (1 : ℝ) / 6 ≤ circDist (x₀ + (i : ℝ) * ((w : ℝ) / g)) := by
  -- Reduce by `d = gcd w g`: the orbit has order `n = g / d ≥ 2`.
  have hd0 : 0 < Nat.gcd w g := Nat.gcd_pos_of_pos_right w hg
  have hdg : Nat.gcd w g ∣ g := Nat.gcd_dvd_right w g
  have hdw : Nat.gcd w g ∣ w := Nat.gcd_dvd_left w g
  have hcop : Nat.Coprime (w / Nat.gcd w g) (g / Nat.gcd w g) :=
    Nat.coprime_div_gcd_div_gcd hd0
  set d : ℕ := Nat.gcd w g with hd
  set n : ℕ := g / d with hndef
  set w' : ℕ := w / d with hw'def
  have hdlt : d < g := lt_of_le_of_ne (Nat.le_of_dvd hg hdg) (fun h => hndvd (h ▸ hdw))
  have hgdn : g = d * n := (Nat.mul_div_cancel' hdg).symm
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso; interval_cases n <;> omega
    · exact h
  have hn0 : 0 < n := by omega
  -- Real bridge: `(w : ℝ) / g = w' / n`.
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hwf : (w : ℝ) = (d : ℝ) * (w' : ℝ) := by
    rw [hw'def, ← Nat.cast_mul, Nat.mul_div_cancel' hdw]
  have hgf : (g : ℝ) = (d : ℝ) * (n : ℝ) := by
    rw [hndef, ← Nat.cast_mul, Nat.mul_div_cancel' hdg]
  have hratio : (w : ℝ) / g = (w' : ℝ) / n := by
    rw [hwf, hgf, mul_div_mul_left _ _ hdR.ne']
  -- Choose the residue `r` putting `fract (x₀ + r/n)` near `1/2`.
  set j₀ : ℤ := round ((n : ℝ) * (1 / 2 - Int.fract x₀)) with hj0
  have hround : |(n : ℝ) * (1 / 2 - Int.fract x₀) - (j₀ : ℝ)| ≤ 1 / 2 := by
    rw [hj0]; exact abs_sub_round _
  set r : ℕ := (j₀ % (n : ℤ)).toNat with hrdef
  have hr_emod : (r : ℤ) = j₀ % (n : ℤ) := by
    rw [hrdef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg j₀ (by exact_mod_cast hn0.ne'))
  have hrlt : r < n := by
    have h : (r : ℤ) < (n : ℤ) := by
      rw [hr_emod]; exact Int.emod_lt_of_pos j₀ (by exact_mod_cast hn0)
    exact_mod_cast h
  have hr_real : (r : ℝ) = (j₀ : ℝ) - (n : ℝ) * ((j₀ / (n : ℤ) : ℤ) : ℝ) := by
    have h1 : (r : ℤ) = j₀ - (n : ℤ) * (j₀ / (n : ℤ)) := by rw [hr_emod, Int.emod_def]
    exact_mod_cast h1
  -- Realize residue `r`: `∃ i, (w' · i) % n = r`.
  obtain ⟨i, hi⟩ := bhk_prop11_residue_solve w' n hn0 hcop r
  rw [Nat.mod_eq_of_lt hrlt] at hi
  set Q : ℕ := (w' * i) / n with hQ
  have hdivmod : w' * i = n * Q + r := by
    rw [hQ, ← hi]; exact (Nat.div_add_mod (w' * i) n).symm
  have hiwR : (i : ℝ) * (w' : ℝ) = (n : ℝ) * (Q : ℝ) + (r : ℝ) := by
    have h : i * w' = n * Q + r := by rw [Nat.mul_comm]; exact hdivmod
    exact_mod_cast h
  have hiw : (i : ℝ) * ((w : ℝ) / g) = (i : ℝ) * (w' : ℝ) / n := by rw [hratio]; ring
  -- The orbit point equals `(fract x₀ + j₀/n)` shifted by an integer `K`.
  set K : ℤ := ⌊x₀⌋ + (Q : ℤ) - j₀ / (n : ℤ) with hKdef
  have hK : x₀ + (i : ℝ) * ((w : ℝ) / g)
      = (Int.fract x₀ + (j₀ : ℝ) / (n : ℝ)) + (K : ℝ) := by
    rw [hiw, hiwR, hr_real, hKdef]
    push_cast
    rw [Int.fract]
    field_simp
    ring
  -- Bounds: `fract x₀ + j₀/n ∈ [1/4, 3/4]`.
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hdiff : (1 : ℝ) / 2 - (Int.fract x₀ + (j₀ : ℝ) / n)
      = ((n : ℝ) * (1 / 2 - Int.fract x₀) - j₀) / n := by
    field_simp; ring
  have habs : |(1 : ℝ) / 2 - (Int.fract x₀ + (j₀ : ℝ) / n)| ≤ 1 / 4 := by
    rw [hdiff, abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
    calc |(n : ℝ) * (1 / 2 - Int.fract x₀) - j₀| ≤ 1 / 2 := hround
      _ ≤ 1 / 4 * n := by linarith [hn2R]
  have hb := abs_le.mp habs
  have hlo : (1 : ℝ) / 4 ≤ Int.fract x₀ + (j₀ : ℝ) / n := by linarith [hb.2]
  have hhi : Int.fract x₀ + (j₀ : ℝ) / n ≤ 3 / 4 := by linarith [hb.1]
  refine ⟨i, ?_⟩
  have hF : Int.fract (x₀ + (i : ℝ) * ((w : ℝ) / g)) = Int.fract x₀ + (j₀ : ℝ) / (n : ℝ) := by
    rw [hK, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold circDist
  rw [hF]
  exact le_min (by linarith) (by linarith)

/-- **BHK §5 Part 2 — divisibility from full coverage (Lemma 12, "use (2)").** If a
    single runner `w` covers *every* period-`1/g` translate of a base point
    (`circDist (x₀ + i·(w/g)) < 1/6` for all `i`), then its orbit collapses to one
    point: `g ∣ w`. This is the contrapositive of `bhk_prop11_orbit_escape`, and is
    exactly how BHK forces the denominator of `v_b` to divide `q` once runner `b`
    is the only available cover at a `0123a`-gap point. -/
lemma bhk_prop11_dvd_of_orbit_covered (w g : ℕ) (hg : 0 < g) (x₀ : ℝ)
    (hcov : ∀ i : ℕ, circDist (x₀ + (i : ℝ) * ((w : ℝ) / g)) < 1 / 6) : g ∣ w := by
  by_contra hndvd
  obtain ⟨i, hi⟩ := bhk_prop11_orbit_escape w g hg hndvd x₀
  exact absurd (hcov i) (not_lt.mpr hi)

/-- **Half-shift escapes the bad arc.** If `y` is covered (`circDist y < 1/6`) and
    `s ∈ [1/2, 2/3]` then `y + s` is safe (`circDist (y + s) ≥ 1/6`). Shifting a
    point of the bad arc `(−1/6, 1/6)` by roughly a half-turn lands it solidly in
    the safe region `[1/6, 5/6]`. This is the geometric heart of the counting
    bound (34): the shift injects covered times into safe times. -/
lemma bhk_prop11_shift_safe (y s : ℝ) (hb : circDist y < 1 / 6)
    (hs1 : 1 / 2 ≤ s) (hs2 : s ≤ 2 / 3) : (1 : ℝ) / 6 ≤ circDist (y + s) := by
  have hfr : Int.fract (y + s) = Int.fract (Int.fract y + s) := by
    conv_lhs => rw [← Int.floor_add_fract y]
    rw [show (⌊y⌋ : ℝ) + Int.fract y + s = (Int.fract y + s) + ((⌊y⌋ : ℤ) : ℝ) from by
      ring, Int.fract_add_intCast]
  have hfy0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hfy1 : Int.fract y < 1 := Int.fract_lt_one y
  unfold circDist at hb ⊢
  rw [hfr]
  rcases min_lt_iff.mp hb with hlt | hlt
  · -- `Int.fract y < 1/6`: `y + s` lands in `[1/2, 5/6)`.
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact le_min (by linarith) (by linarith)
  · -- `1 - Int.fract y < 1/6` (i.e. `Int.fract y > 5/6`): lands in `(1/3, 2/3)`.
    rw [show Int.fract y + s = (Int.fract y + s - 1) + ((1 : ℤ) : ℝ) from by push_cast; ring,
      Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact le_min (by linarith) (by linarith)

/-- **Existence of a half-turn shift.** If `g ∤ w` then some translate index `δ`
    advances runner `w`'s circle position by an amount in `[1/2, 2/3]` (mod 1):
    `Int.fract (δ · (w/g)) ∈ [1/2, 2/3]`. With `n = g / gcd(w,g) ≥ 2` the position
    advances in steps of `1/n ≤ 1/2`, so the target window `[1/2, 2/3]` is hit by
    `Δ = ⌈n/2⌉` steps (realised via `bhk_prop11_residue_solve`). -/
lemma bhk_prop11_exists_half_shift (w g : ℕ) (hg : 0 < g) (hndvd : ¬ g ∣ w) :
    ∃ δ : ℕ, (1 : ℝ) / 2 ≤ Int.fract ((δ : ℝ) * ((w : ℝ) / g))
      ∧ Int.fract ((δ : ℝ) * ((w : ℝ) / g)) ≤ 2 / 3 := by
  have hd0 : 0 < Nat.gcd w g := Nat.gcd_pos_of_pos_right w hg
  have hdg : Nat.gcd w g ∣ g := Nat.gcd_dvd_right w g
  have hdw : Nat.gcd w g ∣ w := Nat.gcd_dvd_left w g
  have hcop : Nat.Coprime (w / Nat.gcd w g) (g / Nat.gcd w g) :=
    Nat.coprime_div_gcd_div_gcd hd0
  set d : ℕ := Nat.gcd w g with hd
  set n : ℕ := g / d with hndef
  set w' : ℕ := w / d with hw'def
  have hdlt : d < g := lt_of_le_of_ne (Nat.le_of_dvd hg hdg) (fun h => hndvd (h ▸ hdw))
  have hgdn : g = d * n := (Nat.mul_div_cancel' hdg).symm
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso; interval_cases n <;> omega
    · exact h
  have hn0 : 0 < n := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hwf : (w : ℝ) = (d : ℝ) * (w' : ℝ) := by
    rw [hw'def, ← Nat.cast_mul, Nat.mul_div_cancel' hdw]
  have hgf : (g : ℝ) = (d : ℝ) * (n : ℝ) := by
    rw [hndef, ← Nat.cast_mul, Nat.mul_div_cancel' hdg]
  have hratio : (w : ℝ) / g = (w' : ℝ) / n := by
    rw [hwf, hgf, mul_div_mul_left _ _ hdR.ne']
  -- `Δ = ⌈n/2⌉` steps land in `[1/2, 2/3]`.
  set Δ : ℕ := (n + 1) / 2 with hΔdef
  have hΔn : Δ < n := by omega
  have hΔlo : n ≤ 2 * Δ := by omega
  have hΔhi : 3 * Δ ≤ 2 * n := by omega
  obtain ⟨δ, hδ⟩ := bhk_prop11_residue_solve w' n hn0 hcop Δ
  rw [Nat.mod_eq_of_lt hΔn] at hδ
  set Q : ℕ := (w' * δ) / n with hQ
  have hdivmod : w' * δ = n * Q + Δ := by
    rw [hQ, ← hδ]; exact (Nat.div_add_mod (w' * δ) n).symm
  have hfract : Int.fract ((δ : ℝ) * ((w : ℝ) / g)) = (Δ : ℝ) / n := by
    rw [hratio]
    have hstep : (δ : ℝ) * ((w' : ℝ) / n) = (Q : ℝ) + (Δ : ℝ) / n := by
      rw [show (δ : ℝ) * ((w' : ℝ) / n) = ((δ * w' : ℕ) : ℝ) / n from by push_cast; ring,
        show δ * w' = n * Q + Δ from by rw [Nat.mul_comm]; exact hdivmod]
      push_cast; field_simp
    rw [hstep, show (Q : ℝ) = ((Q : ℤ) : ℝ) from by push_cast; ring, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by positivity, by rw [div_lt_one hnR]; exact_mod_cast hΔn⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [hfract, le_div_iff₀ hnR]
    have : (n : ℝ) ≤ 2 * Δ := by exact_mod_cast hΔlo
    linarith
  · rw [hfract, div_le_iff₀ hnR]
    have : 3 * (Δ : ℝ) ≤ 2 * n := by exact_mod_cast hΔhi
    linarith

/-- **BHK §5 Part 2 — counting bound (34).** Over one period `Finset.range g` of the
    period-`1/g` translation, runner `w` (with `g ∤ w`) covers *at most half* the
    times: `2 · #{covered i} ≤ g`. The half-turn shift `i ↦ (i + δ) % g`
    (`bhk_prop11_exists_half_shift`) injects covered times into safe times
    (`bhk_prop11_shift_safe`), so the covered set is no larger than its complement.
    This is the density input to BHK's "`∃ a, n_a = 1`" step in Lemma 12. -/
lemma bhk_prop11_orbit_half (w g : ℕ) (hg : 0 < g) (hndvd : ¬ g ∣ w) (x₀ : ℝ) :
    2 * ((Finset.range g).filter
        (fun i : ℕ => circDist (x₀ + (i : ℝ) * ((w : ℝ) / g)) < 1 / 6)).card ≤ g := by
  obtain ⟨δ, hs1, hs2⟩ := bhk_prop11_exists_half_shift w g hg hndvd
  set s : ℝ := Int.fract ((δ : ℝ) * ((w : ℝ) / g)) with hsdef
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  set Bad : Finset ℕ := (Finset.range g).filter
    (fun i : ℕ => circDist (x₀ + (i : ℝ) * ((w : ℝ) / g)) < 1 / 6) with hBaddef
  have hsub : Bad ⊆ Finset.range g := Finset.filter_subset _ _
  -- The half-turn shift injects `Bad` into its complement `range g \ Bad`.
  have hcard : Bad.card ≤ (Finset.range g \ Bad).card := by
    apply Finset.card_le_card_of_injOn (fun i => (i + δ) % g)
    · intro i hi
      simp only [Finset.mem_coe, hBaddef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hilt, hbad⟩ := hi
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_range, hBaddef, Finset.mem_filter]
      refine ⟨Nat.mod_lt _ hg, fun hcontra => ?_⟩
      set m : ℕ := (i + δ) % g with hm
      set c : ℕ := (i + δ) / g with hc
      have hcm : i + δ = g * c + m := by rw [hm, hc]; exact (Nat.div_add_mod (i + δ) g).symm
      have hcmR : (m : ℝ) = (i : ℝ) + δ - (g : ℝ) * c := by
        have h := congrArg (Nat.cast (R := ℝ)) hcm
        push_cast at h; linarith
      have hsR : s = (δ : ℝ) * ((w : ℝ) / g) - (⌊(δ : ℝ) * ((w : ℝ) / g)⌋ : ℝ) := by
        rw [hsdef, Int.fract]
      have hKid : x₀ + (m : ℝ) * ((w : ℝ) / g)
          = (x₀ + (i : ℝ) * ((w : ℝ) / g) + s)
            + (((⌊(δ : ℝ) * ((w : ℝ) / g)⌋ - (c : ℤ) * (w : ℤ)) : ℤ) : ℝ) := by
        rw [hcmR, hsR]; push_cast; field_simp; ring
      have hsafe : (1 : ℝ) / 6 ≤ circDist (x₀ + (m : ℝ) * ((w : ℝ) / g)) := by
        rw [hKid, bhk_prop11_circDist_add_int]
        exact bhk_prop11_shift_safe _ s hbad hs1 hs2
      exact absurd hcontra.2 (not_lt.mpr hsafe)
    · intro i₁ h₁ i₂ h₂ heq
      have hi1 : i₁ < g := Finset.mem_range.mp (hsub (Finset.mem_coe.mp h₁))
      have hi2 : i₂ < g := Finset.mem_range.mp (hsub (Finset.mem_coe.mp h₂))
      simp only at heq
      have e : (i₁ + δ) ≡ (i₂ + δ) [MOD g] := heq
      have h12 : i₁ ≡ i₂ [MOD g] := Nat.ModEq.add_right_cancel' δ e
      calc i₁ = i₁ % g := (Nat.mod_eq_of_lt hi1).symm
        _ = i₂ % g := h12
        _ = i₂ := Nat.mod_eq_of_lt hi2
  have hsd : (Finset.range g \ Bad).card = g - Bad.card := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hsub]
  omega

/-- **BHK §5 Part 2 — Lemma 12 "use (1)".** Two runners `wa, wb`, each with an
    order-`≥ 2` orbit (`g ∤ wa`, `g ∤ wb`), cannot jointly cover every period-`1/g`
    translate of a point at which they *both* cover (`circDist xa, xb < 1/6`).
    Each covers at most half the period (`bhk_prop11_orbit_half`), so together they
    cover at most all of it — but the shared cover at `i = 0` makes the union fall
    strictly short. This is BHK's "`∃ a ∈ {4,5}, n_a = 1`": at least one runner's
    orbit must collapse (`g ∣ w_a`). -/
lemma bhk_prop11_no_double (g : ℕ) (hg : 0 < g) (wa wb : ℕ)
    (hna : ¬ g ∣ wa) (hnb : ¬ g ∣ wb) (xa xb : ℝ)
    (hua : circDist xa < 1 / 6) (hub : circDist xb < 1 / 6)
    (hcov : ∀ i : ℕ, circDist (xa + (i : ℝ) * ((wa : ℝ) / g)) < 1 / 6
        ∨ circDist (xb + (i : ℝ) * ((wb : ℝ) / g)) < 1 / 6) : False := by
  have hAhalf := bhk_prop11_orbit_half wa g hg hna xa
  have hBhalf := bhk_prop11_orbit_half wb g hg hnb xb
  set A : Finset ℕ := (Finset.range g).filter
    (fun i : ℕ => circDist (xa + (i : ℝ) * ((wa : ℝ) / g)) < 1 / 6) with hA
  set B : Finset ℕ := (Finset.range g).filter
    (fun i : ℕ => circDist (xb + (i : ℝ) * ((wb : ℝ) / g)) < 1 / 6) with hB
  have hAsub : A ⊆ Finset.range g := Finset.filter_subset _ _
  have hBsub : B ⊆ Finset.range g := Finset.filter_subset _ _
  have hunion : A ∪ B = Finset.range g := by
    apply Finset.Subset.antisymm (Finset.union_subset hAsub hBsub)
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [Finset.mem_union, hA, hB, Finset.mem_filter, Finset.mem_range]
    rcases hcov i with h | h
    · exact Or.inl ⟨hi, h⟩
    · exact Or.inr ⟨hi, h⟩
  have h0 : (0 : ℕ) ∈ A ∩ B := by
    simp only [Finset.mem_inter, hA, hB, Finset.mem_filter, Finset.mem_range, Nat.cast_zero,
      zero_mul, add_zero]
    exact ⟨⟨hg, hua⟩, ⟨hg, hub⟩⟩
  have hinter : 1 ≤ (A ∩ B).card := Finset.card_pos.mpr ⟨0, h0⟩
  have hkey := Finset.card_union_add_card_inter A B
  rw [hunion, Finset.card_range] at hkey
  omega

/-- **Orbit periodicity for a divisor speed.** If `g ∣ v` then runner `v`'s
    position is unchanged by the period-`1/g` translation: `circDist (v·u + i·(v/g))
    = circDist (v·u)`, since `v/g` is an integer. Used to propagate `0123`-safety
    (and, in Lemma 12's "use (2)", a divisor runner's safety) to every translate. -/
lemma bhk_prop11_circDist_orbit_dvd (v g : ℕ) (hg : 0 < g) (hdvd : g ∣ v) (u : ℝ) (i : ℕ) :
    circDist ((v : ℝ) * u + (i : ℝ) * ((v : ℝ) / g)) = circDist ((v : ℝ) * u) := by
  obtain ⟨c, hc⟩ := hdvd
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hstep : (i : ℝ) * ((v : ℝ) / g) = ((i * c : ℕ) : ℝ) := by
    have hvR : (v : ℝ) = (g : ℝ) * (c : ℝ) := by rw [hc]; push_cast; ring
    rw [hvR]; push_cast; field_simp
  rw [hstep, show ((i * c : ℕ) : ℝ) = (((i * c : ℕ) : ℤ) : ℝ) from by push_cast; ring,
    bhk_prop11_circDist_add_int]

/-- **BHK §5 Part 2 — Lemma 12.** For a `0123`-gap `[a,b]` (runners 1,2,3 safe
    throughout) under the indirect covering assumption, with `g` dividing the
    speeds of runners 1,2,3: either runner 4 covers the whole gap, or runner 5
    does, or *both* `v₄ = r/q` and `v₅ = s/q` (`g ∣ w₃ ∧ g ∣ w₄`). Use (1)
    (`bhk_prop11_no_double`) forces one denominator to divide `g`; use (2)
    (`bhk_prop11_dvd_of_orbit_covered`) then forces the other. -/
lemma bhk_prop11_lemma12 (w : Fin 5 → ℕ) (g : ℕ) (hg : 0 < g)
    (hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    {a b : ℝ} (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s)) :
    Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∨ Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
      ∨ (g ∣ w ⟨3, by omega⟩ ∧ g ∣ w ⟨4, by omega⟩) := by
  by_cases h4 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩
  · exact Or.inl h4
  by_cases h5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ?_)
  have hcov45 := bhk_prop11_gap_covered w hcover hgap
  obtain ⟨u, huIcc, hu4, hu5⟩ := bhk_prop11_overlap w hcov45 h4 h5
  -- Translates of any 0123-safe point are covered by runner 4 or 5.
  have htrans : ∀ (p : ℝ), p ∈ Set.Icc a b → ∀ i : ℕ,
      circDist ((w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) < 1 / 6 ∨
      circDist ((w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) < 1 / 6 := by
    intro p hp i
    obtain ⟨k, hk⟩ := hcover (p + (i : ℝ) * (1 / g))
    -- runners 1,2,3 stay safe at the translate
    have hsafe012 : ∀ j : Fin 3,
        (1 : ℝ) / 6 ≤ circDist ((w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))) := by
      intro j
      have hjexp : (w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))
          = (w ⟨j.val, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨j.val, by omega⟩ : ℝ) / g) := by
        ring
      rw [hjexp, bhk_prop11_circDist_orbit_dvd _ g hg (hdvd012 j)]
      exact hgap p hp j
    -- so the covering runner k is 4 or 5
    fin_cases k
    · exact absurd hk (not_lt.mpr (hsafe012 0))
    · exact absurd hk (not_lt.mpr (hsafe012 1))
    · exact absurd hk (not_lt.mpr (hsafe012 2))
    · left
      rw [show (w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)
            = (w ⟨3, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
      exact hk
    · right
      rw [show (w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)
            = (w ⟨4, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
      exact hk
  -- use (1): at least one of runners 4, 5 has its orbit collapse (g ∣ w_a).
  have hua : circDist ((w ⟨3, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu4
  have hub : circDist ((w ⟨4, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu5
  have hor : g ∣ w ⟨3, by omega⟩ ∨ g ∣ w ⟨4, by omega⟩ := by
    by_contra hcon
    rw [not_or] at hcon
    exact bhk_prop11_no_double g hg _ _ hcon.1 hcon.2 _ _ hua hub (htrans u huIcc)
  -- use (2): a point where runner `a` is also safe forces runner `b` to cover all
  -- translates, collapsing its orbit too.
  rcases hor with h3 | h4'
  · -- `g ∣ w₃`; pick a point where runner 4 (`w₃`) is also safe, forcing runner 5.
    refine ⟨h3, ?_⟩
    rw [Set.not_subset] at h4
    obtain ⟨p, hpIcc, hp4⟩ := h4
    rw [mem_unsafeOf_iff, not_lt] at hp4
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨4, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exfalso
      have hsafe3 : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h3]; exact hp4
      linarith
    · exact h
  · -- `g ∣ w₄`; pick a point where runner 5 (`w₄`) is also safe, forcing runner 4.
    refine ⟨?_, h4'⟩
    rw [Set.not_subset] at h5
    obtain ⟨p, hpIcc, hp5⟩ := h5
    rw [mem_unsafeOf_iff, not_lt] at hp5
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨3, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exact h
    · exfalso
      have hsafe4 : (1 : ℝ) / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h4']; exact hp5
      linarith

/-- **BHK §5 Part 2 — Lemma 17 (`v₄ = r/q`, `v₅ = s/q`).** Conditional on
    `q = w₂ / gcd(w₀,w₂) ≥ 5` (BHK Lemma 13), the denominators of runners 4 and 5
    both divide `q`: `g ∣ w₃ ∧ g ∣ w₄` with `g = gcd(w₀,w₂)`. Corollary 15
    (`bhk_prop11_witness_time`) produces a `0123`-gap of length `1/(3 w₂)`; since
    `w₃, w₄ > w₂` this exceeds both block widths, so the gap lies in neither `B₄`
    nor `B₅`, and Lemma 12 leaves only the divisibility conclusion. -/
lemma bhk_prop11_lemma17 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) :
    Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨3, by omega⟩ ∧
      Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨4, by omega⟩ := by
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgdvd0 : g ∣ w ⟨0, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
  have hgdvd2 : g ∣ w ⟨2, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
  have hgdvd1 : g ∣ w ⟨1, by omega⟩ := by
    have he : w ⟨1, by omega⟩ = w ⟨2, by omega⟩ - w ⟨0, by omega⟩ := by omega
    rw [he]; exact Nat.dvd_sub hgdvd2 hgdvd0
  have hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩ := by
    intro i; fin_cases i
    · exact hgdvd0
    · exact hgdvd1
    · exact hgdvd2
  -- Corollary 15 + the 0123-gap construction.
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  have hgap := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  -- The gap (length `1/(3 w₂)`) is too long to fit in `B₄` or `B₅`.
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos ⟨2, by omega⟩
  have hgaplen : ∀ (j : Fin 5), w ⟨2, by omega⟩ < w j →
      (1 : ℝ) / (3 * (w j : ℝ)) < (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) - t := by
    intro j hj
    rw [add_sub_cancel_left]
    have hwj : (w ⟨2, by omega⟩ : ℝ) < (w j : ℝ) := by exact_mod_cast hj
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hn4 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨3, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨3, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨3, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  have hn5 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨4, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨4, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  rcases bhk_prop11_lemma12 w g hg0 hdvd012 hcover hgap with hc | hc | hc
  · exact absurd hc hn4
  · exact absurd hc hn5
  · exact hc

/-- **Runner safe on an interval (window form).** If runner `i`'s position
    `v · t` stays in a single integer's safe window `[k+1/6, k+5/6]` across all of
    `[a,b]`, then `circDist (v · t) ≥ 1/6` throughout. The workhorse for the
    explicit `q = 4` gaps `I₁, I₂` of BHK Lemma 13 (no half-integer time, so the
    `gap123`/`witness_time` machinery — which needs `q ≥ 5` — does not apply). -/
lemma bhk_prop11_safe_on_Icc (v : ℝ) (k : ℤ) {a b : ℝ}
    (hlo : (k : ℝ) + 1 / 6 ≤ v * a) (hhi : v * b ≤ (k : ℝ) + 5 / 6) (hv : 0 ≤ v) :
    ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist (v * s) := by
  intro s hs
  obtain ⟨hsl, hsu⟩ := hs
  have hva : v * a ≤ v * s := mul_le_mul_of_nonneg_left hsl hv
  have hvb : v * s ≤ v * b := mul_le_mul_of_nonneg_left hsu hv
  have h1 : (k : ℝ) + 1 / 6 ≤ v * s := le_trans hlo hva
  have h2 : v * s ≤ (k : ℝ) + 5 / 6 := le_trans hvb hhi
  have hfr : Int.fract (v * s) = v * s - (k : ℝ) := by
    conv_lhs => rw [show v * s = (k : ℝ) + (v * s - (k : ℝ)) from by ring]
    rw [Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  simp only [circDist]; rw [hfr]
  exact le_min (by linarith) (by linarith)

/-- **Assemble a `123`-gap** from the three per-runner safety facts. Packages
    `∀ i : Fin 3` so the gap lemmas can consume it. -/
lemma bhk_prop11_mk123 (w : Fin 5 → ℕ) {a b : ℝ}
    (h0 : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s))
    (h1 : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s))
    (h2 : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)) :
    ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
  intro s hs i; fin_cases i
  · exact h0 s hs
  · exact h1 s hs
  · exact h2 s hs

/-- **`1234`-gap span bound.** A `1234`-gap (runners 1,2,3,4 all `≥ 1/6`) is,
    under the covering assumption, contained in `B₅`, so `block_containment`
    bounds the span of runner 5: `w₄ · (b - a) < 1/3`. The engine of every
    `r`-case of BHK Lemma 13. -/
lemma bhk_prop11_gap1234_b5span (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s)) :
    (w ⟨4, by omega⟩ : ℝ) * (b - a) < 1 / 3 := by
  have hcov45 := bhk_prop11_gap_covered w hcover hgap
  have hsub5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩ := by
    intro s hs
    rcases hcov45 hs with h | h
    · exact absurd ((mem_unsafeOf_iff w _ s).mp h) (not_lt.mpr (h4safe s hs))
    · exact h
  obtain ⟨k, hk1, hk2⟩ := block_containment w ⟨4, by omega⟩ (hpos _) a b hab hsub5
  rw [mul_sub]; linarith

/-- **Sixth-multiple covering.** If a runner sitting at `n/6` (mod 1) is within
    `1/6` of the origin then `6 ∣ n`: the only sixth landing in the bad arc is the
    integer one. Used for BHK Lemma 13's observation at time `t = 2/3`. -/
lemma bhk_prop11_dvd_six_of_circDist {n : ℕ} (h : circDist ((n : ℝ) / 6) < 1 / 6) :
    6 ∣ n := by
  by_contra hnd
  have hmod : n % 6 ≠ 0 := fun hh => hnd (Nat.dvd_of_mod_eq_zero hh)
  have hmlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hge1 : 1 ≤ n % 6 := by omega
  have key : (n : ℝ) = 6 * ((n / 6 : ℕ) : ℝ) + ((n % 6 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n 6).symm
  have hsplit : (n : ℝ) / 6 = ((n % 6 : ℕ) : ℝ) / 6 + ((n / 6 : ℕ) : ℝ) := by
    rw [key]; ring
  have hfr : Int.fract ((n : ℝ) / 6) = ((n % 6 : ℕ) : ℝ) / 6 := by
    rw [hsplit, Int.fract_add_natCast]
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one (by norm_num)]; exact_mod_cast hmlt
  have h1 : (1 : ℝ) ≤ ((n % 6 : ℕ) : ℝ) := by exact_mod_cast hge1
  have h5 : ((n % 6 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (by omega : n % 6 ≤ 5)
  have hsafe : (1 : ℝ) / 6 ≤ circDist ((n : ℝ) / 6) := by
    simp only [circDist]; rw [hfr]; exact le_min (by linarith) (by linarith)
  linarith

/-- **BHK Lemma 13 (`q ≥ 5`).** Under the indirect covering assumption, the
    reduced denominator `q = w₂ / gcd(w₀,w₂)` is at least `5`; equivalently the
    case `v₁ = 1/4` (`q = 4`) cannot occur. BHK rule this out via the explicit
    `123`-gaps `I₁ = [2/3, 5/6]` and `I₂ = [13/6, 44/18]` (in normalised time,
    i.e. `[1/(6w₀), 5/(24w₀)]` and `[13/(24w₀), 11/(18w₀)]` here since `w₂ = 4w₀`)
    together with Lemma 4 and the orbit-divisibility Lemma 12. -/
theorem bhk_prop11_lemma13 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6) :
    5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) := by
  by_contra hq
  push_neg at hq
  -- ## Step 0 — reduce to `q = 4`, `p = 1`, hence `w₂ = 4 w₀`.
  set w0 : ℕ := w ⟨0, by omega⟩ with hw0_def
  set w2 : ℕ := w ⟨2, by omega⟩ with hw2_def
  set g : ℕ := Nat.gcd w0 w2 with hg_def
  have hw0pos : 0 < w0 := hpos _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hw0pos
  have hgw0 : g ∣ w0 := by rw [hg_def]; exact Nat.gcd_dvd_left w0 w2
  have hgw2 : g ∣ w2 := by rw [hg_def]; exact Nat.gcd_dvd_right w0 w2
  obtain ⟨p, hp⟩ := hgw0
  obtain ⟨q, hqe⟩ := hgw2
  have hqval : w2 / g = q := by rw [hqe, Nat.mul_div_cancel_left _ hg0]
  rw [hqval] at hq
  have hppos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, mul_zero] at hp; omega
    · exact h
  have h3pq : 3 * p < q := by
    have key : g * (3 * p) < g * q := by
      have h := hsmall; rw [hp, hqe] at h
      calc g * (3 * p) = 3 * (g * p) := by ring
        _ < g * q := h
    exact Nat.lt_of_mul_lt_mul_left key
  have hq4 : q = 4 := by omega
  have hp1 : p = 1 := by omega
  have hgw0_eq : g = w0 := by rw [hp, hp1, mul_one]
  have hw2_eq : w2 = 4 * w0 := by rw [hqe, hq4, hgw0_eq]; ring
  -- ## Step 1 — real-valued setup and the explicit gap `I₂ = [a, b]`.
  have hw0R : (0 : ℝ) < (w0 : ℝ) := by exact_mod_cast hw0pos
  have hw1_eq : w ⟨1, by omega⟩ = 3 * w0 := by omega
  have hw1R : ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) := by rw [hw1_eq]; push_cast; ring
  have hw2R : ((w2 : ℕ) : ℝ) = 4 * (w0 : ℝ) := by exact_mod_cast hw2_eq
  set a : ℝ := 13 / (24 * (w0 : ℝ)) with ha_def
  set b : ℝ := 11 / (18 * (w0 : ℝ)) with hb_def
  have e0a : (w0 : ℝ) * a = 13 / 24 := by rw [ha_def]; field_simp
  have e0b : (w0 : ℝ) * b = 11 / 18 := by rw [hb_def]; field_simp
  have e1a : (3 * (w0 : ℝ)) * a = 13 / 8 := by rw [ha_def]; field_simp; ring
  have e1b : (3 * (w0 : ℝ)) * b = 11 / 6 := by rw [hb_def]; field_simp; ring
  have e2a : (4 * (w0 : ℝ)) * a = 13 / 6 := by rw [ha_def]; field_simp; ring
  have e2b : (4 * (w0 : ℝ)) * b = 22 / 9 := by rw [hb_def]; field_simp; ring
  have hab : a ≤ b := by
    have h : (w0 : ℝ) * a ≤ (w0 : ℝ) * b := by rw [e0a, e0b]; norm_num
    exact le_of_mul_le_mul_left h hw0R
  -- `I₂` is a 123-gap: runners 1, 2, 3 (Lean indices 0, 1, 2) stay `≥ 1/6`.
  have hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
      exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [e0a]; norm_num)
        (by rw [e0b]; norm_num) hw0R.le s hs
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
      rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
      exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [e1a]; norm_num)
        (by rw [e1b]; norm_num) (by positivity) s hs
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
      rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
      exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 2 (by rw [e2a]; norm_num)
        (by rw [e2b]; norm_num) (by positivity) s hs
  -- The gap is covered by runners 4 and 5.
  have hcov45 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩ :=
    bhk_prop11_gap_covered w hcover hgap
  -- ## Step 2 — BHK (35): `I₂ ⊄ B₄` and `I₂ ⊄ B₅`.
  -- If `[a,b] ⊆ unsafeOf i` then `block_containment` traps it in one block
  -- `m`; since `wᵢ > 4 w₀` the block index is `m ≥ 3`, which together with the
  -- span bound `wᵢ (b-a) < 1/3` is contradictory.
  have h35 : ∀ i : Fin 5, 4 * w0 < w i → ¬ Set.Icc a b ⊆ unsafeOf w i := by
    intro i hwi hsub
    have hwi0 : 0 < w i := by omega
    have hwiR : 4 * (w0 : ℝ) < (w i : ℝ) := by exact_mod_cast hwi
    obtain ⟨m, hm1, hm2⟩ := block_containment w i hwi0 a b hab hsub
    have hva : (w i : ℝ) * a = 13 / 24 * ((w i : ℝ) / (w0 : ℝ)) := by rw [ha_def]; ring
    have hvb : (w i : ℝ) * b = 11 / 18 * ((w i : ℝ) / (w0 : ℝ)) := by rw [hb_def]; ring
    set ρ : ℝ := (w i : ℝ) / (w0 : ℝ) with hρ
    have hρ4 : 4 < ρ := by rw [hρ, lt_div_iff₀ hw0R]; linarith
    rw [hva] at hm1; rw [hvb] at hm2
    have hm3 : (3 : ℤ) ≤ m := by
      by_contra h; push_neg at h
      have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
      linarith [hm2, hρ4, hm2']
    have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith [hm1, hm2, hρ4, hm3R]
  have hw3gt : 4 * w0 < w ⟨3, by omega⟩ := by
    have h := hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega) :
      (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩); omega
  have hw4gt : 4 * w0 < w ⟨4, by omega⟩ := by
    have h := hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega) :
      (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩); omega
  have hn4 := h35 ⟨3, by omega⟩ hw3gt
  have hn5 := h35 ⟨4, by omega⟩ hw4gt
  -- ## Step 3 — Lemma 12 ⟹ `w₀ ∣ w₃` and `w₀ ∣ w₄` (`v₄ = r/4`, `v₅ = s/4`).
  have hd0 : w0 ∣ w ⟨0, by omega⟩ := ⟨1, by rw [mul_one]⟩
  have hd1 : w0 ∣ w ⟨1, by omega⟩ := ⟨3, by rw [hw1_eq]; ring⟩
  have hd2 : w0 ∣ w ⟨2, by omega⟩ := ⟨4, by rw [← hw2_def, hw2_eq]; ring⟩
  have hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩ := by
    rw [hgw0_eq]; intro i; fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  rcases bhk_prop11_lemma12 w g hg0 hdvd012 hcover hgap with hc | hc | hc
  · exact hn4 hc
  · exact hn5 hc
  · obtain ⟨hgw3, hgw4⟩ := hc
    rw [hgw0_eq] at hgw3 hgw4
    obtain ⟨r, hr⟩ := hgw3
    obtain ⟨s, hseq⟩ := hgw4
    have hrR : ((w ⟨3, by omega⟩ : ℕ) : ℝ) = (w0 : ℝ) * (r : ℝ) := by rw [hr]; push_cast; ring
    have hseqR : ((w ⟨4, by omega⟩ : ℕ) : ℝ) = (w0 : ℝ) * (s : ℝ) := by
      rw [hseq]; push_cast; ring
    -- ## Step 4 — bounds: `5 ≤ r ≤ 9`, `r < s`, and `6 ∣ r ∨ 6 ∣ s`.
    have hr5 : 5 ≤ r := by
      rcases Nat.lt_or_ge r 5 with h | h
      · exfalso
        have hmul : w0 * r ≤ w0 * 4 := Nat.mul_le_mul le_rfl (by omega)
        omega
      · exact h
    have hsr : r < s := by
      have h34 := hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega) :
        (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩)
      rw [hr, hseq] at h34
      exact Nat.lt_of_mul_lt_mul_left h34
    have hbaW : (w0 : ℝ) * (b - a) = 5 / 72 := by rw [mul_sub, e0b, e0a]; norm_num
    have hr9 : r ≤ 9 := by
      have hl4 := bhk_lemma_4 w hmono hpos a b hab hcov45
      rw [hrR] at hl4
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      have hD : (0 : ℝ) < 3 * ((w0 : ℝ) * (r : ℝ)) := by positivity
      rw [lt_div_iff₀ hD] at hl4
      have hexp : (b - a) * (3 * ((w0 : ℝ) * (r : ℝ))) = 5 * (r : ℝ) / 24 := by
        have e : (b - a) * (3 * ((w0 : ℝ) * (r : ℝ)))
            = 3 * (r : ℝ) * ((w0 : ℝ) * (b - a)) := by ring
        rw [e, hbaW]; ring
      rw [hexp] at hl4
      have : (r : ℝ) < 10 := by linarith
      have : r < 10 := by exact_mod_cast this
      omega
    have hobs : 6 ∣ r ∨ 6 ∣ s := by
      set t0 : ℝ := 1 / (6 * (w0 : ℝ)) with ht0
      have et1 : (w0 : ℝ) * t0 = 1 / 6 := by rw [ht0]; field_simp
      have et2 : 3 * (w0 : ℝ) * t0 = 1 / 2 := by rw [ht0]; field_simp; ring
      have et3 : 4 * (w0 : ℝ) * t0 = 2 / 3 := by rw [ht0]; field_simp; ring
      have p3 : (w ⟨3, by omega⟩ : ℝ) * t0 = (r : ℝ) / 6 := by
        rw [hrR, ht0]; field_simp
      have p4 : (w ⟨4, by omega⟩ : ℝ) * t0 = (s : ℝ) / 6 := by
        rw [hseqR, ht0]; field_simp
      have ht0mem : t0 ∈ Set.Icc t0 t0 := ⟨le_refl t0, le_refl t0⟩
      obtain ⟨i, hi⟩ := hcover t0
      fin_cases i
      · exact absurd hi (not_lt.mpr (bhk_prop11_safe_on_Icc (w0 : ℝ) 0
          (by rw [et1]; norm_num) (by rw [et1]; norm_num) hw0R.le t0 ht0mem))
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
        exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0
          (by rw [et2]; norm_num) (by rw [et2]; norm_num) (by positivity) t0 ht0mem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
        exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0
          (by rw [et3]; norm_num) (by rw [et3]; norm_num) (by positivity) t0 ht0mem
      · exact Or.inl (bhk_prop11_dvd_six_of_circDist (by rw [← p3]; exact hi))
      · exact Or.inr (bhk_prop11_dvd_six_of_circDist (by rw [← p4]; exact hi))
    -- ## Step 5 — casework on `r ∈ {5,…,9}`.
    interval_cases r
    · -- r = 5: the gap `[13/(24w₀), 17/(30w₀)]` (= `[13/6, 68/30]`) is a 1234-gap,
      -- bounding `s ≤ 13`; with `6 ∣ s` this gives `s ∈ {6, 12}`. For both, the
      -- explicit time `t = 13/(30 w₀)` (runner positions `{1,3,4,5,s}·13/30`) is
      -- lonely, contradicting the covering assumption.
      set a5 : ℝ := 13 / (24 * (w0 : ℝ)) with ha5
      set b5 : ℝ := 17 / (30 * (w0 : ℝ)) with hb5
      have f0a : (w0 : ℝ) * a5 = 13 / 24 := by rw [ha5]; field_simp
      have f0b : (w0 : ℝ) * b5 = 17 / 30 := by rw [hb5]; field_simp
      have f1a : 3 * (w0 : ℝ) * a5 = 13 / 8 := by rw [ha5]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b5 = 17 / 10 := by rw [hb5]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a5 = 13 / 6 := by rw [ha5]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b5 = 34 / 15 := by rw [hb5]; field_simp; ring
      have f3a : 5 * (w0 : ℝ) * a5 = 65 / 24 := by rw [ha5]; field_simp; ring
      have f3b : 5 * (w0 : ℝ) * b5 = 17 / 6 := by rw [hb5]; field_simp; ring
      have hab5 : a5 ≤ b5 := by
        have h : (w0 : ℝ) * a5 ≤ (w0 : ℝ) * b5 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg5 : ∀ s ∈ Set.Icc a5 b5, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 2 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a5 b5, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 5 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (5 * (w0 : ℝ)) 2 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab5 hg5 h4safe
      have hba5W : (w0 : ℝ) * (b5 - a5) = 1 / 40 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b5 - a5) = (s : ℝ) * ((w0 : ℝ) * (b5 - a5)) := by ring
      rw [hseqR, hc, hba5W] at hspan
      have hsR : (s : ℝ) < 14 := by linarith
      have hsle13 : s ≤ 13 := by
        have : s < 14 := by exact_mod_cast hsR
        omega
      have hs612 : s = 6 ∨ s = 12 := by omega
      -- The lonely time `t = 13/(30 w₀)`.
      set tW : ℝ := 13 / (30 * (w0 : ℝ)) with htW
      have gw0 : (w0 : ℝ) * tW = 13 / 30 := by rw [htW]; field_simp
      have gw1 : 3 * (w0 : ℝ) * tW = 13 / 10 := by rw [htW]; field_simp; ring
      have gw2 : 4 * (w0 : ℝ) * tW = 26 / 15 := by rw [htW]; field_simp; ring
      have gw3 : 5 * (w0 : ℝ) * tW = 13 / 6 := by rw [htW]; field_simp; ring
      have gw46 : 6 * (w0 : ℝ) * tW = 13 / 5 := by rw [htW]; field_simp; ring
      have gw412 : 12 * (w0 : ℝ) * tW = 26 / 5 := by rw [htW]; field_simp; ring
      have htWmem : tW ∈ Set.Icc tW tW := ⟨le_refl _, le_refl _⟩
      obtain ⟨i, hi⟩ := hcover tW
      fin_cases i
      · exact absurd hi (not_lt.mpr (bhk_prop11_safe_on_Icc (w0 : ℝ) 0
          (by rw [gw0]; norm_num) (by rw [gw0]; norm_num) hw0R.le tW htWmem))
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
        exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [gw1]; norm_num)
          (by rw [gw1]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
        exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 1 (by rw [gw2]; norm_num)
          (by rw [gw2]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 5 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (5 * (w0 : ℝ)) 2 (by rw [gw3]; norm_num)
          (by rw [gw3]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rcases hs612 with rfl | rfl
        · rw [show ((w ⟨4, by omega⟩ : ℕ) : ℝ) = 6 * (w0 : ℝ) from by rw [hseqR]; push_cast; ring]
          exact bhk_prop11_safe_on_Icc (6 * (w0 : ℝ)) 2 (by rw [gw46]; norm_num)
            (by rw [gw46]; norm_num) (by positivity) tW htWmem
        · rw [show ((w ⟨4, by omega⟩ : ℕ) : ℝ) = 12 * (w0 : ℝ) from by rw [hseqR]; push_cast; ring]
          exact bhk_prop11_safe_on_Icc (12 * (w0 : ℝ)) 5 (by rw [gw412]; norm_num)
            (by rw [gw412]; norm_num) (by positivity) tW htWmem
    · -- r = 6: runner 4 = `6 w₀` is also safe on `I₂`, making it a 1234-gap.
      have h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 6 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        refine bhk_prop11_safe_on_Icc (6 * (w0 : ℝ)) 3 ?_ ?_ (by positivity) s hs
        · rw [show 6 * (w0 : ℝ) * a = 6 * ((w0 : ℝ) * a) from by ring, e0a]; norm_num
        · rw [show 6 * (w0 : ℝ) * b = 6 * ((w0 : ℝ) * b) from by ring, e0b]; norm_num
      have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab hgap h4safe
      have hc : (w0 : ℝ) * (s : ℝ) * (b - a) = (s : ℝ) * ((w0 : ℝ) * (b - a)) := by ring
      rw [hseqR, hc, hbaW] at hspan
      have hsR : (s : ℝ) < 5 := by linarith
      have : s < 5 := by exact_mod_cast hsR
      omega
    · -- r = 7: `I₁ = [1/(6w₀), 5/(24w₀)]` is a 1234-gap (runner 4 = `7 w₀`).
      set a1 : ℝ := 1 / (6 * (w0 : ℝ)) with ha1
      set b1 : ℝ := 5 / (24 * (w0 : ℝ)) with hb1
      have f0a : (w0 : ℝ) * a1 = 1 / 6 := by rw [ha1]; field_simp
      have f0b : (w0 : ℝ) * b1 = 5 / 24 := by rw [hb1]; field_simp
      have f1a : 3 * (w0 : ℝ) * a1 = 1 / 2 := by rw [ha1]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b1 = 5 / 8 := by rw [hb1]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a1 = 2 / 3 := by rw [ha1]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b1 = 5 / 6 := by rw [hb1]; field_simp; ring
      have f3a : 7 * (w0 : ℝ) * a1 = 7 / 6 := by rw [ha1]; field_simp
      have f3b : 7 * (w0 : ℝ) * b1 = 35 / 24 := by rw [hb1]; field_simp; ring
      have hab1 : a1 ≤ b1 := by
        have h : (w0 : ℝ) * a1 ≤ (w0 : ℝ) * b1 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg1 : ∀ s ∈ Set.Icc a1 b1, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a1 b1, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 7 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (7 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab1 hg1 h4safe
      have hba1W : (w0 : ℝ) * (b1 - a1) = 1 / 24 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b1 - a1) = (s : ℝ) * ((w0 : ℝ) * (b1 - a1)) := by ring
      rw [hseqR, hc, hba1W] at hspan
      have : (s : ℝ) < 8 := by linarith
      have : s < 8 := by exact_mod_cast this
      omega
    · -- r = 8: as r = 7 but runner 4 = `8 w₀` (window `k = 1`).
      set a1 : ℝ := 1 / (6 * (w0 : ℝ)) with ha1
      set b1 : ℝ := 5 / (24 * (w0 : ℝ)) with hb1
      have f0a : (w0 : ℝ) * a1 = 1 / 6 := by rw [ha1]; field_simp
      have f0b : (w0 : ℝ) * b1 = 5 / 24 := by rw [hb1]; field_simp
      have f1a : 3 * (w0 : ℝ) * a1 = 1 / 2 := by rw [ha1]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b1 = 5 / 8 := by rw [hb1]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a1 = 2 / 3 := by rw [ha1]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b1 = 5 / 6 := by rw [hb1]; field_simp; ring
      have f3a : 8 * (w0 : ℝ) * a1 = 4 / 3 := by rw [ha1]; field_simp; ring
      have f3b : 8 * (w0 : ℝ) * b1 = 5 / 3 := by rw [hb1]; field_simp; ring
      have hab1 : a1 ≤ b1 := by
        have h : (w0 : ℝ) * a1 ≤ (w0 : ℝ) * b1 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg1 : ∀ s ∈ Set.Icc a1 b1, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a1 b1, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 8 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (8 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab1 hg1 h4safe
      have hba1W : (w0 : ℝ) * (b1 - a1) = 1 / 24 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b1 - a1) = (s : ℝ) * ((w0 : ℝ) * (b1 - a1)) := by ring
      rw [hseqR, hc, hba1W] at hspan
      have : (s : ℝ) < 8 := by linarith
      have : s < 8 := by exact_mod_cast this
      omega
    · -- r = 9: the gap `[1/(6w₀), 11/(54w₀)]` (= `[2/3, 44/54]`) is a 1234-gap.
      set a9 : ℝ := 1 / (6 * (w0 : ℝ)) with ha9
      set b9 : ℝ := 11 / (54 * (w0 : ℝ)) with hb9
      have f0a : (w0 : ℝ) * a9 = 1 / 6 := by rw [ha9]; field_simp
      have f0b : (w0 : ℝ) * b9 = 11 / 54 := by rw [hb9]; field_simp
      have f1a : 3 * (w0 : ℝ) * a9 = 1 / 2 := by rw [ha9]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b9 = 11 / 18 := by rw [hb9]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a9 = 2 / 3 := by rw [ha9]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b9 = 22 / 27 := by rw [hb9]; field_simp; ring
      have f3a : 9 * (w0 : ℝ) * a9 = 3 / 2 := by rw [ha9]; field_simp; ring
      have f3b : 9 * (w0 : ℝ) * b9 = 11 / 6 := by rw [hb9]; field_simp; ring
      have hab9 : a9 ≤ b9 := by
        have h : (w0 : ℝ) * a9 ≤ (w0 : ℝ) * b9 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg9 : ∀ s ∈ Set.Icc a9 b9, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a9 b9, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 9 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (9 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab9 hg9 h4safe
      have hba9W : (w0 : ℝ) * (b9 - a9) = 1 / 27 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b9 - a9) = (s : ℝ) * ((w0 : ℝ) * (b9 - a9)) := by ring
      rw [hseqR, hc, hba9W] at hspan
      have : (s : ℝ) < 9 := by linarith
      have : s < 9 := by exact_mod_cast this
      omega

/-- **Corollary 16, unconditional.** `v₄ < 2` (`w₃ < 2 w₂`), now that Lemma 13
    discharges the `q ≥ 5` side condition. -/
theorem bhk_prop11_v4_lt_2v3_uncond (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6) :
    (w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ) :=
  bhk_prop11_v4_lt_2v3 w hmono hpos hsum hsmall hcover
    (bhk_prop11_lemma13 w hmono hpos hsum hsmall hcover)

/-- **Lemma 17, unconditional.** `v₄ = r/q` and `v₅ = s/q` (`g ∣ w₃ ∧ g ∣ w₄`
    for `g = gcd(w₀,w₂)`), with the `q ≥ 5` side condition discharged by
    Lemma 13. This is the rational structure Part 3 feeds to the main lemma. -/
theorem bhk_prop11_lemma17_uncond (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6) :
    Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨3, by omega⟩ ∧
      Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨4, by omega⟩ :=
  bhk_prop11_lemma17 w hmono hpos hsum hsmall hcover
    (bhk_prop11_lemma13 w hmono hpos hsum hsmall hcover)

/-- **BHK §5 Part 3 — the no-good-time fact (eq. (36)–(37)).** Under the
    covering assumption, there is *no* half-integer time `t` (`{w₂ t} = 1/2`)
    with runner 1 in `[1/6, 1/3]` *and* runner 4 in `[1/6, 1/2]`. Such a `t`
    would extend the `123`-gap `[t, t + 1/(3w₂)]` to a `1234`-gap
    `[t, t + 1/(3w₃)]` (runner 4 stays within `[1/6, 5/6]` across it), which
    runner 5 cannot cover (`bhk_prop11_gap1234_b5span` would force `w₄ < w₃`).
    Equivalently: the set `S = {({v₄(l+½)}, {v₁(l+½)})}` avoids the `1/3 × 1/6`
    rectangle `R`, the hypothesis of the main-lemma application. -/
theorem bhk_prop11_no_good_time (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3)
    (h4lo : 1 / 6 ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h4hi : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 1 / 2) :
    False := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3pos : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
  have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
  have hgap2 := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  set b3 : ℝ := t + 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) with hb3
  have hab3 : t ≤ b3 := by rw [hb3]; exact le_add_of_nonneg_right (by positivity)
  have hlen_le : 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  -- The `123`-gap restricted to the shorter interval.
  have hgap_sub : ∀ s ∈ Set.Icc t b3, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    exact hgap2 s ⟨hs.1, by rw [hb3] at hs; linarith [hs.2]⟩ i
  -- Runner 4 stays safe across `[t, b3]`.
  have h4safe : ∀ s ∈ Set.Icc t b3, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hdu : (w ⟨3, by omega⟩ : ℝ) * (s - t) ≤ 1 / 3 := by
      have h1 : (w ⟨3, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left (by rw [hb3] at hs; linarith [hs.2]) hw3pos.le
      have h2 : (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) = 1 / 3 := by
        field_simp
      linarith [h1, h2]
    have hbnn : 0 ≤ (w ⟨3, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw3pos.le hd0
    have hfs : Int.fract ((w ⟨3, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) + (w ⟨3, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨3, by omega⟩ : ℝ) * s
            = (w ⟨3, by omega⟩ : ℝ) * t + (w ⟨3, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith) (by linarith)]
    simp only [circDist]; rw [hfs]; exact le_min (by linarith) (by linarith)
  have hspan := bhk_prop11_gap1234_b5span w hpos hcover hab3 hgap_sub h4safe
  rw [hb3, add_sub_cancel_left, mul_one_div, div_lt_iff₀ (by positivity)] at hspan
  -- hspan : w₄ < 1/3 * (3 * w₃) = w₃, contradicting w₃ < w₄.
  nlinarith [hspan, hw34]

/-- **BHK §5 Part 3 — the exceptional pair (`q ≥ 18` branch).** Wiring the
    no-good-time fact into the main-lemma application. Writing `g = gcd(w₀,w₂)`,
    `p = w₀/g`, `q = w₂/g`, `r = w₃/g`, `s = w₄/g` (Lemma 17 gives `g ∣ w₃, w₄`),
    the set `S = {({v₄(l+½)}, {v₁(l+½)})}` avoids the `1/3 × 1/6` rectangle `R`,
    so `bhk_corollary_6` (its hypothesis `αβ = 1/18 ≥ 1/q` holding iff `q ≥ 18`)
    yields a nonzero *exceptional generator pair* `(i,j)` in the cone
    `0 ≤ i < 6`, `|j| < 3 + i/2`. Parts 4–6 then rule out every such pair. -/
theorem bhk_prop11_exceptional_q18 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((w i : ℝ) * t) < 1 / 6)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) :
    ∃ g p q r s : ℕ, 0 < g ∧
      w ⟨0, by omega⟩ = g * p ∧ w ⟨2, by omega⟩ = g * q ∧
      w ⟨3, by omega⟩ = g * r ∧ w ⟨4, by omega⟩ = g * s ∧
      Nat.gcd p q = 1 ∧ 18 ≤ q ∧
      ∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
        (∃ k : ℤ, Int.fract ((ij.1 : ℝ) / q) = Int.fract ((k : ℝ) * r / q) ∧
                  Int.fract ((ij.2 : ℝ) / q) = Int.fract ((k : ℝ) * p / q)) ∧
        0 ≤ ij.1 ∧ (ij.1 : ℝ) < 6 ∧
        -3 - 1 / 2 * (ij.1 : ℝ) < (ij.2 : ℝ) ∧ (ij.2 : ℝ) < 3 + 1 / 2 * (ij.1 : ℝ) := by
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgw0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
  have hgw2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
  obtain ⟨hgw3, hgw4⟩ := bhk_prop11_lemma17_uncond w hmono hpos hsum hsmall hcover
  set p : ℕ := w ⟨0, by omega⟩ / g with hpdef
  set q : ℕ := w ⟨2, by omega⟩ / g with hqdef
  set r : ℕ := w ⟨3, by omega⟩ / g with hrdef
  set s : ℕ := w ⟨4, by omega⟩ / g with hsdef
  have hp : w ⟨0, by omega⟩ = g * p := (Nat.mul_div_cancel' hgw0).symm
  have hq : w ⟨2, by omega⟩ = g * q := (Nat.mul_div_cancel' hgw2).symm
  have hr : w ⟨3, by omega⟩ = g * r := (Nat.mul_div_cancel' hgw3).symm
  have hs : w ⟨4, by omega⟩ = g * s := (Nat.mul_div_cancel' hgw4).symm
  have hcop : Nat.gcd p q = 1 := Nat.coprime_div_gcd_div_gcd hg_pos
  have hqpos : 0 < q := by omega
  -- Cast helpers.
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hr
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
  -- The no-good-time fact transported to `(r/q, p/q)` ratios.
  have h_nogood : ∀ k : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3)) := by
    intro k hk
    obtain ⟨hrmem, hpmem⟩ := hk
    set t : ℝ := ((k : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (k : ℝ) + 1 / 2 := by
      rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time w hmono hpos hsum hsmall hcover t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  obtain ⟨ij, hne, hmem, h0, h1β, hc1, hc2⟩ :=
    bhk_part3_exceptional r p q (by omega) hcop h_nogood
  exact ⟨g, p, q, r, s, hg_pos, hp, hq, hr, hs, hcop, by omega, ij, hne, hmem, h0, h1β, hc1, hc2⟩

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
