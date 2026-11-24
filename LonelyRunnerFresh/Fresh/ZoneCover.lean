import Mathlib
import Fresh.M4SplitCheck

/-!
# Gap-pattern zones: an exact covering checker for "a clear instant for every reading vector"
(2026-11-22)

New file; nothing existing is edited.

**The object.**  Readings `g : Fin 7 → ℝ`, all positive.  A *gap pattern* `m : Fin 7 → ℕ` puts
reading `s` in the closed gap `[8 m_s + 1, 8 m_s + 7]` at the instant `R`.  For a fixed `m`, the
set of reading vectors having such an `R` is the zone

  `C_m = { g : (8 m_r + 1) · g_s ≤ (8 m_s + 7) · g_r  for all r, s }`

(take `R = max_r (8 m_r + 1)/g_r`; the pair conditions say exactly `R · g_s ≤ 8 m_s + 7`).
So "every reading vector of a region has a clear instant" is "the region lies in the union of
the zones `C_m`", and the faces of the `C_m` are ratio hyperplanes `g_s / g_r = c`.

**The checker.**  A zone is a 7×7 matrix of bounds `(p, q)`, read `q · g_s ≤ p · g_r`.  The
root is the box.  A certificate tree either ends in a `leaf m` (the zone lies in `C_m`, a
pairwise test on the matrix entries) or `cut`s along a ratio hyperplane `q · g_s ≤ p · g_r`
into the two closed sides, whose matrices are updated through the new constraint
(`addC`, the one-constraint update of a difference-bound matrix, normalised by `gcd`).
Soundness needs only that every entry is a valid bound; tightness of the update is used by
the certificate generator, never by the proof.  The two sides cover the zone by `le_total`, so
no covering step is assumed: the cut is a case split.

`zc_sound`: a `true` verdict on a valid matrix gives, for every reading vector satisfying it,
an instant `R` at which every reading is in a closed gap, with reading `0` in a gap of index at
most `w`.  With `g 0 = 1` and `w = 0` that is a clear instant `R ∈ [1,7]` (`GoodR`).
The clear instant is the place: the first exit edge `(8 m_r + 1)/g_r` over the readings.
-/

namespace Fresh.ZoneCover

open Fresh Fresh.Certs Fresh.M4SplitCheck

/-! ## Data and the checker (natural-number arithmetic only) -/

/-- Entry `(r, s)` of a matrix (default `(0,0)`, the vacuous bound). -/
def getU (U : List (List (ℕ × ℕ))) (r s : ℕ) : ℕ × ℕ := (U.getD r []).getD s (0, 0)

/-- Divide a bound by the gcd of its two parts. -/
def bnorm (a : ℕ × ℕ) : ℕ × ℕ :=
  if Nat.gcd a.1 a.2 = 0 then a else (a.1 / Nat.gcd a.1 a.2, a.2 / Nat.gcd a.1 a.2)

/-- The bound along a path `x → r → s → y`. -/
def bmul3 (a c b : ℕ × ℕ) : ℕ × ℕ := bnorm (a.1 * c.1 * b.1, a.2 * c.2 * b.2)

/-- The smaller of two bounds. -/
def bmin (a b : ℕ × ℕ) : ℕ × ℕ := if a.1 * b.2 ≤ b.1 * a.2 then a else b

/-- Add the constraint `q · g_s ≤ p · g_r`. -/
def addC (U : List (List (ℕ × ℕ))) (r s p q : ℕ) : List (List (ℕ × ℕ)) :=
  (List.range 7).map (fun x => (List.range 7).map (fun y =>
    bmin (getU U x y) (bmul3 (getU U x r) (p, q) (getU U s y))))

/-- The zone of a box (faces `[a_i/2, b_i/2]`): `a_r · g_s ≤ b_s · g_r`, and `1 · g_r ≤ 1 · g_r`. -/
def rootZ (box : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  (List.range 7).map (fun r => (List.range 7).map (fun s =>
    if r = s then (1, 1) else ((box.getD s (0, 0)).2, (box.getD r (0, 0)).1)))

/-- The zone lies in `C_m`, and reading `0`'s gap index is at most `w`. -/
def leafOKz (w : ℕ) (m : List ℕ) (U : List (List (ℕ × ℕ))) : Bool :=
  decide (m.getD 0 0 ≤ w) &&
  (List.range 7).all (fun r => (List.range 7).all (fun s =>
    decide (0 < (getU U r s).2) &&
    decide ((getU U r s).1 * (8 * m.getD r 0 + 1) ≤ (8 * m.getD s 0 + 7) * (getU U r s).2)))

/-- Certificate trees. -/
inductive ZT where
  | leaf (m : List ℕ)
  | cut (r s p q : ℕ) (a b : ZT)

/-- The verdict of a certificate on a zone. -/
def zc (w : ℕ) : ZT → List (List (ℕ × ℕ)) → Bool
  | .leaf m, U => leafOKz w m U
  | .cut r s p q a b, U =>
      decide (r < 7) && decide (s < 7) && zc w a (addC U r s p q) && zc w b (addC U s r q p)

/-! ## Soundness -/

/-- Every entry is a valid bound for `g`. -/
-- STANDING: DEFINITION
def Valid (U : List (List (ℕ × ℕ))) (g : Fin 7 → ℝ) : Prop :=
  ∀ r s : Fin 7, ((getU U r s).2 : ℝ) * g s ≤ ((getU U r s).1 : ℝ) * g r

theorem bnorm_valid {a : ℕ × ℕ} {u v : ℝ} (h : (a.2 : ℝ) * u ≤ (a.1 : ℝ) * v) :
    ((bnorm a).2 : ℝ) * u ≤ ((bnorm a).1 : ℝ) * v := by
  unfold bnorm
  split_ifs with hd
  · exact h
  · set d := Nat.gcd a.1 a.2
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have h1 : (a.1 : ℝ) = d * ((a.1 / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a.1 a.2)).symm
    have h2 : (a.2 : ℝ) = d * ((a.2 / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a.1 a.2)).symm
    rw [h1, h2] at h
    have h' : d * (((a.2 / d : ℕ) : ℝ) * u) ≤ d * (((a.1 / d : ℕ) : ℝ) * v) := by linarith
    exact le_of_mul_le_mul_left h' hdpos

theorem bmul3_valid {a c b : ℕ × ℕ} {gx gr gs gy : ℝ} (hr : 0 ≤ gr) (hs : 0 ≤ gs)
    (ha : (a.2 : ℝ) * gr ≤ (a.1 : ℝ) * gx) (hc : (c.2 : ℝ) * gs ≤ (c.1 : ℝ) * gr)
    (hb : (b.2 : ℝ) * gy ≤ (b.1 : ℝ) * gs) :
    ((bmul3 a c b).2 : ℝ) * gy ≤ ((bmul3 a c b).1 : ℝ) * gx := by
  unfold bmul3
  apply bnorm_valid
  simp only [Nat.cast_mul]
  have e1 : (0 : ℝ) ≤ a.2 := Nat.cast_nonneg _
  have e2 : (0 : ℝ) ≤ c.2 := Nat.cast_nonneg _
  have e3 : (0 : ℝ) ≤ b.1 := Nat.cast_nonneg _
  have e4 : (0 : ℝ) ≤ c.1 := Nat.cast_nonneg _
  calc (a.2 : ℝ) * c.2 * b.2 * gy = (a.2 * c.2) * (b.2 * gy) := by ring
    _ ≤ (a.2 * c.2) * (b.1 * gs) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (a.2 * b.1) * (c.2 * gs) := by ring
    _ ≤ (a.2 * b.1) * (c.1 * gr) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (b.1 * c.1) * (a.2 * gr) := by ring
    _ ≤ (b.1 * c.1) * (a.1 * gx) := mul_le_mul_of_nonneg_left ha (by positivity)
    _ = a.1 * c.1 * b.1 * gx := by ring

theorem bmin_valid {a b : ℕ × ℕ} {u v : ℝ} (ha : (a.2 : ℝ) * u ≤ (a.1 : ℝ) * v)
    (hb : (b.2 : ℝ) * u ≤ (b.1 : ℝ) * v) :
    ((bmin a b).2 : ℝ) * u ≤ ((bmin a b).1 : ℝ) * v := by
  unfold bmin; split_ifs <;> assumption

theorem getU_map (f : ℕ → ℕ → ℕ × ℕ) (x y : Fin 7) :
    getU ((List.range 7).map (fun x => (List.range 7).map (fun y => f x y))) x y = f x y := by
  simp [getU, List.getD_eq_getElem?_getD]

theorem addC_valid {U : List (List (ℕ × ℕ))} {g : Fin 7 → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hU : Valid U g) (r s : Fin 7) (p q : ℕ) (hc : (q : ℝ) * g s ≤ (p : ℝ) * g r) :
    Valid (addC U r s p q) g := by
  intro x y
  unfold addC
  rw [getU_map]
  exact bmin_valid (hU x y) (bmul3_valid (hg r) (hg s) (hU x r) hc (hU s y))

theorem rootZ_valid {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ} (hb : InBox 1 box g) :
    Valid (rootZ box) g := by
  intro r s
  unfold rootZ
  rw [getU_map]
  obtain ⟨-, hin⟩ := hb
  by_cases hrs : (r : ℕ) = (s : ℕ)
  · have : r = s := Fin.ext hrs
    subst this; simp
  · rw [if_neg hrs]
    simp only
    have h1 := (hin r).1
    have h2 := (hin s).2
    set a := ((box.getD r (0, 0)).1 : ℝ)
    set b := ((box.getD s (0, 0)).2 : ℝ)
    have ha : 0 ≤ a := Nat.cast_nonneg _
    have hb' : 0 ≤ b := Nat.cast_nonneg _
    simp only [pow_one] at h1 h2
    nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h1 hb']

/-- The leaf: a clear instant from a gap pattern. -/
theorem leafOKz_sound {w : ℕ} {m : List ℕ} {U : List (List (ℕ × ℕ))} {g : Fin 7 → ℝ}
    (hg : ∀ i, 0 < g i) (hU : Valid U g) (h : leafOKz w m U = true) :
    ∃ R : ℝ, (∀ s : Fin 7, ∃ j : ℤ, g s * R ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)) ∧
      ∃ k : ℕ, k ≤ w ∧ (8 * k + 1 : ℝ) ≤ g 0 * R ∧ g 0 * R ≤ 8 * k + 7 := by
  simp only [leafOKz, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hw, hall⟩ := h
  set M : Fin 7 → ℝ := fun i => (m.getD i 0 : ℝ) with hM
  -- the pair conditions `(8 m_r + 1) g_s ≤ (8 m_s + 7) g_r`
  have hpair : ∀ r s : Fin 7, (8 * M r + 1) * g s ≤ (8 * M s + 7) * g r := by
    intro r s
    obtain ⟨hq, hle⟩ := hall r r.isLt s s.isLt
    have hv := hU r s
    set e := getU U r s
    have hq' : (0 : ℝ) < e.2 := by exact_mod_cast hq
    have hle' : (e.1 : ℝ) * (8 * M r + 1) ≤ (8 * M s + 7) * e.2 := by
      have := (Nat.cast_le (α := ℝ)).mpr hle; push_cast at this; simpa [hM] using this
    have hMr : 0 ≤ 8 * M r + 1 := by positivity
    have hgr : 0 ≤ g r := (hg r).le
    have key : (e.2 : ℝ) * ((8 * M r + 1) * g s) ≤ (e.2 : ℝ) * ((8 * M s + 7) * g r) := by
      calc (e.2 : ℝ) * ((8 * M r + 1) * g s) = (8 * M r + 1) * (e.2 * g s) := by ring
        _ ≤ (8 * M r + 1) * (e.1 * g r) := mul_le_mul_of_nonneg_left hv hMr
        _ = (e.1 * (8 * M r + 1)) * g r := by ring
        _ ≤ ((8 * M s + 7) * e.2) * g r := mul_le_mul_of_nonneg_right hle' hgr
        _ = (e.2 : ℝ) * ((8 * M s + 7) * g r) := by ring
    exact le_of_mul_le_mul_left key hq'
  -- the instant: the largest first exit edge
  obtain ⟨r0, -, hr0⟩ := Finset.exists_max_image Finset.univ
    (fun r : Fin 7 => (8 * M r + 1) / g r) ⟨0, Finset.mem_univ _⟩
  set R := (8 * M r0 + 1) / g r0 with hR
  have hlow : ∀ s : Fin 7, 8 * M s + 1 ≤ g s * R := by
    intro s
    have := hr0 s (Finset.mem_univ _)
    rw [div_le_iff₀ (hg s)] at this
    linarith [mul_comm (g s) R]
  have hhigh : ∀ s : Fin 7, g s * R ≤ 8 * M s + 7 := by
    intro s
    rw [hR, mul_div_assoc', div_le_iff₀ (hg r0)]
    have := hpair r0 s
    linarith [mul_comm (g s) (8 * M r0 + 1)]
  refine ⟨R, fun s => ⟨(m.getD s 0 : ℤ), ?_, ?_⟩, m.getD 0 0, hw, ?_, ?_⟩
  · have := hlow s; push_cast; simpa [hM] using this
  · have := hhigh s; push_cast; simpa [hM] using this
  · have := hlow 0; simpa [hM] using this
  · have := hhigh 0; simpa [hM] using this

#print axioms leafOKz_sound

theorem zc_sound (w : ℕ) (t : ZT) (U : List (List (ℕ × ℕ))) (h : zc w t U = true)
    (g : Fin 7 → ℝ) (hg : ∀ i, 0 < g i) (hU : Valid U g) :
    ∃ R : ℝ, (∀ s : Fin 7, ∃ j : ℤ, g s * R ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)) ∧
      ∃ k : ℕ, k ≤ w ∧ (8 * k + 1 : ℝ) ≤ g 0 * R ∧ g 0 * R ≤ 8 * k + 7 := by
  induction t generalizing U with
  | leaf m => exact leafOKz_sound hg hU h
  | cut r s p q a b iha ihb =>
    simp only [zc, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, hs⟩, ha⟩, hb⟩ := h
    have hg0 : ∀ i, 0 ≤ g i := fun i => (hg i).le
    rcases le_total ((q : ℝ) * g ⟨s, hs⟩) ((p : ℝ) * g ⟨r, hr⟩) with hc | hc
    · exact iha _ ha (addC_valid hg0 hU ⟨r, hr⟩ ⟨s, hs⟩ p q hc)
    · exact ihb _ hb (addC_valid hg0 hU ⟨s, hs⟩ ⟨r, hr⟩ q p hc)

#print axioms zc_sound

/-- **The M4 form**: on a box pinned at `g 0 = 1`, a `true` verdict with `w = 0` gives a clear
instant `R ∈ [1,7]` for every reading vector of the box. -/
theorem zc_goodR (t : ZT) (box : List (ℕ × ℕ)) (h : zc 0 t (rootZ box) = true)
    (g : Fin 7 → ℝ) (hb : InBox 1 box g) (hg : ∀ i, 0 < g i) (h0 : g 0 = 1) :
    ∃ R, GoodR g R := by
  obtain ⟨R, hall, k, hk, h1, h7⟩ := zc_sound 0 t _ h g hg (rootZ_valid hb)
  have hk0 : k = 0 := by omega
  subst hk0
  rw [h0, one_mul] at h1 h7
  refine ⟨R, by simpa using h1, by simpa using h7, fun i => ?_⟩
  exact (clearAt_R_iff (g i) R).mpr (hall i)

#print axioms zc_goodR

end Fresh.ZoneCover
