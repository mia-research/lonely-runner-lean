import LonelyRunner.LRC.Defs
import Mathlib

/-!
# The mirror centre of a lonely cell, at every order

2026-09-25.  Theorem 9 represents every lonely instant by the opening that begins its cell.  This
file gives the other end of the same picture: every lonely cell also contains the **mirror meeting**
of the runner that opens it and the runner that closes it, the instant where those two read `x` and
`1 − x`.  At the ideal (disparities `D, 2D, …, 7D` at order eight) the cell has width zero and the
mirror meeting is the global instant itself; in general it is that event, thickened.

Let `t > 0` be lonely at `1/n`.  For each disparity `d`, `T_d = (⌊d t⌋ + 1/n)/d` is its last
opening at or before `t` and `C_d = (⌊d t⌋ + 1 − 1/n)/d` its first closing at or after `t`.  With
`T = max T_d` (attained by `e`) and `C = min C_d` (attained by `e'`):

* every instant of `[T, C]` is lonely (`lonely_of_mem_window`);
* the mirror meeting `K/(e + e')`, `K = ⌊e t⌋ + ⌊e' t⌋ + 1`, lies in `[T, C]`.

Hence **lonely at some `t > 0` gives a lonely mirror meeting `K/(d + d')` of two disparities**
(`exists_lonely_mirror_meeting`), `d = d'` allowed (the half-lap point `K/(2d)`).  The converse is
immediate, so loneliness is equivalent to a lonely mirror meeting.  No hypothesis on `n` beyond the
loneliness itself, and the disparities are real.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.MirrorCentre

/-- A circular distance of at least `a` puts the fractional part in `[a, 1 − a]`. -/
theorem fract_bounds_of_circDist {x a : ℝ} (h : a ≤ circDist x) :
    a ≤ Int.fract x ∧ Int.fract x ≤ 1 - a := by
  unfold circDist at h
  exact ⟨le_trans h (min_le_left _ _), by linarith [min_le_right (Int.fract x) (1 - Int.fract x)]⟩

/-- A value within `[m + a, m + 1 − a]`, `m` an integer, is at circular distance at least `a`. -/
theorem circDist_ge_of_window {x a : ℝ} {m : ℤ} (h1 : (m : ℝ) + a ≤ x) (h2 : x ≤ (m : ℝ) + 1 - a)
    (ha : 0 < a) : a ≤ circDist x := by
  have hfl : ⌊x⌋ = m := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  have hfr : Int.fract x = x - m := by rw [Int.fract, hfl]
  unfold circDist
  rw [hfr]
  exact le_min (by linarith) (by linarith)

/-- **The window is lonely.**  If every disparity `x` has `⌊x t⌋ + a ≤ x·T` and
`x·C ≤ ⌊x t⌋ + 1 − a`, then every instant `s ∈ [T, C]` is lonely at `a`. -/
theorem lonely_of_mem_window {S : Finset ℝ} (hpos : ∀ d ∈ S, 0 < d) {a t T C s : ℝ} (ha : 0 < a)
    (hT : ∀ x ∈ S, (⌊x * t⌋ : ℝ) + a ≤ x * T) (hC : ∀ x ∈ S, x * C ≤ (⌊x * t⌋ : ℝ) + 1 - a)
    (hs1 : T ≤ s) (hs2 : s ≤ C) : ∀ x ∈ S, a ≤ circDist (x * s) := by
  intro x hx
  have hx0 := hpos x hx
  exact circDist_ge_of_window (m := ⌊x * t⌋)
    (le_trans (hT x hx) (mul_le_mul_of_nonneg_left hs1 hx0.le))
    (le_trans (mul_le_mul_of_nonneg_left hs2 hx0.le) (hC x hx)) ha

/-- **The mirror centre.**  If the subject is lonely at `1/n` at some `t > 0`, then some mirror
meeting `K/(d + d')` of two disparities `d, d'` (possibly equal) is lonely: at it `d` and `d'` read
`x` and `1 − x`.  It lies in the lonely cell of `t`, between the opening that begins that cell and
the closing that ends it. -/
theorem exists_lonely_mirror_meeting {n : ℕ} (hn : 0 < n) {S : Finset ℝ} (hpos : ∀ d ∈ S, 0 < d)
    (hne : S.Nonempty) {t : ℝ} (ht : 0 < t) (hl : ∀ d ∈ S, ((n : ℝ))⁻¹ ≤ circDist (d * t)) :
    ∃ d ∈ S, ∃ d' ∈ S, ∃ K : ℤ, 0 < (K : ℝ) / (d + d') ∧
      ∀ x ∈ S, ((n : ℝ))⁻¹ ≤ circDist (x * ((K : ℝ) / (d + d'))) := by
  set a : ℝ := ((n : ℝ))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  -- the last opening and first closing of each runner around t
  set Tf : ℝ → ℝ := fun d => ((⌊d * t⌋ : ℝ) + a) / d with hTf
  set Cf : ℝ → ℝ := fun d => ((⌊d * t⌋ : ℝ) + 1 - a) / d with hCf
  have hfr : ∀ d ∈ S, a ≤ Int.fract (d * t) ∧ Int.fract (d * t) ≤ 1 - a :=
    fun d hd => fract_bounds_of_circDist (hl d hd)
  have hdt : ∀ d ∈ S, d * t = (⌊d * t⌋ : ℝ) + Int.fract (d * t) :=
    fun d _ => (Int.floor_add_fract (d * t)).symm
  obtain ⟨e, he, hemax⟩ := S.exists_max_image Tf hne
  obtain ⟨e', he', hemin⟩ := S.exists_min_image Cf hne
  set T := Tf e with hTdef
  set C := Cf e' with hCdef
  have he0 := hpos e he
  have he'0 := hpos e' he'
  -- each runner, scaled: ⌊x t⌋ + a ≤ x T and x C ≤ ⌊x t⌋ + 1 − a
  have hT : ∀ x ∈ S, (⌊x * t⌋ : ℝ) + a ≤ x * T := by
    intro x hx
    have hx0 := hpos x hx
    have h := hemax x hx
    have : x * Tf x = (⌊x * t⌋ : ℝ) + a := by simp only [hTf]; field_simp
    calc (⌊x * t⌋ : ℝ) + a = x * Tf x := this.symm
      _ ≤ x * T := mul_le_mul_of_nonneg_left h hx0.le
  have hC : ∀ x ∈ S, x * C ≤ (⌊x * t⌋ : ℝ) + 1 - a := by
    intro x hx
    have hx0 := hpos x hx
    have h := hemin x hx
    have : x * Cf x = (⌊x * t⌋ : ℝ) + 1 - a := by simp only [hCf]; field_simp
    calc x * C ≤ x * Cf x := mul_le_mul_of_nonneg_left h hx0.le
      _ = (⌊x * t⌋ : ℝ) + 1 - a := this
  -- the window is non-empty: T ≤ t ≤ C
  have hTt : T ≤ t := by
    have h1 := (hfr e he).1
    have h2 := hdt e he
    simp only [hTdef, hTf]
    rw [div_le_iff₀ he0]; linarith
  have htC : t ≤ C := by
    have h1 := (hfr e' he').2
    have h2 := hdt e' he'
    simp only [hCdef, hCf]
    rw [le_div_iff₀ he'0]; linarith
  -- the mirror meeting
  set K : ℤ := ⌊e * t⌋ + ⌊e' * t⌋ + 1 with hK
  have hsum : 0 < e + e' := by linarith
  have heT : e * T = (⌊e * t⌋ : ℝ) + a := by simp only [hTdef, hTf]; field_simp
  have he'C : e' * C = (⌊e' * t⌋ : ℝ) + 1 - a := by simp only [hCdef, hCf]; field_simp
  have hTC : T ≤ C := le_trans hTt htC
  have hlo : T ≤ (K : ℝ) / (e + e') := by
    rw [le_div_iff₀ hsum]
    have : e' * T ≤ e' * C := mul_le_mul_of_nonneg_left hTC he'0.le
    push_cast [hK]; nlinarith
  have hhi : (K : ℝ) / (e + e') ≤ C := by
    rw [div_le_iff₀ hsum]
    have : e * T ≤ e * C := mul_le_mul_of_nonneg_left hTC he0.le
    push_cast [hK]; nlinarith
  have hTpos : 0 < T := by
    have hfl : (0 : ℤ) ≤ ⌊e * t⌋ := Int.floor_nonneg.mpr (by positivity)
    have : (0 : ℝ) ≤ (⌊e * t⌋ : ℝ) := by exact_mod_cast hfl
    simp only [hTdef, hTf]; positivity
  exact ⟨e, he, e', he', K, lt_of_lt_of_le hTpos hlo,
    lonely_of_mem_window hpos ha hT hC hlo hhi⟩

end LRC.MirrorCentre
