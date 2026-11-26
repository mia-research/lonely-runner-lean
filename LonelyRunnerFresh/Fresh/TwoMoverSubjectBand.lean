import Fresh.CascadeLandingG
import Fresh.TwoMoverLandingAll

/-!
Rules: 1–4, 8–18. New symbolic A04/A05 subject-mover family.
The frozen readings lie in their native first-lap band [a,b]. A free reading
that is captured at the a-opening exits before b closes when
`2*a*b ≤ (7*a-b)*d`. The actual cascade either fixes at the a-opening or
moves to that reading's own next opening. Closed equality edges are retained.
This is a local retained-phase statement, not a universal move budget.
-/

open Classical
namespace Fresh.OneMover
open Fresh

/-- An actually captured reading exits less than a quarter of its own lap later. -/
theorem subject_nextOpening_lt {d t : ℝ} (hd : 0 < d) (hw : InWay d t) :
    nextOpening d t < t + 1 / (4*d) := by
  obtain ⟨k, hk⟩ := Fresh.Cascade.exists_near_int hw
  rw [Fresh.Cascade.nextOpening_eq hk]
  apply (div_lt_iff₀ hd).2
  have hk' := (abs_lt.mp hk).1
  have he : (t + 1 / (4*d))*d = t*d + 1/4 := by field_simp
  rw [he]
  linarith

/-- Actual first cascade displacement for a first-lap frozen band and one outsider.
Every named disparity is retained; a captured outsider is the only setter. -/
theorem subject_band_first {ds : Finset ℝ} {a b d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (had : a ≤ d)
    (hamem : a ∈ ds) (hdmem : d ∈ ds)
    (hshape : ∀ e ∈ ds, e = d ∨ (a ≤ e ∧ e ≤ b))
    (hretain : 2*a*b ≤ (7*a-b)*d) :
    ∃ T : ℝ, 1/(8*a) ≤ T ∧ IsMove ds (1/(8*a)) T ∧
      Fresh.Cascade.LonelyAt ds T ∧
      (∀ s : ℝ, 0 < s → Fresh.Cascade.LonelyAt ds s → T ≤ s) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hd : 0 < d := lt_of_lt_of_le ha had
  have hgap : 0 < 7*a-b := by
    by_contra hn
    have hn' : (7*a-b)*d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd.le
    have hp : 0 < 2*a*b := by positivity
    linarith
  have hratio : b ≤ 7*a := by linarith
  have hlen : 1/(8*a) + 1/(4*d) ≤ 7/(8*b) := by
    field_simp
    nlinarith
  have hband : ∀ e ∈ ds, e ≠ d → ∀ t : ℝ,
      1/(8*a) ≤ t → t ≤ 7/(8*b) → (1/8 : ℝ) ≤ distInt (e*t) := by
    intro e he hed t htl htr
    have heab := (hshape e he).resolve_left hed
    have he0 : 0 ≤ e := le_trans ha.le heab.1
    apply Fresh.Localisation.clear_of_window 0
    · have hlo : (1/8 : ℝ) ≤ e*(1/(8*a)) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        nlinarith [heab.1]
      have := mul_le_mul_of_nonneg_left htl he0
      push_cast
      linarith
    · have hhi : e*(7/(8*b)) ≤ (7/8 : ℝ) := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [heab.2]
      have := mul_le_mul_of_nonneg_left htr he0
      push_cast
      linarith
  have hclear0 : ∀ e ∈ ds, e ≠ d → ¬ InWay e (1/(8*a)) := by
    intro e he hed
    exact Fresh.Cascade.not_inWay_iff.mpr (hband e he hed _ le_rfl (by linarith [show 0 < 1/(4*d) by positivity]))
  by_cases hw : InWay d (1/(8*a))
  · have hTlo := (Fresh.Cascade.lt_nextOpening hd hw).le
    have hThi : nextOpening d (1/(8*a)) ≤ 7/(8*b) :=
      le_trans (subject_nextOpening_lt hd hw).le hlen
    refine ⟨nextOpening d (1/(8*a)), hTlo, ?_, ?_, ?_⟩
    · right
      refine ⟨d, hdmem, hw, rfl, ?_⟩
      intro e he hew
      by_cases hed : e = d
      · simpa [hed]
      · exact False.elim ((hclear0 e he hed) hew)
    · intro e he
      by_cases hed : e = d
      · rw [hed, Fresh.Cascade.distInt_at_nextOpening hd]
      · exact hband e he hed _ hTlo hThi
    · intro s hs hls
      have hslo := Fresh.Cascade.bound_le_of_lonely hamem ha hls hs
      by_contra hn
      exact (Fresh.Cascade.not_inWay_iff.mpr (hls d hdmem))
        (Fresh.Cascade.inWay_until_opening hd hw hslo (lt_of_not_ge hn))
  · refine ⟨1/(8*a), le_rfl, ?_, ?_, ?_⟩
    · left
      refine ⟨?_, rfl⟩
      intro e he
      by_cases hed : e = d
      · simpa [hed] using hw
      · exact hclear0 e he hed
    · intro e he
      by_cases hed : e = d
      · simpa [hed] using (Fresh.Cascade.not_inWay_iff.mp hw)
      · exact hband e he hed _ le_rfl (by linarith [show 0 < 1/(4*d) by positivity])
    · intro s hs hls
      exact Fresh.Cascade.bound_le_of_lonely hamem ha hls hs

#print axioms subject_nextOpening_lt
#print axioms subject_band_first
end Fresh.OneMover
