import LonelyRunner.LRC.Spec.ZoneLinkN

/-!
# Symbolic mechanisms extracted from the cascade map

Source: running log E333 (the closer) and E344 (two earlier captures).
Coordinates: positive subject disparities rho and positions in eighths.
The statements are uniform in every displayed speed, phase, and lap parameter.
They do not assume that every cascade has the required earlier captures.
No enumeration, floating-point decision, or numerical certificate is used.
-/

namespace LRC.MappedCascadeRules

/-- At a clear event, a faster reading reaches its next entering edge before
the opener can traverse its own whole clear band. The phase p is in eighths. -/
theorem faster_closes_before_opener {a d p : ℝ} (ha : 0 < a)
    (had : a < d) (hp : 1 ≤ p) : (7 - p) / d < 6 / a := by
  have hd : 0 < d := lt_trans ha had
  apply (div_lt_div_iff₀ hd ha).mpr
  nlinarith

/-- If the opener's own next entering edge is earliest, no reading is faster.
This includes ties between closers; positivity of the window is not needed. -/
theorem own_closer_maximal (S : Finset ι) (d p : ι → ℝ) {a : ℝ}
    (ha : 0 < a) (hp : ∀ i ∈ S, 1 ≤ p i)
    (hcloser : ∀ i ∈ S, 6 / a ≤ (7 - p i) / d i) :
    ∀ i ∈ S, d i ≤ a := by
  intro i hi
  by_contra h
  have hf := faster_closes_before_opener ha (lt_of_not_ge h) (hp i hi)
  exact (not_lt_of_ge (hcloser i hi)) hf

/-- Any positive-lap setter exiting before a's lap-1 opening is faster than a. -/
theorem earlier_setter_faster {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (j : ℕ) (hj : 1 ≤ j)
    (hearlier : (8 * (j : ℝ) + 1) / d < 9 / a) : a < d := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he := (div_lt_div_iff₀ hd ha).mp hearlier
  nlinarith

/-- E333's excluded K2s1 class: at a lap-1 landing preceded by another
positive-lap setter, that previous reading closes strictly before the opener.
Only its clear phase at the landing is used; no window on the speeds is imposed. -/
theorem previous_setter_closes_first {a d p : ℝ} (ha : 0 < a) (hd : 0 < d)
    (j : ℕ) (hj : 1 ≤ j) (hp : 1 ≤ p)
    (hearlier : (8 * (j : ℝ) + 1) / d < 9 / a) :
    (7 - p) / d < 6 / a :=
  faster_closes_before_opener ha (earlier_setter_faster ha hd j hj hearlier) hp

/-- The next entering edge of a reading after a clear phase has the stated
remaining travel time, with its integer lap retained exactly. -/
theorem closing_displacement {d R p : ℝ} (hd : d ≠ 0) (k : ℤ)
    (hphase : d * R = 8 * (k : ℝ) + p) :
    (8 * (k : ℝ) + 7) / d - R = (7 - p) / d := by
  apply (div_left_inj' hd).mp
  field_simp
  nlinarith

/-- Two lower constraints from earlier captures multiply to a lower bound
on the later opener. Closed inequalities also cover limiting boundary shapes. -/
theorem two_capture_speed_bound {b c G A B C : ℝ}
    (hG : 0 < G) (hA : 0 ≤ A)
    (hgate : C ≤ G * c) (hlink : A * c ≤ B * b) :
    A * C ≤ G * B * b := by
  have h1 := mul_le_mul_of_nonneg_left hgate hA
  have h2 := mul_le_mul_of_nonneg_left hlink hG.le
  nlinarith

/-- Any later opening on lap J is bounded by the product of the two earlier
capture factors. Existence of the two captures is an explicit hypothesis. -/
theorem two_capture_opening_bound {b c G : ℝ} (hb : 0 < b) (hG : 0 < G)
    (k L H J : ℕ) (hL : 1 ≤ L) (hH : 1 ≤ H)
    (hgate : 8 * (H : ℝ) - 1 ≤ G * c)
    (hlink : (8 * (L : ℝ) - 1) * c ≤ (8 * (k : ℝ) + 1) * b) :
    (8 * (J : ℝ) + 1) / b ≤
      G * (8 * (J : ℝ) + 1) * (8 * (k : ℝ) + 1) /
        ((8 * (L : ℝ) - 1) * (8 * (H : ℝ) - 1)) := by
  have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hj : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hden : 0 < (8 * (L : ℝ) - 1) * (8 * (H : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hs := two_capture_speed_bound hG
    (by linarith : 0 ≤ 8 * (L : ℝ) - 1) hgate hlink
  apply (div_le_div_iff₀ hb hden).mpr
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * (J : ℝ) + 1)
  nlinarith

/-- Connect the product rule to the map's actual exit-to-capture relation,
rather than requiring an independently supplied linear link certificate. -/
theorem opening_bound_of_zone_link {b c G : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hG : 0 < G) (k L H J : ℕ) (hL : 1 ≤ L) (hH : 1 ≤ H)
    (hgate : 8 * (H : ℝ) - 1 < G * c)
    (hlink : ZoneLink.InZone c b k L) :
    (8 * (J : ℝ) + 1) / b ≤
      G * (8 * (J : ℝ) + 1) * (8 * (k : ℝ) + 1) /
        ((8 * (L : ℝ) - 1) * (8 * (H : ℝ) - 1)) := by
  exact two_capture_opening_bound hb hG k L H J hL hH hgate.le
    ((ZoneLink.inZone_iff hc hb).mp hlink).1.le

/-- E344's late cell bound is an exact instance, not a numerical LP assertion.
No bound for arrangements lacking these two earlier constraints is asserted. -/
theorem mapped_late_bound {b c : ℝ} (hb : 0 < b)
    (hgate : 47 ≤ 9 * c) (hlink : 47 * c ≤ 33 * b) :
    89 / b ≤ (26433 : ℝ) / 2209 ∧ (26433 : ℝ) / 2209 < 12 := by
  have h := two_capture_opening_bound (c := c) hb (by norm_num : (0 : ℝ) < 9)
    4 6 6 11 (by norm_num) (by norm_num) (by norm_num; exact hgate)
    (by norm_num; exact hlink)
  constructor
  · norm_num at h
    exact h
  · norm_num

end LRC.MappedCascadeRules
