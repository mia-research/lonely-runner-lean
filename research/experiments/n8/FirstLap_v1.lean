import Mathlib

/-!
# First-lap clearance

The extremal shadowing exception over multisets of seven positive differences with `gcd = 1`
is `(2,3,4,5,6,7,16)`: six of its seven flanks are shadowed, and the survivor is `e = 16`,
clear at `A = 9`.

Reading the survivor off directly: `9*d` for `d = 2,…,7` is `18, 27, 36, 45, 54, 63`, every
one inside `[16, 112] = [e, 7e]`, and none of them reaches `8e = 128`. No modular reduction
happens at all — the residue *is* the product. That is the whole mechanism, and it needs no
hypothesis about the flank being largest, nor any denominator:

```
    e ≤ d*A ≤ 7e   for every other difference d   ⟹   the flank is clear at A.
```

An admissible `A` exists exactly when the other differences fit in a window of ratio 7 — the
flank itself is exempt, since a flank never blocks its own openings. For `e = 16` the window
is `A ∈ [e/2, 7e/7] = [8, 16]`, and `A = 9` is the unique `A ≡ 1 (mod 8)` in it.

Native counts backing this up, both verified exhaustively:
* with `gcd = 1` over the multiset, every flank has **exactly `e`** openings (`L = e`);
* a mover `d` covers exactly `c * gcd(d,e)` of them, `c` its blocked classes mod `q`.
The resulting count `Σ_j c_j * gcd(d_j,e) ≥ e` is **necessary but not sufficient** for
shadowing: at `e = 16` it gives `24 ≥ 16` and the flank is clear regardless.
-/

namespace FirstLap

/-- Runner at difference `d` is in the way at the opening of flank `e` with numerator `A`. -/
def inWay (d A e : ℤ) : Prop :=
  min ((d * A) % (8 * e)) (8 * e - (d * A) % (8 * e)) < e

/-- **No wraparound.**  If `0 ≤ d*A ≤ 7e` then the residue is the product itself. -/
theorem residue_eq_of_window {d A e : ℤ} (he : 0 < e) (h0 : 0 ≤ d * A) (h7 : d * A ≤ 7 * e) :
    (d * A) % (8 * e) = d * A :=
  Int.emod_eq_of_lt h0 (by omega)

/-- **First-lap clearance, one mover.**  A difference lying in the window `[e, 7e]` after
scaling by `A` is not in the way. -/
theorem not_inWay_of_window {d A e : ℤ} (he : 0 < e) (hlo : e ≤ d * A) (hhi : d * A ≤ 7 * e) :
    ¬ inWay d A e := by
  unfold inWay
  rw [residue_eq_of_window he (by omega) hhi]
  simp only [not_lt, le_min_iff]
  exact ⟨hlo, by omega⟩

/-- **First-lap clearance, whole flank.**  If every difference at the flank lands in `[e, 7e]`
when scaled by the opening numerator, the flank is clear there — hence the subject is lonely
at the instant `A / (8e)`. No hypothesis on denominators, sizes or which flank this is. -/
theorem flank_clear_of_window {ds : List ℤ} {A e : ℤ} (he : 0 < e)
    (h : ∀ d ∈ ds, e ≤ d * A ∧ d * A ≤ 7 * e) :
    ∀ d ∈ ds, ¬ inWay d A e := by
  intro d hd
  exact not_inWay_of_window he (h d hd).1 (h d hd).2

/-- **The window criterion in terms of the differences.**  If every difference lies between
`e/A` and `7e/A` — stated multiplicatively to stay in `ℤ` — the flank is clear at `A`. -/
theorem flank_clear_of_bounds {ds : List ℤ} {A e dlo dhi : ℤ} (he : 0 < e) (hA : 0 < A)
    (hlo : e ≤ dlo * A) (hhi : dhi * A ≤ 7 * e)
    (hds : ∀ d ∈ ds, dlo ≤ d ∧ d ≤ dhi) :
    ∀ d ∈ ds, ¬ inWay d A e := by
  intro d hd
  obtain ⟨h1, h2⟩ := hds d hd
  refine not_inWay_of_window he (le_trans hlo ?_) (le_trans ?_ hhi) <;>
    exact mul_le_mul_of_nonneg_right (by omega) (by omega)

/-- **The extremal exception, closed.**  The survivor flank of `(2,3,4,5,6,7,16)` is clear at
`A = 9`: every other difference lies in `[2,7]`, and `2*9 = 18 ≥ 16` with `7*9 = 63 ≤ 112`. -/
theorem extremal_survivor : ∀ d ∈ [(2:ℤ),3,4,5,6,7], ¬ inWay d 9 16 := by
  intro d hd
  refine flank_clear_of_bounds (dlo := 2) (dhi := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ d hd
  intro x hx
  fin_cases hx <;> constructor <;> norm_num

/-! ## The window witness respects the cap

`Spec/Doors.lean` names `DoorFirstLap`: the cascade never passes `1/e`, one lap of the nearest
runner.  That is a different statement from the clearance above — same phrase, different object —
but the two meet here.  A window witness has `d*A ≤ 7e < 8e` for **every** runner, so at the
instant `A/(8e)` no runner has completed a lap relative to the subject.  The witness produced by
first-lap clearance therefore lies under the cap, rather than merely somewhere. -/

/-- The window never reaches a full period. -/
theorem window_before_full_lap {d A e : ℤ} (he : 0 < e) (hhi : d * A ≤ 7 * e) :
    d * A < 8 * e := by omega

/-- **The witness lies inside the first lap.**  Over the reals, the opening `A/(8e)` supplied by
a window is strictly below `1/d` for every difference `d` in that window. -/
theorem opening_lt_first_lap {d A e : ℝ} (he : 0 < e) (hd : 0 < d)
    (h : d * A ≤ 7 * e) : A / (8 * e) < 1 / d := by
  rw [div_lt_div_iff₀ (by linarith) hd]
  linarith

end FirstLap

#print axioms FirstLap.residue_eq_of_window
#print axioms FirstLap.not_inWay_of_window
#print axioms FirstLap.flank_clear_of_window
#print axioms FirstLap.flank_clear_of_bounds
#print axioms FirstLap.extremal_survivor
#print axioms FirstLap.window_before_full_lap
#print axioms FirstLap.opening_lt_first_lap
