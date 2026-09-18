import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The neighbour at a grid instant is a function of the residues alone

Owner's question: *"does the variation away from AP/grid change the neighbour of the isolation
in a predictable way?"*

Write a commensurable arrangement in reduced units as `w i = π i + n · q i` — residue plus whole
laps.  Deformation therefore has two independent parts, and this file settles the `q` part.

At a grid instant `t = p/n`, runner `j`'s position relative to subject `i` is `gridPos n p (w j −
w i)`, and `gridPos_congr` shows that number depends on the disparity only through its residue
mod `n`.  `laps_invisible` is the consequence: moving whole laps moves nothing.  So the entire
cyclic ordering of the pack around the subject — hence which runner is nearest ahead and which
nearest behind — is fixed by `π`, and the `q` part of a deformation is invisible.

`neighbour_laps_invisible` states that for the nearest-ahead runner itself.

Verified 16,000 of 16,000 in `experiments/n8/neighbour_rule_v4.py`; the sharper `±p` form of the
rule (ahead is the runner at residue offset `p`, using `p⁻¹ = p` in the Klein group `(ℤ/8)ˣ`)
12,800 of 12,800 in `neighbour_rule_v1.py`.

Scope: **grid instants only.**  At the cascade's own instant the same invariance holds 10.4% of
the time, against a matched null of 1.9% (`neighbour_rule_v5.py`) — so residues carry real
information there, roughly 5× the null, and come nowhere near determining the answer.  See
`NEIGHBOUR_DEFORMATION_v1.md`.
Development file; nothing here is load-bearing for a manuscript result. -/

namespace GridNeighbour

/-- Runner `j`'s position relative to subject `i` at the grid instant `p/n`, where `d = w j − w i`
is the disparity in reduced (integer) units. -/
noncomputable def gridPos (n p : ℕ) (d : ℤ) : ℝ := Int.fract ((d : ℝ) * p / n)

theorem gridPos_eq (n p : ℕ) (d : ℤ) :
    gridPos n p d = (((d * p) % n : ℤ) : ℝ) / n := by
  unfold gridPos
  have h : (d : ℝ) * p / n = ((d * p : ℤ) : ℝ) / n := by push_cast; ring
  rw [h, Int.fract_div_intCast_eq_div_intCast_mod]

/-- **A relative position at a grid instant sees only the disparity's residue.** -/
theorem gridPos_congr (n p : ℕ) {d d' : ℤ} (h : d % n = d' % n) :
    gridPos n p d = gridPos n p d' := by
  rw [gridPos_eq, gridPos_eq, Int.mul_emod, h, ← Int.mul_emod]

/-- **Whole laps are invisible.**  Two arrangements with the same residues `π` and any whole-lap
parts `q`, `q'` put every runner at the same place relative to every subject, at every grid
instant.  Deforming `q` therefore cannot move the neighbour. -/
theorem laps_invisible (n p : ℕ) (π q q' : Fin 8 → ℤ) (i j : Fin 8) :
    gridPos n p ((π j + n * q j) - (π i + n * q i))
      = gridPos n p ((π j + n * q' j) - (π i + n * q' i)) := by
  refine gridPos_congr n p ?_
  have e1 : (π j + (n:ℤ) * q j) - (π i + (n:ℤ) * q i)
      = (π j - π i) + (n:ℤ) * (q j - q i) := by ring
  have e2 : (π j + (n:ℤ) * q' j) - (π i + (n:ℤ) * q' i)
      = (π j - π i) + (n:ℤ) * (q' j - q' i) := by ring
  rw [e1, e2, Int.add_mul_emod_self_left, Int.add_mul_emod_self_left]

/-- The nearest-ahead runner is the same under any whole-lap deformation: the two arrangements
present the subject with the *same function* `j ↦ gridPos`, so any selection rule stated in that
function — nearest ahead, nearest behind, the whole cyclic order — returns the same answer. -/
theorem neighbour_laps_invisible (n p : ℕ) (π q q' : Fin 8 → ℤ) (i : Fin 8) :
    (fun j => gridPos n p ((π j + n * q j) - (π i + n * q i)))
      = fun j => gridPos n p ((π j + n * q' j) - (π i + n * q' i)) :=
  funext fun j => laps_invisible n p π q q' i j



/-! ## Which runners can ever be the tight pair

The `±p` rule says the neighbour at instant `p` is at residue offset `±p`, and `p` runs over the
*units* mod `n`. So as the instant varies, a runner at offset `d` visits the slots `d·p`, which is
the orbit of `d` under multiplication by `(ℤ/n)ˣ` — and that orbit is pinned by `gcd (d, n)`.

The consequence is a floor no arrangement can lower: **a runner whose residue offset shares a
factor with `n` can never approach the subject.** At `n = 8` the orbits are `{0}`, `{1,3,5,7}`,
`{2,6}`, `{4}`, indexed by the 2-adic valuation, and the closest a runner at offset `d` ever comes
is exactly `2^ν₂(d) / 8` (`experiments/n8/offset_valuation_v1.py`, exhaustive over all 8 offsets ×
4 instants). So in *any* grid, 3 of the subject's 7 disparities — the ones at offsets 2, 4, 6 —
are structurally barred from ever being the binding constraint at a grid instant; offset 4 is
antipodal at every one of them.

This is the same object Barajas–Serra run the `n = 7` argument on, one prime down: there `ν` is
the 7-adic valuation, here `n = 8 = 2³` and it is the 2-adic one. -/

/-- The slot a runner at offset `d` occupies at instant `p` has the same gcd with `n` that the
offset does — multiplying by a unit cannot change it. -/
theorem slot_gcd (n : ℕ) (d p : ℤ) (hp : Int.gcd p n = 1) :
    Int.gcd ((d * p) % n) n = Int.gcd d n := by
  rw [Int.gcd_emod, Int.gcd_mul_left_left_of_gcd_eq_one hp]

/-- **The floor.**  A runner at offset `d` that is not sitting on the subject stands at least
`gcd (d, n)` slots from it, on both sides, at every grid instant. -/
theorem slot_ge (n : ℕ) (d p : ℤ) (hp : Int.gcd p n = 1) (h0 : (d * p) % n ≠ 0) (hn : 0 < n) :
    (Int.gcd d n : ℤ) ≤ (d * p) % n ∧ (Int.gcd d n : ℤ) ≤ n - (d * p) % n := by
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  have hlt : (d * p) % n < n := Int.emod_lt_of_pos _ hn'
  have hge : 0 ≤ (d * p) % n := Int.emod_nonneg _ (by omega)
  have hg := slot_gcd n d p hp
  have h1 : (Int.gcd d n : ℤ) ∣ (d * p) % n := by rw [← hg]; exact Int.gcd_dvd_left _ _
  have h2 : (Int.gcd d n : ℤ) ∣ (n : ℤ) := by rw [← hg]; exact Int.gcd_dvd_right _ _
  exact ⟨Int.le_of_dvd (by omega) h1, Int.le_of_dvd (by omega) (dvd_sub h2 h1)⟩

/-- The same floor as a distance: the runner's position is caged in `[gcd/n, 1 − gcd/n]`. -/
theorem gridPos_caged (n p : ℕ) (d : ℤ) (hp : Int.gcd (p:ℤ) n = 1) (h0 : (d * p) % n ≠ 0)
    (hn : 0 < n) :
    (Int.gcd d n : ℝ) / n ≤ gridPos n p d ∧ gridPos n p d ≤ 1 - (Int.gcd d n : ℝ) / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨hg1, hg2⟩ := slot_ge n d (p:ℤ) hp h0 hn
  rw [gridPos_eq]
  refine ⟨by gcongr; exact_mod_cast hg1, ?_⟩
  rw [le_sub_iff_add_le, ← add_div, div_le_one hn']
  exact_mod_cast (by omega : (d * (p:ℤ)) % n + (Int.gcd d n : ℤ) ≤ n)

/-- **At `n = 8`, an even residue offset is never the tight pair.**  It is caged at quarter
distance or beyond, at every one of the four grid instants, in every arrangement. -/
theorem even_offset_caged (p : ℕ) (d : ℤ) (hp : Int.gcd (p:ℤ) ((8:ℕ):ℤ) = 1) (hd : d % 2 = 0)
    (h0 : (d * p) % ((8:ℕ):ℤ) ≠ 0) :
    (2:ℝ) / 8 ≤ gridPos 8 p d ∧ gridPos 8 p d ≤ 1 - (2:ℝ) / 8 := by
  have h2N : (2:ℕ) ∣ Int.gcd d ((8:ℕ):ℤ) :=
    Int.dvd_gcd (Int.dvd_of_emod_eq_zero hd) (show (2:ℤ) ∣ ((8:ℕ):ℤ) by norm_num)
  have hgpos : 0 < Int.gcd d ((8:ℕ):ℤ) := Int.gcd_pos_of_ne_zero_right _ (by norm_num)
  have hge : (2:ℝ) ≤ ((Int.gcd d ((8:ℕ):ℤ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hgpos h2N
  obtain ⟨hlo, hhi⟩ := gridPos_caged 8 p d hp h0 (by norm_num)
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · gcongr; norm_num
  · gcongr; norm_num

end GridNeighbour
