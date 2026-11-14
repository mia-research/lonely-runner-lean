import Fresh.BandNoCarve

/-!
# The pinch-family data discharge: the seven h₃ plane windows (E843)

Written 2026-11-11.  New file; nothing existing is edited.  This implements E843's
compression (log `docs/n8/RUNNING_LOG_order8_v1.md` entry E843; artifacts
`experiments/n8/tail_h3_pinch_windows_v1.out` and `tail_h3_pinch_dump_v1.jsonl`): all 509
h₃ straddler boxes (`D = 512`, `a = 11`, `b = 3`, so `8b+1 = 25`) share ONE m-tuple over
just 7 plane-window cells `lo5P = hi5P = W`, `W ∈ {2645, 2646, 2647, 2686, 2687, 2726,
2727}`, each of width 1 with `W + 1 ≤ 12800 ≤ 7W` (the R*-in-[1,7] window
`hi5P+1 ≤ 25D ≤ 7·lo5P`).  Delivered here: the 7 parametric window theorems
`pinchWindow_<W>` (interval bounds ⇒ `Fresh.Pinch.PinchIntCond 11 3 (512:ℤ) k mj W W`),
the glue to `Fresh.BandNoCarve.BandPinch` (`rho5Window_of_inBox`, `bandPinch_of_window`,
`bandPinch_of_window_cell`), and one worked per-box instantiation (the first JSONL line,
`bandPinch_kBox1`).

## The index mapping (artifact 6-tuple → Lean `Fin 7`)

The artifact keeps the 6-tuple `k6 = (k[0],…,k[5])` of ρ₂..ρ₇ cells verbatim (E843 dump);
the Lean side is the E832 convention of `Fresh.CarveExclusionCerts`/`Fresh.BandNoCarve`:
readings `g : Fin 7 → ℝ` with `g 0 = ρ₁ = 1`, `g i = ρ_{i+1}`.  So artifact index `i`
is Lean index `i+1`:

| artifact | reading | Lean idx | in `PinchIntCond` | shared m |
|    0     |   ρ₂    |    1     |       yes         | `mj 1 = 1` |
|    1     |   ρ₃    |    2     |       yes         | `mj 2 = 1` |
|    2     |   ρ₄    |    3     |       yes         | `mj 3 = 2` |
|    3     |   ρ₅    |    4     | EXCLUDED (`i ≠ 4`) | — (`k 4 = W` is the ρ₅-window, glue) |
|    4     |   ρ₆    |    5     |       yes         | `mj 5 = 4` |
|    5     |   ρ₇    |    6     | EXCLUDED (`i ≠ 6`) | — (spans ≤ 5 cells per window, unbounded) |
|   none   |   ρ₁    |    0     |       yes         | `mj 0 = 0` (added, see below) |

The artifact k-intervals `[lo, hi]` per reading ARE the Lean `PinchIntCond` faces
rearranged: the low endpoint is exactly the binding case of `(8m+1)(W+1) ≤ 25k_i` and the
high endpoint of `25(k_i+1) ≤ (8m+7)W` (both clauses monotone in `k_i`, so the interval
implies both throughout) — e.g. W = 2645, ρ₂: `9·2646 = 23814 ≤ 25·953` and
`25·1587 = 39675 = 15·2645` (exactly tight).

**The one artifact-silent face, stated as a hypothesis and not hidden:** `PinchIntCond`'s
`∀ i ≠ 4, i ≠ 6` ranges over Lean index 0 = ρ₁ too, and the artifact (6-tuple over
ρ₂..ρ₇ with ρ₁ = 1 normalized away) records no ρ₁ cell.  Added uniformly: `k 0 ∈
[511, 512]` (both closed cells contain ρ₁ = 1 at `D = 512`) and `mj 0 = 0` — ρ₁'s own gap
at R*, exact: `25·g 0/g 4 ∈ [12775/2646, 12825/2645] ⊆ [1, 7] = [8·0+1, 8·0+7]` for every
window (slack is large: the faces need only `W ≤ 12774` and `W ≥ 1833`).

## Grading (rule 18) and divergences, stated honestly

* PROVED here: the 7 window theorems (pure integer arithmetic: the interval bounds at
  their endpoints, `omega`/`norm_num`), the ρ₅-window-from-box step, the glue, and the
  worked box.  All `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
* CITED, not replicated: E843's machine check — 509/509 boxes verified clause-for-clause
  (`tail_h3_pinch_dump_v1.py`, exact Fractions), 0 violations in 2036 membership checks
  (`tail_h3_pinch_windows_v1.py`).  No covering claim is made in this file (rule 7(b)):
  every theorem here is an implication over its box faces, vacuous off the box.
* OWED (data-side, not here): the per-box instantiation of the remaining 508 boxes (each
  JSONL line's `k6` into its window's intervals, `k 0 ∈ [511,512]` adjoined); the ρ₇ cell
  spans per window (`k5 ∈ [9419..9423]` etc., unconstrained in `PinchIntCond`); and the
  straddler-box three-region composition (off-plane sides) — that totality is
  `Fresh.BandNoCarve.BandCertData`'s hypothesis, not this file's.
-/

open Classical

namespace Fresh.BandPinchData

/-! ## The seven window theorems

Each takes the shared m-tuple as value hypotheses (`mj 0 = 0`, `mj 1 = 1`, `mj 2 = 1`,
`mj 3 = 2`, `mj 5 = 4`; indices 4 and 6 are `PinchIntCond`'s excluded ones) and the
window's per-reading k-intervals as hypotheses (Lean indices; `hk0` is the added ρ₁ face),
and concludes `PinchIntCond` at `lo5P = hi5P = W`.  The per-window intervals, from
`tail_h3_pinch_windows_v1.out` (artifact indices 0,1,2,4 = Lean 1,2,3,5):

W = 2645: ρ₂ [953,1586], ρ₃ [953,1586], ρ₄ [1800,2432], ρ₆ [3493,4125]
W = 2646: ρ₂ [953,1586], ρ₃ [953,1586], ρ₄ [1800,2433], ρ₆ [3495,4126]
W = 2647: ρ₂ [954,1587], ρ₃ [954,1587], ρ₄ [1801,2434], ρ₆ [3496,4128]
W = 2686: ρ₂ [968,1610], ρ₃ [968,1610], ρ₄ [1828,2470], ρ₆ [3547,4189]
W = 2687: ρ₂ [968,1611], ρ₃ [968,1611], ρ₄ [1828,2471], ρ₆ [3549,4190]
W = 2726: ρ₂ [982,1634], ρ₃ [982,1634], ρ₄ [1855,2506], ρ₆ [3600,4251]
W = 2727: ρ₂ [983,1635], ρ₃ [983,1635], ρ₄ [1856,2507], ρ₆ [3601,4253] -/

/-- Window W = 2645 (15 boxes in the dump; the interval tops are exactly tight:
`25·1587 = 39675 = 15·2645`). -/
theorem pinchWindow_2645 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 953 ≤ k 1 ∧ k 1 ≤ 1586) (hk2 : 953 ≤ k 2 ∧ k 2 ≤ 1586)
    (hk3 : 1800 ≤ k 3 ∧ k 3 ≤ 2432) (hk5 : 3493 ≤ k 5 ∧ k 5 ≤ 4125) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2645 2645 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2645

/-- Window W = 2646 (the ρ₇ five-cell window, `k5 ∈ [9419..9423]` data-side). -/
theorem pinchWindow_2646 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 953 ≤ k 1 ∧ k 1 ≤ 1586) (hk2 : 953 ≤ k 2 ∧ k 2 ≤ 1586)
    (hk3 : 1800 ≤ k 3 ∧ k 3 ≤ 2433) (hk5 : 3495 ≤ k 5 ∧ k 5 ≤ 4126) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2646 2646 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2646

/-- Window W = 2647. -/
theorem pinchWindow_2647 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 954 ≤ k 1 ∧ k 1 ≤ 1587) (hk2 : 954 ≤ k 2 ∧ k 2 ≤ 1587)
    (hk3 : 1801 ≤ k 3 ∧ k 3 ≤ 2434) (hk5 : 3496 ≤ k 5 ∧ k 5 ≤ 4128) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2647 2647 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2647

/-- Window W = 2686. -/
theorem pinchWindow_2686 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 968 ≤ k 1 ∧ k 1 ≤ 1610) (hk2 : 968 ≤ k 2 ∧ k 2 ≤ 1610)
    (hk3 : 1828 ≤ k 3 ∧ k 3 ≤ 2470) (hk5 : 3547 ≤ k 5 ∧ k 5 ≤ 4189) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2686 2686 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2686

/-- Window W = 2687 (the dump's modal window, 195 of the 509 boxes). -/
theorem pinchWindow_2687 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 968 ≤ k 1 ∧ k 1 ≤ 1611) (hk2 : 968 ≤ k 2 ∧ k 2 ≤ 1611)
    (hk3 : 1828 ≤ k 3 ∧ k 3 ≤ 2471) (hk5 : 3549 ≤ k 5 ∧ k 5 ≤ 4190) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2687 2687 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2687

/-- Window W = 2726. -/
theorem pinchWindow_2726 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 982 ≤ k 1 ∧ k 1 ≤ 1634) (hk2 : 982 ≤ k 2 ∧ k 2 ≤ 1634)
    (hk3 : 1855 ≤ k 3 ∧ k 3 ≤ 2506) (hk5 : 3600 ≤ k 5 ∧ k 5 ≤ 4251) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2726 2726 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2726

/-- Window W = 2727. -/
theorem pinchWindow_2727 {k mj : Fin 7 → ℤ}
    (hm0 : mj 0 = 0) (hm1 : mj 1 = 1) (hm2 : mj 2 = 1) (hm3 : mj 3 = 2) (hm5 : mj 5 = 4)
    (hk0 : 511 ≤ k 0 ∧ k 0 ≤ 512)
    (hk1 : 983 ≤ k 1 ∧ k 1 ≤ 1635) (hk2 : 983 ≤ k 2 ∧ k 2 ≤ 1635)
    (hk3 : 1856 ≤ k 3 ∧ k 3 ≤ 2507) (hk5 : 3601 ≤ k 5 ∧ k 5 ≤ 4253) :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj 2727 2727 := by
  unfold Fresh.Pinch.PinchIntCond
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro i hi4 hi6
    fin_cases i <;> simp_all
  · intro i hi4 hi6
    fin_cases i <;> simp_all <;> omega

#print axioms pinchWindow_2727

/-! ## The glue to `BandNoCarve.BandPinch` -/

/-- The InBox-implies-ρ₅-window step: when the ρ₅ cell IS the window (`k 4 = W`), the box
face `[k 4/D, (k 4+1)/D]` is exactly `BandPinch`'s window `[lo5P/D, (hi5P+1)/D]` at
`lo5P = hi5P = W`. -/
theorem rho5Window_of_inBox {D : ℕ} {W : ℤ} {k : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hbox : Fresh.Pinch.InBox D k g) (hk4 : k 4 = W) :
    ((W : ℝ)) / D ≤ g 4 ∧ g 4 ≤ ((W + 1 : ℤ) : ℝ) / D := by
  obtain ⟨hlo, hhi⟩ := hbox 4
  rw [hk4] at hlo hhi
  exact ⟨hlo, hhi⟩

#print axioms rho5Window_of_inBox

/-- The glue: a reading-vector in the dyadic box with ρ₅ in the plane region's grid window
`[W/512, (W+1)/512]`, exactly on the tangency plane (`a = 11, b = 3`), and a `PinchIntCond`
at `lo5P = hi5P = W` (any of the seven window theorems above) gives
`Fresh.BandNoCarve.BandPinch g` — schema class 4, soundness `noCarve_of_pinch`. -/
theorem bandPinch_of_window {W : ℤ} {k mj : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hcond : Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj W W)
    (hbox : Fresh.Pinch.InBox 512 k g)
    (h5P : ((W : ℝ)) / (512 : ℕ) ≤ g 4 ∧ g 4 ≤ ((W + 1 : ℤ) : ℝ) / (512 : ℕ))
    (hplane : Fresh.Pinch.TangentPlane 11 3 g) :
    Fresh.BandNoCarve.BandPinch g :=
  ⟨11, 3, 512, k, mj, W, W, by norm_num, hbox, h5P, hplane, hcond⟩

#print axioms bandPinch_of_window

/-- The cell form of the glue: the ρ₅-window is derived from the box itself (`k 4 = W`),
so only the box, the plane and the window's `PinchIntCond` are needed. -/
theorem bandPinch_of_window_cell {W : ℤ} {k mj : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hcond : Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) k mj W W)
    (hbox : Fresh.Pinch.InBox 512 k g) (hk4 : k 4 = W)
    (hplane : Fresh.Pinch.TangentPlane 11 3 g) :
    Fresh.BandNoCarve.BandPinch g :=
  bandPinch_of_window hcond hbox (rho5Window_of_inBox hbox hk4) hplane

#print axioms bandPinch_of_window_cell

/-! ## The worked per-box instantiation (the first JSONL line of E843's dump)

`{"D": 512, "k6": [1202, 1576, 2027, 2645, 3615, 9419], "lo5P": 2645, "hi5P": 2645,
"m": {"0": 1, "1": 1, "2": 2, "4": 4}}` — window 2645; the pattern theorem for the
remaining 508 boxes.  `k 0 = 511` is the added artifact-silent ρ₁ cell (`ρ₁ = 1 ∈
[511/512, 512/512]`). -/

/-- The shared m-tuple of all 509 boxes, in Lean indices (`mj 0 = 0` is ρ₁'s own gap,
added; indices 4 and 6 unused — `PinchIntCond`'s excluded ones). -/
def mjShared : Fin 7 → ℤ := ![0, 1, 1, 2, 0, 4, 0]

/-- The worked box: the first line of `tail_h3_pinch_dump_v1.jsonl` (`k 4 = 2645` is the
ρ₅ cell = the window, `k 6 = 9419` the ρ₇ cell, both `PinchIntCond`-free). -/
def kBox1 : Fin 7 → ℤ := ![511, 1202, 1576, 2027, 2645, 3615, 9419]

/-- The worked box's interval membership and its resulting `PinchIntCond` (via
`pinchWindow_2645`): ρ₂ 1202 ∈ [953,1586], ρ₃ 1576 ∈ [953,1586], ρ₄ 2027 ∈ [1800,2432],
ρ₆ 3615 ∈ [3493,4125], ρ₁ 511 ∈ [511,512]. -/
theorem pinchIntCond_kBox1 :
    Fresh.Pinch.PinchIntCond 11 3 (512 : ℤ) kBox1 mjShared 2645 2645 :=
  pinchWindow_2645 (by simp [mjShared]) (by simp [mjShared]) (by simp [mjShared])
    (by simp [mjShared]) (by simp [mjShared]) (by simp [kBox1]) (by simp [kBox1])
    (by simp [kBox1]) (by simp [kBox1]) (by simp [kBox1])

#print axioms pinchIntCond_kBox1

/-- The per-box pattern, glued: every arrangement in the worked box on the h₃ tangency
plane is a `BandPinch` tuple (hence, by `Fresh.BandNoCarve.noCarve_of_pinch`, not a
carve). -/
theorem bandPinch_kBox1 {g : Fin 7 → ℝ}
    (hbox : Fresh.Pinch.InBox 512 kBox1 g)
    (hplane : Fresh.Pinch.TangentPlane 11 3 g) :
    Fresh.BandNoCarve.BandPinch g :=
  bandPinch_of_window_cell pinchIntCond_kBox1 hbox rfl hplane

#print axioms bandPinch_kBox1

end Fresh.BandPinchData
