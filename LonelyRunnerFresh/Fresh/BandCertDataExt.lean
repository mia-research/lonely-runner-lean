import Fresh.BandNoCarve
import Fresh.SideWindowCert

/-!
# The sixth schema class and the 15 leaves3739 discharge lines

The band data disjunction `Fresh.BandNoCarve.BandCertData` (fixed-R0, window-type,
seam-cycle-plane, pinch, second-window witness) is extended by a sixth schema class:
the side-window-vertex certificate `SideWindowCertV` of `Fresh.SideWindowCert` (E846
item 3).  `BandCertData6` adds, per tuple, the alternative that `g` lies in the side
region `box ∩ {linForm a ≤ 0}` of a `SideWindowCertV`; soundness is
`sideWindowCertV_noCarve`, consumed through `clearPoint_of_noCarve` exactly like the
other no-carve schemas, giving `bandNoCarve6 : BandCertData6 → OutsideBelow17`.

The 15 worked data lines of `experiments/n8/onefast_audit/leaves3739_split_v1.out`
(the five `[37,39)` leaves at D = 32, boxes B1-B5, split by the planes
P1 = 7ρ₅ − 9ρ₄, w1 = 23ρ₇ − 137ρ₅, w2 = 5ρ₇ − 27ρ₆) are instantiated as 15
`SideWindowCertV` records with consumption theorems `swc3739_Bk_<side>_noCarve`, and
the per-box totality is composed as `leaves3739_discharged` over the five boxes.

Sign convention (matching `SideWindowCertV`'s side `linForm a g ≤ 0` and the worked
line `leaves3739_B1_P1pos`): the P1 ≥ 0 side is `9ρ₄ − 7ρ₅ ≤ 0` (`pairL 3 4 9 7`), the
w1 ≥ 0 side is `137ρ₅ − 23ρ₇ ≤ 0` (`pairL 4 6 137 23`), the w1 ≤ 0 side is
`23ρ₇ − 137ρ₅ ≤ 0` (`pairL 6 4 23 137`), the w2 ≤ 0 side is `5ρ₇ − 27ρ₆ ≤ 0`
(`pairL 6 5 5 27`), and the coupled side σ is `33ρ₆ − 47ρ₄ ≤ 0` (`pairL 5 3 33 47`).

Composition remarks.  The data-side leaves after the first split are cut by TWO planes,
while `SideWindowCertV` carries one; each leaf's window rides on a single-plane side
that contains it.  For the P1 ≥ 0 leaves (window A `9/ρ₅ → 7/ρ₄`) and the w1 ≥ 0 leaves
(window B `137/ρ₇ → 23/ρ₅`) the coupled inequality hv2 IS the side condition, and the
other four families hold on the whole box.  For the w1 < 0 leaves of B1/B2 (window C
`25/ρ₆ → 135/ρ₇`) hv2 (`25ρ₇ ≤ 135ρ₆`, i.e. w2 ≤ 0) follows from the w1 ≤ 0 side plus
the box faces.  B3's w1 < 0 leaf splits by w2 into a w2 ≤ 0 certificate (hv2 = side)
and a σ-side certificate for the w2 > 0 rest (σ follows from P1 < 0 ∧ w2 > 0 plus the
faces); B4's w1 < 0 leaf rides on σ (from P1 < 0 ∧ w1 < 0 plus the faces); B5's P1 < 0
leaf implies w1 ≥ 0 (P1 < 0 forces ρ₄ to its top face, whence `137ρ₅ ≤ 23ρ₇` on the
box).  All arithmetic is integer-exact at D = 32.
-/

namespace Fresh.BandNoCarve

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FilterAssembly

/-! ## The sixth schema class at the data level -/

/-- The per-tuple reading of the five-schema disjunction `BandCertData`. -/
-- STANDING: DEFINITION
def BandCertData5 (g : Fin 7 → ℝ) : Prop :=
  BandFixedR0 g ∨ BandWindowType g ∨ BandSeamPlane g ∨ BandPinch g ∨ BandW1 g

/-- **Schema class 6 (side-window-vertex)**: `g` lies in the side region of a
`SideWindowCertV` — a dyadic box (with ρ₁ pinned to `1`) cut by one homogeneous linear
side condition `linForm a ≤ 0`, carrying a window `[na/ρ_ka, nb/ρ_kb]` with per-reading
laps whose five inequality families hold on the half-box's vertex set.  Soundness:
`sideWindowCertV_noCarve`. -/
-- STANDING: DEFINITION
def BandSideWindowV (g : Fin 7 → ℝ) : Prop :=
  ∃ c : SideWindowCertV, (∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) ∧ linForm c.a g ≤ 0

/-- **The extended band data**: the five-schema disjunction or the sixth
(side-window-vertex) class.  [PROVISIONAL: covering] -/
-- STANDING: DEFINITION
def BandCertData6 : Prop :=
  ∀ g : Fin 7 → ℝ, BandRange g → BandCertData5 g ∨ BandSideWindowV g

/-- `BandCertData` is the five-schema part of `BandCertData6`. -/
theorem bandCertData6_of_bandData (h : BandCertData) : BandCertData6 :=
  fun g hr => Or.inl (h g hr)

/-- Schema 6 excludes carving, by `sideWindowCertV_noCarve`. -/
theorem noCarve_of_sideWindowV {g : Fin 7 → ℝ} (h : BandSideWindowV g) :
    Fresh.Certs.NoCarve g := by
  obtain ⟨c, hbox, hs⟩ := h
  exact sideWindowCertV_noCarve c g hbox hs

/-- Schema 6 gives the clear point through the no-carve route. -/
theorem clearPoint_of_sideWindowV {g : Fin 7 → ℝ} (h : BandSideWindowV g) :
    BandClearPoint g :=
  clearPoint_of_noCarve (noCarve_of_sideWindowV h)

/-- Each certificate class of the extended disjunction gives a clear point in one of the
two windows. -/
theorem clearPoint_of_bandCert6 {g : Fin 7 → ℝ}
    (h : BandCertData5 g ∨ BandSideWindowV g) : BandClearPoint g := by
  rcases h with h5 | h6
  · exact clearPoint_of_bandCert h5
  · exact clearPoint_of_sideWindowV h6

/-- **The O3 composition, extended**: band totality with the sixth schema class gives
`OutsideBelow17`. -/
theorem outsideBelow17_of_bandData6 (hData : BandCertData6) : OutsideBelow17 := by
  intro v hv k m hm hex hmax
  obtain ⟨g, hrange, himage⟩ := bandTuple hv hm hex hmax
  obtain ⟨s, hs1, hs2, hsw, hcl⟩ := clearPoint_of_bandCert6 (hData g hrange)
  exact cascadeLandsBelow17_of_clearPoint hv hm s hs1 hs2 hsw (clear_of_image himage hcl)

/-- **The main theorem, `OutsideBelow17`'s statement verbatim**, from the extended band
data. -/
theorem bandNoCarve6 (hData : BandCertData6) :
    ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ (k : Fin 8) (m : ℝ), Fresh.IsDmin v k m →
      (∃ d ∈ disparitySet v k, 17 * m < d) → (∀ d ∈ disparitySet v k, d ≤ 49 * m) →
      Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m :=
  outsideBelow17_of_bandData6 hData

/-! ## The 15 worked lines: shared lap vectors, boxes, case helpers -/

/-- Laps of window B (`X = 137/ρ₇`, `Y = 23/ρ₅`): `(8j+1) = [9, 9, 17, 17, 25, 137]`
over ρ₂..ρ₇. -/
def swc3739_jB : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 17]

/-- Laps of window C (`X = 25/ρ₆`, `Y = 135/ρ₇`): `(8j+1) = [9, 9, 17, 17, 25, 129]`
over ρ₂..ρ₇. -/
def swc3739_jC : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 16]

/-- Laps of window D (`X = 33/ρ₄`, `Y = 47/ρ₆`): `(8j+1) = [17, 25, 33, 41, 41, 249]`
over ρ₂..ρ₇. -/
def swc3739_jD : Fin 7 → ℤ := ![0, 2, 3, 4, 5, 5, 31]

/-- The per-window lap values, as rewrite lemmas (the window-A laps are
`leaves3739_B1_j` of `Fresh.SideWindowCert`). -/
theorem swc3739_jA_0 : leaves3739_B1_j 0 = 0 := rfl
theorem swc3739_jA_1 : leaves3739_B1_j 1 = 0 := rfl
theorem swc3739_jA_2 : leaves3739_B1_j 2 = 0 := rfl
theorem swc3739_jA_3 : leaves3739_B1_j 3 = 0 := rfl
theorem swc3739_jA_4 : leaves3739_B1_j 4 = 1 := rfl
theorem swc3739_jA_5 : leaves3739_B1_j 5 = 1 := rfl
theorem swc3739_jA_6 : leaves3739_B1_j 6 = 6 := rfl
theorem swc3739_jB_0 : swc3739_jB 0 = 0 := rfl
theorem swc3739_jB_1 : swc3739_jB 1 = 1 := rfl
theorem swc3739_jB_2 : swc3739_jB 2 = 1 := rfl
theorem swc3739_jB_3 : swc3739_jB 3 = 2 := rfl
theorem swc3739_jB_4 : swc3739_jB 4 = 2 := rfl
theorem swc3739_jB_5 : swc3739_jB 5 = 3 := rfl
theorem swc3739_jB_6 : swc3739_jB 6 = 17 := rfl
theorem swc3739_jC_0 : swc3739_jC 0 = 0 := rfl
theorem swc3739_jC_1 : swc3739_jC 1 = 1 := rfl
theorem swc3739_jC_2 : swc3739_jC 2 = 1 := rfl
theorem swc3739_jC_3 : swc3739_jC 3 = 2 := rfl
theorem swc3739_jC_4 : swc3739_jC 4 = 2 := rfl
theorem swc3739_jC_5 : swc3739_jC 5 = 3 := rfl
theorem swc3739_jC_6 : swc3739_jC 6 = 16 := rfl
theorem swc3739_jD_0 : swc3739_jD 0 = 0 := rfl
theorem swc3739_jD_1 : swc3739_jD 1 = 2 := rfl
theorem swc3739_jD_2 : swc3739_jD 2 = 3 := rfl
theorem swc3739_jD_3 : swc3739_jD 3 = 4 := rfl
theorem swc3739_jD_4 : swc3739_jD 4 = 5 := rfl
theorem swc3739_jD_5 : swc3739_jD 5 = 5 := rfl
theorem swc3739_jD_6 : swc3739_jD 6 = 31 := rfl

/-- Case analysis over `Fin 7` with the seven cases at the literal indices (so the goals
match literal-index hypotheses up to the definitional equality of `Fin` literals). -/
theorem swc_forallFin7 {p : Fin 7 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3)
    (h4 : p 4) (h5 : p 5) (h6 : p 6) : ∀ i, p i := by
  intro i
  fin_cases i <;> first
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact h6

/-- Box B2 at D = 32: ρ₂ ∈ [92/32, 93/32], ρ₃ ∈ [123/32, 124/32], ρ₄ ∈ [157/32, 158/32],
ρ₅ ∈ [202/32, 203/32], ρ₆ ∈ [224/32, 225/32], ρ₇ ∈ [1209/32, 1210/32]. -/
noncomputable def swc3739_B2_lo : Fin 7 → ℝ :=
  ![1, 92/32, 123/32, 157/32, 202/32, 224/32, 1209/32]

noncomputable def swc3739_B2_hi : Fin 7 → ℝ :=
  ![1, 93/32, 124/32, 158/32, 203/32, 225/32, 1210/32]

/-- Box B3 at D = 32: ρ₂ ∈ [92/32, 93/32], ρ₃ ∈ [123/32, 124/32], ρ₄ ∈ [157/32, 158/32],
ρ₅ ∈ [203/32, 204/32], ρ₆ ∈ [224/32, 225/32], ρ₇ ∈ [1209/32, 1210/32]. -/
noncomputable def swc3739_B3_lo : Fin 7 → ℝ :=
  ![1, 92/32, 123/32, 157/32, 203/32, 224/32, 1209/32]

noncomputable def swc3739_B3_hi : Fin 7 → ℝ :=
  ![1, 93/32, 124/32, 158/32, 204/32, 225/32, 1210/32]

/-- Box B4 at D = 32: ρ₂ ∈ [92/32, 93/32], ρ₃ ∈ [123/32, 124/32], ρ₄ ∈ [157/32, 158/32],
ρ₅ ∈ [203/32, 204/32], ρ₆ ∈ [224/32, 225/32], ρ₇ ∈ [1210/32, 1211/32]. -/
noncomputable def swc3739_B4_lo : Fin 7 → ℝ :=
  ![1, 92/32, 123/32, 157/32, 203/32, 224/32, 1210/32]

noncomputable def swc3739_B4_hi : Fin 7 → ℝ :=
  ![1, 93/32, 124/32, 158/32, 204/32, 225/32, 1211/32]

/-- Box B5 at D = 32: ρ₂ ∈ [92/32, 93/32], ρ₃ ∈ [123/32, 124/32], ρ₄ ∈ [157/32, 158/32],
ρ₅ ∈ [203/32, 204/32], ρ₆ ∈ [224/32, 225/32], ρ₇ ∈ [1211/32, 1212/32]. -/
noncomputable def swc3739_B5_lo : Fin 7 → ℝ :=
  ![1, 92/32, 123/32, 157/32, 203/32, 224/32, 1211/32]

noncomputable def swc3739_B5_hi : Fin 7 → ℝ :=
  ![1, 93/32, 124/32, 158/32, 204/32, 225/32, 1212/32]

/-! ### The per-box vertex face bounds (polymorphic in the plane vector) -/

/-- The seven face pairs of B1, as literal per-reading bounds, for any plane vector. -/
theorem swc3739_B1_boxV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)
    (hv : SideVertex leaves3739_B1_lo leaves3739_B1_hi a v) :
    (91/32 : ℝ) ≤ v 1 ∧ v 1 ≤ 92/32 ∧ 123/32 ≤ v 2 ∧ v 2 ≤ 124/32 ∧
      157/32 ≤ v 3 ∧ v 3 ≤ 158/32 ∧ 202/32 ≤ v 4 ∧ v 4 ≤ 203/32 ∧
      224/32 ≤ v 5 ∧ v 5 ≤ 225/32 ∧ 1209/32 ≤ v 6 ∧ v 6 ≤ 1210/32 := by
  have hb := sideVertex_box (by
    intro i
    fin_cases i <;>
      norm_num [leaves3739_B1_lo, leaves3739_B1_hi, Matrix.cons_val_zero,
        Matrix.cons_val_succ]) hv
  exact ⟨(hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2, (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2,
    (hb 5).1, (hb 5).2, (hb 6).1, (hb 6).2⟩

/-- The seven face pairs of B2, as literal per-reading bounds, for any plane vector. -/
theorem swc3739_B2_boxV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)
    (hv : SideVertex swc3739_B2_lo swc3739_B2_hi a v) :
    (92/32 : ℝ) ≤ v 1 ∧ v 1 ≤ 93/32 ∧ 123/32 ≤ v 2 ∧ v 2 ≤ 124/32 ∧
      157/32 ≤ v 3 ∧ v 3 ≤ 158/32 ∧ 202/32 ≤ v 4 ∧ v 4 ≤ 203/32 ∧
      224/32 ≤ v 5 ∧ v 5 ≤ 225/32 ∧ 1209/32 ≤ v 6 ∧ v 6 ≤ 1210/32 := by
  have hb := sideVertex_box (by
    intro i
    fin_cases i <;>
      norm_num [swc3739_B2_lo, swc3739_B2_hi, Matrix.cons_val_zero,
        Matrix.cons_val_succ]) hv
  exact ⟨(hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2, (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2,
    (hb 5).1, (hb 5).2, (hb 6).1, (hb 6).2⟩

/-- The seven face pairs of B3, as literal per-reading bounds, for any plane vector. -/
theorem swc3739_B3_boxV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)
    (hv : SideVertex swc3739_B3_lo swc3739_B3_hi a v) :
    (92/32 : ℝ) ≤ v 1 ∧ v 1 ≤ 93/32 ∧ 123/32 ≤ v 2 ∧ v 2 ≤ 124/32 ∧
      157/32 ≤ v 3 ∧ v 3 ≤ 158/32 ∧ 203/32 ≤ v 4 ∧ v 4 ≤ 204/32 ∧
      224/32 ≤ v 5 ∧ v 5 ≤ 225/32 ∧ 1209/32 ≤ v 6 ∧ v 6 ≤ 1210/32 := by
  have hb := sideVertex_box (by
    intro i
    fin_cases i <;>
      norm_num [swc3739_B3_lo, swc3739_B3_hi, Matrix.cons_val_zero,
        Matrix.cons_val_succ]) hv
  exact ⟨(hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2, (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2,
    (hb 5).1, (hb 5).2, (hb 6).1, (hb 6).2⟩

/-- The seven face pairs of B4, as literal per-reading bounds, for any plane vector. -/
theorem swc3739_B4_boxV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)
    (hv : SideVertex swc3739_B4_lo swc3739_B4_hi a v) :
    (92/32 : ℝ) ≤ v 1 ∧ v 1 ≤ 93/32 ∧ 123/32 ≤ v 2 ∧ v 2 ≤ 124/32 ∧
      157/32 ≤ v 3 ∧ v 3 ≤ 158/32 ∧ 203/32 ≤ v 4 ∧ v 4 ≤ 204/32 ∧
      224/32 ≤ v 5 ∧ v 5 ≤ 225/32 ∧ 1210/32 ≤ v 6 ∧ v 6 ≤ 1211/32 := by
  have hb := sideVertex_box (by
    intro i
    fin_cases i <;>
      norm_num [swc3739_B4_lo, swc3739_B4_hi, Matrix.cons_val_zero,
        Matrix.cons_val_succ]) hv
  exact ⟨(hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2, (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2,
    (hb 5).1, (hb 5).2, (hb 6).1, (hb 6).2⟩

/-- The seven face pairs of B5, as literal per-reading bounds, for any plane vector. -/
theorem swc3739_B5_boxV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)
    (hv : SideVertex swc3739_B5_lo swc3739_B5_hi a v) :
    (92/32 : ℝ) ≤ v 1 ∧ v 1 ≤ 93/32 ∧ 123/32 ≤ v 2 ∧ v 2 ≤ 124/32 ∧
      157/32 ≤ v 3 ∧ v 3 ≤ 158/32 ∧ 203/32 ≤ v 4 ∧ v 4 ≤ 204/32 ∧
      224/32 ≤ v 5 ∧ v 5 ≤ 225/32 ∧ 1211/32 ≤ v 6 ∧ v 6 ≤ 1212/32 := by
  have hb := sideVertex_box (by
    intro i
    fin_cases i <;>
      norm_num [swc3739_B5_lo, swc3739_B5_hi, Matrix.cons_val_zero,
        Matrix.cons_val_succ]) hv
  exact ⟨(hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2, (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2,
    (hb 5).1, (hb 5).2, (hb 6).1, (hb 6).2⟩

/-! ## B1: lines 1-3 (P1 ≥ 0, w1 ≥ 0, w1 < 0) -/

/-- **Line 1** (B1, side `P1 ≥ 0`) is the verified worked line `leaves3739_B1_P1pos` of
`Fresh.SideWindowCert` (window `X = 9/ρ₅`, `Y = 7/ρ₄`, laps `(8j+1) = [1, 1, 1, 9, 9,
49]`), restated with the explicit plane vector `9ρ₄ − 7ρ₅`. -/
theorem swc3739_B1_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, leaves3739_B1_lo i ≤ g i ∧ g i ≤ leaves3739_B1_hi i)
    (hs : linForm (pairL 3 4 9 7) g ≤ 0) : Fresh.Certs.NoCarve g :=
  leaves3739_B1_P1pos_noCarve g hbox hs

/-- **Line 2** (B1, side `w1 ≥ 0`, stated `137ρ₅ − 23ρ₇ ≤ 0`): window `X = 137/ρ₇`,
`Y = 23/ρ₅`, laps `(8j+1) = [9, 9, 17, 17, 25, 137]`.  The coupled inequality hv2 is the
side condition itself; the other four families hold on the whole box. -/
noncomputable def swc3739_B1_w1pos : SideWindowCertV :=
  { lo := leaves3739_B1_lo
    hi := leaves3739_B1_hi
    a := pairL 4 6 137 23
    na := 137
    ka := 6
    nb := 23
    kb := 4
    j := swc3739_jB
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [leaves3739_B1_lo, leaves3739_B1_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show leaves3739_B1_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show leaves3739_B1_lo 4 = (202 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [leaves3739_B1_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith }

/-- **Line 2 consumption**: every arrangement in B1 with `137ρ₅ ≤ 23ρ₇` (the w1 ≥ 0
side) is not a carve of `[1,7]`. -/
theorem swc3739_B1_w1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, leaves3739_B1_lo i ≤ g i ∧ g i ≤ leaves3739_B1_hi i)
    (hs : linForm (pairL 4 6 137 23) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B1_w1pos g hbox hs

/-- **Line 3** (B1, side `w1 < 0`, stated `23ρ₇ − 137ρ₅ ≤ 0`): window `X = 25/ρ₆`,
`Y = 135/ρ₇`, laps `(8j+1) = [9, 9, 17, 17, 25, 129]`.  hv1/hv3/hv4/hv5 hold on the
whole box; hv2 (`25ρ₇ ≤ 135ρ₆`, i.e. w2 ≤ 0) follows from the side `23ρ₇ ≤ 137ρ₅` plus
the faces ρ₅ ≤ 203/32, ρ₆ ≥ 224/32. -/
noncomputable def swc3739_B1_w1neg : SideWindowCertV :=
  { lo := leaves3739_B1_lo
    hi := leaves3739_B1_hi
    a := pairL 6 4 23 137
    na := 25
    ka := 5
    nb := 135
    kb := 6
    j := swc3739_jC
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [leaves3739_B1_lo, leaves3739_B1_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show leaves3739_B1_lo 5 = (224 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show leaves3739_B1_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [leaves3739_B1_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 6 4 23 137) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 6 4 23 137) v hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 6 4 23 137) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 6 4 23 137) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B1_boxV (pairL 6 4 23 137) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith }

/-- **Line 3 consumption**: every arrangement in B1 with `23ρ₇ < 137ρ₅` (the w1 < 0
leaf's side, stated in the `pairL 4 6 137 23` orientation) is not a carve of `[1,7]`. -/
theorem swc3739_B1_w1neg_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, leaves3739_B1_lo i ≤ g i ∧ g i ≤ leaves3739_B1_hi i)
    (hs : 0 < linForm (pairL 4 6 137 23) g) : Fresh.Certs.NoCarve g := by
  have key : linForm swc3739_B1_w1neg.a g ≤ 0 := by
    have eS : linForm swc3739_B1_w1neg.a g = 23 * g 6 - 137 * g 4 :=
      linForm_pairL 6 4 23 137 g
    have eT : linForm (pairL 4 6 137 23) g = 137 * g 4 - 23 * g 6 :=
      linForm_pairL 4 6 137 23 g
    rw [eS]
    rw [eT] at hs
    linarith
  exact sideWindowCertV_noCarve swc3739_B1_w1neg g hbox key

/-! ## B2: lines 4-6 (P1 ≥ 0, w1 ≥ 0, w1 < 0) -/

/-- **Line 4** (B2, side `P1 ≥ 0`, stated `9ρ₄ − 7ρ₅ ≤ 0`): window `X = 9/ρ₅`,
`Y = 7/ρ₄`, laps `(8j+1) = [1, 1, 1, 9, 9, 49]`.  hv2 is the side condition itself; the
other four families hold on the whole box. -/
noncomputable def swc3739_B2_P1pos : SideWindowCertV :=
  { lo := swc3739_B2_lo
    hi := swc3739_B2_hi
    a := pairL 3 4 9 7
    na := 9
    ka := 4
    nb := 7
    kb := 3
    j := leaves3739_B1_j
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, swc3739_B2_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B2_lo 4 = (202 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B2_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith }

/-- **Line 4 consumption**: every arrangement in B2 with `9ρ₄ ≤ 7ρ₅` (the P1 ≥ 0 side)
is not a carve of `[1,7]`. -/
theorem swc3739_B2_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B2_lo i ≤ g i ∧ g i ≤ swc3739_B2_hi i)
    (hs : linForm (pairL 3 4 9 7) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B2_P1pos g hbox hs

/-- **Line 5** (B2, side `w1 ≥ 0`, stated `137ρ₅ − 23ρ₇ ≤ 0`): window `X = 137/ρ₇`,
`Y = 23/ρ₅`, laps `(8j+1) = [9, 9, 17, 17, 25, 137]`. -/
noncomputable def swc3739_B2_w1pos : SideWindowCertV :=
  { lo := swc3739_B2_lo
    hi := swc3739_B2_hi
    a := pairL 4 6 137 23
    na := 137
    ka := 6
    nb := 23
    kb := 4
    j := swc3739_jB
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, swc3739_B2_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B2_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B2_lo 4 = (202 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith }

/-- **Line 5 consumption**: every arrangement in B2 with `137ρ₅ ≤ 23ρ₇` (the w1 ≥ 0
side) is not a carve of `[1,7]`. -/
theorem swc3739_B2_w1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B2_lo i ≤ g i ∧ g i ≤ swc3739_B2_hi i)
    (hs : linForm (pairL 4 6 137 23) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B2_w1pos g hbox hs

/-- **Line 6** (B2, side `w1 < 0`, stated `23ρ₇ − 137ρ₅ ≤ 0`): window `X = 25/ρ₆`,
`Y = 135/ρ₇`, laps `(8j+1) = [9, 9, 17, 17, 25, 129]`.  hv2 follows from the side plus
the faces ρ₅ ≤ 203/32, ρ₆ ≥ 224/32. -/
noncomputable def swc3739_B2_w1neg : SideWindowCertV :=
  { lo := swc3739_B2_lo
    hi := swc3739_B2_hi
    a := pairL 6 4 23 137
    na := 25
    ka := 5
    nb := 135
    kb := 6
    j := swc3739_jC
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, swc3739_B2_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B2_lo 5 = (224 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B2_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B2_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 6 4 23 137) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 6 4 23 137) v hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 6 4 23 137) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 6 4 23 137) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B2_boxV (pairL 6 4 23 137) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith }

/-- **Line 6 consumption**: every arrangement in B2 with `23ρ₇ < 137ρ₅` (the w1 < 0
leaf's side) is not a carve of `[1,7]`. -/
theorem swc3739_B2_w1neg_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B2_lo i ≤ g i ∧ g i ≤ swc3739_B2_hi i)
    (hs : 0 < linForm (pairL 4 6 137 23) g) : Fresh.Certs.NoCarve g := by
  have key : linForm swc3739_B2_w1neg.a g ≤ 0 := by
    have eS : linForm swc3739_B2_w1neg.a g = 23 * g 6 - 137 * g 4 :=
      linForm_pairL 6 4 23 137 g
    have eT : linForm (pairL 4 6 137 23) g = 137 * g 4 - 23 * g 6 :=
      linForm_pairL 4 6 137 23 g
    rw [eS]
    rw [eT] at hs
    linarith
  exact sideWindowCertV_noCarve swc3739_B2_w1neg g hbox key

/-! ## B3: lines 7-10 (P1 ≥ 0, w1 ≥ 0, w2 ≤ 0, w2 > 0) -/

/-- **Line 7** (B3, side `P1 ≥ 0`, stated `9ρ₄ − 7ρ₅ ≤ 0`): window `X = 9/ρ₅`,
`Y = 7/ρ₄`, laps `(8j+1) = [1, 1, 1, 9, 9, 49]`. -/
noncomputable def swc3739_B3_P1pos : SideWindowCertV :=
  { lo := swc3739_B3_lo
    hi := swc3739_B3_hi
    a := pairL 3 4 9 7
    na := 9
    ka := 4
    nb := 7
    kb := 3
    j := leaves3739_B1_j
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, swc3739_B3_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B3_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B3_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith }

/-- **Line 7 consumption**: every arrangement in B3 with `9ρ₄ ≤ 7ρ₅` (the P1 ≥ 0 side)
is not a carve of `[1,7]`. -/
theorem swc3739_B3_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i)
    (hs : linForm (pairL 3 4 9 7) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B3_P1pos g hbox hs

/-- **Line 8** (B3, side `w1 ≥ 0`, stated `137ρ₅ − 23ρ₇ ≤ 0`): window `X = 137/ρ₇`,
`Y = 23/ρ₅`, laps `(8j+1) = [9, 9, 17, 17, 25, 137]`. -/
noncomputable def swc3739_B3_w1pos : SideWindowCertV :=
  { lo := swc3739_B3_lo
    hi := swc3739_B3_hi
    a := pairL 4 6 137 23
    na := 137
    ka := 6
    nb := 23
    kb := 4
    j := swc3739_jB
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, swc3739_B3_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B3_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B3_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith }

/-- **Line 8 consumption**: every arrangement in B3 with `137ρ₅ ≤ 23ρ₇` (the w1 ≥ 0
side) is not a carve of `[1,7]`. -/
theorem swc3739_B3_w1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i)
    (hs : linForm (pairL 4 6 137 23) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B3_w1pos g hbox hs

/-- **Line 9** (B3, side `w2 ≤ 0`, stated `5ρ₇ − 27ρ₆ ≤ 0`): window `X = 25/ρ₆`,
`Y = 135/ρ₇`, laps `(8j+1) = [9, 9, 17, 17, 25, 129]`.  hv2 (`25ρ₇ ≤ 135ρ₆`) is the
side condition scaled by 5; the other four families hold on the whole box. -/
noncomputable def swc3739_B3_w2neg : SideWindowCertV :=
  { lo := swc3739_B3_lo
    hi := swc3739_B3_hi
    a := pairL 6 5 5 27
    na := 25
    ka := 5
    nb := 135
    kb := 6
    j := swc3739_jC
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, swc3739_B3_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B3_lo 5 = (224 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B3_lo 6 = (1209 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 6 5 5 27) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 6 5 5 27) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 6 5 5 27) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 6 5 5 27) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jC_0, swc3739_jC_1, swc3739_jC_2, swc3739_jC_3,
          swc3739_jC_4, swc3739_jC_5, swc3739_jC_6]
      all_goals linarith }

/-- **Line 9 consumption**: every arrangement in B3 with `5ρ₇ ≤ 27ρ₆` (the w2 ≤ 0 side)
is not a carve of `[1,7]`. -/
theorem swc3739_B3_w2neg_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i)
    (hs : linForm (pairL 6 5 5 27) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B3_w2neg g hbox hs

/-- **Line 10** (B3, the w2 > 0 rest of the w1 < 0 leaf, side σ `33ρ₆ − 47ρ₄ ≤ 0`):
window `X = 33/ρ₄`, `Y = 47/ρ₆`, laps `(8j+1) = [17, 25, 33, 41, 41, 249]`.  hv2 is the
side condition itself; the other four families hold on the whole box. -/
noncomputable def swc3739_B3_w2pos : SideWindowCertV :=
  { lo := swc3739_B3_lo
    hi := swc3739_B3_hi
    a := pairL 5 3 33 47
    na := 33
    ka := 3
    nb := 47
    kb := 5
    j := swc3739_jD
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, swc3739_B3_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B3_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B3_lo 5 = (224 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B3_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 5 3 33 47) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 5 3 33 47) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 5 3 33 47) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jD_0, swc3739_jD_1, swc3739_jD_2, swc3739_jD_3,
          swc3739_jD_4, swc3739_jD_5, swc3739_jD_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B3_boxV (pairL 5 3 33 47) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jD_0, swc3739_jD_1, swc3739_jD_2, swc3739_jD_3,
          swc3739_jD_4, swc3739_jD_5, swc3739_jD_6]
      all_goals linarith }

/-- **Line 10 consumption**: every arrangement in B3 with P1 < 0 (`9ρ₄ > 7ρ₅`), w2 > 0
(`5ρ₇ > 27ρ₆`) lies on the σ side `33ρ₆ ≤ 47ρ₄` (σ follows from the two side facts plus
the faces ρ₅ ≥ 203/32, ρ₇ ≤ 1210/32) and is not a carve of `[1,7]`. -/
theorem swc3739_B3_w2pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i)
    (hP1 : 0 < linForm (pairL 3 4 9 7) g)
    (hw2 : 0 < linForm (pairL 6 5 5 27) g) : Fresh.Certs.NoCarve g := by
  have key : linForm swc3739_B3_w2pos.a g ≤ 0 := by
    have eS : linForm swc3739_B3_w2pos.a g = 33 * g 5 - 47 * g 3 :=
      linForm_pairL 5 3 33 47 g
    have eP : linForm (pairL 3 4 9 7) g = 9 * g 3 - 7 * g 4 := linForm_pairL 3 4 9 7 g
    have eW : linForm (pairL 6 5 5 27) g = 5 * g 6 - 27 * g 5 := linForm_pairL 6 5 5 27 g
    rw [eS]
    rw [eP] at hP1
    rw [eW] at hw2
    have f4 : (203 / 32 : ℝ) ≤ g 4 := hbox 4 |>.1
    have f6 : g 6 ≤ (1210 / 32 : ℝ) := hbox 6 |>.2
    linarith
  exact sideWindowCertV_noCarve swc3739_B3_w2pos g hbox key

/-! ## B4: lines 11-13 (P1 ≥ 0, w1 ≥ 0, w1 < 0 via σ) -/

/-- **Line 11** (B4, side `P1 ≥ 0`, stated `9ρ₄ − 7ρ₅ ≤ 0`): window `X = 9/ρ₅`,
`Y = 7/ρ₄`, laps `(8j+1) = [1, 1, 1, 9, 9, 49]`. -/
noncomputable def swc3739_B4_P1pos : SideWindowCertV :=
  { lo := swc3739_B4_lo
    hi := swc3739_B4_hi
    a := pairL 3 4 9 7
    na := 9
    ka := 4
    nb := 7
    kb := 3
    j := leaves3739_B1_j
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, swc3739_B4_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B4_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B4_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith }

/-- **Line 11 consumption**: every arrangement in B4 with `9ρ₄ ≤ 7ρ₅` (the P1 ≥ 0 side)
is not a carve of `[1,7]`. -/
theorem swc3739_B4_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B4_lo i ≤ g i ∧ g i ≤ swc3739_B4_hi i)
    (hs : linForm (pairL 3 4 9 7) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B4_P1pos g hbox hs

/-- **Line 12** (B4, side `w1 ≥ 0`, stated `137ρ₅ − 23ρ₇ ≤ 0`): window `X = 137/ρ₇`,
`Y = 23/ρ₅`, laps `(8j+1) = [9, 9, 17, 17, 25, 137]`. -/
noncomputable def swc3739_B4_w1pos : SideWindowCertV :=
  { lo := swc3739_B4_lo
    hi := swc3739_B4_hi
    a := pairL 4 6 137 23
    na := 137
    ka := 6
    nb := 23
    kb := 4
    j := swc3739_jB
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, swc3739_B4_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B4_lo 6 = (1210 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B4_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith }

/-- **Line 12 consumption**: every arrangement in B4 with `137ρ₅ ≤ 23ρ₇` (the w1 ≥ 0
side) is not a carve of `[1,7]`. -/
theorem swc3739_B4_w1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B4_lo i ≤ g i ∧ g i ≤ swc3739_B4_hi i)
    (hs : linForm (pairL 4 6 137 23) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B4_w1pos g hbox hs

/-- **Line 13** (B4, the w1 < 0 leaf, side σ `33ρ₆ − 47ρ₄ ≤ 0`): window `X = 33/ρ₄`,
`Y = 47/ρ₆`, laps `(8j+1) = [17, 25, 33, 41, 41, 249]`.  hv2 is the side condition
itself; the other four families hold on the whole box. -/
noncomputable def swc3739_B4_w1neg : SideWindowCertV :=
  { lo := swc3739_B4_lo
    hi := swc3739_B4_hi
    a := pairL 5 3 33 47
    na := 33
    ka := 3
    nb := 47
    kb := 5
    j := swc3739_jD
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, swc3739_B4_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B4_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B4_lo 5 = (224 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B4_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 5 3 33 47) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 5 3 33 47) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 5 3 33 47) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jD_0, swc3739_jD_1, swc3739_jD_2, swc3739_jD_3,
          swc3739_jD_4, swc3739_jD_5, swc3739_jD_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B4_boxV (pairL 5 3 33 47) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jD_0, swc3739_jD_1, swc3739_jD_2, swc3739_jD_3,
          swc3739_jD_4, swc3739_jD_5, swc3739_jD_6]
      all_goals linarith }

/-- **Line 13 consumption**: every arrangement in B4 with P1 < 0 (`9ρ₄ > 7ρ₅`) and
w1 < 0 (`137ρ₅ > 23ρ₇`) lies on the σ side `33ρ₆ ≤ 47ρ₄` (σ follows from the two side
facts plus the faces ρ₆ ≥ 1210/32, ρ₇ ≥ 1210/32, ρ₆ ≤ 225/32) and is not a carve of
`[1,7]`. -/
theorem swc3739_B4_w1neg_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B4_lo i ≤ g i ∧ g i ≤ swc3739_B4_hi i)
    (hP1 : 0 < linForm (pairL 3 4 9 7) g)
    (hw1 : 0 < linForm (pairL 4 6 137 23) g) : Fresh.Certs.NoCarve g := by
  have key : linForm swc3739_B4_w1neg.a g ≤ 0 := by
    have eS : linForm swc3739_B4_w1neg.a g = 33 * g 5 - 47 * g 3 :=
      linForm_pairL 5 3 33 47 g
    have eP : linForm (pairL 3 4 9 7) g = 9 * g 3 - 7 * g 4 := linForm_pairL 3 4 9 7 g
    have eW : linForm (pairL 4 6 137 23) g = 137 * g 4 - 23 * g 6 :=
      linForm_pairL 4 6 137 23 g
    rw [eS]
    rw [eP] at hP1
    rw [eW] at hw1
    have f5 : g 5 ≤ (225 / 32 : ℝ) := hbox 5 |>.2
    have f6 : (1210 / 32 : ℝ) ≤ g 6 := hbox 6 |>.1
    linarith
  exact sideWindowCertV_noCarve swc3739_B4_w1neg g hbox key

/-! ## B5: lines 14-15 (P1 ≥ 0, P1 < 0 via w1 ≥ 0) -/

/-- **Line 14** (B5, side `P1 ≥ 0`, stated `9ρ₄ − 7ρ₅ ≤ 0`): window `X = 9/ρ₅`,
`Y = 7/ρ₄`, laps `(8j+1) = [1, 1, 1, 9, 9, 49]`. -/
noncomputable def swc3739_B5_P1pos : SideWindowCertV :=
  { lo := swc3739_B5_lo
    hi := swc3739_B5_hi
    a := pairL 3 4 9 7
    na := 9
    ka := 4
    nb := 7
    kb := 3
    j := leaves3739_B1_j
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B5_lo, swc3739_B5_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B5_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B5_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B5_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 3 4 9 7) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 3 4 9 7) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jA_0, swc3739_jA_1, swc3739_jA_2, swc3739_jA_3,
          swc3739_jA_4, swc3739_jA_5, swc3739_jA_6]
      all_goals linarith }

/-- **Line 14 consumption**: every arrangement in B5 with `9ρ₄ ≤ 7ρ₅` (the P1 ≥ 0 side)
is not a carve of `[1,7]`. -/
theorem swc3739_B5_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B5_lo i ≤ g i ∧ g i ≤ swc3739_B5_hi i)
    (hs : linForm (pairL 3 4 9 7) g ≤ 0) : Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve swc3739_B5_P1pos g hbox hs

/-- **Line 15** (B5, the P1 < 0 leaf, side `w1 ≥ 0`, stated `137ρ₅ − 23ρ₇ ≤ 0`): window
`X = 137/ρ₇`, `Y = 23/ρ₅`, laps `(8j+1) = [9, 9, 17, 17, 25, 137]`. -/
noncomputable def swc3739_B5_P1neg : SideWindowCertV :=
  { lo := swc3739_B5_lo
    hi := swc3739_B5_hi
    a := pairL 4 6 137 23
    na := 137
    ka := 6
    nb := 23
    kb := 4
    j := swc3739_jB
    hp0 := ⟨rfl, rfl⟩
    hlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B5_lo, swc3739_B5_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show swc3739_B5_lo 6 = (1211 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show swc3739_B5_lo 4 = (203 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [swc3739_B5_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv2 := by
      intro v hvx
      have hs := sideVertex_side hvx
      rw [linForm_pairL] at hs
      linarith
    hv3 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 4 6 137 23) v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, hb3hi, hb4lo, hb4hi, hb5lo, hb5hi,
        hb6lo, hb6hi⟩ := swc3739_B5_boxV (pairL 4 6 137 23) v hvx
      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals
        norm_num [swc3739_jB_0, swc3739_jB_1, swc3739_jB_2, swc3739_jB_3,
          swc3739_jB_4, swc3739_jB_5, swc3739_jB_6]
      all_goals linarith }

/-- **Line 15 consumption**: every arrangement in B5 with P1 < 0 (`9ρ₄ > 7ρ₅`) lies on
the w1 ≥ 0 side `137ρ₅ ≤ 23ρ₇` (w1 ≥ 0 follows from P1 < 0 plus the faces ρ₄ ≤ 158/32,
ρ₇ ≥ 1211/32) and is not a carve of `[1,7]`. -/
theorem swc3739_B5_P1neg_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B5_lo i ≤ g i ∧ g i ≤ swc3739_B5_hi i)
    (hP1 : 0 < linForm (pairL 3 4 9 7) g) : Fresh.Certs.NoCarve g := by
  have key : linForm swc3739_B5_P1neg.a g ≤ 0 := by
    have eS : linForm swc3739_B5_P1neg.a g = 137 * g 4 - 23 * g 6 :=
      linForm_pairL 4 6 137 23 g
    have eP : linForm (pairL 3 4 9 7) g = 9 * g 3 - 7 * g 4 := linForm_pairL 3 4 9 7 g
    rw [eS]
    rw [eP] at hP1
    have f3 : g 3 ≤ (158 / 32 : ℝ) := hbox 3 |>.2
    have f6 : (1211 / 32 : ℝ) ≤ g 6 := hbox 6 |>.1
    linarith
  exact sideWindowCertV_noCarve swc3739_B5_P1neg g hbox key

/-! ## The per-box totality and the leaves3739 discharge -/

/-- **B1 discharged**: the three certificates cover the box (case tree: P1 ≥ 0; else
w1 ≥ 0; else w1 < 0). -/
theorem swc3739_B1_discharged (g : Fin 7 → ℝ)
    (hbox : ∀ i, leaves3739_B1_lo i ≤ g i ∧ g i ≤ leaves3739_B1_hi i) :
    Fresh.Certs.NoCarve g := by
  rcases le_or_gt (linForm (pairL 3 4 9 7) g) 0 with h | h
  · exact swc3739_B1_P1pos_noCarve g hbox h
  · rcases le_or_gt (linForm (pairL 4 6 137 23) g) 0 with h2 | h2
    · exact swc3739_B1_w1pos_noCarve g hbox h2
    · exact swc3739_B1_w1neg_noCarve g hbox h2

/-- **B2 discharged**: the three certificates cover the box (same case tree as B1). -/
theorem swc3739_B2_discharged (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B2_lo i ≤ g i ∧ g i ≤ swc3739_B2_hi i) :
    Fresh.Certs.NoCarve g := by
  rcases le_or_gt (linForm (pairL 3 4 9 7) g) 0 with h | h
  · exact swc3739_B2_P1pos_noCarve g hbox h
  · rcases le_or_gt (linForm (pairL 4 6 137 23) g) 0 with h2 | h2
    · exact swc3739_B2_w1pos_noCarve g hbox h2
    · exact swc3739_B2_w1neg_noCarve g hbox h2

/-- **B3 discharged**: the four certificates cover the box (case tree: P1 ≥ 0; else
w1 ≥ 0; else w2 ≤ 0; else w2 > 0, which forces σ). -/
theorem swc3739_B3_discharged (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i) :
    Fresh.Certs.NoCarve g := by
  rcases le_or_gt (linForm (pairL 3 4 9 7) g) 0 with h | h
  · exact swc3739_B3_P1pos_noCarve g hbox h
  · rcases le_or_gt (linForm (pairL 4 6 137 23) g) 0 with h2 | h2
    · exact swc3739_B3_w1pos_noCarve g hbox h2
    · rcases le_or_gt (linForm (pairL 6 5 5 27) g) 0 with h3 | h3
      · exact swc3739_B3_w2neg_noCarve g hbox h3
      · exact swc3739_B3_w2pos_noCarve g hbox h h3

/-- **B4 discharged**: the three certificates cover the box (case tree: P1 ≥ 0; else
w1 ≥ 0; else w1 < 0, which forces σ). -/
theorem swc3739_B4_discharged (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B4_lo i ≤ g i ∧ g i ≤ swc3739_B4_hi i) :
    Fresh.Certs.NoCarve g := by
  rcases le_or_gt (linForm (pairL 3 4 9 7) g) 0 with h | h
  · exact swc3739_B4_P1pos_noCarve g hbox h
  · rcases le_or_gt (linForm (pairL 4 6 137 23) g) 0 with h2 | h2
    · exact swc3739_B4_w1pos_noCarve g hbox h2
    · exact swc3739_B4_w1neg_noCarve g hbox h h2

/-- **B5 discharged**: the two certificates cover the box (case tree: P1 ≥ 0; else
P1 < 0, which forces w1 ≥ 0). -/
theorem swc3739_B5_discharged (g : Fin 7 → ℝ)
    (hbox : ∀ i, swc3739_B5_lo i ≤ g i ∧ g i ≤ swc3739_B5_hi i) :
    Fresh.Certs.NoCarve g := by
  rcases le_or_gt (linForm (pairL 3 4 9 7) g) 0 with h | h
  · exact swc3739_B5_P1pos_noCarve g hbox h
  · exact swc3739_B5_P1neg_noCarve g hbox h

/-- **The leaves3739 discharge over the 15 lines**: every arrangement in one of the five
D = 32 boxes `[37,39)` (B1-B5 of `leaves3739_split_v1.out`) is not a carve of `[1,7]`
— the 15 side-window-vertex certificates cover all five boxes. -/
theorem leaves3739_discharged (g : Fin 7 → ℝ)
    (h : (∀ i, leaves3739_B1_lo i ≤ g i ∧ g i ≤ leaves3739_B1_hi i) ∨
        (∀ i, swc3739_B2_lo i ≤ g i ∧ g i ≤ swc3739_B2_hi i) ∨
        (∀ i, swc3739_B3_lo i ≤ g i ∧ g i ≤ swc3739_B3_hi i) ∨
        (∀ i, swc3739_B4_lo i ≤ g i ∧ g i ≤ swc3739_B4_hi i) ∨
        (∀ i, swc3739_B5_lo i ≤ g i ∧ g i ≤ swc3739_B5_hi i)) :
    Fresh.Certs.NoCarve g := by
  rcases h with hb | hb | hb | hb | hb
  · exact swc3739_B1_discharged g hb
  · exact swc3739_B2_discharged g hb
  · exact swc3739_B3_discharged g hb
  · exact swc3739_B4_discharged g hb
  · exact swc3739_B5_discharged g hb

#print axioms bandNoCarve6
#print axioms leaves3739_discharged
#print axioms swc3739_B3_w2pos_noCarve
#print axioms swc3739_B1_w1neg_noCarve
#print axioms sideWindowCertV_noCarve

end Fresh.BandNoCarve
