import Fresh.BandNoCarve

namespace Fresh.BandNoCarve

open Fresh Fresh.Certs Set

/-- A window certificate on a box cut by one linear inequality. -/
structure SideWindowCert where
  lo : Fin 7 → ℚ
  hi : Fin 7 → ℚ
  normal : Fin 7 → ℚ
  lap : Fin 7 → ℤ
  left : ℚ
  right : ℚ
  leftSetter : Fin 7
  rightSetter : Fin 7

-- STANDING: DEFINITION
def SideWindowCert.Region (c : SideWindowCert) (g : Fin 7 → ℝ) : Prop :=
  (∀ i, (c.lo i : ℝ) ≤ g i ∧ g i ≤ (c.hi i : ℝ)) ∧
    0 ≤ ∑ i, (c.normal i : ℝ) * g i

/-- The linear inequalities are stated after clearing positive denominators. -/
-- STANDING: DEFINITION
def SideWindowCert.Valid (c : SideWindowCert) : Prop :=
  ∀ g, c.Region g →
    (∀ i, 0 < g i) ∧
    g c.leftSetter ≤ (c.left : ℝ) ∧
    (c.right : ℝ) ≤ 7 * g c.rightSetter ∧
    (c.left : ℝ) * g c.rightSetter ≤ (c.right : ℝ) * g c.leftSetter ∧
    ∀ i, (8 * (c.lap i : ℝ) + 1) * g c.leftSetter ≤ (c.left : ℝ) * g i ∧
      (c.right : ℝ) * g i ≤ (8 * (c.lap i : ℝ) + 7) * g c.rightSetter

/-- [PROVISIONAL: covering] A valid side window gives a clear point in W₀. -/
theorem SideWindowCert.clearPoint {c : SideWindowCert} (hc : c.Valid)
    {g : Fin 7 → ℝ} (hg : c.Region g) : BandClearPoint g := by
  obtain ⟨hp,hl,hr,hlr,hgap⟩ := hc g hg
  let x : ℝ := c.left / g c.leftSetter
  let y : ℝ := c.right / g c.rightSetter
  have hx : 1 ≤ x := (le_div_iff₀ (hp _)).2 (by simpa using hl)
  have hy : y ≤ 7 := (div_le_iff₀ (hp _)).2 hr
  have hxy : x ≤ y := (div_le_div_iff₀ (hp _) (hp _)).2 hlr
  refine ⟨x,hx,by linarith,Or.inl (hxy.trans hy),fun i => ?_⟩
  apply (clearAt_R_iff _ _).mpr
  refine ⟨c.lap i,?_⟩
  have h₁ : 8 * (c.lap i : ℝ) + 1 ≤ g i * x := by
    dsimp [x]
    rw [← mul_div_assoc,le_div_iff₀ (hp _),mul_comm (g i)]
    exact (hgap i).1
  have h₂ : g i * y ≤ 8 * (c.lap i : ℝ) + 7 := by
    dsimp [y]
    rw [← mul_div_assoc,div_le_iff₀ (hp _),mul_comm (g i)]
    exact (hgap i).2
  have hm := mul_le_mul_of_nonneg_left hxy (hp i).le
  constructor <;> push_cast <;> linarith

/-- [PROVISIONAL: covering] The two recorded h₃ sides share one window.
Only the two inequalities comparing its moving opening to the closing
need correlations beyond the hull of the 509 boxes. -/
theorem h3_clearPoint_of_hull {g : Fin 7 → ℝ}
    (h₀ : g 0 = 1)
    (hbox : ∀ i, (![512,1202,1576,2027,2645,3615,9419] : Fin 7 → ℝ) i / 512 ≤ g i ∧
      g i ≤ (![512,1244,1625,2090,2728,3726,9712] : Fin 7 → ℝ) i / 512)
    (h₅ : 25 * g 2 ≤ 15 * g 4) (h₇ : 89 * g 2 ≤ 15 * g 6) :
    BandClearPoint g := by
  have hp (i : Fin 7) : 0 < g i := by
    have h := (hbox i).1
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_succ] at h ⊢ <;> linarith
  let x := max (25 / g 4) (89 / g 6)
  let y := 15 / g 2
  have hxy : x ≤ y := max_le
    ((div_le_div_iff₀ (hp _) (hp _)).2 h₅)
    ((div_le_div_iff₀ (hp _) (hp _)).2 h₇)
  have hx : 1 ≤ x := (le_div_iff₀ (hp 4)).2 (by
    have h := (hbox 4).2
    change g 4 ≤ (2728:ℝ)/512 at h
    linarith) |>.trans (le_max_left _ _)
  have hy : y ≤ 7 := (div_le_iff₀ (hp 2)).2 (by
    have h := (hbox 2).1
    change (1576:ℝ)/512 ≤ g 2 at h
    linarith)
  refine ⟨x,hx,by linarith,Or.inl (hxy.trans hy),fun i => ?_⟩
  apply (clearAt_R_iff _ _).mpr
  let j : Fin 7 → ℤ := ![0,1,1,2,3,4,11]
  refine ⟨j i,?_⟩
  have hleft : 8 * (j i : ℝ) + 1 ≤ g i * x := by
    have h := mul_le_mul_of_nonneg_left (le_max_left (25/g 4) (89/g 6)) (hp i).le
    have h' := mul_le_mul_of_nonneg_left (le_max_right (25/g 4) (89/g 6)) (hp i).le
    change g i * (25/g 4) ≤ g i * x at h
    change g i * (89/g 6) ≤ g i * x at h'
    have b₄ := hbox 4
    have b₆ := hbox 6
    have bi := hbox i
    change (2645:ℝ)/512 ≤ g 4 ∧ g 4 ≤ 2728/512 at b₄
    change (9419:ℝ)/512 ≤ g 6 ∧ g 6 ≤ 9712/512 at b₆
    fin_cases i <;> norm_num [j, Matrix.cons_val_zero, Matrix.cons_val_succ] at bi h h' ⊢
    all_goals first
      | linarith
      | apply le_trans _ h
        rw [← mul_div_assoc,le_div_iff₀ (hp 4)]
        first | (ring_nf; rfl) | linarith [bi.1,bi.2,b₄.1,b₄.2]
      | apply le_trans _ h'
        rw [← mul_div_assoc,le_div_iff₀ (hp 6)]
        first | (ring_nf; rfl) | linarith [bi.1,bi.2,b₆.1,b₆.2]
  have hright : g i * y ≤ 8 * (j i : ℝ) + 7 := by
    dsimp [y]
    rw [← mul_div_assoc,div_le_iff₀ (hp 2)]
    have bi := hbox i
    have b₂ := hbox 2
    change (1576:ℝ)/512 ≤ g 2 ∧ g 2 ≤ 1625/512 at b₂
    fin_cases i <;> norm_num [j] at bi ⊢
    all_goals first | (ring_nf; rfl) | linarith [bi.1,bi.2,b₂.1,b₂.2]
  have hm := mul_le_mul_of_nonneg_left hxy (hp i).le
  constructor <;> push_cast <;> linarith

/-- [PROVISIONAL: covering] A single window covers the seven h₃ grid
groups. The two bounds in each group are the closing reading's upper
face and the last reading's lower face. -/
theorem h3_clearPoint_of_grid_groups {g : Fin 7 → ℝ}
    (h₀ : g 0 = 1)
    (hbox : ∀ i, (![512,1202,1576,2027,2645,3615,9419] : Fin 7 → ℝ) i / 512 ≤ g i ∧
      g i ≤ (![512,1244,1625,2090,2728,3726,9712] : Fin 7 → ℝ) i / 512)
    (hgroup :
      (2645/512 ≤ g 4 ∧ g 2 ≤ 1577/512 ∧ 9419/512 ≤ g 6) ∨
      (2646/512 ≤ g 4 ∧ g 2 ≤ 1577/512 ∧ 9419/512 ≤ g 6) ∨
      (2647/512 ≤ g 4 ∧ g 2 ≤ 1577/512 ∧ 9423/512 ≤ g 6) ∨
      (2686/512 ≤ g 4 ∧ g 2 ≤ 1601/512 ∧ 9563/512 ≤ g 6) ∨
      (2687/512 ≤ g 4 ∧ g 2 ≤ 1602/512 ∧ 9565/512 ≤ g 6) ∨
      (2726/512 ≤ g 4 ∧ g 2 ≤ 1625/512 ∧ 9707/512 ≤ g 6) ∨
      (2727/512 ≤ g 4 ∧ g 2 ≤ 1625/512 ∧ 9708/512 ≤ g 6)) :
    BandClearPoint g := by
  apply h3_clearPoint_of_hull h₀ hbox <;>
    rcases hgroup with h | h | h | h | h | h | h <;> linarith [h.1,h.2.1,h.2.2]

#print axioms SideWindowCert.clearPoint
#print axioms h3_clearPoint_of_hull
#print axioms h3_clearPoint_of_grid_groups

/-! ## The vertex principle: a box cut by one linear plane (E846 item 3)

E846 measured the schema gap: the off-plane family of `[17,23)` is discharged by window
certificates holding on HALF-BOXES (a dyadic box cut by one linear side condition), and
zero of the 1,018 recorded side certificates extend to their axis-aligned bounding boxes.
The coupled-corner principle of E833 (a linear inequality holding at a box's 64 corners
holds on the box) extends to the half-box: the side region `box ∩ {h ≤ 0}` is the convex
hull of its VERTICES — the box corners on the side, together with the intersections of the
box's edges with the plane (`SideVertex` below; the vertex-set semantics of E833's split
machinery for one plane) — so a linear inequality holding at those vertices holds on the
whole side region.

The proof (`walkToVertex`) is a dimension walk, not a hull computation: from any point of
the side region violating an inequality, walk to another point of the region still
violating it with one fewer strictly-interior coordinate — a coordinate chord inside the
region, or an in-plane two-coordinate chord on the plane — until a vertex is reached.  The
contrapositive is `linLe_of_sideVertices`. -/

/-- The linear form with coefficient vector `a`.  The planes of the data are homogeneous
(`h₃ = 25ρ₇ − 89ρ₅` has constant term 0) and the certificate inequalities are linear. -/
def linForm (a : Fin 7 → ℝ) (g : Fin 7 → ℝ) : ℝ := ∑ i, a i * g i

/-- The number of coordinates of `g` strictly between the faces. -/
noncomputable def interiorCnt (lo hi : Fin 7 → ℝ) (g : Fin 7 → ℝ) : ℕ :=
  Finset.card (Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i))

/-- The vertex set of the side region `{g ∈ box : h g ≤ 0}` for the linear plane
`h = linForm a`: the box corners on the side, and the points of the box's edges (all but
at most one coordinate at a face) lying exactly on the plane. -/
-- STANDING: DEFINITION
def SideVertex (lo hi : Fin 7 → ℝ) (a : Fin 7 → ℝ) (g : Fin 7 → ℝ) : Prop :=
  ((∀ i, g i = lo i ∨ g i = hi i) ∧ linForm a g ≤ 0) ∨
    (∃ i₀ : Fin 7, (∀ i, i ≠ i₀ → g i = lo i ∨ g i = hi i) ∧ lo i₀ < g i₀ ∧ g i₀ < hi i₀ ∧
        linForm a g = 0)

/-- The vertex set of the OTHER side `{g ∈ box : 0 ≤ h g}` (the side the schema's `Region`
uses): box corners on the side, plus edge-plane points. -/
-- STANDING: DEFINITION
def SideVertexGE (lo hi : Fin 7 → ℝ) (a : Fin 7 → ℝ) (g : Fin 7 → ℝ) : Prop :=
  ((∀ i, g i = lo i ∨ g i = hi i) ∧ 0 ≤ linForm a g) ∨
    (∃ i₀ : Fin 7, (∀ i, i ≠ i₀ → g i = lo i ∨ g i = hi i) ∧ lo i₀ < g i₀ ∧ g i₀ < hi i₀ ∧
        linForm a g = 0)

/-! ### Linear-form helpers -/

/-- Updating one coordinate: the change of a linear form is the coefficient times the
coordinate change. -/
theorem linForm_update (a f : Fin 7 → ℝ) (i : Fin 7) (x : ℝ) :
    linForm a (fun l => if l = i then x else f l) = linForm a f + a i * (x - f i) := by
  classical
  have h : ∀ l : Fin 7, a l * (if l = i then x else f l)
      = a l * f l + (if l = i then a l * (x - f l) else 0) := by
    intro l; by_cases hl : l = i <;> simp only [hl, if_true, if_false] <;> ring
  unfold linForm
  simp only [h, Finset.sum_add_distrib]
  have h2 : ∑ l : Fin 7, (if l = i then a l * (x - f l) else 0) = a i * (x - f i) := by
    rw [Finset.sum_ite_eq' Finset.univ i (fun l => a l * (x - f l))]
    simp
  rw [h2]

#print axioms linForm_update

/-- Linear forms respect convex combinations. -/
theorem linForm_lin_combo (a p q : Fin 7 → ℝ) (w₁ w₂ : ℝ) :
    linForm a (fun l => w₁ * p l + w₂ * q l) = w₁ * linForm a p + w₂ * linForm a q := by
  have h : ∀ l : Fin 7, a l * (w₁ * p l + w₂ * q l) = w₁ * (a l * p l) + w₂ * (a l * q l) :=
    fun l => by ring
  unfold linForm
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]

#print axioms linForm_lin_combo

theorem linForm_neg (a g : Fin 7 → ℝ) : linForm (fun i => -a i) g = -linForm a g := by
  unfold linForm
  simp [Finset.sum_neg_distrib, mul_neg]

#print axioms linForm_neg

theorem linForm_single (i : Fin 7) (k : ℝ) (g : Fin 7 → ℝ) :
    linForm (fun l => if l = i then k else 0) g = k * g i := by
  classical
  have h : ∀ l : Fin 7, (if l = i then k else 0 : ℝ) * g l
      = (if l = i then k * g l else 0) := by
    intro l; by_cases hl : l = i <;> simp [hl]
  unfold linForm
  simp only [h]
  rw [Finset.sum_ite_eq' Finset.univ i (fun l => k * g l)]
  simp

#print axioms linForm_single

theorem linForm_two (i j : Fin 7) (ki kj : ℝ) (g : Fin 7 → ℝ) (hij : i ≠ j) :
    linForm (fun l => if l = i then ki else if l = j then kj else 0) g
      = ki * g i + kj * g j := by
  classical
  have h : ∀ l : Fin 7, (if l = i then ki else if l = j then kj else 0 : ℝ) * g l
      = (if l = i then ki * g l else 0) + (if l = j then kj * g l else 0) := by
    intro l
    by_cases h1 : l = i
    · subst h1
      rw [if_pos rfl, if_pos rfl, if_neg hij, add_zero]
    · by_cases h2 : l = j
      · subst h2
        rw [if_neg (Ne.symm hij), if_neg (Ne.symm hij), if_pos rfl, if_pos rfl, zero_add]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, zero_mul, zero_add]
  unfold linForm
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ i (fun l => ki * g l),
    Finset.sum_ite_eq' Finset.univ j (fun l => kj * g l)]
  simp

#print axioms linForm_two

/-- A convex combination above `κ` has an endpoint above `κ` (weights nonnegative,
summing to one; degenerate weights allowed). -/
theorem bad_of_combo (κ x y w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1)
    (h : κ < w₁ * x + w₂ * y) : κ < x ∨ κ < y := by
  by_contra hcon
  push_neg at hcon
  have e1 : w₁ * x ≤ w₁ * κ := mul_le_mul_of_nonneg_left hcon.1 hw₁
  have e2 : w₂ * y ≤ w₂ * κ := mul_le_mul_of_nonneg_left hcon.2 hw₂
  have e3 : w₁ * κ + w₂ * κ = κ := by rw [← add_mul, hw, one_mul]
  linarith

#print axioms bad_of_combo

/-! ### Interior-count helpers -/

theorem atFace_of_ninterior {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {i : Fin 7}
    (hbx : lo i ≤ g i ∧ g i ≤ hi i) (hn : ¬(lo i < g i ∧ g i < hi i)) :
    g i = lo i ∨ g i = hi i := by
  by_cases h : g i < hi i
  · by_cases h' : lo i < g i
    · exact absurd ⟨h', h⟩ hn
    · exact Or.inl (le_antisymm (le_of_not_gt h') hbx.1)
  · exact Or.inr (le_antisymm hbx.2 (le_of_not_gt h))

#print axioms atFace_of_ninterior

theorem interiorCnt_le {lo hi : Fin 7 → ℝ} {g q : Fin 7 → ℝ}
    (hsub : ∀ l, (lo l < q l ∧ q l < hi l) → lo l < g l ∧ g l < hi l) :
    interiorCnt lo hi q ≤ interiorCnt lo hi g := by
  apply Finset.card_le_card
  intro l hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hsub l (Finset.mem_filter.mp hl).2⟩

#print axioms interiorCnt_le

theorem interiorCnt_drop {lo hi : Fin 7 → ℝ} {g q : Fin 7 → ℝ} {d : Fin 7}
    (hintd : lo d < g d ∧ g d < hi d) (hqd : q d = lo d ∨ q d = hi d)
    (hsub : ∀ l, (lo l < q l ∧ q l < hi l) → lo l < g l ∧ g l < hi l) :
    interiorCnt lo hi q + 1 ≤ interiorCnt lo hi g := by
  classical
  unfold interiorCnt
  have hsub' : (Finset.univ.filter (fun l => lo l < q l ∧ q l < hi l))
      ⊆ (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).erase d := by
    intro l hl
    have hq := (Finset.mem_filter.mp hl).2
    have hne : l ≠ d := by
      intro heq
      rw [heq] at hq
      rcases hqd with h | h
      · rw [h] at hq; linarith
      · rw [h] at hq; linarith
    exact Finset.mem_erase.mpr ⟨hne,
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, hsub l hq⟩⟩
  have h1 := Finset.card_le_card hsub'
  have h2 : ((Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).erase d).card
      = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hintd⟩)
  have h3 : 1 ≤ (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card :=
    Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hintd⟩⟩
  omega

#print axioms interiorCnt_drop

/-! ### The hit-time helpers (in-plane chord machinery) -/

/-- The first time the moving coordinate `l` of `g l + t * w` reaches a face (`w ≠ 0`,
`g l` strictly between the faces); positive. -/
noncomputable def hitUp (lo hi : Fin 7 → ℝ) (g : Fin 7 → ℝ) (l : Fin 7) (w : ℝ) : ℝ :=
  if 0 < w then (hi l - g l) / w else (lo l - g l) / w

theorem hitUp_pos {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {l : Fin 7} {w : ℝ} (hw : w ≠ 0)
    (hint : lo l < g l ∧ g l < hi l) : 0 < hitUp lo hi g l w := by
  unfold hitUp
  rcases lt_or_gt_of_ne hw with h | h
  · rw [if_neg (by linarith)]
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rw [if_pos h]
    exact div_pos (by linarith) h

#print axioms hitUp_pos

theorem mem_box_of_le_hitUp {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {l : Fin 7} {w t : ℝ}
    (hw : w ≠ 0) (hint : lo l < g l ∧ g l < hi l) (ht0 : 0 ≤ t)
    (ht : t ≤ hitUp lo hi g l w) : lo l ≤ g l + t * w ∧ g l + t * w ≤ hi l := by
  rcases lt_or_gt_of_ne hw with h | h
  · have hH : hitUp lo hi g l w = (lo l - g l) / w := if_neg (by linarith)
    rw [hH] at ht
    have hkey : (lo l - g l) / w * w = lo l - g l := by field_simp
    have htw : (lo l - g l) / w * w ≤ t * w :=
      mul_le_mul_of_nonpos_right ht (by linarith)
    rw [hkey] at htw
    have hnp : t * w ≤ 0 := by
      have h2 : t * w ≤ t * 0 := mul_le_mul_of_nonneg_left (by linarith) ht0
      linarith
    exact ⟨by linarith, by linarith⟩
  · have hH : hitUp lo hi g l w = (hi l - g l) / w := if_pos h
    rw [hH] at ht
    have hkey : (hi l - g l) / w * w = hi l - g l := by field_simp
    have htw : t * w ≤ (hi l - g l) / w * w :=
      mul_le_mul_of_nonneg_right ht (le_of_lt h)
    rw [hkey] at htw
    have hnp : 0 ≤ t * w := by
      have h2 : 0 * w ≤ t * w := mul_le_mul_of_nonneg_right ht0 h.le
      linarith
    exact ⟨by linarith, by linarith⟩

#print axioms mem_box_of_le_hitUp

theorem eq_face_of_hitUp {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {l : Fin 7} {w : ℝ}
    (hw : w ≠ 0) (hint : lo l < g l ∧ g l < hi l) :
    g l + hitUp lo hi g l w * w = hi l ∨ g l + hitUp lo hi g l w * w = lo l := by
  rcases lt_or_gt_of_ne hw with h | h
  · refine Or.inr ?_
    have hH : hitUp lo hi g l w = (lo l - g l) / w := if_neg (by linarith)
    rw [hH]
    have hkey : (lo l - g l) / w * w = lo l - g l := by field_simp
    rw [hkey]
    ring
  · refine Or.inl ?_
    have hH : hitUp lo hi g l w = (hi l - g l) / w := if_pos h
    rw [hH]
    have hkey : (hi l - g l) / w * w = hi l - g l := by field_simp
    rw [hkey]
    ring

#print axioms eq_face_of_hitUp

/-! ### The leaf: a side point with at most one interior coordinate is a vertex -/

theorem sideVertex_of_interior_le_one (lo hi a : Fin 7 → ℝ) {g : Fin 7 → ℝ}
    (hbox : ∀ i, lo i ≤ g i ∧ g i ≤ hi i) (hcnt : interiorCnt lo hi g ≤ 1)
    (hg : linForm a g = 0) : SideVertex lo hi a g := by
  classical
  unfold interiorCnt at hcnt
  by_cases hc : (Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i)).card = 0
  · refine Or.inl ⟨fun i => ?_, by linarith⟩
    have hempty : (Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i)) = ∅ :=
      Finset.card_eq_zero.mp hc
    have hni : ¬(lo i < g i ∧ g i < hi i) := by
      intro hint
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hint⟩)
        (by rw [hempty]; exact Finset.notMem_empty i)
    exact atFace_of_ninterior (hbox i) hni
  · have h1 : (Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i)).card = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    have hmem : e ∈ Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i) := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨hle, hge⟩ := (Finset.mem_filter.mp hmem).2
    refine Or.inr ⟨e, fun i hie => ?_, hle, hge, hg⟩
    have hni : ¬(lo i < g i ∧ g i < hi i) := by
      intro hint
      have : i ∈ Finset.univ.filter (fun i => lo i < g i ∧ g i < hi i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hint⟩
      rw [he] at this
      exact absurd (Finset.mem_singleton.mp this) hie
    exact atFace_of_ninterior (hbox i) hni

#print axioms sideVertex_of_interior_le_one

/-! ### The in-plane two-coordinate chord (the plane-case walk step) -/

/-- **The in-plane chord step.**  From a point `g` exactly on the plane `linForm a = 0`,
with two strictly-interior coordinates `i ≠ j` and velocities `wi, wj` along them whose
`a`-weighted sum vanishes (`a i * wi + a j * wj = 0`), not both zero: there are two points
`q₁, q₂` of the box, both exactly on the plane, each with one of `i, j` at a face, such
that `g` is a strictly-convex combination of `q₁, q₂` (for every linear form).  This is
the plane half of the dimension walk: moving along the chord keeps `h = 0` and reaches
box faces. -/
theorem planeChord {lo hi a : Fin 7 → ℝ} {g : Fin 7 → ℝ} {i j : Fin 7} (hij : i ≠ j)
    (hbox : ∀ l, lo l ≤ g l ∧ g l ≤ hi l)
    (hinti : lo i < g i ∧ g i < hi i) (hintj : lo j < g j ∧ g j < hi j)
    (wi wj : ℝ) (hwv : a i * wi + a j * wj = 0) (hwne : wi ≠ 0 ∨ wj ≠ 0) :
    ∃ q₁ q₂ : Fin 7 → ℝ,
      (∀ l, lo l ≤ q₁ l ∧ q₁ l ≤ hi l) ∧ (∀ l, lo l ≤ q₂ l ∧ q₂ l ≤ hi l) ∧
        linForm a q₁ = linForm a g ∧ linForm a q₂ = linForm a g ∧
        (∀ l, (lo l < q₁ l ∧ q₁ l < hi l) → lo l < g l ∧ g l < hi l) ∧
        (∀ l, (lo l < q₂ l ∧ q₂ l < hi l) → lo l < g l ∧ g l < hi l) ∧
        (∃ d₁, (lo d₁ < g d₁ ∧ g d₁ < hi d₁) ∧ (q₁ d₁ = lo d₁ ∨ q₁ d₁ = hi d₁)) ∧
        (∃ d₂, (lo d₂ < g d₂ ∧ g d₂ < hi d₂) ∧ (q₂ d₂ = lo d₂ ∨ q₂ d₂ = hi d₂)) ∧
        (∃ u₁ u₂ : ℝ, 0 < u₁ ∧ 0 < u₂ ∧ u₁ + u₂ = 1 ∧
          ∀ cc : Fin 7 → ℝ, linForm cc g = u₁ * linForm cc q₁ + u₂ * linForm cc q₂) := by
  classical
  -- the moving point, decomposed so that `linForm_update` applies twice
  obtain ⟨base, hb⟩ : ∃ base : ℝ → (Fin 7 → ℝ),
      ∀ t l, base t l = if l = j then g j + t * wj else g l :=
    ⟨fun t l => if l = j then g j + t * wj else g l, fun t l => rfl⟩
  obtain ⟨pt, hp⟩ : ∃ pt : ℝ → (Fin 7 → ℝ),
      ∀ t l, pt t l = if l = i then g i + t * wi else base t l :=
    ⟨fun t l => if l = i then g i + t * wi else base t l, fun t l => rfl⟩
  -- linearity of the moving point in t, for every coefficient vector
  have hlinPt : ∀ (cc : Fin 7 → ℝ) (t : ℝ),
      linForm cc (pt t) = linForm cc g + t * (cc i * wi + cc j * wj) := by
    intro cc t
    have hptl : pt t = fun l => if l = i then (g i + t * wi) else base t l := funext (hp t)
    have hbtl : base t = fun l => if l = j then (g j + t * wj) else g l := funext (hb t)
    have hbi : base t i = g i := by rw [hb t i, if_neg hij]
    rw [hptl, linForm_update cc (base t) i (g i + t * wi), hbi, hbtl,
      linForm_update cc g j (g j + t * wj)]
    ring
  -- the forward and backward hit times
  have hneIfw : wi = 0 → wj ≠ 0 := by
    intro h
    rcases hwne with h1 | h2
    · exact absurd h h1
    · exact h2
  -- the forward hit time: first coordinate among {i, j} to reach a face
  obtain ⟨tp, htp0, htpi, htpj, htpface⟩ : ∃ tp : ℝ,
      (0 < tp) ∧ (wi ≠ 0 → tp ≤ hitUp lo hi g i wi) ∧ (wj ≠ 0 → tp ≤ hitUp lo hi g j wj) ∧
        (∃ d, (lo d < g d ∧ g d < hi d) ∧ (pt tp d = lo d ∨ pt tp d = hi d)) := by
    by_cases hwi : wi = 0
    · refine ⟨hitUp lo hi g j wj, hitUp_pos (hneIfw hwi) hintj, by intro h; exact absurd hwi h,
        fun _ => le_refl _, ⟨j, hintj, ?_⟩⟩
      rcases eq_face_of_hitUp (hneIfw hwi) hintj with h | h
      · refine Or.inr ?_
        rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl]
        exact h
      · refine Or.inl ?_
        rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl]
        exact h
    by_cases hwj : wj = 0
    · refine ⟨hitUp lo hi g i wi, hitUp_pos hwi hinti, fun _ => le_refl _,
        by intro h; exact absurd hwj h, ⟨i, hinti, ?_⟩⟩
      rcases eq_face_of_hitUp hwi hinti with h | h
      · refine Or.inr ?_
        rw [hp _, if_pos rfl]
        exact h
      · refine Or.inl ?_
        rw [hp _, if_pos rfl]
        exact h
    · refine ⟨min (hitUp lo hi g i wi) (hitUp lo hi g j wj), lt_min (hitUp_pos hwi hinti)
        (hitUp_pos hwj hintj), fun _ => min_le_left _ _, fun _ => min_le_right _ _, ?_⟩
      rcases le_total (hitUp lo hi g i wi) (hitUp lo hi g j wj) with hle | hle
      · refine ⟨i, hinti, ?_⟩
        rcases eq_face_of_hitUp hwi hinti with h | h
        · refine Or.inr ?_
          rw [hp _, if_pos rfl, min_eq_left hle]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_pos rfl, min_eq_left hle]
          exact h
      · refine ⟨j, hintj, ?_⟩
        rcases eq_face_of_hitUp hwj hintj with h | h
        · refine Or.inr ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl, min_eq_right hle]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl, min_eq_right hle]
          exact h
  -- the backward hit time: the mirror construction with negated velocities
  obtain ⟨tm, htm0, htmi, htmj, htmface⟩ : ∃ tm : ℝ,
      (tm < 0) ∧ (wi ≠ 0 → -tm ≤ hitUp lo hi g i (-wi)) ∧ (wj ≠ 0 → -tm ≤ hitUp lo hi g j (-wj)) ∧
        (∃ d, (lo d < g d ∧ g d < hi d) ∧ (pt tm d = lo d ∨ pt tm d = hi d)) := by
    by_cases hwi : wi = 0
    · refine ⟨-(hitUp lo hi g j (-wj)), ?_, by intro h; exact absurd hwi h, ?_, ⟨j, hintj, ?_⟩⟩
      · have h := hitUp_pos (neg_ne_zero.mpr (hneIfw hwi)) hintj
        linarith
      · intro _
        rw [neg_neg]
      · rcases eq_face_of_hitUp (neg_ne_zero.mpr (hneIfw hwi)) hintj with h | h
        · refine Or.inr ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl]
          have e : g j + -(hitUp lo hi g j (-wj)) * wj
              = g j + hitUp lo hi g j (-wj) * (-wj) := by ring
          rw [e]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl]
          have e : g j + -(hitUp lo hi g j (-wj)) * wj
              = g j + hitUp lo hi g j (-wj) * (-wj) := by ring
          rw [e]
          exact h
    by_cases hwj : wj = 0
    · refine ⟨-(hitUp lo hi g i (-wi)), ?_, ?_, by intro h; exact absurd hwj h, ⟨i, hinti, ?_⟩⟩
      · have h := hitUp_pos (neg_ne_zero.mpr hwi) hinti
        linarith
      · intro _
        rw [neg_neg]
      · rcases eq_face_of_hitUp (neg_ne_zero.mpr hwi) hinti with h | h
        · refine Or.inr ?_
          rw [hp _, if_pos rfl]
          have e : g i + -(hitUp lo hi g i (-wi)) * wi
              = g i + hitUp lo hi g i (-wi) * (-wi) := by ring
          rw [e]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_pos rfl]
          have e : g i + -(hitUp lo hi g i (-wi)) * wi
              = g i + hitUp lo hi g i (-wi) * (-wi) := by ring
          rw [e]
          exact h
    · refine ⟨-(min (hitUp lo hi g i (-wi)) (hitUp lo hi g j (-wj))), ?_, ?_, ?_, ?_⟩
      · have h := lt_min (hitUp_pos (neg_ne_zero.mpr hwi) hinti)
          (hitUp_pos (neg_ne_zero.mpr hwj) hintj)
        linarith
      · intro _
        rw [neg_neg]
        exact min_le_left _ _
      · intro _
        rw [neg_neg]
        exact min_le_right _ _
      rcases le_total (hitUp lo hi g i (-wi)) (hitUp lo hi g j (-wj)) with hle | hle
      · refine ⟨i, hinti, ?_⟩
        rcases eq_face_of_hitUp (neg_ne_zero.mpr hwi) hinti with h | h
        · refine Or.inr ?_
          rw [hp _, if_pos rfl, min_eq_left hle]
          have e : g i + -(hitUp lo hi g i (-wi)) * wi
              = g i + hitUp lo hi g i (-wi) * (-wi) := by ring
          rw [e]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_pos rfl, min_eq_left hle]
          have e : g i + -(hitUp lo hi g i (-wi)) * wi
              = g i + hitUp lo hi g i (-wi) * (-wi) := by ring
          rw [e]
          exact h
      · refine ⟨j, hintj, ?_⟩
        rcases eq_face_of_hitUp (neg_ne_zero.mpr hwj) hintj with h | h
        · refine Or.inr ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl, min_eq_right hle]
          have e : g j + -(hitUp lo hi g j (-wj)) * wj
              = g j + hitUp lo hi g j (-wj) * (-wj) := by ring
          rw [e]
          exact h
        · refine Or.inl ?_
          rw [hp _, if_neg (Ne.symm hij), hb _, if_pos rfl, min_eq_right hle]
          have e : g j + -(hitUp lo hi g j (-wj)) * wj
              = g j + hitUp lo hi g j (-wj) * (-wj) := by ring
          rw [e]
          exact h
  -- the chord endpoints and the strictly-positive convex combination
  refine ⟨pt tp, pt tm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- q₁ in the box
    intro l
    by_cases hli : l = i
    · rw [hli]
      by_cases hwi : wi = 0
      · rw [hp tp i, if_pos rfl, hwi, mul_zero]
        exact ⟨by linarith, by linarith⟩
      · rw [hp tp i, if_pos rfl]
        exact mem_box_of_le_hitUp hwi hinti htp0.le (htpi hwi)
    by_cases hlj : l = j
    · rw [hlj]
      by_cases hwj : wj = 0
      · rw [hp tp j, if_neg (Ne.symm hij), hb tp j, if_pos rfl, hwj, mul_zero]
        exact ⟨by linarith, by linarith⟩
      · rw [hp tp j, if_neg (Ne.symm hij), hb tp j, if_pos rfl]
        exact mem_box_of_le_hitUp hwj hintj htp0.le (htpj hwj)
    · rw [hp tp l, if_neg hli, hb tp l, if_neg hlj]
      exact hbox l
  · -- q₂ in the box
    intro l
    by_cases hli : l = i
    · rw [hli]
      by_cases hwi : wi = 0
      · rw [hp tm i, if_pos rfl, hwi, mul_zero]
        exact ⟨by linarith, by linarith⟩
      · rw [hp tm i, if_pos rfl]
        have hmem := mem_box_of_le_hitUp (neg_ne_zero.mpr hwi) hinti (by linarith) (htmi hwi)
        have hconv : g i + tm * wi = g i + (-tm) * (-wi) := by ring
        rw [hconv]
        exact hmem
    by_cases hlj : l = j
    · rw [hlj]
      by_cases hwj : wj = 0
      · rw [hp tm j, if_neg (Ne.symm hij), hb tm j, if_pos rfl, hwj, mul_zero]
        exact ⟨by linarith, by linarith⟩
      · rw [hp tm j, if_neg (Ne.symm hij), hb tm j, if_pos rfl]
        have hmem := mem_box_of_le_hitUp (neg_ne_zero.mpr hwj) hintj (by linarith) (htmj hwj)
        have hconv : g j + tm * wj = g j + (-tm) * (-wj) := by ring
        rw [hconv]
        exact hmem
    · rw [hp tm l, if_neg hli, hb tm l, if_neg hlj]
      exact hbox l
  · -- q₁ on the plane
    rw [hlinPt a tp, hwv]
    ring
  · -- q₂ on the plane
    rw [hlinPt a tm, hwv]
    ring
  · -- interior coordinates of q₁ are interior coordinates of g
    intro l hl
    by_cases hli : l = i
    · subst hli
      exact hinti
    by_cases hlj : l = j
    · subst hlj
      exact hintj
    · have hql : pt tp l = g l := by rw [hp tp l, if_neg hli, hb tp l, if_neg hlj]
      rw [hql] at hl
      exact hl
  · -- interior coordinates of q₂ are interior coordinates of g
    intro l hl
    by_cases hli : l = i
    · subst hli
      exact hinti
    by_cases hlj : l = j
    · subst hlj
      exact hintj
    · have hql : pt tm l = g l := by rw [hp tm l, if_neg hli, hb tm l, if_neg hlj]
      rw [hql] at hl
      exact hl
  · -- q₁ at a face
    obtain ⟨d, hd, hf⟩ := htpface
    exact ⟨d, hd, hf⟩
  · -- q₂ at a face
    obtain ⟨d, hd, hf⟩ := htmface
    exact ⟨d, hd, hf⟩
  · -- the strictly-positive convex combination
    have hden : (0:ℝ) < tp - tm := by linarith
    have hne : tp - tm ≠ 0 := by linarith
    have hu₁ : (0:ℝ) < -tm / (tp - tm) := div_pos (by linarith) hden
    have hu₂ : (0:ℝ) < tp / (tp - tm) := div_pos (by linarith) hden
    have heq : (-tm / (tp - tm)) + (tp / (tp - tm)) = 1 := by
      rw [← add_div, div_eq_iff hne]
      ring
    refine ⟨-tm / (tp - tm), tp / (tp - tm), hu₁, hu₂, heq, ?_⟩
    intro cc
    have h1 := hlinPt cc tp
    have h2 := hlinPt cc tm
    have hw1 : (-tm / (tp - tm)) * tp + (tp / (tp - tm)) * tm = 0 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, neg_mul, ← add_div, div_eq_zero_iff]
      exact Or.inl (by ring)
    have key : (-tm / (tp - tm)) * (linForm cc g + tp * (cc i * wi + cc j * wj))
        + (tp / (tp - tm)) * (linForm cc g + tm * (cc i * wi + cc j * wj))
        = linForm cc g := by
      have e1 : ((-tm / (tp - tm)) + (tp / (tp - tm))) * linForm cc g
          = linForm cc g := by rw [heq, one_mul]
      have e2 : ((-tm / (tp - tm)) * tp + (tp / (tp - tm)) * tm) * (cc i * wi + cc j * wj)
          = 0 := by rw [hw1]; ring
      calc (-tm / (tp - tm)) * (linForm cc g + tp * (cc i * wi + cc j * wj))
          + (tp / (tp - tm)) * (linForm cc g + tm * (cc i * wi + cc j * wj))
          = ((-tm / (tp - tm)) + (tp / (tp - tm))) * linForm cc g
            + ((-tm / (tp - tm)) * tp + (tp / (tp - tm)) * tm) * (cc i * wi + cc j * wj) := by ring
        _ = linForm cc g + 0 := by rw [e1, e2]
        _ = linForm cc g := by ring
    rw [h1, h2]
    exact key.symm

/-! ### The coordinate-move toolkit (the walk's moving point) -/

/-- The point `g` with coordinate `d` moved to `x`. -/
def moveP (g : Fin 7 → ℝ) (d : Fin 7) (x : ℝ) : Fin 7 → ℝ := fun l => if l = d then x else g l

theorem moveP_self (g : Fin 7 → ℝ) (d : Fin 7) (x : ℝ) : moveP g d x d = x := by
  unfold moveP
  exact if_pos rfl

theorem moveP_ne (g : Fin 7 → ℝ) (d : Fin 7) (x : ℝ) {l : Fin 7} (hl : l ≠ d) :
    moveP g d x l = g l := by
  unfold moveP
  exact if_neg hl

theorem linForm_moveP (cc : Fin 7 → ℝ) (g : Fin 7 → ℝ) (d : Fin 7) (x : ℝ) :
    linForm cc (moveP g d x) = linForm cc g + cc d * (x - g d) :=
  linForm_update cc g d x

theorem moveP_box {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {d : Fin 7} {x : ℝ}
    (hbox : ∀ l, lo l ≤ g l ∧ g l ≤ hi l) (hx : lo d ≤ x ∧ x ≤ hi d) (l : Fin 7) :
    lo l ≤ moveP g d x l ∧ moveP g d x l ≤ hi l := by
  by_cases hl : l = d
  · rw [hl, moveP_self]
    exact hx
  · rw [moveP_ne _ _ _ hl]
    exact hbox l

theorem moveP_interior_drop {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {d : Fin 7} {x : ℝ}
    (hintd : lo d < g d ∧ g d < hi d) (hx : x = lo d ∨ x = hi d) :
    interiorCnt lo hi (moveP g d x) + 1 ≤ interiorCnt lo hi g :=
  interiorCnt_drop hintd (by rw [moveP_self]; exact hx)
    (by
      intro l hl
      by_cases hld : l = d
      · rw [hld, moveP_self] at hl
        rcases hx with h | h
        · rw [h] at hl
          exact (lt_irrefl _ hl.1).elim
        · rw [h] at hl
          exact (lt_irrefl _ hl.2).elim
      · rw [moveP_ne _ _ _ hld] at hl
        exact hl)

theorem interiorCnt_congr {lo hi : Fin 7 → ℝ} {g q : Fin 7 → ℝ}
    (h : ∀ l, (lo l < g l ∧ g l < hi l) ↔ (lo l < q l ∧ q l < hi l)) :
    interiorCnt lo hi g = interiorCnt lo hi q := by
  have heq : Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)
      = Finset.univ.filter (fun l => lo l < q l ∧ q l < hi l) := by
    refine Finset.ext fun l => ?_
    simp only [Finset.mem_filter, h l]
  calc interiorCnt lo hi g
      = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card := rfl
    _ = (Finset.univ.filter (fun l => lo l < q l ∧ q l < hi l)).card := by rw [heq]
    _ = interiorCnt lo hi q := rfl

theorem exists_interior_ne {lo hi : Fin 7 → ℝ} {g : Fin 7 → ℝ} {d : Fin 7}
    (hd : lo d < g d ∧ g d < hi d) (hcnt : 2 ≤ interiorCnt lo hi g) :
    ∃ e : Fin 7, e ≠ d ∧ lo e < g e ∧ g e < hi e := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l) ⊆ {d} := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    by_cases he : l = d
    · rw [he]
      exact Finset.mem_singleton_self d
    · exact absurd hl'.right (not_lt.mpr (hcon l he hl'.left))
  have h1 := Finset.card_le_card hsub
  have h2 : ({d} : Finset (Fin 7)).card = 1 := rfl
  have h3 : 1 ≤ (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card :=
    Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩⟩
  have heq : interiorCnt lo hi g = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card := rfl
  omega

theorem interiorCnt_le_card (lo hi : Fin 7 → ℝ) (g : Fin 7 → ℝ) :
    interiorCnt lo hi g ≤ 7 := by
  have h1 : (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card
      ≤ (Finset.univ (α := Fin 7)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h2 : (Finset.univ (α := Fin 7)).card = 7 := rfl
  calc interiorCnt lo hi g
      = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card := rfl
    _ ≤ 7 := by omega

/-! ### Convex-combination transfer lemmas -/

/-- A nonpositive convex combination has a nonpositive endpoint (strictly positive
weights). -/
theorem combo_nonpos {x y w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (h : w₁ * x + w₂ * y ≤ 0) : x ≤ 0 ∨ y ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have h1 : 0 < w₁ * x := mul_pos hw₁ hcon.1
  have h2 : 0 < w₂ * y := mul_pos hw₂ hcon.2
  linarith

/-- A convex combination is bounded by one of its endpoints (strictly positive weights,
summing to one). -/
theorem combo_le_max {x y w₁ w₂ z : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hws : w₁ + w₂ = 1)
    (h : w₁ * x + w₂ * y = z) : z ≤ x ∨ z ≤ y := by
  by_contra hcon
  push_neg at hcon
  have e1 : w₁ * x < w₁ * z := mul_lt_mul_of_pos_left hcon.1 hw₁
  have e2 : w₂ * y < w₂ * z := mul_lt_mul_of_pos_left hcon.2 hw₂
  have h1 : w₁ * z + w₂ * z = z := by rw [← add_mul, hws, one_mul]
  linarith

/-! ### The one-step walk -/

/-- **The one-step walk** (the half-box coupled-corner principle's engine): from a side
point `g` (`h g ≤ 0`) violating a linear inequality (`0 < linForm cc g`) with at least one
interior coordinate, either a side VERTEX already dominates `g`, or there is a side point
`q` with strictly fewer interior coordinates that dominates `g`.  The three move types:
`M1` face-or-plane-crossing along a `cc`-increasing coordinate; `M2` the in-plane chord
(`planeChord`) at the crossing point; `M3` the `cc`-preserving face move. -/
theorem walkStep (lo hi a cc : Fin 7 → ℝ) {g : Fin 7 → ℝ}
    (hbox : ∀ l, lo l ≤ g l ∧ g l ≤ hi l) (hs : linForm a g ≤ 0) (hviol : 0 < linForm cc g)
    (hcnt : 1 ≤ interiorCnt lo hi g) :
    (∃ v, SideVertex lo hi a v ∧ linForm cc g ≤ linForm cc v) ∨
      ∃ q : Fin 7 → ℝ, interiorCnt lo hi q < interiorCnt lo hi g ∧
        (∀ l, lo l ≤ q l ∧ q l ≤ hi l) ∧ linForm a q ≤ 0 ∧ linForm cc g ≤ linForm cc q := by
  classical
  by_cases hcc : ∃ d, (lo d < g d ∧ g d < hi d) ∧ cc d ≠ 0
  · obtain ⟨d, hdint, hdcc⟩ := hcc
    -- the cc-increasing direction u
    obtain ⟨u, hucc, hudir⟩ : ∃ u : ℝ, cc d * u > 0 ∧ (g d + u = hi d ∨ g d + u = lo d) := by
      rcases lt_or_gt_of_ne hdcc with hc | hc
      · exact ⟨lo d - g d, mul_pos_of_neg_of_neg hc (by linarith), Or.inr (by linarith)⟩
      · exact ⟨hi d - g d, mul_pos hc (by linarith), Or.inl (by linarith)⟩
    -- the face-hit point
    have hxd : lo d ≤ g d + u ∧ g d + u ≤ hi d := by
      rcases hudir with h | h
      · rw [h]; exact ⟨by linarith, le_refl _⟩
      · rw [h]; exact ⟨le_refl _, by linarith⟩
    have hqFbox : ∀ l, lo l ≤ moveP g d (g d + u) l ∧ moveP g d (g d + u) l ≤ hi l :=
      fun l => moveP_box hbox hxd l
    have hqFface : moveP g d (g d + u) d = hi d ∨ moveP g d (g d + u) d = lo d := by
      rw [moveP_self]; exact hudir
    have hdropF : interiorCnt lo hi (moveP g d (g d + u)) + 1 ≤ interiorCnt lo hi g :=
      moveP_interior_drop hdint hudir.symm
    have hccF : linForm cc g ≤ linForm cc (moveP g d (g d + u)) := by
      rw [linForm_moveP]; linarith
    have haF : linForm a (moveP g d (g d + u)) = linForm a g + a d * u := by
      rw [linForm_moveP]
      ring
    by_cases hqFa : linForm a (moveP g d (g d + u)) ≤ 0
    · -- face case: the face-hit point stays on the side
      refine Or.inr ⟨moveP g d (g d + u), hdropF, hqFbox, hqFa, hccF⟩
    · -- crossing case: h > 0 at the face, so the chord exits the side; find the crossing
      have hqFpos : 0 < linForm a (moveP g d (g d + u)) := by linarith
      have hadu : 0 < a d * u := by linarith
      obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = -(linForm a g) / (a d * u) := ⟨_, rfl⟩
      have hs0 : 0 ≤ s := by rw [hsdef]; exact div_nonneg (neg_nonneg.mpr hs) hadu.le
      have hs1 : s < 1 := by rw [hsdef, div_lt_iff₀ hadu]; linarith
      have hsu : s * (a d * u) = -(linForm a g) := by
        have h2 : a d * u ≠ 0 := ne_of_gt hadu
        have h3 := hsdef
        rw [eq_div_iff h2] at h3
        exact h3
      -- the crossing point t* (on the plane, dominating g)
      have htstar_h : linForm a (moveP g d (g d + s * u)) = 0 := by
        rw [linForm_moveP]
        have h2 : a d * (g d + s * u - g d) = s * (a d * u) := by ring
        rw [h2, hsu]
        ring
      have htstar_cc : linForm cc g ≤ linForm cc (moveP g d (g d + s * u)) := by
        rw [linForm_moveP]
        have h2 : cc d * (g d + s * u - g d) = s * (cc d * u) := by ring
        rw [h2]
        have h3 : 0 ≤ s * (cc d * u) := mul_nonneg hs0 hucc.le
        linarith
      have htstar_box : ∀ l, lo l ≤ moveP g d (g d + s * u) l ∧ moveP g d (g d + s * u) l ≤ hi l :=
        fun l => moveP_box hbox (by
          rcases hudir with h | h
          · have hu' : (0:ℝ) < u := by linarith
            have hp1 : 0 ≤ s * u := mul_nonneg hs0 hu'.le
            have hsu' : s * u < u := by
              have h6 : (s - 1) * u < 0 := mul_neg_of_neg_of_pos (by linarith) hu'
              rw [show (s - 1) * u = s * u - u from by ring] at h6
              linarith
            exact ⟨by linarith, by linarith⟩
          · have hu' : u < 0 := by linarith
            have hp1 : s * u ≤ 0 := by
              have h3 : s * u ≤ s * 0 := mul_le_mul_of_nonneg_left (le_of_lt hu') hs0
              linarith
            have hsu' : u < s * u := by
              have h6 : (0:ℝ) < (s - 1) * u := mul_pos_of_neg_of_neg (by linarith) hu'
              rw [show (s - 1) * u = s * u - u from by ring] at h6
              linarith
            exact ⟨by linarith, by linarith⟩) l
      have htstar_int : lo d < g d + s * u ∧ g d + s * u < hi d := by
        rcases hudir with h | h
        · have hu' : (0:ℝ) < u := by linarith
          have hp1 : 0 ≤ s * u := mul_nonneg hs0 hu'.le
          have hsu' : s * u < u := by
            have h6 : (s - 1) * u < 0 := mul_neg_of_neg_of_pos (by linarith) hu'
            rw [show (s - 1) * u = s * u - u from by ring] at h6
            linarith
          exact ⟨by linarith, by linarith⟩
        · have hu' : u < 0 := by linarith
          have hp1 : s * u ≤ 0 := by
            have h3 : s * u ≤ s * 0 := mul_le_mul_of_nonneg_left (le_of_lt hu') hs0
            linarith
          have hsu' : u < s * u := by
            have h6 : (0:ℝ) < (s - 1) * u := mul_pos_of_neg_of_neg (by linarith) hu'
            rw [show (s - 1) * u = s * u - u from by ring] at h6
            linarith
          exact ⟨by linarith, by linarith⟩
      have htcnt : interiorCnt lo hi (moveP g d (g d + s * u)) = interiorCnt lo hi g := by
        apply interiorCnt_congr
        intro l
        by_cases hl : l = d
        · rw [hl, moveP_self]
          exact ⟨fun _ => hdint, fun _ => htstar_int⟩
        · rw [moveP_ne _ _ _ hl]
      by_cases hone : interiorCnt lo hi g = 1
      · -- count = 1: the crossing point is itself a side vertex (one interior coordinate)
        have hc1 : Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l) = {d} := by
          have hdin : d ∈ Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ d, hdint⟩
          have hcard : (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card = 1 := by
            calc (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card
                = interiorCnt lo hi g := rfl
              _ = 1 := hone
          obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
          have hde : d = e := by
            have h2 : d ∈ Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l) := hdin
            rw [he] at h2
            exact Finset.mem_singleton.mp h2
          rw [he, hde]
        refine Or.inl ⟨moveP g d (g d + s * u),
          Or.inr ⟨d, ?_, by rw [moveP_self]; exact htstar_int.1,
            by rw [moveP_self]; exact htstar_int.2, htstar_h⟩, htstar_cc⟩
        intro l hl
        rw [moveP_ne _ _ _ hl]
        have hnl : l ∉ Finset.univ.filter (fun l2 => lo l2 < g l2 ∧ g l2 < hi l2) := by
          intro hmem
          rw [hc1] at hmem
          exact hl (Finset.mem_singleton.mp hmem)
        exact atFace_of_ninterior (hbox l)
          (fun hint => hnl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hint⟩))
      · -- count ≥ 2: inline the plane-step at the crossing point
        have hge2 : 2 ≤ interiorCnt lo hi (moveP g d (g d + s * u)) := by rw [htcnt]; omega
        by_cases hex : ∃ e, (lo e < moveP g d (g d + s * u) e ∧
              moveP g d (g d + s * u) e < hi e) ∧ a e ≠ 0
        · -- M2: the in-plane chord at t* (planeChord)
          obtain ⟨e, hinte, hae⟩ := hex
          obtain ⟨e2, he2ne, hinte2⟩ := exists_interior_ne hinte hge2
          obtain ⟨q₁, q₂, hq1box, hq2box, hpl1, hpl2, hint1, hint2, hface1, hface2,
              hu₁, hu₂, hupos, huppos, husum, hcombo⟩ :=
            planeChord (lo := lo) (hi := hi) (a := a) (g := moveP g d (g d + s * u))
              (Ne.symm he2ne) htstar_box hinte hinte2 (a e2) (-(a e))
              (show a e * (a e2) + a e2 * -(a e) = 0 by ring)
              (Or.inr (neg_ne_zero.mpr hae))
          obtain ⟨d₁, hd₁int, hd₁face⟩ := hface1
          have hdrop1 : interiorCnt lo hi q₁ + 1 ≤ interiorCnt lo hi (moveP g d (g d + s * u)) :=
            interiorCnt_drop hd₁int hd₁face hint1
          obtain ⟨d₂, hd₂int, hd₂face⟩ := hface2
          have hdrop2 : interiorCnt lo hi q₂ + 1 ≤ interiorCnt lo hi (moveP g d (g d + s * u)) :=
            interiorCnt_drop hd₂int hd₂face hint2
          rcases combo_le_max hupos huppos husum (hcombo cc).symm with h1' | h2'
          · refine Or.inr ⟨q₁, ?_, hq1box, ?_, ?_⟩
            · omega
            · rw [hpl1]; linarith [htstar_h]
            · exact le_trans htstar_cc h1'
          · refine Or.inr ⟨q₂, ?_, hq2box, ?_, ?_⟩
            · omega
            · rw [hpl2]; linarith [htstar_h]
            · exact le_trans htstar_cc h2'
        · -- M3-directional: a e = 0 on every interior coordinate of t*; move one to a face
          push_neg at hex
          obtain ⟨e, hinte⟩ :
              ∃ e, lo e < moveP g d (g d + s * u) e ∧ moveP g d (g d + s * u) e < hi e := by
            have hne : (Finset.univ.filter (fun l => lo l < moveP g d (g d + s * u) l ∧
                moveP g d (g d + s * u) l < hi l)) ≠ ∅ := by
              intro hempty
              have hcard := Finset.card_eq_zero.mpr hempty
              have heq2 : interiorCnt lo hi (moveP g d (g d + s * u))
                  = (Finset.univ.filter (fun l => lo l < moveP g d (g d + s * u) l ∧
                    moveP g d (g d + s * u) l < hi l)).card := rfl
              omega
            obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            exact ⟨e, (Finset.mem_filter.mp he).2⟩
          obtain ⟨x, hxdir, hxle⟩ : ∃ x : ℝ, (x = lo e ∨ x = hi e) ∧
              0 ≤ cc e * (x - moveP g d (g d + s * u) e) := by
            rcases lt_trichotomy (cc e) 0 with hclt | hceq | hcgt
            · exact ⟨lo e, Or.inl rfl, le_of_lt (mul_pos_of_neg_of_neg hclt (by linarith))⟩
            · exact ⟨hi e, Or.inr rfl, by rw [hceq, zero_mul]⟩
            · exact ⟨hi e, Or.inr rfl, le_of_lt (mul_pos hcgt (by linarith))⟩
          have hxe : lo e ≤ x ∧ x ≤ hi e := by
            rcases hxdir with h | h
            · rw [h]; exact ⟨le_refl _, le_trans (htstar_box e).1 (htstar_box e).2⟩
            · rw [h]; exact ⟨le_trans (htstar_box e).1 (htstar_box e).2, le_refl _⟩
          refine Or.inr ⟨moveP (moveP g d (g d + s * u)) e x, ?_,
            fun l => moveP_box htstar_box hxe l, ?_, ?_⟩
          · have hdrop : interiorCnt lo hi (moveP (moveP g d (g d + s * u)) e x) + 1 ≤
              interiorCnt lo hi (moveP g d (g d + s * u)) :=
              moveP_interior_drop hinte hxdir
            omega
          · have hae0 : a e = 0 := hex e hinte
            have hq : linForm a (moveP (moveP g d (g d + s * u)) e x)
                = linForm a (moveP g d (g d + s * u)) + a e * (x - moveP g d (g d + s * u) e) :=
              linForm_moveP a (moveP g d (g d + s * u)) e x
            rw [hq, htstar_h, hae0]
            linarith
          · have hq : linForm cc (moveP (moveP g d (g d + s * u)) e x)
                = linForm cc (moveP g d (g d + s * u)) + cc e * (x - moveP g d (g d + s * u) e) :=
              linForm_moveP cc (moveP g d (g d + s * u)) e x
            rw [hq]
            exact le_trans htstar_cc (by linarith)
  · -- no interior coordinate has cc ≠ 0: the cc-preserving face move (M3)
    push_neg at hcc
    obtain ⟨d, hdint⟩ : ∃ d, lo d < g d ∧ g d < hi d := by
      have hne : (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)) ≠ ∅ := by
        intro hempty
        have hcard := Finset.card_eq_zero.mpr hempty
        have heq : interiorCnt lo hi g
            = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card := rfl
        omega
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact ⟨e, (Finset.mem_filter.mp he).2⟩
    have hne2 : hi d ≠ lo d := by linarith
    have hpt : ∀ l, g l = (hi d - g d)/(hi d - lo d) * moveP g d (lo d) l
        + (g d - lo d)/(hi d - lo d) * moveP g d (hi d) l := by
      intro l
      by_cases hl : l = d
      · rw [hl, moveP_self, moveP_self]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          eq_div_iff (sub_ne_zero_of_ne hne2)]
        ring
      · rw [moveP_ne _ _ _ hl, moveP_ne _ _ _ hl]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          eq_div_iff (sub_ne_zero_of_ne hne2)]
        ring
    have hsum : linForm a g = (hi d - g d)/(hi d - lo d) * linForm a (moveP g d (lo d))
        + (g d - lo d)/(hi d - lo d) * linForm a (moveP g d (hi d)) := by
      have hgeq : (fun l => (hi d - g d)/(hi d - lo d) * moveP g d (lo d) l
          + (g d - lo d)/(hi d - lo d) * moveP g d (hi d) l) = g :=
        funext (fun l => (hpt l).symm)
      rw [← linForm_lin_combo a (moveP g d (lo d)) (moveP g d (hi d)), hgeq]
    have hccd : cc d = 0 := hcc d hdint
    have hw₁ : 0 < (hi d - g d)/(hi d - lo d) := div_pos (by linarith) (by linarith)
    have hw₂ : 0 < (g d - lo d)/(hi d - lo d) := div_pos (by linarith) (by linarith)
    have hs' : (hi d - g d)/(hi d - lo d) * linForm a (moveP g d (lo d))
        + (g d - lo d)/(hi d - lo d) * linForm a (moveP g d (hi d)) ≤ 0 := by
      rw [← hsum]; exact hs
    rcases combo_nonpos hw₁ hw₂ hs' with h1 | h2
    · refine Or.inr ⟨moveP g d (lo d), moveP_interior_drop hdint (Or.inl rfl),
        moveP_box hbox ⟨le_refl _, (le_of_lt hdint.1).trans hdint.2.le⟩, h1, ?_⟩
      have hq : linForm cc (moveP g d (lo d)) = linForm cc g + cc d * (lo d - g d) :=
        linForm_moveP cc g d (lo d)
      rw [hq, hccd]
      linarith
    · refine Or.inr ⟨moveP g d (hi d), moveP_interior_drop hdint (Or.inr rfl),
        moveP_box hbox ⟨(le_of_lt hdint.1).trans hdint.2.le, le_refl _⟩, h2, ?_⟩
      have hq : linForm cc (moveP g d (hi d)) = linForm cc g + cc d * (hi d - g d) :=
        linForm_moveP cc g d (hi d)
      rw [hq, hccd]
      linarith

/-- **The walk** (strong form of the half-box coupled-corner principle): a linear
inequality violated at a side point is violated at a side VERTEX — so if every side vertex
satisfies it, so does every side point.  Induction on the interior-coordinate count; the
engine is `walkStep` (every recursive call strictly drops the count). -/
theorem walkVerts (lo hi a cc : Fin 7 → ℝ) : ∀ (N : ℕ) (g : Fin 7 → ℝ),
    interiorCnt lo hi g ≤ N → (∀ l, lo l ≤ g l ∧ g l ≤ hi l) → linForm a g ≤ 0 →
      0 < linForm cc g → ∃ v, SideVertex lo hi a v ∧ linForm cc g ≤ linForm cc v := by
  classical
  intro N
  induction N with
  | zero =>
    intro g hcnt hbox hs hv
    refine ⟨g, Or.inl ⟨fun l => atFace_of_ninterior (hbox l) ?_, hs⟩, le_refl _⟩
    intro hint
    have hsub : (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).Nonempty :=
      ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hint⟩⟩
    have hcard : 1 ≤ (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr hsub)
    have heq : interiorCnt lo hi g
        = (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)).card := rfl
    omega
  | succ N ih =>
    intro g hcnt hbox hs hv
    by_cases h0 : (Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l)) = ∅
    · refine ⟨g, Or.inl ⟨fun l => atFace_of_ninterior (hbox l) ?_, hs⟩, le_refl _⟩
      intro hint
      have hmem : l ∈ Finset.univ.filter (fun l => lo l < g l ∧ g l < hi l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ l, hint⟩
      rw [h0] at hmem
      exact absurd hmem (Finset.notMem_empty l)
    · have hge1 : 1 ≤ interiorCnt lo hi g :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
      rcases walkStep lo hi a cc hbox hs hv hge1 with ⟨v, hvx, hle⟩ | ⟨q, hqcnt, hqbox, hqs, hqle⟩
      · exact ⟨v, hvx, hle⟩
      · have hqN : interiorCnt lo hi q ≤ N := by omega
        have hqviol : 0 < linForm cc q := by linarith
        obtain ⟨v, hvx, hvq⟩ := ih q hqN hqbox hqs hqviol
        exact ⟨v, hvx, le_trans hqle hvq⟩

/-! ### Homogeneous pair inequalities as linear forms -/

/-- The coefficient vector of the homogeneous pair inequality `A * g s ≤ B * g t`. -/
def pairL (s t : Fin 7) (A B : ℝ) : Fin 7 → ℝ :=
  fun l => (if l = s then A else 0) - (if l = t then B else 0)

theorem pairL_eq (s t : Fin 7) (A B : ℝ) (l : Fin 7) :
    pairL s t A B l = (if l = s then A else 0) - (if l = t then B else 0) := rfl

theorem linForm_pairL (s t : Fin 7) (A B : ℝ) (v : Fin 7 → ℝ) :
    linForm (pairL s t A B) v = A * v s - B * v t := by
  have h : ∀ l : Fin 7, (pairL s t A B l) * v l
      = (if l = s then A * v l else 0) - (if l = t then B * v l else 0) := by
    intro l
    unfold pairL
    by_cases h1 : l = s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : l = t
      · rw [if_pos h2, if_pos h2]
        ring
      · rw [if_neg h2, if_neg h2]
        ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : l = t
      · rw [if_pos h2, if_pos h2]
        ring
      · rw [if_neg h2, if_neg h2]
        ring
  unfold linForm
  simp only [h, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' Finset.univ s (fun l => A * v l),
    Finset.sum_ite_eq' Finset.univ t (fun l => B * v l)]
  simp

/-- **The half-box coupled-corner principle** (the extension E846 item 3 names): a
homogeneous pair inequality `A * g s ≤ B * g t` holding on the whole vertex set of the
side region `{g ∈ box : linForm a g ≤ 0}` holds on the whole side region.  This is the
vertex-set semantics of E833's split machinery (the `holds()` test of
`leaves3739_split_v1.py`) with the box replaced by the box-plus-one-plane polytope. -/
theorem pairLe_of_sideVertices (lo hi a : Fin 7 → ℝ) (s t : Fin 7) (A B : ℝ) {g : Fin 7 → ℝ}
    (hbox : ∀ l, lo l ≤ g l ∧ g l ≤ hi l) (hs : linForm a g ≤ 0)
    (hv : ∀ v, SideVertex lo hi a v → A * v s ≤ B * v t) :
    A * g s ≤ B * g t := by
  have hkey : linForm (pairL s t A B) g ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v, hvx, hle⟩ :=
      walkVerts lo hi a (pairL s t A B) 7 g (interiorCnt_le_card lo hi g) hbox hs hcon
    have hv' := hv v hvx
    have hv2 : linForm (pairL s t A B) v = A * v s - B * v t := linForm_pairL s t A B v
    rw [linForm_pairL] at hle hcon
    linarith
  rw [linForm_pairL] at hkey
  linarith

/-! ## The fifth schema: the side-window certificate (E846 item 3's `SideWindowCert`)

The E849 hull-form `SideWindowCert` above assumes its inequalities on the whole region;
E846 measured that the recorded off-plane family does NOT admit that form (0 of 1,018
recorded side certificates extend to their bounding boxes).  The vertex form below carries
the window data as the E833 artifacts do — left end `X = na/ρ_ka`, right end `Y = nb/ρ_kb`,
per-reading laps — with the five inequality families required only on the VERTEX SET of the
half-box (`SideVertex`); `pairLe_of_sideVertices` transfers them to the whole side region.
The `h₃` data of `tail_h3_offplane_dump_v1.jsonl` (X = 25/ρ₅ or 89/ρ₇, Y = 15/ρ₃, laps
(1, 1, 2, 3, 4, 11) over ρ₂..ρ₇) and the 15 discharge lines of `leaves3739_split_v1.out`
are both of this shape. -/

/-- The vertex-form side-window certificate: a dyadic box, one linear side condition
(`linForm a ≤ 0`), and a window `[na/ρ_ka, nb/ρ_kb]` whose five inequality families hold on
the half-box's vertex set. -/
structure SideWindowCertV where
  lo : Fin 7 → ℝ
  hi : Fin 7 → ℝ
  a : Fin 7 → ℝ
  na : ℝ
  ka : Fin 7
  nb : ℝ
  kb : Fin 7
  j : Fin 7 → ℤ
  hp0 : lo 0 = 1 ∧ hi 0 = 1
  hlo : ∀ i, lo i ≤ hi i
  hposka : 0 < lo ka
  hposkb : 0 < lo kb
  hposlo : ∀ i, 0 ≤ lo i
  hv1 : ∀ v, SideVertex lo hi a v → (1 : ℝ) * v ka ≤ na * v 0
  hv2 : ∀ v, SideVertex lo hi a v → na * v kb ≤ nb * v ka
  hv3 : ∀ v, SideVertex lo hi a v → nb * v 0 ≤ 7 * v kb
  hv4 : ∀ v, SideVertex lo hi a v → ∀ i, ((8 * j i + 1 : ℤ) : ℝ) * v ka ≤ na * v i
  hv5 : ∀ v, SideVertex lo hi a v → ∀ i, nb * v i ≤ ((8 * j i + 7 : ℤ) : ℝ) * v kb

/-- A side vertex has `ρ₁ = 1` (the pinned reading: its face is the single point 1, so it
is never the interior coordinate). -/
theorem sideVertex_pinned {lo hi a : Fin 7 → ℝ} {v : Fin 7 → ℝ}
    (hp0 : lo 0 = 1 ∧ hi 0 = 1) (hv : SideVertex lo hi a v) : v 0 = 1 := by
  rcases hv with ⟨hall, -⟩ | ⟨i₀, hrest, hloi, hiii, -⟩
  · rcases hall 0 with h | h
    · rw [h, hp0.1]
    · rw [h, hp0.2]
  · have hni0 : ¬(lo 0 < v 0 ∧ v 0 < hi 0) := by
      rw [hp0.1, hp0.2]
      intro hcon
      linarith
    have hne : i₀ ≠ 0 := by
      intro heq
      rw [heq] at hloi hiii
      exact hni0 ⟨hloi, hiii⟩
    rcases hrest 0 (Ne.symm hne) with h | h
    · rw [h, hp0.1]
    · rw [h, hp0.2]

/-- A side vertex lies on the certified side. -/
theorem sideVertex_side {lo hi a : Fin 7 → ℝ} {v : Fin 7 → ℝ} (hv : SideVertex lo hi a v) :
    linForm a v ≤ 0 := by
  rcases hv with ⟨-, hle⟩ | ⟨-, -, -, -, hz⟩
  · exact hle
  · rw [hz]

/-- A side vertex lies in the box. -/
theorem sideVertex_box {lo hi a : Fin 7 → ℝ} {v : Fin 7 → ℝ}
    (hlo : ∀ i, lo i ≤ hi i) (hv : SideVertex lo hi a v) :
    ∀ l, lo l ≤ v l ∧ v l ≤ hi l := by
  rcases hv with ⟨hall, -⟩ | ⟨i₀, hrest, hloi, hiii, -⟩
  · intro l
    rcases hall l with h | h
    · rw [h]
      exact ⟨le_refl _, hlo l⟩
    · rw [h]
      exact ⟨hlo l, le_refl _⟩
  · intro l
    by_cases hl : l = i₀
    · rw [hl]
      exact ⟨hloi.le, hiii.le⟩
    · rcases hrest l hl with h | h
      · rw [h]
        exact ⟨le_refl _, hlo l⟩
      · rw [h]
        exact ⟨hlo l, le_refl _⟩

/-- **The certified window** of a side-window certificate: at every side point the window
ends satisfy `1 ≤ X(g) ≤ Y(g) ≤ 7` with `X(g) = na/ρ_ka`, `Y(g) = nb/ρ_kb`. -/
theorem sideWindowCertV_window (c : SideWindowCertV) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) (hs : linForm c.a g ≤ 0) :
    (1 : ℝ) ≤ c.na / g c.ka ∧ c.na / g c.ka ≤ c.nb / g c.kb ∧ c.nb / g c.kb ≤ 7 := by
  have hp0 : g 0 = 1 := by
    have h0 := hbox 0
    rw [c.hp0.1, c.hp0.2] at h0
    linarith
  have hka : (0 : ℝ) < g c.ka := lt_of_lt_of_le c.hposka (hbox _).1
  have hkb : (0 : ℝ) < g c.kb := lt_of_lt_of_le c.hposkb (hbox _).1
  have hX1 : (1 : ℝ) * g c.ka ≤ c.na * g 0 :=
    pairLe_of_sideVertices c.lo c.hi c.a c.ka 0 1 c.na hbox hs c.hv1
  have hXY : c.na * g c.kb ≤ c.nb * g c.ka :=
    pairLe_of_sideVertices c.lo c.hi c.a c.kb c.ka c.na c.nb hbox hs c.hv2
  have hY7 : c.nb * g 0 ≤ 7 * g c.kb :=
    pairLe_of_sideVertices c.lo c.hi c.a 0 c.kb c.nb 7 hbox hs c.hv3
  rw [hp0] at hX1 hY7
  exact ⟨(le_div_iff₀ hka).mpr (by linarith), (div_le_div_iff₀ hka hkb).mpr hXY,
    (div_le_iff₀ hkb).mpr (by linarith)⟩

/-- **Soundness, per-reading**: every reading of a side point is clear at the instant
`X(g)/8` with `X(g) = na/ρ_ka` — the whole `[X(g), Y(g)]` window lies in one closed gap of
every reading, so `X(g)/8` is a lonely instant of `W₀`. -/
theorem sideWindowCertV_clear (c : SideWindowCertV) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) (hs : linForm c.a g ≤ 0) :
    ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (c.na / g c.ka / 8)) := by
  obtain ⟨hX1, hXY, hY7⟩ := sideWindowCertV_window c g hbox hs
  have hka : (0 : ℝ) < g c.ka := lt_of_lt_of_le c.hposka (hbox _).1
  have hkb : (0 : ℝ) < g c.kb := lt_of_lt_of_le c.hposkb (hbox _).1
  have hgi : ∀ i, (0 : ℝ) ≤ g i := fun i => le_trans (c.hposlo i) (hbox i).1
  intro i
  have hexiti : ((8 * c.j i + 1 : ℤ) : ℝ) * g c.ka ≤ c.na * g i :=
    pairLe_of_sideVertices c.lo c.hi c.a c.ka i ((8 * c.j i + 1 : ℤ) : ℝ) c.na hbox hs
      (fun v hvx => c.hv4 v hvx i)
  have hentryi : c.nb * g i ≤ ((8 * c.j i + 7 : ℤ) : ℝ) * g c.kb :=
    pairLe_of_sideVertices c.lo c.hi c.a i c.kb c.nb ((8 * c.j i + 7 : ℤ) : ℝ) hbox hs
      (fun v hvx => c.hv5 v hvx i)
  have h1 : ((8 * c.j i : ℤ) : ℝ) + 1 ≤ g i * (c.na / g c.ka) := by
    have hxi := hexiti
    rw [Int.cast_add, Int.cast_one] at hxi
    rw [show g i * (c.na / g c.ka) = c.na * g i / g c.ka from by ring]
    exact (le_div_iff₀ hka).mpr hxi
  have h2 : g i * (c.na / g c.ka) ≤ ((8 * c.j i : ℤ) : ℝ) + 7 := by
    have hxi := hentryi
    rw [Int.cast_add] at hxi
    calc g i * (c.na / g c.ka) ≤ g i * (c.nb / g c.kb) :=
          mul_le_mul_of_nonneg_left hXY (hgi i)
      _ = c.nb * g i / g c.kb := by ring
      _ ≤ ((8 * c.j i : ℤ) : ℝ) + 7 := (div_le_iff₀ hkb).mpr hxi
  rw [clearAt_R_iff (g i) (c.na / g c.ka)]
  exact ⟨c.j i, Set.mem_Icc.mpr ⟨h1, h2⟩⟩

/-- **Soundness of the fifth schema** (`sideWindowCert_noCarve` of E846 item 3): an
arrangement in the box, on the certified side of the plane, does not carve `[1,7]` — the
carve would cover `R = X(g) ∈ [1,7]`, putting a reading in the way inside the certified
window. -/
theorem sideWindowCertV_noCarve (c : SideWindowCertV) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) (hs : linForm c.a g ≤ 0) :
    Fresh.Certs.NoCarve g := by
  intro hcarve
  obtain ⟨hX1, hXY, hY7⟩ := sideWindowCertV_window c g hbox hs
  obtain ⟨ρ, hρmem, k, hz1, hz2⟩ := hcarve (c.na / g c.ka) hX1 (hXY.trans hY7)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz1' : (((8 * k - 1 : ℤ) : ℝ)) < g i * (c.na / g c.ka) := by push_cast; linarith
  have hz2' : g i * (c.na / g c.ka) < (((8 * k + 1 : ℤ) : ℝ)) := by push_cast; linarith
  have hway := inWay_of_zone (ρ := g i) (R := c.na / g c.ka) hz1' hz2'
  have hclear := sideWindowCertV_clear c g hbox hs i
  unfold Fresh.InWay at hway
  linarith

/-! ### The three-region composition -/

/-- **The strict three-region composition** (the composition E846 names): the box splits
into the left open side, the plane, and the right open side; certificates on all three
give `NoCarve` on the whole box. -/
theorem sideRegions_cover (a : Fin 7 → ℝ) (g : Fin 7 → ℝ)
    (hL : linForm a g < 0 → Fresh.Certs.NoCarve g)
    (hP : linForm a g = 0 → Fresh.Certs.NoCarve g)
    (hR : 0 < linForm a g → Fresh.Certs.NoCarve g) :
    Fresh.Certs.NoCarve g := by
  rcases lt_trichotomy (linForm a g) 0 with hlt | heq | hgt
  · exact hL hlt
  · exact hP heq
  · exact hR hgt

/-- The closed-side form: the two CLOSED half-boxes already cover the box (the plane strip
lies in both), so two closed-side certificates suffice — the shape of the 1,018 recorded
h₃-side regions of `tail_h3_offplane_dump_v1.jsonl`. -/
theorem sideRegions_cover_closed (a : Fin 7 → ℝ) (g : Fin 7 → ℝ)
    (hL : linForm a g ≤ 0 → Fresh.Certs.NoCarve g)
    (hR : 0 ≤ linForm a g → Fresh.Certs.NoCarve g) :
    Fresh.Certs.NoCarve g := by
  rcases le_total (linForm a g) 0 with hle | hge
  · exact hL hle
  · exact hR hge

/-- The h₃ plane vector: `25ρ₇ − 89ρ₅` (the exit-exit tangency, `Fresh.Pinch.PlaneH3`). -/
def planeH3vec : Fin 7 → ℝ := fun l => if l = 6 then 25 else if l = 4 then -89 else 0

theorem linForm_planeH3vec (g : Fin 7 → ℝ) : linForm planeH3vec g = 25 * g 6 - 89 * g 4 := by
  have he : planeH3vec = fun l => if l = 6 then (25 : ℝ) else if l = 4 then -89 else 0 := rfl
  rw [he, linForm_two 6 4 25 (-89) g (by decide)]
  ring

/-- **The h₃ straddler composition**: left closed side ∨ on-plane pinch (`Fresh.Pinch.PlaneH3`)
∨ right closed side — the totality shape of E846 for the `[17,23)` straddler boxes. -/
theorem sideRegions_cover_h3 (g : Fin 7 → ℝ)
    (hL : linForm planeH3vec g < 0 → Fresh.Certs.NoCarve g)
    (hP : Fresh.Pinch.PlaneH3 g → Fresh.Certs.NoCarve g)
    (hR : 0 < linForm planeH3vec g → Fresh.Certs.NoCarve g) :
    Fresh.Certs.NoCarve g := by
  refine sideRegions_cover planeH3vec g hL ?_ hR
  intro heq
  rw [linForm_planeH3vec] at heq
  have h3 : (25 : ℝ) * g 6 = 89 * g 4 := by linarith
  exact hP h3

/-! ### The worked line: leaves3739 B1, side `P1 ≥ 0` -/

/-- **The worked line** (line 1 of the 15 in `leaves3739_split_v1.out`, box B1 at D = 32,
side `P1 ≥ 0`): the box ρ₂ ∈ [91/32, 92/32], ρ₃ ∈ [123/32, 124/32], ρ₄ ∈ [157/32, 158/32],
ρ₅ ∈ [202/32, 203/32], ρ₆ ∈ [224/32, 225/32], ρ₇ ∈ [1209/32, 1210/32] cut by
`P1 = 7ρ₅ − 9ρ₄ ≥ 0` (stated here as `9ρ₄ − 7ρ₅ ≤ 0`), with window `X = 9/ρ₅`, `Y = 7/ρ₄`,
laps `(8j+1) = [1, 1, 1, 9, 9, 49]` over ρ₂..ρ₇.  Fourteen of the fifteen inequalities
hold on the WHOLE box; the coupled one (`9ρ₄ ≤ 7ρ₅`) is exactly the side condition — the
vertex set is needed only for it. -/
noncomputable def leaves3739_B1_lo : Fin 7 → ℝ :=
  ![1, 91/32, 123/32, 157/32, 202/32, 224/32, 1209/32]

noncomputable def leaves3739_B1_hi : Fin 7 → ℝ :=
  ![1, 92/32, 124/32, 158/32, 203/32, 225/32, 1210/32]

def leaves3739_B1_j : Fin 7 → ℤ := ![0, 0, 0, 0, 1, 1, 6]

/-- The seven face pairs of B1, as literal per-reading bounds (the Matrix-cons applications
reduce definitionally). -/
theorem leaves3739_B1_box (v : Fin 7 → ℝ)
    (hv : SideVertex leaves3739_B1_lo leaves3739_B1_hi (pairL 3 4 9 7) v) :
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

noncomputable def leaves3739_B1_P1pos : SideWindowCertV :=
  { lo := leaves3739_B1_lo
    hi := leaves3739_B1_hi
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
        norm_num [leaves3739_B1_lo, leaves3739_B1_hi, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    hposka := by
      rw [show leaves3739_B1_lo 4 = (202 / 32 : ℝ) from rfl]
      norm_num
    hposkb := by
      rw [show leaves3739_B1_lo 3 = (157 / 32 : ℝ) from rfl]
      norm_num
    hposlo := by
      intro i
      fin_cases i <;>
        norm_num [leaves3739_B1_lo, Matrix.cons_val_zero, Matrix.cons_val_succ]
    hv1 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨-, -, -, -, -, -, -, hb4hi, -, -, -, -⟩ := leaves3739_B1_box v hvx
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
      obtain ⟨-, -, -, -, hb3lo, -, -, -, -, -, -, -⟩ := leaves3739_B1_box v hvx
      rw [h0]
      linarith
    hv4 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, -, hb2lo, -, hb3lo, -, hb4lo, hb4hi, hb5lo, -, hb6lo, -⟩ :=
        leaves3739_B1_box v hvx
      have j0 : leaves3739_B1_j 0 = 0 := rfl
      have j1 : leaves3739_B1_j 1 = 0 := rfl
      have j2 : leaves3739_B1_j 2 = 0 := rfl
      have j3 : leaves3739_B1_j 3 = 0 := rfl
      have j4 : leaves3739_B1_j 4 = 1 := rfl
      have j5 : leaves3739_B1_j 5 = 1 := rfl
      have j6 : leaves3739_B1_j 6 = 6 := rfl
      intro i
      have hv7 : i.val < 7 := Fin.is_lt i
      by_cases hq0 : i = 0
      · rw [hq0, j0]; norm_num <;> linarith
      by_cases hq1 : i = 1
      · rw [hq1, j1]; norm_num <;> linarith
      by_cases hq2 : i = 2
      · rw [hq2, j2]; norm_num <;> linarith
      by_cases hq3 : i = 3
      · rw [hq3, j3]; norm_num <;> linarith
      by_cases hq4 : i = 4
      · rw [hq4, j4]; norm_num <;> linarith
      by_cases hq5 : i = 5
      · rw [hq5, j5]; norm_num <;> linarith
      by_cases hq6 : i = 6
      · rw [hq6, j6]; norm_num <;> linarith
      · have w0 : i.val ≠ 0 := fun h => hq0 (Fin.val_inj.mp h)
        have w1 : i.val ≠ 1 := fun h => hq1 (Fin.val_inj.mp h)
        have w2 : i.val ≠ 2 := fun h => hq2 (Fin.val_inj.mp h)
        have w3 : i.val ≠ 3 := fun h => hq3 (Fin.val_inj.mp h)
        have w4 : i.val ≠ 4 := fun h => hq4 (Fin.val_inj.mp h)
        have w5 : i.val ≠ 5 := fun h => hq5 (Fin.val_inj.mp h)
        have w6 : i.val ≠ 6 := fun h => hq6 (Fin.val_inj.mp h)
        omega
    hv5 := by
      intro v hvx
      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx
      obtain ⟨hb1lo, hb1hi, hb2lo, hb2hi, hb3lo, -, -, hb4hi, -, hb5hi, -, hb6hi⟩ :=
        leaves3739_B1_box v hvx
      have j0 : leaves3739_B1_j 0 = 0 := rfl
      have j1 : leaves3739_B1_j 1 = 0 := rfl
      have j2 : leaves3739_B1_j 2 = 0 := rfl
      have j3 : leaves3739_B1_j 3 = 0 := rfl
      have j4 : leaves3739_B1_j 4 = 1 := rfl
      have j5 : leaves3739_B1_j 5 = 1 := rfl
      have j6 : leaves3739_B1_j 6 = 6 := rfl
      intro i
      have hv7 : i.val < 7 := Fin.is_lt i
      by_cases hq0 : i = 0
      · rw [hq0, j0]; norm_num <;> linarith
      by_cases hq1 : i = 1
      · rw [hq1, j1]; norm_num <;> linarith
      by_cases hq2 : i = 2
      · rw [hq2, j2]; norm_num <;> linarith
      by_cases hq3 : i = 3
      · rw [hq3, j3]; norm_num <;> linarith
      by_cases hq4 : i = 4
      · rw [hq4, j4]; norm_num <;> linarith
      by_cases hq5 : i = 5
      · rw [hq5, j5]; norm_num <;> linarith
      by_cases hq6 : i = 6
      · rw [hq6, j6]; norm_num <;> linarith
      · have w0 : i.val ≠ 0 := fun h => hq0 (Fin.val_inj.mp h)
        have w1 : i.val ≠ 1 := fun h => hq1 (Fin.val_inj.mp h)
        have w2 : i.val ≠ 2 := fun h => hq2 (Fin.val_inj.mp h)
        have w3 : i.val ≠ 3 := fun h => hq3 (Fin.val_inj.mp h)
        have w4 : i.val ≠ 4 := fun h => hq4 (Fin.val_inj.mp h)
        have w5 : i.val ≠ 5 := fun h => hq5 (Fin.val_inj.mp h)
        have w6 : i.val ≠ 6 := fun h => hq6 (Fin.val_inj.mp h)
        omega }

/-- The worked line discharges B1's `P1 ≥ 0` side: every arrangement in the box with
`9ρ₄ ≤ 7ρ₅` is not a carve of `[1,7]`. -/
theorem leaves3739_B1_P1pos_noCarve (g : Fin 7 → ℝ)
    (hbox : ∀ i, leaves3739_B1_P1pos.lo i ≤ g i ∧ g i ≤ leaves3739_B1_P1pos.hi i)
    (hside : linForm leaves3739_B1_P1pos.a g ≤ 0) :
    Fresh.Certs.NoCarve g :=
  sideWindowCertV_noCarve leaves3739_B1_P1pos g hbox hside

#print axioms planeChord
#print axioms moveP_self
#print axioms moveP_ne
#print axioms linForm_moveP
#print axioms moveP_box
#print axioms moveP_interior_drop
#print axioms interiorCnt_congr
#print axioms exists_interior_ne
#print axioms interiorCnt_le_card
#print axioms combo_nonpos
#print axioms combo_le_max
#print axioms walkStep
#print axioms walkVerts
#print axioms pairL_eq
#print axioms linForm_pairL
#print axioms pairLe_of_sideVertices
#print axioms sideVertex_pinned
#print axioms sideVertex_side
#print axioms sideVertex_box
#print axioms sideWindowCertV_window
#print axioms sideWindowCertV_clear
#print axioms sideWindowCertV_noCarve
#print axioms sideRegions_cover
#print axioms sideRegions_cover_closed
#print axioms linForm_planeH3vec
#print axioms sideRegions_cover_h3
#print axioms leaves3739_B1_P1pos_noCarve

end Fresh.BandNoCarve
