import Fresh.FilterAssembly

/-!
# Composed-cap conflict engine: the E813 product-form extension of `joinEdge_conflict`

Written 2026-11-13.  New file; nothing existing is edited.  This closes the named data gap
from the joinedge dump: the OneSided spine lift cannot consume 65 of 68 one-sided boxes as
`JoinFam` families because their killing caps are COMPOSED (products of a box-end bound and
1-5 seam ratios — E813 item 7 / E814 item 4's form) or face-factor transposes, not raw
`8m±1` edges.

Contents (all PROVED; no OWED):
* `rationalEdge_conflict` — the general-rational one-ratio engine: demand `ρx/ρy < A/B`,
  cap `ρy/ρx ≤ C/D`, datum `A·C ≤ B·D`, positivity ⟹ False, for ANY positive reals
  `A B C D` (hence any positive rationals, which embed canonically).  `JoinFam`'s 8m±1
  engine `Fresh.SpineSound.joinEdge_conflict` is exactly the special case where `A` is an
  `8m₊+1` comb numerator and `B` an `8m₋−1` face denominator etc. — the datum check
  `A·C ≤ B·D` is identical, so the face-factor (2/(2n−1)-style transposes) caps need no new
  engine.
* `ChainReal` / `chain_real_compose` / `composedCap_conflict` — the n-step cap chain
  `ρy/ρz₁ ≤ c₁, ρz₁/ρz₂ ≤ c₂, …, ρzₙ/ρx ≤ cₙ` through the intermediate readings, with the
  composed datum `d·c₁⋯cₙ ≤ 1` (d = A/B, i.e. `A·c₁⋯cₙ ≤ B`) ⟹ False.  The composition
  telescopes through the readings exactly as `joinEdge_conflict` does for n = 1 (each cap
  bounds the ratio of consecutive readings; the product multiplies out against the demand).
  No `8m±1` form anywhere — any positive caps `cᵢ`.
* `ComposedEdge` / `ComposedFam` / `ComposedFamData` / `composedFamRefutes` /
  `composedJoinFam_singleton` — the family data-carrier extension mirroring `JoinFam` /
  `famRefutes` / `joinFam_singleton`: one record per `(x, y, A, B)` word demand, bundling
  its composed cap chain (the demand list and the cap-chain list of the joinedge dump,
  paired per record — the pairing is what the per-arrangement kill consumes), with the
  datum product ≤ 1 as the validity condition.
* Corollaries: `joinEdge_n1_composed` (the raw engine recovered as the n = 1 chain),
  `joinEdge_from_rational` (the raw engine recovered as the rational special case), and
  the banked `c-raw` family of box (1,2,3,4,5,6,8) (`Fresh.SpineTotalData.fam12568`,
  discharged by `spineFamData_12568`) restated as a composed instance with its
  composed-engine kill.

Demand-direction note: `joinEdge_conflict` states the word demand as `ρx/ρy < A/B` with
`d = A/B`; the joinedge dump's "ρx/ρy > d" phrasing is the transpose (`ρy/ρx > B/A`).  All
engines here use the `joinEdge_conflict` convention; the conflict is symmetric under it.
-/

namespace Fresh.JoinFamComposed

open Fresh.FilterAssembly

/-! ## 1. The general-rational one-ratio engine (E813 item 4's datum check, generalized) -/

/-- The general-rational one-ratio conflict: the `W₁` word's edge demands `ρx/ρy < A/B`,
the `W₀` chain caps `ρy/ρx ≤ C/D`, the datum `A·C ≤ B·D` holds, and the readings are
positive — then the pair cannot survive.  This is `Fresh.SpineSound.joinEdge_conflict`
with the integer `8m±1` data replaced by arbitrary positive reals (in particular any
positive rationals, and any face-factor transpose cap): the proof is the same
transposed-cap cross-multiplication, needing no arithmetic form on `A B C D`. -/
theorem rationalEdge_conflict {ρx ρy A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAC : A * C ≤ B * D)
    (hxpos : 0 < ρx) (hypos : 0 < ρy)
    (hdemand : ρx / ρy < A / B) (hcap : ρy / ρx ≤ C / D) : False := by
  have hdem : ρx * B < A * ρy := (div_lt_div_iff₀ hypos hB).mp hdemand
  have hcap' : ρy * D ≤ C * ρx := (div_le_div_iff₀ hxpos hD).mp hcap
  -- multiply the demand by D > 0, shape it, chain through A·(cap), divide by ρx > 0
  have hchain2 : (B * D) * ρx < (A * ρy) * D := by
    have h := mul_lt_mul_of_pos_right hdem hD
    have e3 : (B * D) * ρx = (ρx * B) * D := by ring
    rw [e3]
    exact h
  have hmid : (A * ρy) * D ≤ (A * C) * ρx := by
    have h := mul_le_mul_of_nonneg_left hcap' hA.le
    calc (A * ρy) * D = A * (ρy * D) := by ring
      _ ≤ A * (C * ρx) := h
      _ = (A * C) * ρx := by ring
  have hcombo : (B * D) * ρx < (A * C) * ρx := lt_of_lt_of_le hchain2 hmid
  exact absurd hcombo (not_lt.mpr (mul_le_mul_of_nonneg_right hAC hxpos.le))

#print axioms rationalEdge_conflict

/-- `Fresh.SpineSound.joinEdge_conflict` recovered as the general-rational engine applied
to the `JoinEdge` integer datum: the `8m±1` numerator forms are never used (exactly the
two positivity derivations the original engine performs are reused); only `0 < B`,
`0 < D`, `A·C ≤ B·D` and the realized readings enter. -/
theorem joinEdge_from_rational {e : JoinEdge} {g : Fin 7 → ℝ}
    (hB : 0 < e.B) (hD : 0 < e.D) (hAC : e.A * e.C ≤ e.B * e.D)
    (hxpos : 0 < g e.x) (hypos : 0 < g e.y)
    (hdemand : g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ))
    (hcap : g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)) : False := by
  have hB' : (0 : ℝ) < (e.B : ℝ) := by exact_mod_cast hB
  have hD' : (0 : ℝ) < (e.D : ℝ) := by exact_mod_cast hD
  -- the cap side: C > 0 (from the realized cap and 0 < D)
  have hCDpos : (0 : ℝ) < (e.C : ℝ) / (e.D : ℝ) := lt_of_lt_of_le (div_pos hypos hxpos) hcap
  have hC' : (0 : ℝ) < (e.C : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.C : ℝ) / (e.D : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hD']
      linarith
    exact absurd hCDpos (not_lt.mpr h2)
  -- the demand side: A > 0 (from the realized demand and 0 < B)
  have hABpos : (0 : ℝ) < (e.A : ℝ) / (e.B : ℝ) := lt_trans (div_pos hxpos hypos) hdemand
  have hA' : (0 : ℝ) < (e.A : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.A : ℝ) / (e.B : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hB']
      linarith
    exact absurd hABpos (not_lt.mpr h2)
  exact rationalEdge_conflict hA' hB' hC' hD' (by exact_mod_cast hAC) hxpos hypos hdemand hcap

#print axioms joinEdge_from_rational

/-! ## 2. The n-step composed cap chain through the readings (E813 item 7's product form) -/

/-- A realized cap chain on `g`: the walk `u → z₁ → … → w` through the node/cap list
`(z₁, c₁), …, (zₙ, cₙ)`, where each step's readings realize the cap `ρ_cur / ρ_next ≤ c`
and every reading on the walk is positive.  This is the reading-side bridge of the
composed kill: the caps are ordinary positive reals (the E813 seam ratios), no `8m±1`
form. -/
inductive ChainReal (g : Fin 7 → ℝ) : Fin 7 → List (Fin 7 × ℝ) → Fin 7 → Prop
  | nil (u : Fin 7) (hupos : 0 < g u) : ChainReal g u [] u
  | cons (u v : Fin 7) (c : ℝ) (l : List (Fin 7 × ℝ)) (w : Fin 7)
      (hcap : g u / g v ≤ c) (hupos : 0 < g u) (hvpos : 0 < g v)
      (hrest : ChainReal g v l w) : ChainReal g u ((v, c) :: l) w

/-- The chain composition: a realized chain from `u` to `w` gives positive endpoint
readings, a positive cap product, and the telescoped bound
`ρu/ρw ≤ c₁·c₂⋯cₙ` — each step's cap multiplies through the actual readings
(`ρu/ρw = (ρu/ρz₁)·(ρz₁/ρw)`).  This is the n-step generalization of the
transitivity-through-readings chain inside `joinEdge_conflict`. -/
theorem chain_real_compose {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : ChainReal g u caps w) :
    0 < g u ∧ 0 < g w ∧ 0 < (caps.map Prod.snd).prod ∧
      g u / g w ≤ (caps.map Prod.snd).prod := by
  induction h with
  | nil u hupos =>
      refine ⟨hupos, hupos, by norm_num [List.map_nil, List.prod_nil], ?_⟩
      have h1 : (([] : List (Fin 7 × ℝ)).map Prod.snd).prod = 1 := by simp
      rw [h1, div_self (ne_of_gt hupos)]
  | cons u v c l w hcap hupos hvpos hrest ih =>
      obtain ⟨hv, hw, hprod, hcapchain⟩ := ih
      have huvpos : (0 : ℝ) < g u / g v := div_pos hupos hvpos
      have hcpos : (0 : ℝ) < c := lt_of_lt_of_le huvpos hcap
      refine ⟨hupos, hw, ?_, ?_⟩
      · have hmap : (((v, c) :: l).map Prod.snd).prod = c * (l.map Prod.snd).prod := by simp
        rw [hmap]
        exact mul_pos hcpos hprod
      · have key : g u / g w = g u / g v * (g v / g w) := by field_simp
        rw [key, List.map_cons, List.prod_cons]
        exact mul_le_mul hcap hcapchain (div_pos hvpos hw).le hcpos.le

#print axioms chain_real_compose

/-- **The composed-cap conflict** (E813 item 7's product form at the per-arrangement
level): the word demands `ρx/ρy < d = A/B` (the transpose of the dump's `ρx/ρy > B/A`
phrasing), the box + join gives a CHAIN of caps `ρy/ρz₁ ≤ c₁, ρz₁/ρz₂ ≤ c₂, …, ρzₙ/ρx ≤ cₙ`
realized through the intermediate readings, and the composed datum
`d · c₁ · c₂ ⋯ cₙ ≤ 1` holds (i.e. `A·c₁⋯cₙ ≤ B`) — then False.  Proof: the chain
telescopes to `ρy/ρx ≤ c₁⋯cₙ` (`chain_real_compose`), and the one-ratio engine
(`rationalEdge_conflict`, `C = c₁⋯cₙ`, `D = 1`) closes exactly as `joinEdge_conflict` does
for n = 1.  The composition needs no `8m±1` form — any positive rationals `cᵢ`. -/
theorem composedCap_conflict {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (hreal : ChainReal g u caps w)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hdemand : g w / g u < A / B)
    (hdatum : A * (caps.map Prod.snd).prod ≤ B) : False := by
  obtain ⟨hu, hw, hprod, hcapc⟩ := chain_real_compose hreal
  refine rationalEdge_conflict (D := 1) hA hB hprod (by norm_num) ?_ hw hu hdemand ?_
  · rw [mul_one]
    exact hdatum
  · rw [div_one]
    exact hcapc

#print axioms composedCap_conflict

/-- The raw `8m±1` engine recovered as the n = 1 case of the composed engine: the single
cap `ρy/ρx ≤ C/D` is the one-step chain `y → x` with cap `C/D`, and the datum
`A·C ≤ B·D` is `A·(C/D) ≤ B`.  Same hypotheses as `Fresh.SpineSound.joinEdge_conflict`. -/
theorem joinEdge_n1_composed {e : JoinEdge} {g : Fin 7 → ℝ}
    (hB : 0 < e.B) (hD : 0 < e.D) (hAC : e.A * e.C ≤ e.B * e.D)
    (hxpos : 0 < g e.x) (hypos : 0 < g e.y)
    (hdemand : g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ))
    (hcap : g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)) : False := by
  have hB' : (0 : ℝ) < (e.B : ℝ) := by exact_mod_cast hB
  have hD' : (0 : ℝ) < (e.D : ℝ) := by exact_mod_cast hD
  have hABpos : (0 : ℝ) < (e.A : ℝ) / (e.B : ℝ) := lt_trans (div_pos hxpos hypos) hdemand
  have hA' : (0 : ℝ) < (e.A : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.A : ℝ) / (e.B : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hB']
      linarith
    exact absurd hABpos (not_lt.mpr h2)
  refine composedCap_conflict
    (ChainReal.cons e.y e.x ((e.C : ℝ) / (e.D : ℝ)) [] e.x hcap hypos hxpos
      (ChainReal.nil e.x hxpos)) hA' hB' hdemand ?_
  have hAC' : (e.A : ℝ) * (e.C : ℝ) ≤ (e.B : ℝ) * (e.D : ℝ) := by exact_mod_cast hAC
  have h1 : (e.A : ℝ) * ((e.C : ℝ) / (e.D : ℝ)) ≤ (e.B : ℝ) * ((e.D : ℝ) / (e.D : ℝ)) := by
    have hDinv : (0 : ℝ) ≤ 1 / (e.D : ℝ) := le_of_lt (div_pos (by norm_num) hD')
    calc (e.A : ℝ) * ((e.C : ℝ) / (e.D : ℝ))
        = (e.A : ℝ) * (e.C : ℝ) * (1 / (e.D : ℝ)) := by ring
      _ ≤ (e.B : ℝ) * (e.D : ℝ) * (1 / (e.D : ℝ)) := mul_le_mul_of_nonneg_right hAC' hDinv
      _ = (e.B : ℝ) * ((e.D : ℝ) / (e.D : ℝ)) := by ring
  rw [div_self (ne_of_gt hD'), mul_one] at h1
  rw [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  exact h1

#print axioms joinEdge_n1_composed

/-! ## 3. The family data-carrier extension (mirrors `JoinFam` / `famRefutes`) -/

/-- One composed record: the `(x, y, A, B)` word demand bundled with ITS composed cap
chain — the caps walk `y → z₁ → … → x` through the node/cap list `(z₁, c₁), …, (zₙ, cₙ)`
(the E813 box-end bound + seam-ratio products).  The joinedge dump's "list of
`(x, y, A, B)` demands + list of composed cap chains" is carried as this record list: the
demand-chain pairing is what the per-arrangement kill consumes. -/
structure ComposedEdge where
  x : Fin 7
  y : Fin 7
  A : ℤ
  B : ℤ
  caps : List (Fin 7 × ℝ)

/-- The walk end of a cap chain started at `y` (the datum-level endpoint check). -/
noncomputable def chainEnd (y : Fin 7) (caps : List (Fin 7 × ℝ)) : Fin 7 :=
  caps.foldl (fun _ p => p.1) y

/-- Datum-level validity of one composed record: positive demand numerator/denominator,
positive caps, the chain runs from `y` to `x`, and the composed datum
`A·c₁⋯cₙ ≤ B` (`d·∏c ≤ 1`).  Note: NO `8m±1` numerator condition — that is exactly what
the composed extension drops (E813 item 7: composed caps are not raw `8m±1` edges). -/
-- STANDING: DEFINITION
def ComposedEdgeValid (e : ComposedEdge) : Prop :=
  0 < e.A ∧ 0 < e.B ∧ (∀ p ∈ e.caps, 0 < p.2) ∧ chainEnd e.y e.caps = e.x ∧
    (e.A : ℝ) * (e.caps.map Prod.snd).prod ≤ (e.B : ℝ)

/-- The composed family carrier: the list of composed records (each demand with its
chain). -/
structure ComposedFam where
  edges : List ComposedEdge

/-- The family validity datum (mirrors `JoinFam`'s datum role): every record in the
family satisfies the composed datum conditions. -/
-- STANDING: DEFINITION
def ComposedFamData (f : ComposedFam) : Prop := ∀ e ∈ f.edges, ComposedEdgeValid e

/-- Realization of a composed record on the readings `g`: positive readings at the demand
endpoints, the word demand realized, and the composed cap chain realized through the
intermediate readings (`ChainReal`).  Mirrors `EdgeRealized`. -/
-- STANDING: DEFINITION
def ComposedEdgeRealized (g : Fin 7 → ℝ) (e : ComposedEdge) : Prop :=
  0 < g e.x ∧ 0 < g e.y ∧ g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ) ∧
    ChainReal g e.y e.caps e.x

/-- The composed family lift (mirrors `famRefutes`): if the composed family is valid
(`ComposedFamData`) and some record is realized on `g`, the pair `(W₁ word, W₀ chain)`
does not survive.  The family's endpoint/cap-positivity data are carried but unused in
the refutation (the realization's `ChainReal` carries the semantic content), exactly as
`famRefutes` leaves `JoinFam`'s `8m±1` fields unused. -/
theorem composedFamRefutes {f : ComposedFam} (hfam : ComposedFamData f) {g : Fin 7 → ℝ}
    (hreal : ∃ e ∈ f.edges, ComposedEdgeRealized g e) : False := by
  obtain ⟨e, he, hxpos, hypos, hdemand, hchain⟩ := hreal
  obtain ⟨hA, hB, -, -, hdatum⟩ := hfam e he
  exact composedCap_conflict hchain (by exact_mod_cast hA) (by exact_mod_cast hB) hdemand
    hdatum

#print axioms composedFamRefutes

/-- The composed family is valid for a SINGLETON record exactly when the record's datum
satisfies the composed conditions (positivity of the demand data and the caps, the chain
endpoints, and the composed datum product `A·∏c ≤ B`) — mirroring
`Fresh.SpineSound.joinFam_singleton`. -/
theorem composedJoinFam_singleton (x y : Fin 7) (A B : ℤ) (caps : List (Fin 7 × ℝ))
    (hA : 0 < A) (hB : 0 < B) (hcappos : ∀ p ∈ caps, 0 < p.2)
    (hend : chainEnd y caps = x)
    (hdatum : (A : ℝ) * (caps.map Prod.snd).prod ≤ B) :
    ComposedFamData ⟨[⟨x, y, A, B, caps⟩]⟩ := by
  intro e he
  rcases List.mem_singleton.mp he with rfl
  exact ⟨hA, hB, hcappos, hend, hdatum⟩

#print axioms composedJoinFam_singleton

/-! ## 4. The banked `c-raw` family of box (1,2,3,4,5,6,8) as composed instances

`Fresh.SpineTotalData.fam12568 = {⟨1, 5, 25, 63, 17, 7⟩, ⟨1, 5, 25, 63, 41, 17⟩}`
(discharged by `spineFamData_12568`): word-edge readings (2,6) — demand `ρ₂/ρ₆ < 25/63`
(index `x = 1`, `y = 5`) — against the chain caps `ρ₆/ρ₂ ≤ 17/7` and `ρ₆/ρ₂ ≤ 41/17`.
Restated as composed records: each raw cap is the singleton chain from `y = 5` to `x = 1`
with cap `C/D`, and the composed datum is the same conflict product
(`25·17 = 425 ≤ 441 = 63·7`; `25·41 = 1025 ≤ 1071 = 63·17`). -/

/-- The banked `c-raw` family of box (1,2,3,4,5,6,8) restated as composed records. -/
noncomputable def compFam12568 : ComposedFam :=
  ⟨[⟨1, 5, 25, 63, [(1, 17 / 7)]⟩, ⟨1, 5, 25, 63, [(1, 41 / 17)]⟩]⟩

/-- The composed-family validity datum for the banked `c-raw` family of box
(1,2,3,4,5,6,8) — the composed restatement of `Fresh.SpineTotalData.spineFamData_12568`'s
`JoinFam` discharge (conflicts `25·17 = 425 ≤ 441 = 63·7`, `25·41 = 1025 ≤ 1071 =
63·17`). -/
theorem composedFamData_12568 : ComposedFamData compFam12568 := by
  intro e he
  simp only [compFam12568, List.mem_cons] at he
  rcases he with rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp
      simp at hp
      subst hp
      norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp
      simp at hp
      subst hp
      norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms composedFamData_12568

/-- The composed-engine kill of box (1,2,3,4,5,6,8)'s top `c-raw` datum (singleton chain;
the same hypotheses as `Fresh.SpineSound.refute_box_12568`): demand `ρ₂/ρ₆ < 25/63`
against the cap `ρ₆/ρ₂ ≤ 17/7`, conflict `25·17 = 425 ≤ 441 = 63·7`. -/
theorem composedRefute_box_12568 {g : Fin 7 → ℝ}
    (hxpos : 0 < g 1) (hypos : 0 < g 5)
    (hdemand : g 1 / (g 5) < (25 : ℝ) / 63) (hcap : g 5 / (g 1) ≤ (17 : ℝ) / 7) : False :=
  composedCap_conflict
    (ChainReal.cons 5 1 (17 / 7) [] 1 hcap hypos hxpos (ChainReal.nil 1 hxpos))
    (by norm_num) (by norm_num) hdemand
    (by norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one])

#print axioms composedRefute_box_12568

/-- The same kill lifted through the family carrier (`composedFamRefutes` on
`compFam12568` with `composedFamData_12568`): the family-level composed mirror of
`Fresh.SpineSound.refute_box_12568`. -/
theorem composedRefute_box_12568_fam {g : Fin 7 → ℝ}
    (hxpos : 0 < g 1) (hypos : 0 < g 5)
    (hdemand : g 1 / (g 5) < (25 : ℝ) / 63) (hcap : g 5 / (g 1) ≤ (17 : ℝ) / 7) : False := by
  refine composedFamRefutes composedFamData_12568
    ⟨⟨1, 5, 25, 63, [(1, 17 / 7)]⟩, ?_, hxpos, hypos, hdemand, ?_⟩
  · simp [compFam12568]
  · exact ChainReal.cons 5 1 (17 / 7) [] 1 hcap hypos hxpos (ChainReal.nil 1 hxpos)

#print axioms composedRefute_box_12568_fam

end Fresh.JoinFamComposed
