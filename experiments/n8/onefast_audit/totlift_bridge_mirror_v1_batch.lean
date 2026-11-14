import Mathlib

/-!
## BRIDGE MIRROR (artifact: totlift_bridge_mirror_v1[_batch].lean, built by
totlift_mirror_v1.py)

Standalone-Mathlib mirror of Fresh/TotalityLifts.lean's one-sided sections (the
compfam_bridge_mirror.lean pattern, batched).  Per batch: the banked Fresh bodies pasted
VERBATIM -- `import Fresh.*` lines stripped, the declarations UNUSED by the one-sided
template dropped (each dropped theorem is ./check.sh-verified inside its own Fresh file),
every namespace the pasted bodies open present in the mirror -- plus the batch's compFam
record blocks VERBATIM from Fresh/ComposedFamData.lean with a BATCH-LOCAL coveredSet /
compFamOf / oneSidedTotalData regenerated over exactly those boxes (the real 68-element
versions are verbatim in Fresh/ComposedFamData.lean; their 68-deep membership walks are
./check.sh-verified).  The Fresh.TotalityLifts body at the end is totlift_gen_v1.py
--mirror's output (the one-sided sections + retargetings + totals of
Fresh/TotalityLifts.lean verbatim, at the batch's coveredSet).  The D-variants
(Fresh.DumpDomData) and the 5 pairwise instances (Fresh.SpineTotalData) are NOT mirrored --
they add no new wiring and are ./check.sh-verified.  The #print axioms outputs of the
mirrored theorems apply verbatim to the real file.  The bridge's `lake env lean` search
path lacks LonelyRunnerFresh/build, hence the mirror (gate on verified/return_code, never
`success`).
-/


namespace Fresh

noncomputable def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

end Fresh



namespace Fresh.FilterAssembly

noncomputable def FaceLo (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2

noncomputable def FaceHi (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((2 * n i + 1 : ℤ) : ℝ) / 2

/-- A raw-edge conflict datum (verbatim from Fresh/FilterAssembly.lean). -/
structure JoinEdge where
  x : Fin 7
  y : Fin 7
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
deriving DecidableEq

/-- The covering hypothesis's range check (verbatim). -/
def InRange17 (n : Fin 7 → ℤ) : Prop := ∀ i, 1 ≤ n i ∧ n i ≤ 17

instance (n : Fin 7 → ℤ) : Decidable (InRange17 n) := Fintype.decidableForallFintype

end Fresh.FilterAssembly



namespace Fresh.FrontierFamilyCap

/-- A carve of `[1,7]` (verbatim from Fresh/FrontierFamilyCap.lean). -/
def CarvesOneSeven (rs : Finset ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R ≤ 7 → ∃ ρ ∈ rs, ∃ j : ℤ,
    ((j : ℝ)) * 8 - 1 < ρ * R ∧ ρ * R < ((j : ℝ)) * 8 + 1

end Fresh.FrontierFamilyCap



namespace Fresh.SpineSound

open Fresh.FilterAssembly

/-- The box faces are positive (verbatim from Fresh/SpineSound.lean). -/
theorem faceLo_pos (n : Fin 7 → ℤ) (i : Fin 7) : 0 < FaceLo n i := by
  unfold FaceLo
  have h3 : (0 : ℤ) < max (2 * n i - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  exact div_pos (by exact_mod_cast h3) (by norm_num : (0 : ℝ) < 2)

/-- Every arrangement in a box has positive readings (verbatim). -/
theorem face_pos {n : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) (i : Fin 7) : 0 < g i :=
  lt_of_lt_of_le (faceLo_pos n i) (hface i).1

end Fresh.SpineSound



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



end Fresh.JoinFamComposed



namespace Fresh.OneSidedComposed

open Fresh.JoinFamComposed

/-- Box (1, 4, 5, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 68 of the box's 4489 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 4489).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 6, 6, 8), (4,1,49/15←J cap 26950/135501); (4,2,49/39←J cap 1010625/1400177); (4,2,49/47←J cap 1010625/1400177); (4,2,49/55←J cap 1010625/1400177). -/
noncomputable def compFam_1_4_5_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨3, 0, 49, 15, [(3, (26950 / 135501))]⟩,
    ⟨3, 1, 49, 39, [(3, (1010625 / 1400177))]⟩,
    ⟨3, 1, 49, 47, [(3, (1010625 / 1400177))]⟩,
    ⟨3, 1, 49, 55, [(3, (1010625 / 1400177))]⟩
  ]⟩

theorem compFamData_1_4_5_5_6_6_8 : ComposedFamData compFam_1_4_5_5_6_6_8 := by
  intro e he
  simp only [compFam_1_4_5_5_6_6_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_5_6_6_8

/-- Box (1, 4, 5, 5, 6, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 64 of the box's 2889 word deaths; the box's honest residual is 7 derived-only deaths (chain-side coverable total: 2882).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 6, 7, 7), (3,1,49/15←J cap 311542/1420575); (3,2,49/47←J cap 155771/170469); (3,2,49/55←J cap 155771/170469); (3,2,7/9←J cap 155771/170469). -/
noncomputable def compFam_1_4_5_5_6_7_7 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (311542 / 1420575))]⟩,
    ⟨2, 1, 49, 47, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 49, 55, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 7, 9, [(2, (155771 / 170469))]⟩
  ]⟩

theorem compFamData_1_4_5_5_6_7_7 : ComposedFamData compFam_1_4_5_5_6_7_7 := by
  intro e he
  simp only [compFam_1_4_5_5_6_7_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_5_6_7_7

/-- Box (1, 4, 5, 5, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 2444 of the box's 178093 word deaths; the box's honest residual is 7252 derived-only deaths (chain-side coverable total: 170841).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 6, 7, 8), (7,5,1/1←J cap 187/235); (6,1,73/15←J cap 2/13); (6,2,73/47←J cap 935/1457); (6,2,73/55←J cap 935/1457). -/
noncomputable def compFam_1_4_5_5_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 4, 1, 1, [(6, (187 / 235))]⟩,
    ⟨5, 0, 73, 15, [(5, (2 / 13))]⟩,
    ⟨5, 1, 73, 47, [(5, (935 / 1457))]⟩,
    ⟨5, 1, 73, 55, [(5, (935 / 1457))]⟩
  ]⟩

theorem compFamData_1_4_5_5_6_7_8 : ComposedFamData compFam_1_4_5_5_6_7_8 := by
  intro e he
  simp only [compFam_1_4_5_5_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_5_6_7_8

/-- Box (1, 4, 5, 6, 6, 7, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 12 of the box's 429 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 429).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 6, 6, 7, 9), (6,1,13/3←J cap 34/235); (6,2,5/3←J cap 833/1457); (6,2,65/47←J cap 833/1457); (6,2,13/11←J cap 833/1457). -/
noncomputable def compFam_1_4_5_6_6_7_9 : ComposedFam :=
  ⟨[
    ⟨5, 0, 13, 3, [(5, (34 / 235))]⟩,
    ⟨5, 1, 5, 3, [(5, (833 / 1457))]⟩,
    ⟨5, 1, 65, 47, [(5, (833 / 1457))]⟩,
    ⟨5, 1, 13, 11, [(5, (833 / 1457))]⟩
  ]⟩

theorem compFamData_1_4_5_6_6_7_9 : ComposedFamData compFam_1_4_5_6_6_7_9 := by
  intro e he
  simp only [compFam_1_4_5_6_6_7_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_6_6_7_9

/-- Box (1, 4, 5, 6, 6, 7, 11): the top-8 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 8 records account for 40 of the box's 626 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 626).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 6, 6, 7, 11), (6,1,13/3←J cap 1/7); (6,2,5/3←J cap 50881/89817); (6,2,65/47←J cap 50881/89817); (6,2,13/11←J cap 50881/89817); (6,2,65/63←J cap 50881/89817); (6,3,65/47←J cap 33825/47089); (6,3,13/11←J cap 33825/47089); (6,3,65/63←J cap 33825/47089). -/
noncomputable def compFam_1_4_5_6_6_7_11 : ComposedFam :=
  ⟨[
    ⟨5, 0, 13, 3, [(5, (1 / 7))]⟩,
    ⟨5, 1, 5, 3, [(5, (50881 / 89817))]⟩,
    ⟨5, 1, 65, 47, [(5, (50881 / 89817))]⟩,
    ⟨5, 1, 13, 11, [(5, (50881 / 89817))]⟩,
    ⟨5, 1, 65, 63, [(5, (50881 / 89817))]⟩,
    ⟨5, 2, 65, 47, [(5, (33825 / 47089))]⟩,
    ⟨5, 2, 13, 11, [(5, (33825 / 47089))]⟩,
    ⟨5, 2, 65, 63, [(5, (33825 / 47089))]⟩
  ]⟩

theorem compFamData_1_4_5_6_6_7_11 : ComposedFamData compFam_1_4_5_6_6_7_11 := by
  intro e he
  simp only [compFam_1_4_5_6_6_7_11, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_6_6_7_11

/-- Box (1, 4, 5, 6, 7, 8, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 68 of the box's 2284 word deaths; the box's honest residual is 2 derived-only deaths (chain-side coverable total: 2282).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 6, 7, 8, 8), (3,1,49/15←J cap 6930/33511); (3,2,49/39←J cap 24255/33511); (3,2,49/47←J cap 24255/33511); (3,2,49/55←J cap 24255/33511). -/
noncomputable def compFam_1_4_5_6_7_8_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (6930 / 33511))]⟩,
    ⟨2, 1, 49, 39, [(2, (24255 / 33511))]⟩,
    ⟨2, 1, 49, 47, [(2, (24255 / 33511))]⟩,
    ⟨2, 1, 49, 55, [(2, (24255 / 33511))]⟩
  ]⟩

theorem compFamData_1_4_5_6_7_8_8 : ComposedFamData compFam_1_4_5_6_7_8_8 := by
  intro e he
  simp only [compFam_1_4_5_6_7_8_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_6_7_8_8

/-- Box (1, 4, 5, 6, 7, 8, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 156 of the box's 5234 word deaths; the box's honest residual is 4 derived-only deaths (chain-side coverable total: 5230).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 6, 7, 8, 9), (3,1,49/15←J cap 2450/12121); (3,2,49/39←J cap 24255/33511); (3,2,49/47←J cap 24255/33511); (3,2,49/55←J cap 24255/33511). -/
noncomputable def compFam_1_4_5_6_7_8_9 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (2450 / 12121))]⟩,
    ⟨2, 1, 49, 39, [(2, (24255 / 33511))]⟩,
    ⟨2, 1, 49, 47, [(2, (24255 / 33511))]⟩,
    ⟨2, 1, 49, 55, [(2, (24255 / 33511))]⟩
  ]⟩

theorem compFamData_1_4_5_6_7_8_9 : ComposedFamData compFam_1_4_5_6_7_8_9 := by
  intro e he
  simp only [compFam_1_4_5_6_7_8_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_4_5_6_7_8_9

/-- Box (1, 5, 5, 6, 7, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 142 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 142).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 5, 5, 6, 7, 7, 8), (3,1,49/15←J cap 18326/94705); (3,2,49/47←J cap 155771/170469); (3,2,49/55←J cap 155771/170469); (3,2,7/9←J cap 155771/170469). -/
noncomputable def compFam_1_5_5_6_7_7_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (18326 / 94705))]⟩,
    ⟨2, 1, 49, 47, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 49, 55, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 7, 9, [(2, (155771 / 170469))]⟩
  ]⟩

theorem compFamData_1_5_5_6_7_7_8 : ComposedFamData compFam_1_5_5_6_7_7_8 := by
  intro e he
  simp only [compFam_1_5_5_6_7_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · refine ⟨by norm_num, by norm_num, ?_, by simp [chainEnd], ?_⟩
    · intro p hp; simp at hp; subst hp; norm_num
    · norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
  · exact absurd h0 (by simp)

#print axioms compFamData_1_5_5_6_7_7_8

/-- batch-local coveredSet: the 8 boxes of this bridge batch. -/
def coveredSet : Finset (Fin 7 → ℤ) :=
  {![1, 4, 5, 5, 6, 6, 8],
   ![1, 4, 5, 5, 6, 7, 7],
   ![1, 4, 5, 5, 6, 7, 8],
   ![1, 4, 5, 6, 6, 7, 9],
   ![1, 4, 5, 6, 6, 7, 11],
   ![1, 4, 5, 6, 7, 8, 8],
   ![1, 4, 5, 6, 7, 8, 9],
   ![1, 5, 5, 6, 7, 7, 8]}

/-- batch-local `compFamOf` dispatch (the real 68-branch dispatch is verbatim in
Fresh/ComposedFamData.lean). -/
noncomputable def compFamOf (b : Fin 7 → ℤ) : ComposedFam :=
  if b = (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_4_5_5_6_6_8
  else if b = (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) then compFam_1_4_5_5_6_7_7
  else if b = (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_4_5_5_6_7_8
  else if b = (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) then compFam_1_4_5_6_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) then compFam_1_4_5_6_6_7_11
  else if b = (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then compFam_1_4_5_6_7_8_8
  else if b = (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) then compFam_1_4_5_6_7_8_9
  else if b = (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) then compFam_1_5_5_6_7_7_8
  else ⟨[]⟩

/-- batch-local `oneSidedTotalData` (the real [T 68/68] theorem is verbatim in
Fresh/ComposedFamData.lean; same proof shape over the batch's boxes). -/
theorem oneSidedTotalData : ∀ b ∈ coveredSet, ComposedFamData (compFamOf b) := by
  intro b hb
  simp only [coveredSet, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [compFamOf, compFamData_1_4_5_5_6_6_8]
  · simp [compFamOf, compFamData_1_4_5_5_6_7_7]
  · simp [compFamOf, compFamData_1_4_5_5_6_7_8]
  · simp [compFamOf, compFamData_1_4_5_6_6_7_9]
  · simp [compFamOf, compFamData_1_4_5_6_6_7_11]
  · simp [compFamOf, compFamData_1_4_5_6_7_8_8]
  · simp [compFamOf, compFamData_1_4_5_6_7_8_9]
  · simp [compFamOf, compFamData_1_5_5_6_7_7_8]

#print axioms oneSidedTotalData

end Fresh.OneSidedComposed



namespace Fresh.OneSidedGlue

open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedComposed
open Fresh.FrontierFamilyCap

/-! ## 1. The bridge: composed chains realized on the readings -/

/-- **The W₀-chain-conditional bridge** (STANDING: DEFINITION): the composed cap chains of
the family `f` are realized on the readings `g` — for every record, `ChainReal g e.y e.caps
e.x`.  Per the dump semantics the banked records' chains carry the transposed-pair J-side
caps (implied by every W₀ chain's closed table; the box-side caps hold on the whole box), so
this is the one-sided hypothesis at the pieces' level: implied by `g` admitting a W₀ chain,
vacuous on chainless arrangements, and not an interval statement — exactly the form the
`Fresh.SpineTotalData` no-go lemmas forbid deriving from the box interval, which is why it
enters as a hypothesis and not as a consequence of `FaceLo`/`FaceHi`. -/
-- STANDING: DEFINITION
def capChainsRealized (g : Fin 7 → ℝ) (f : ComposedFam) : Prop :=
  ∀ e ∈ f.edges, ChainReal g e.y e.caps e.x



/-! ## 2. The per-record kill through the banked data -/

/-- **The per-record kill**: family datum valid (`ComposedFamData`), the family's chains
realized on `g` (the bridge), and one record's word demand realized on `g` (positivity +
`ρ_x/ρ_y < A/B`) — then the pair cannot survive (`composedFamRefutes` closes through
`composedCap_conflict`). -/
theorem composedEdge_kill {f : ComposedFam} (hdata : ComposedFamData f)
    {g : Fin 7 → ℝ} (hchains : capChainsRealized g f)
    {e : ComposedEdge} (he : e ∈ f.edges)
    (hxpos : 0 < g e.x) (hypos : 0 < g e.y)
    (hdemand : g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ)) : False :=
  composedFamRefutes hdata ⟨e, he, hxpos, hypos, hdemand, hchains e he⟩

#print axioms composedEdge_kill


/-! ## 3. The banked-data kills on a covered box -/



/-! ## 4. The composed totality OWED and THE GLUE -/

/-- **OWED — the composed one-sided totality** (data-side; the census word-cover side,
`Fresh.SpineTotalData` §5 direction (b) in composed form — the artifact law behind
`j2_cycle_v6/v10.out`'s `no-raw-kill pairs 0` lifted over the real box through the W₁ word
cover of `[9,15]`): for an arrangement in the box whose chains are realized (the
W₀-chain-conditional) and which carves `[1,7]` but admits no W₁ clear point, some record's
word demand is realized on `g`.  (Mirrors `Fresh.SpineSound.SpineTotalOneSided`, with the
family the banked `compFamOf b` and the chain side the composed bridge.) -/
-- STANDING: OWED
def ComposedTotalOneSided (b : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) →
    capChainsRealized g f →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
    ∃ e ∈ f.edges, 0 < g e.x ∧ 0 < g e.y ∧ g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ)

/-- **THE GLUE — `oneSidedSound_of_composedData`**: for a covered box `b`, the banked data
(`oneSidedTotalData b hb` — no longer a hypothesis) + the composed totality datum + the
W₀-chain-conditional bridge (`capChainsRealized`) give `Fresh.FilterAssembly.OneSidedSound`'s
exact conclusion shape: an arrangement `g` in the box that carves `[1,7]` admits a W₁ clear
point over its faces.  Proof: if not, the totality datum realizes some record's demand;
that record dies against its banked datum (`composedEdge_kill`).  This mirrors
`Fresh.SpineSound.oneSidedSound_at` with `JoinFam` replaced by the banked `ComposedFamData`
and the raw-cap conditional replaced by the composed bridge. -/
theorem oneSidedSound_of_composedData (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (htotal : ComposedTotalOneSided b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨e, he, hxpos, hypos, hdem⟩ := htotal g hface hchains hcarve hnoc
  exact composedEdge_kill (oneSidedTotalData b hb) hchains he hxpos hypos hdem

#print axioms oneSidedSound_of_composedData



end Fresh.OneSidedGlue



namespace Fresh.WordCoverSide

open Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
open Fresh.FilterAssembly Fresh.FrontierFamilyCap

/-! ## 1. The zone vocabulary and the W₁ word -/

/-- A reading `ρ = g u` at comb level `j` covers `R` when `8j−1 < ρR < 8j+1` — the zone
form of `Fresh.FrontierFamilyCap.CarvesOneSeven` (with `j : ℕ`; `W₁` zones have `j ≥ 1`). -/
-- STANDING: DEFINITION
def inZone (g : Fin 7 → ℝ) (u : Fin 7) (j : ℕ) (R : ℝ) : Prop :=
  ((j : ℝ) * 8 - 1 < g u * R ∧ g u * R < (j : ℝ) * 8 + 1)

/-- Two entries are ADJACENT in the word: consecutive members of the list
(`w = l₁ ++ p :: q :: l₂`). -/
-- STANDING: DEFINITION
def HasAdj (w : List (Fin 7 × ℕ)) (p q : Fin 7 × ℕ) : Prop :=
  ∃ l₁ l₂ : List (Fin 7 × ℕ), w = l₁ ++ p :: q :: l₂

/-- **A `W₁` word realized on `g`**: a monotone zone chain of `g`'s readings covering
`[9,15]` — (i) the word's readings are positive and its levels `≥ 1` (the `W₁` window's
comb levels), (ii) every `R ∈ [9,15]` lies in some zone of the chain, (iii) consecutive
zones have strictly increasing levels and OVERLAP inside `[9,15]` (the chain is connected:
the word's zone edges cover the carved window without a gap). -/
-- STANDING: DEFINITION
def WordRealized (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)) : Prop :=
  (∀ p ∈ w, 0 < g p.1 ∧ 1 ≤ p.2) ∧
  (∀ R : ℝ, 9 ≤ R → R ≤ 15 → ∃ p ∈ w, inZone g p.1 p.2 R) ∧
  (∀ p q : Fin 7 × ℕ, HasAdj w p q → p.2 < q.2 ∧
    ∃ R : ℝ, 9 ≤ R ∧ R ≤ 15 ∧ inZone g p.1 p.2 R ∧ inZone g q.1 q.2 R)

/-- A word edge `(x, y, P, Q)`: the word has consecutive zones `(x, jx) → (y, jy)` — the
`x`-zone FIRST (lower level), the `y`-zone second — with `P = 8jx+1`, `Q = 8jy−1`.  The
realized demand is then `g x / g y < P/Q` (`wordEdge_demand`): in the `ComposedEdge`
convention the record is `(e.x, e.y, A, B) = (x, y, P, Q)` (demand numerator side = first
zone's reading; chain from `e.y`, the second zone's reading, to `e.x` — cf. the banked
`ρ₆/ρ₂ ≤ 17/7` cap of `fam12568`'s `ρ₂/ρ₆ < 25/63` demand).  This is the structural
(word-side) predicate; the demand's realization on `g` is derived, not assumed. -/
-- STANDING: DEFINITION
def WordEdgeOf (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)) (x y : Fin 7) (P Q : ℤ) : Prop :=
  ∃ jx jy : ℕ, HasAdj w (x, jx) (y, jy) ∧
    P = ((jx : ℤ) * 8 + 1) ∧ Q = ((jy : ℤ) * 8 - 1)

/-- A composed record `e` matches the word edge `(x, y, P, Q)`: same demand edge, same
data (`e.x = x`, `e.y = y`, `e.A = P`, `e.B = Q`). -/
-- STANDING: DEFINITION
def SameEdge (e : ComposedEdge) (x y : Fin 7) (P Q : ℤ) : Prop :=
  e.x = x ∧ e.y = y ∧ e.A = P ∧ e.B = Q

/-! ## 2. The seam-demand realization lemma and the edge-existence lemma -/

/-- **THE SEAM-DEMAND REALIZATION LEMMA** (direction (b)'s engine): consecutive zones
`(x, jx) → (y, jy)` of a realized word (`jx < jy`, the `x`-zone first) overlap inside
`[9,15]`, so their readings share a point `R` with `g x·R < 8jx+1` (first zone's upper
side) and `g y·R > 8jy−1` (second zone's lower side); cross-multiplying
`(8jy−1)/(g y) < R < (8jx+1)/(g x)` forces `(8jy−1)·g x < (8jx+1)·g y`, i.e. the word
edge's demand `g x / g y < P/Q` realized on `g`, with the positivity the composed engine
needs. -/
theorem wordEdge_demand {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hw : WordRealized g w) {x y : Fin 7} {P Q : ℤ} (hedge : WordEdgeOf g w x y P Q) :
    0 < g x ∧ 0 < g y ∧ g x / g y < (P : ℝ) / (Q : ℝ) := by
  obtain ⟨hpos, hcov, hlink⟩ := hw
  obtain ⟨jx, jy, hadj, hP, hQ⟩ := hedge
  obtain ⟨l₁, l₂, hweq⟩ := hadj
  have hxm : (x, jx) ∈ w := by rw [hweq]; simp
  have hym : (y, jy) ∈ w := by rw [hweq]; simp
  have hxpos : 0 < g x := (hpos (x, jx) hxm).1
  have hypos : 0 < g y := (hpos (y, jy) hym).1
  have hx1 : 1 ≤ jx := (hpos (x, jx) hxm).2
  obtain ⟨hmono, R, hR1, hR2, hxz, hyz⟩ := hlink (x, jx) (y, jy) ⟨l₁, l₂, hweq⟩
  obtain ⟨_, hxa⟩ := hxz   -- g x * R < (jx : ℝ) * 8 + 1   (first zone's upper side)
  obtain ⟨hya, _⟩ := hyz   -- (jy : ℝ) * 8 - 1 < g y * R   (second zone's lower side)
  have hjy2 : (2 : ℝ) ≤ (jy : ℝ) := by
    have h2 : (2 : ℕ) ≤ jy := by omega
    exact_mod_cast h2
  have eP : (P : ℝ) = (jx : ℝ) * 8 + 1 := by exact_mod_cast hP
  have eQ : (Q : ℝ) = (jy : ℝ) * 8 - 1 := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by rw [eQ]; linarith
  have hxa' : g x * R < (P : ℝ) := by linarith
  have hya' : (Q : ℝ) < g y * R := by linarith
  -- the shared point: (8jy−1)/g y < R < (8jx+1)/g x  ⟹  Q·g x < g y·R·g x < P·g y
  have m1 : (Q : ℝ) * g x < g y * R * g x := mul_lt_mul_of_pos_right hya' hxpos
  have m2 : g x * R * g y < (P : ℝ) * g y := mul_lt_mul_of_pos_right hxa' hypos
  have k3 : g x * (Q : ℝ) < (P : ℝ) * g y := by linarith
  exact ⟨hxpos, hypos, (div_lt_div_iff₀ hypos hQpos).mpr k3⟩

#print axioms wordEdge_demand

/-- **A realized word has an edge**: a single zone (reading positive, level `≥ 1`) cannot
cover both window endpoints — covering `9` gives `8j−1 < 9ρ`, covering `15` gives
`15ρ < 8j+1`, whence `ρ < 1/3` and `8j < 4`, contradicting `j ≥ 1`.  So the chain has at
least two zones, and its first two form an edge. -/
theorem wordRealized_has_edge {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hw : WordRealized g w) :
    ∃ x y : Fin 7, ∃ P Q : ℤ, WordEdgeOf g w x y P Q := by
  obtain ⟨hpos, hcov, hlink⟩ := hw
  obtain ⟨p, hp, h9⟩ := hcov 9 (by norm_num) (by norm_num)
  cases w with
  | nil => exact absurd hp (by simp)
  | cons u rest =>
    cases rest with
    | nil =>
      obtain ⟨q, hq, h15⟩ := hcov 15 (by norm_num) (by norm_num)
      simp only [List.mem_singleton] at hp hq
      rw [hp] at h9
      rw [hq] at h15
      obtain ⟨h91, _⟩ := h9
      obtain ⟨_, h152⟩ := h15
      have hgu : (0 : ℝ) < g u.1 := (hpos u (by simp)).1
      have hr1 : (1 : ℝ) ≤ ((u.2 : ℕ) : ℝ) := by exact_mod_cast (hpos u (by simp)).2
      have hlt : ((u.2 : ℕ) : ℝ) < 1 := by linarith
      exact absurd hlt (not_lt.mpr hr1)
    | cons v rest' =>
      exact ⟨u.1, v.1, ((u.2 : ℤ) * 8 + 1), ((v.2 : ℤ) * 8 - 1),
        u.2, v.2, ⟨[], rest', rfl⟩, rfl, rfl⟩

#print axioms wordRealized_has_edge

/-! ## 3. Direction (b): the word-cover realization and the kill -/

/-- **Direction (b)'s conclusion shape**: a `W₁` word realized on `g`, the
W₀-chain-conditional bridge (direction (a)'s hypothesis form: the family's composed cap
chains realized on `g`), and family exhaustiveness (every realized word edge of the word
maps into the family) ⟹ some family record is FULLY realized on `g` — demand (from the
seam lemma) and chain (from the bridge), i.e. `ComposedEdgeRealized`. -/
theorem wordCover_realizes {g : Fin 7 → ℝ} {f : ComposedFam}
    (hchains : capChainsRealized g f)
    {w : List (Fin 7 × ℕ)} (hw : WordRealized g w)
    (hFam : ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q) :
    ∃ e ∈ f.edges, ComposedEdgeRealized g e := by
  obtain ⟨x, y, P, Q, hedge⟩ := wordRealized_has_edge hw
  obtain ⟨hxpos, hypos, hdem⟩ := wordEdge_demand hw hedge
  obtain ⟨e, he, hsame⟩ := hFam x y P Q hedge
  refine ⟨e, he, ?_, ?_, ?_, hchains e he⟩
  · rw [hsame.1]; exact hxpos
  · rw [hsame.2.1]; exact hypos
  · rw [hsame.1, hsame.2.1, hsame.2.2.1, hsame.2.2.2]; exact hdem

#print axioms wordCover_realizes

/-- **THE WORD-COVER KILL** (`wordCover_demands`): a `W₁` word realized on `g` + the
W₀-chain-conditional bridge + family exhaustiveness + the banked composed datum ⟹ False —
the realized record dies through `composedFamRefutes` (whose engine is
`composedCap_conflict`: the demand `ρx/ρy < A/B`, the telescoped chain cap
`ρy/ρx ≤ ∏caps`, the datum `A·∏caps ≤ B`).  This is the one-sided kill shape "IF `g`
carves `W₁` (word realized) and the join side is realized (bridge), the arrangement cannot
exist".  See the module docstring for the recorded divergence from the literal
`∀ e ∈ f.edges, ¬ ChainReal g e.y e.caps e.x` hypothesis shape. -/
theorem wordCover_demands {g : Fin 7 → ℝ} {f : ComposedFam}
    (hdata : ComposedFamData f) (hchains : capChainsRealized g f)
    {w : List (Fin 7 × ℕ)} (hw : WordRealized g w)
    (hFam : ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q) :
    False :=
  composedFamRefutes hdata (wordCover_realizes hchains hw hFam)

#print axioms wordCover_demands

/-! ## 4. The two OWED data-side directions and the glue to `OneSidedGlue` -/

/-- **OWED — the `W₁`-word covering direction** (the finite closed-interval covering
argument recorded as missing in `Fresh.FrontierFamilyCap.FrontierCarveCap`'s docstring):
if `g` admits no `W₁` clear point, then the zones of `g`'s readings cover `[9,15]`
(`distInt (g i * (s/8)) < 1/8` at some reading `i` is exactly the zone condition
`8k−1 < g i·s < 8k+1`), and that cover refines to a monotone connected zone chain — a
realized word.  Not proved here; nothing assumes it. -/
-- STANDING: OWED
def NoClearPointWordRealized (g : Fin 7 → ℝ) : Prop :=
  ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
    ∃ w : List (Fin 7 × ℕ), WordRealized g w

/-- **OWED — family exhaustiveness** (the dump's per-box word-edge totality, the [T
73/73] `join_domination_all_chains`-style law of dump v2 / `no-raw-kill pairs 0` of
`j2_cycle_v6`): for an arrangement in the box, EVERY word edge `(x, y, P, Q)` of every
realized `W₁` word is carried by the box's family — the family enumerates all word-edge
demands of the box.  Data-side: the per-box instantiation for `compFamOf b` is the dump's
exhaustiveness, not proved here. -/
-- STANDING: OWED
def FamilyCoversWordEdges (b : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)),
    (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) → WordRealized g w →
    ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q

/-- **THE GLUE — direction (b) discharged**: for a covered box `b`, the two OWED
data-side directions (the `W₁`-word covering direction, and the family exhaustiveness
datum) give `Fresh.OneSidedGlue.ComposedTotalOneSided b (compFamOf b)` — the composed
one-sided totality whose consumption by `oneSidedSound_of_composedData` completes the
spine.  Proof: no clear point gives a realized word (`NoClearPointWordRealized`); the
word's edges map into the family (`FamilyCoversWordEdges`); `wordCover_realizes` realizes
a record (the bridge `hchains` is a hypothesis of the totality datum itself). -/
theorem composedTotal_of_wordCover (b : Fin 7 → ℤ) (_hb : b ∈ coveredSet)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b)) :
    ComposedTotalOneSided b (compFamOf b) := by
  intro g hface hchains hcarve hnoc
  obtain ⟨w, hw⟩ := hword g hnoc
  obtain ⟨e, he, hxpos, hypos, hdem, _⟩ :=
    wordCover_realizes hchains hw (hexh g w hface hw)
  exact ⟨e, he, hxpos, hypos, hdem⟩

#print axioms composedTotal_of_wordCover


end Fresh.WordCoverSide



/-!
## BRIDGE MIRROR BODY (artifact: totlift_bridge_mirror_v1.lean, built by totlift_mirror_v1.py)

The one-sided sections of Fresh/TotalityLifts.lean VERBATIM (this text is emitted by the
same generator, totlift_gen_v1.py --mirror), pasted into the mirror after the verbatim
Fresh bodies (Framework-min, FilterAssembly-min, FrontierFamilyCap-min, SpineSound-min,
JoinFamComposed, OneSidedGlue, WordCoverSide, ComposedFamData full).  The D-variants and
the 5 pairwise instances are NOT in the mirror (they need Fresh.DumpDomData /
Fresh.SpineTotalData bodies; they add no new wiring and are ./check.sh-verified).
-/

namespace Fresh.TotalityLifts

open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedComposed
  Fresh.OneSidedGlue Fresh.WordCoverSide Fresh.FrontierFamilyCap

/-! ## 1. Family-general retargetings (the banked lemmas are fixed at the `compFamOf`
dispatch; the strict-class `dumpFam` lifts consume these general forms) -/

/-- **Family-general word-cover kill** (`Fresh.WordCoverSide.wordCover_demands` at an
arbitrary family `f` with its exhaustiveness datum `FamilyCoversWordEdges b f`). -/
theorem composedConflict_fam {b : Fin 7 → ℤ} {f : ComposedFam} (hdata : ComposedFamData f)
    (hexh : FamilyCoversWordEdges b f)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g f)
    (hw : WordRealized g w) : False :=
  wordCover_demands hdata hchains hw (hexh g w hface hw)

#print axioms composedConflict_fam

/-- **Family-general totality lift** (`Fresh.WordCoverSide.composedTotal_of_wordCover` is
fixed at the `compFamOf` dispatch; the same derivation at an arbitrary family — the
two data-side OWEDs reduce to `ComposedTotalOneSided b f`). -/
theorem composedTotal_of_wordCover_fam {b : Fin 7 → ℤ} {f : ComposedFam}
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b f) :
    ComposedTotalOneSided b f := by
  intro g hface hchains hcarve hnoc
  obtain ⟨w, hw⟩ := hword g hnoc
  obtain ⟨e, he, hxpos, hypos, hdem, _⟩ :=
    wordCover_realizes hchains hw (hexh g w hface hw)
  exact ⟨e, he, hxpos, hypos, hdem⟩

#print axioms composedTotal_of_wordCover_fam

/-- **Family-general consumption** (`Fresh.OneSidedGlue.oneSidedSound_of_composedData` is
fixed at the `compFamOf` dispatch and the `coveredSet` membership; the same glue at an
arbitrary family with its `ComposedFamData` datum). -/
theorem oneSidedSound_of_total_fam {b : Fin 7 → ℤ} {f : ComposedFam}
    (hdata : ComposedFamData f) (htotal : ComposedTotalOneSided b f)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g f)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨e, he, hxpos, hypos, hdem⟩ := htotal g hface hchains hcarve hnoc
  exact composedEdge_kill hdata hchains he hxpos hypos hdem

#print axioms oneSidedSound_of_total_fam


/-! ## 2. The 68 one-sided boxes: per-box data + word-cover kill + totality lift + consumption

Order: the 11 strict-complete boxes first (dump v2 census section 7, the richest data),
then the remaining 57 in `coveredSet` order. -/

/-! ### Box (1, 4, 5, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 4, 5, 5, 6, 6, 8) carries the banked family
`compFam_1_4_5_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_6_6_8 :
    (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_6_6_8 :
    InRange17 (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_6_6_8⟩

#print axioms spineFamDataOS_1_4_5_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_6_6_8

/-- **The per-box totality lift, box (1, 4, 5, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_6_6_8 hword hexh

#print axioms totalLift_1_4_5_5_6_6_8

/-- **The per-box consumption, box (1, 4, 5, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_6_6_8

/-! ### Box (1, 4, 5, 5, 6, 7, 7) -/

/-- coveredSet membership: box (1, 4, 5, 5, 6, 7, 7) carries the banked family
`compFam_1_4_5_5_6_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_6_7_7 :
    (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_6_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 6, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_6_7_7 :
    InRange17 (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_6_7_7⟩

#print axioms spineFamDataOS_1_4_5_5_6_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 6, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_6_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_6_7_7
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_6_7_7) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_6_7_7

/-- **The per-box totality lift, box (1, 4, 5, 5, 6, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_6_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_6_7_7 hword hexh

#print axioms totalLift_1_4_5_5_6_7_7

/-- **The per-box consumption, box (1, 4, 5, 5, 6, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_6_7_7
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_6_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_6_7_7

/-! ### Box (1, 4, 5, 5, 6, 7, 8) -/

/-- coveredSet membership: box (1, 4, 5, 5, 6, 7, 8) carries the banked family
`compFam_1_4_5_5_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_6_7_8 :
    (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_6_7_8 :
    InRange17 (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_6_7_8⟩

#print axioms spineFamDataOS_1_4_5_5_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_6_7_8

/-- **The per-box totality lift, box (1, 4, 5, 5, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_6_7_8 hword hexh

#print axioms totalLift_1_4_5_5_6_7_8

/-- **The per-box consumption, box (1, 4, 5, 5, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_6_7_8
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_6_7_8

/-! ### Box (1, 4, 5, 6, 6, 7, 9) -/

/-- coveredSet membership: box (1, 4, 5, 6, 6, 7, 9) carries the banked family
`compFam_1_4_5_6_6_7_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_6_6_7_9 :
    (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_6_6_7_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 6, 6, 7, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_6_6_7_9 :
    InRange17 (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_6_6_7_9⟩

#print axioms spineFamDataOS_1_4_5_6_6_7_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 6, 6, 7, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_6_6_7_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_6_6_7_9
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_6_6_7_9) hexh hface hchains hw

#print axioms composedConflict_1_4_5_6_6_7_9

/-- **The per-box totality lift, box (1, 4, 5, 6, 6, 7, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_6_6_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_6_6_7_9 hword hexh

#print axioms totalLift_1_4_5_6_6_7_9

/-- **The per-box consumption, box (1, 4, 5, 6, 6, 7, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_6_6_7_9
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_6_6_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_6_6_7_9

/-! ### Box (1, 4, 5, 6, 6, 7, 11) -/

/-- coveredSet membership: box (1, 4, 5, 6, 6, 7, 11) carries the banked family
`compFam_1_4_5_6_6_7_11` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_6_6_7_11 :
    (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_6_6_7_11

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 6, 6, 7, 11)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_6_6_7_11 :
    InRange17 (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_6_6_7_11⟩

#print axioms spineFamDataOS_1_4_5_6_6_7_11

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 6, 6, 7, 11)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_6_6_7_11`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_6_6_7_11
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_6_6_7_11) hexh hface hchains hw

#print axioms composedConflict_1_4_5_6_6_7_11

/-- **The per-box totality lift, box (1, 4, 5, 6, 6, 7, 11)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_6_6_7_11
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_6_6_7_11 hword hexh

#print axioms totalLift_1_4_5_6_6_7_11

/-- **The per-box consumption, box (1, 4, 5, 6, 6, 7, 11)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_6_6_7_11
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_6_6_7_11 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_6_6_7_11

/-! ### Box (1, 4, 5, 6, 7, 8, 8) -/

/-- coveredSet membership: box (1, 4, 5, 6, 7, 8, 8) carries the banked family
`compFam_1_4_5_6_7_8_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_6_7_8_8 :
    (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_6_7_8_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 6, 7, 8, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_6_7_8_8 :
    InRange17 (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_6_7_8_8⟩

#print axioms spineFamDataOS_1_4_5_6_7_8_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 6, 7, 8, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_6_7_8_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_6_7_8_8
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_6_7_8_8) hexh hface hchains hw

#print axioms composedConflict_1_4_5_6_7_8_8

/-- **The per-box totality lift, box (1, 4, 5, 6, 7, 8, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_6_7_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_6_7_8_8 hword hexh

#print axioms totalLift_1_4_5_6_7_8_8

/-- **The per-box consumption, box (1, 4, 5, 6, 7, 8, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_6_7_8_8
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_6_7_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_6_7_8_8

/-! ### Box (1, 4, 5, 6, 7, 8, 9) -/

/-- coveredSet membership: box (1, 4, 5, 6, 7, 8, 9) carries the banked family
`compFam_1_4_5_6_7_8_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_6_7_8_9 :
    (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_6_7_8_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 6, 7, 8, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_6_7_8_9 :
    InRange17 (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_6_7_8_9⟩

#print axioms spineFamDataOS_1_4_5_6_7_8_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 6, 7, 8, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_6_7_8_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_6_7_8_9
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_6_7_8_9) hexh hface hchains hw

#print axioms composedConflict_1_4_5_6_7_8_9

/-- **The per-box totality lift, box (1, 4, 5, 6, 7, 8, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_6_7_8_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_6_7_8_9 hword hexh

#print axioms totalLift_1_4_5_6_7_8_9

/-- **The per-box consumption, box (1, 4, 5, 6, 7, 8, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_6_7_8_9
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_6_7_8_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_6_7_8_9

/-! ### Box (1, 5, 5, 6, 7, 7, 8) -/

/-- coveredSet membership: box (1, 5, 5, 6, 7, 7, 8) carries the banked family
`compFam_1_5_5_6_7_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_5_5_6_7_7_8 :
    (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem
  exact Finset.mem_singleton.mpr rfl

#print axioms covered_1_5_5_6_7_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 5, 5, 6, 7, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_5_5_6_7_7_8 :
    InRange17 (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_5_5_6_7_7_8⟩

#print axioms spineFamDataOS_1_5_5_6_7_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 5, 5, 6, 7, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_5_5_6_7_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_5_5_6_7_7_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_5_5_6_7_7_8) hexh hface hchains hw

#print axioms composedConflict_1_5_5_6_7_7_8

/-- **The per-box totality lift, box (1, 5, 5, 6, 7, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_5_5_6_7_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_5_5_6_7_7_8 hword hexh

#print axioms totalLift_1_5_5_6_7_7_8

/-- **The per-box consumption, box (1, 5, 5, 6, 7, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_5_5_6_7_7_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_5_5_6_7_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_5_5_6_7_7_8

/-! ## 4. The totals (at the batch coveredSet; the real file states them over the
full 68-element coveredSet -- same proofs, verbatim) -/

theorem totalLifts_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b)) :
    ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b) :=
  fun b hb => composedTotal_of_wordCover b hb hword (hexh b hb)

#print axioms totalLifts_of_exhaustiveness

theorem oneSidedSounds_of_totals
    (htotal : ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b))
    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb (htotal b hb) g hface hchains hcarve

#print axioms oneSidedSounds_of_totals

theorem oneSidedSound_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b))
    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSounds_of_totals (totalLifts_of_exhaustiveness hword hexh) b hb g hface hchains
    hcarve

#print axioms oneSidedSound_of_exhaustiveness

end Fresh.TotalityLifts
