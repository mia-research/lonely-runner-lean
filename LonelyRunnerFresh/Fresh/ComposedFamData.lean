import Fresh.JoinFamComposed

/-!
# Composed-family data for the 68 one-sided boxes: the joinedge per-box dump at scale

Written 2026-11-13.  New file; nothing existing is edited.  This file instantiates
`Fresh.JoinFamComposed.ComposedFamData` box by box from
`experiments/n8/onefast_audit/joinedge_perbox_v1.jsonl` (the per-box JoinEdge dump of the
68 one-sided W0-admitting boxes + 5 two-sided controls), the pattern of the worked instance
`Fresh.JoinFamComposed.composedFamData_12568` at scale.

Per record (dump semantics, verified against `joinedge_perbox_v1.py`'s `step` /
`chainside_cands`, the ground truth of the dump): the W1 word demands
`rho_{x1}/rho_{y1} < P/Q` (the word step asserts the bound on readings (x1, y1), 1-based),
and the chain-side cap `rho_{y1}/rho_{x1} <= C/D` (the dump's transposed-pair table entry:
the `J` side is the join of ALL W0 chains' closed tables, hence implied by every chain;
the `box` side is the box closure `U0`, hence holds on the whole box) kills the word exactly
when `(P/Q)*(C/D) <= 1` -- the dump's `conflict` flag, which is the composed datum
`A*C <= B*D` under `Fresh.JoinFamComposed`'s convention (demand `rho_x/rho_y < A/B`, cap
chain from `y` to `x`).  Each record below is therefore the faithful `ComposedEdge`
`(x1-1, y1-1, A, B, [(x1-1, C/D)])`: the single-step cap chain from `y` to `x` carrying the
dump's conflicting chain-side cap value.  No `8m+-1` condition is imposed anywhere -- the
composed datum is exactly `A*prod(caps) <= B` (positivity + product), which is what
`ComposedEdgeValid` requires; the dump's STRICT/LEANMIN/COMBUNRED/NUM coverage ladder and
its mod-8 rescaling bookkeeping are all subsumed (the census' chain-side coverable set is
94.3% of all one-sided deaths).

Honest residual (rule 22): demands with NO conflicting chain-side cap -- the census's
derived-only deaths, 109592 of 1926698 (5.7%) -- are NOT instantiated: their killing caps
are the word's own accumulated products (box-end bound x word-constraint compositions,
E813 item 7's form), whose per-factor realization is word-conditional, so a faithful
composed chain for them needs a path-decomposition dump v1 does not carry (the dump records
derived caps as values only).  Per box the family carries the top records by death count
(top-4, top-8 for the three census-fully-covered boxes
(1,3,4,4,5,5,7), (1,3,4,5,6,6,7), (1,4,5,6,6,7,11)); the per-record death accounting and
the derived-only residuals are in `experiments/n8/onefast_audit/compfam_audit_v1.out`.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three
(propext, Classical.choice, Quot.sound) -- `sorryAx` is failure.
-/

namespace Fresh.OneSidedComposed

open Fresh.JoinFamComposed

/-- Box (1, 2, 3, 4, 4, 5, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 248 of the box's 6578 word deaths; the box's honest residual is 22 derived-only deaths (chain-side coverable total: 6556).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 4, 5, 7), (7,1,73/15←J cap 1/7); (7,2,73/31←J cap 5/14); (7,2,73/39←J cap 5/14); (7,3,73/39←J cap 33/70). -/
noncomputable def compFam_1_2_3_4_4_5_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (1 / 7))]⟩,
    ⟨6, 1, 73, 31, [(6, (5 / 14))]⟩,
    ⟨6, 1, 73, 39, [(6, (5 / 14))]⟩,
    ⟨6, 2, 73, 39, [(6, (33 / 70))]⟩
  ]⟩

theorem compFamData_1_2_3_4_4_5_7 : ComposedFamData compFam_1_2_3_4_4_5_7 := by
  intro e he
  simp only [compFam_1_2_3_4_4_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_4_5_7

/-- Box (1, 2, 3, 4, 4, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 248 of the box's 6848 word deaths; the box's honest residual is 22 derived-only deaths (chain-side coverable total: 6826).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 4, 6, 7), (7,1,73/15←J cap 1/7); (7,2,73/31←J cap 5/14); (7,2,73/39←J cap 5/14); (7,3,73/39←J cap 153/322). -/
noncomputable def compFam_1_2_3_4_4_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (1 / 7))]⟩,
    ⟨6, 1, 73, 31, [(6, (5 / 14))]⟩,
    ⟨6, 1, 73, 39, [(6, (5 / 14))]⟩,
    ⟨6, 2, 73, 39, [(6, (153 / 322))]⟩
  ]⟩

theorem compFamData_1_2_3_4_4_6_7 : ComposedFamData compFam_1_2_3_4_4_6_7 := by
  intro e he
  simp only [compFam_1_2_3_4_4_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_4_6_7

/-- Box (1, 2, 3, 4, 5, 5, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 508 of the box's 19438 word deaths; the box's honest residual is 400 derived-only deaths (chain-side coverable total: 19038).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 5, 5, 7), (7,1,73/15←J cap 1/7); (7,2,73/31←J cap 125/351); (7,2,73/39←J cap 125/351); (7,3,73/39←J cap 55/117). -/
noncomputable def compFam_1_2_3_4_5_5_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (1 / 7))]⟩,
    ⟨6, 1, 73, 31, [(6, (125 / 351))]⟩,
    ⟨6, 1, 73, 39, [(6, (125 / 351))]⟩,
    ⟨6, 2, 73, 39, [(6, (55 / 117))]⟩
  ]⟩

theorem compFamData_1_2_3_4_5_5_7 : ComposedFamData compFam_1_2_3_4_5_5_7 := by
  intro e he
  simp only [compFam_1_2_3_4_5_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_5_5_7

/-- Box (1, 2, 3, 4, 5, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 104 word deaths; the box's honest residual is 1 derived-only deaths (chain-side coverable total: 103).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 5, 7, 7), (5,1,49/15←J cap 209814/1065935); (5,2,49/31←J cap 3566838/7461545); (5,2,49/39←J cap 3566838/7461545); (5,3,49/31←J cap 9537/16399). -/
noncomputable def compFam_1_2_3_4_5_7_7 : ComposedFam :=
  ⟨[
    ⟨4, 0, 49, 15, [(4, (209814 / 1065935))]⟩,
    ⟨4, 1, 49, 31, [(4, (3566838 / 7461545))]⟩,
    ⟨4, 1, 49, 39, [(4, (3566838 / 7461545))]⟩,
    ⟨4, 2, 49, 31, [(4, (9537 / 16399))]⟩
  ]⟩

theorem compFamData_1_2_3_4_5_7_7 : ComposedFamData compFam_1_2_3_4_5_7_7 := by
  intro e he
  simp only [compFam_1_2_3_4_5_7_7, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_5_7_7

/-- Box (1, 2, 3, 4, 5, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 304 of the box's 7341 word deaths; the box's honest residual is 20 derived-only deaths (chain-side coverable total: 7321).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 5, 7, 8), (6,1,73/15←J cap 34/225); (6,2,73/31←J cap 578/1575); (6,2,73/39←J cap 578/1575); (6,3,73/39←J cap 4913/10695). -/
noncomputable def compFam_1_2_3_4_5_7_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (34 / 225))]⟩,
    ⟨5, 1, 73, 31, [(5, (578 / 1575))]⟩,
    ⟨5, 1, 73, 39, [(5, (578 / 1575))]⟩,
    ⟨5, 2, 73, 39, [(5, (4913 / 10695))]⟩
  ]⟩

theorem compFamData_1_2_3_4_5_7_8 : ComposedFamData compFam_1_2_3_4_5_7_8 := by
  intro e he
  simp only [compFam_1_2_3_4_5_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_5_7_8

/-- Box (1, 2, 3, 4, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 477 of the box's 17209 word deaths; the box's honest residual is 138 derived-only deaths (chain-side coverable total: 17071).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 6, 6, 8), (7,6,1/1←J cap 187/235); (6,1,13/3←J cap 54/329); (6,2,65/31←J cap 135/329); (6,2,5/3←J cap 135/329). -/
noncomputable def compFam_1_2_3_4_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (187 / 235))]⟩,
    ⟨5, 0, 13, 3, [(5, (54 / 329))]⟩,
    ⟨5, 1, 65, 31, [(5, (135 / 329))]⟩,
    ⟨5, 1, 5, 3, [(5, (135 / 329))]⟩
  ]⟩

theorem compFamData_1_2_3_4_6_6_8 : ComposedFamData compFam_1_2_3_4_6_6_8 := by
  intro e he
  simp only [compFam_1_2_3_4_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_6_6_8

/-- Box (1, 2, 3, 4, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 344 of the box's 8534 word deaths; the box's honest residual is 4 derived-only deaths (chain-side coverable total: 8530).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 4, 6, 7, 8), (6,1,73/15←J cap 34/235); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,3,73/39←J cap 4913/10695). -/
noncomputable def compFam_1_2_3_4_6_7_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (34 / 235))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 2, 73, 39, [(5, (4913 / 10695))]⟩
  ]⟩

theorem compFamData_1_2_3_4_6_7_8 : ComposedFamData compFam_1_2_3_4_6_7_8 := by
  intro e he
  simp only [compFam_1_2_3_4_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_4_6_7_8

/-- Box (1, 2, 3, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 309 of the box's 12354 word deaths; the box's honest residual is 49 derived-only deaths (chain-side coverable total: 12305).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 3, 5, 6, 6, 8), (7,6,1/1←J cap 187/235); (6,1,13/3←J cap 1650/10199); (6,2,65/31←J cap 4125/10199); (6,2,5/3←J cap 4125/10199). -/
noncomputable def compFam_1_2_3_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (187 / 235))]⟩,
    ⟨5, 0, 13, 3, [(5, (1650 / 10199))]⟩,
    ⟨5, 1, 65, 31, [(5, (4125 / 10199))]⟩,
    ⟨5, 1, 5, 3, [(5, (4125 / 10199))]⟩
  ]⟩

theorem compFamData_1_2_3_5_6_6_8 : ComposedFamData compFam_1_2_3_5_6_6_8 := by
  intro e he
  simp only [compFam_1_2_3_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_3_5_6_6_8

/-- Box (1, 2, 4, 4, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 276 of the box's 7420 word deaths; the box's honest residual is 1 derived-only deaths (chain-side coverable total: 7419).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 4, 4, 6, 6, 8), (7,6,1/1←J cap 187/235); (6,1,13/3←J cap 102/637); (6,2,65/31←J cap 255/637); (6,2,5/3←J cap 255/637). -/
noncomputable def compFam_1_2_4_4_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (187 / 235))]⟩,
    ⟨5, 0, 13, 3, [(5, (102 / 637))]⟩,
    ⟨5, 1, 65, 31, [(5, (255 / 637))]⟩,
    ⟨5, 1, 5, 3, [(5, (255 / 637))]⟩
  ]⟩

theorem compFamData_1_2_4_4_6_6_8 : ComposedFamData compFam_1_2_4_4_6_6_8 := by
  intro e he
  simp only [compFam_1_2_4_4_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_4_4_6_6_8

/-- Box (1, 2, 4, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 261 of the box's 10934 word deaths; the box's honest residual is 32 derived-only deaths (chain-side coverable total: 10902).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 2, 4, 5, 6, 6, 8), (7,6,1/1←J cap 187/235); (6,1,13/3←J cap 102/637); (6,2,65/31←J cap 255/637); (6,2,5/3←J cap 255/637). -/
noncomputable def compFam_1_2_4_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (187 / 235))]⟩,
    ⟨5, 0, 13, 3, [(5, (102 / 637))]⟩,
    ⟨5, 1, 65, 31, [(5, (255 / 637))]⟩,
    ⟨5, 1, 5, 3, [(5, (255 / 637))]⟩
  ]⟩

theorem compFamData_1_2_4_5_6_6_8 : ComposedFamData compFam_1_2_4_5_6_6_8 := by
  intro e he
  simp only [compFam_1_2_4_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_2_4_5_6_6_8

/-- Box (1, 3, 3, 4, 4, 5, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 144 of the box's 4278 word deaths; the box's honest residual is 10 derived-only deaths (chain-side coverable total: 4268).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 4, 5, 7), (6,1,19/5←J cap 9/49); (6,2,57/31←J cap 153/329); (6,2,19/13←J cap 153/329); (6,2,57/47←J cap 153/329). -/
noncomputable def compFam_1_3_3_4_4_5_7 : ComposedFam :=
  ⟨[
    ⟨5, 0, 19, 5, [(5, (9 / 49))]⟩,
    ⟨5, 1, 57, 31, [(5, (153 / 329))]⟩,
    ⟨5, 1, 19, 13, [(5, (153 / 329))]⟩,
    ⟨5, 1, 57, 47, [(5, (153 / 329))]⟩
  ]⟩

theorem compFamData_1_3_3_4_4_5_7 : ComposedFamData compFam_1_3_3_4_4_5_7 := by
  intro e he
  simp only [compFam_1_3_3_4_4_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_4_5_7

/-- Box (1, 3, 3, 4, 4, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 312 of the box's 8879 word deaths; the box's honest residual is 24 derived-only deaths (chain-side coverable total: 8855).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 4, 6, 7), (7,1,73/15←J cap 1/7); (7,2,73/31←J cap 17/47); (7,2,73/39←J cap 17/47); (7,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_3_4_4_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (1 / 7))]⟩,
    ⟨6, 1, 73, 31, [(6, (17 / 47))]⟩,
    ⟨6, 1, 73, 39, [(6, (17 / 47))]⟩,
    ⟨6, 1, 73, 47, [(6, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_3_4_4_6_7 : ComposedFamData compFam_1_3_3_4_4_6_7 := by
  intro e he
  simp only [compFam_1_3_3_4_4_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_4_6_7

/-- Box (1, 3, 3, 4, 5, 5, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 144 of the box's 3703 word deaths; the box's honest residual is 7 derived-only deaths (chain-side coverable total: 3696).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 5, 5, 7), (6,1,19/5←J cap 50/273); (6,2,57/31←J cap 153/329); (6,2,19/13←J cap 153/329); (6,2,57/47←J cap 153/329). -/
noncomputable def compFam_1_3_3_4_5_5_7 : ComposedFam :=
  ⟨[
    ⟨5, 0, 19, 5, [(5, (50 / 273))]⟩,
    ⟨5, 1, 57, 31, [(5, (153 / 329))]⟩,
    ⟨5, 1, 19, 13, [(5, (153 / 329))]⟩,
    ⟨5, 1, 57, 47, [(5, (153 / 329))]⟩
  ]⟩

theorem compFamData_1_3_3_4_5_5_7 : ComposedFamData compFam_1_3_3_4_5_5_7 := by
  intro e he
  simp only [compFam_1_3_3_4_5_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_5_5_7

/-- Box (1, 3, 3, 4, 5, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 6169 of the box's 391999 word deaths; the box's honest residual is 34213 derived-only deaths (chain-side coverable total: 357786).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 5, 6, 7), (7,4,1/1←J cap 3/5); (6,3,1/1←J cap 3/5); (7,3,1/1←J cap 1/2); (7,5,1/1←J cap 27/35). -/
noncomputable def compFam_1_3_3_4_5_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 3, 1, 1, [(6, (3 / 5))]⟩,
    ⟨5, 2, 1, 1, [(5, (3 / 5))]⟩,
    ⟨6, 2, 1, 1, [(6, (1 / 2))]⟩,
    ⟨6, 4, 1, 1, [(6, (27 / 35))]⟩
  ]⟩

theorem compFamData_1_3_3_4_5_6_7 : ComposedFamData compFam_1_3_3_4_5_6_7 := by
  intro e he
  simp only [compFam_1_3_3_4_5_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_5_6_7

/-- Box (1, 3, 3, 4, 5, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 2648 of the box's 184709 word deaths; the box's honest residual is 8308 derived-only deaths (chain-side coverable total: 176401).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 5, 6, 8), (7,5,1/1←J cap 85/117); (7,4,1/1←J cap 425/713); (5,3,1/1←J cap 17/23); (6,3,1/1←J cap 3/5). -/
noncomputable def compFam_1_3_3_4_5_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 4, 1, 1, [(6, (85 / 117))]⟩,
    ⟨6, 3, 1, 1, [(6, (425 / 713))]⟩,
    ⟨4, 2, 1, 1, [(4, (17 / 23))]⟩,
    ⟨5, 2, 1, 1, [(5, (3 / 5))]⟩
  ]⟩

theorem compFamData_1_3_3_4_5_6_8 : ComposedFamData compFam_1_3_3_4_5_6_8 := by
  intro e he
  simp only [compFam_1_3_3_4_5_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_5_6_8

/-- Box (1, 3, 3, 4, 5, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 64 of the box's 2358 word deaths; the box's honest residual is 8 derived-only deaths (chain-side coverable total: 2350).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 5, 7, 8), (6,1,73/15←J cap 34/235); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_3_4_5_7_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (34 / 235))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 47, [(5, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_3_4_5_7_8 : ComposedFamData compFam_1_3_3_4_5_7_8 := by
  intro e he
  simp only [compFam_1_3_3_4_5_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_5_7_8

/-- Box (1, 3, 3, 4, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 620 of the box's 30522 word deaths; the box's honest residual is 483 derived-only deaths (chain-side coverable total: 30039).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 6, 6, 8), (7,6,1/1←J cap 25/31); (6,1,13/3←J cap 1734/10465); (6,2,65/31←J cap 867/2093); (6,2,5/3←J cap 867/2093). -/
noncomputable def compFam_1_3_3_4_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (25 / 31))]⟩,
    ⟨5, 0, 13, 3, [(5, (1734 / 10465))]⟩,
    ⟨5, 1, 65, 31, [(5, (867 / 2093))]⟩,
    ⟨5, 1, 5, 3, [(5, (867 / 2093))]⟩
  ]⟩

theorem compFamData_1_3_3_4_6_6_8 : ComposedFamData compFam_1_3_3_4_6_6_8 := by
  intro e he
  simp only [compFam_1_3_3_4_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_6_6_8

/-- Box (1, 3, 3, 4, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 464 of the box's 11483 word deaths; the box's honest residual is 14 derived-only deaths (chain-side coverable total: 11469).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 4, 6, 7, 8), (6,1,73/15←J cap 34/235); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_3_4_6_7_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (34 / 235))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 47, [(5, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_3_4_6_7_8 : ComposedFamData compFam_1_3_3_4_6_7_8 := by
  intro e he
  simp only [compFam_1_3_3_4_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_4_6_7_8

/-- Box (1, 3, 3, 5, 5, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 132 of the box's 3644 word deaths; the box's honest residual is 34 derived-only deaths (chain-side coverable total: 3610).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 5, 5, 6, 8), (5,1,49/15←J cap 34/161); (5,2,49/31←J cap 357/611); (5,2,49/39←J cap 357/611); (5,2,49/47←J cap 357/611). -/
noncomputable def compFam_1_3_3_5_5_6_8 : ComposedFam :=
  ⟨[
    ⟨4, 0, 49, 15, [(4, (34 / 161))]⟩,
    ⟨4, 1, 49, 31, [(4, (357 / 611))]⟩,
    ⟨4, 1, 49, 39, [(4, (357 / 611))]⟩,
    ⟨4, 1, 49, 47, [(4, (357 / 611))]⟩
  ]⟩

theorem compFamData_1_3_3_5_5_6_8 : ComposedFamData compFam_1_3_3_5_5_6_8 := by
  intro e he
  simp only [compFam_1_3_3_5_5_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_5_5_6_8

/-- Box (1, 3, 3, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 633 of the box's 35506 word deaths; the box's honest residual is 540 derived-only deaths (chain-side coverable total: 34966).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 5, 6, 6, 8), (7,6,1/1←J cap 25/31); (6,1,13/3←J cap 31790/194649); (6,2,65/31←J cap 867/2093); (6,2,5/3←J cap 867/2093). -/
noncomputable def compFam_1_3_3_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (25 / 31))]⟩,
    ⟨5, 0, 13, 3, [(5, (31790 / 194649))]⟩,
    ⟨5, 1, 65, 31, [(5, (867 / 2093))]⟩,
    ⟨5, 1, 5, 3, [(5, (867 / 2093))]⟩
  ]⟩

theorem compFamData_1_3_3_5_6_6_8 : ComposedFamData compFam_1_3_3_5_6_6_8 := by
  intro e he
  simp only [compFam_1_3_3_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_5_6_6_8

/-- Box (1, 3, 3, 5, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 674 of the box's 30414 word deaths; the box's honest residual is 1026 derived-only deaths (chain-side coverable total: 29388).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 5, 6, 7, 8), (7,6,1/1←J cap 3179/3565); (6,1,73/15←J cap 2/13); (6,2,73/31←J cap 119/299); (6,2,73/39←J cap 119/299). -/
noncomputable def compFam_1_3_3_5_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (3179 / 3565))]⟩,
    ⟨5, 0, 73, 15, [(5, (2 / 13))]⟩,
    ⟨5, 1, 73, 31, [(5, (119 / 299))]⟩,
    ⟨5, 1, 73, 39, [(5, (119 / 299))]⟩
  ]⟩

theorem compFamData_1_3_3_5_6_7_8 : ComposedFamData compFam_1_3_3_5_6_7_8 := by
  intro e he
  simp only [compFam_1_3_3_5_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_5_6_7_8

/-- Box (1, 3, 3, 5, 6, 8, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 68 of the box's 1807 word deaths; the box's honest residual is 5 derived-only deaths (chain-side coverable total: 1802).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 5, 6, 8, 8), (6,1,73/15←J cap 2/15); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_3_5_6_8_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (2 / 15))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 47, [(5, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_3_5_6_8_8 : ComposedFamData compFam_1_3_3_5_6_8_8 := by
  intro e he
  simp only [compFam_1_3_3_5_6_8_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_5_6_8_8

/-- Box (1, 3, 3, 5, 6, 8, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 108 of the box's 2939 word deaths; the box's honest residual is 7 derived-only deaths (chain-side coverable total: 2932).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 3, 5, 6, 8, 9), (6,1,73/15←J cap 2/15); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_3_5_6_8_9 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (2 / 15))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 47, [(5, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_3_5_6_8_9 : ComposedFamData compFam_1_3_3_5_6_8_9 := by
  intro e he
  simp only [compFam_1_3_3_5_6_8_9, List.mem_cons] at he
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

#print axioms compFamData_1_3_3_5_6_8_9

/-- Box (1, 3, 4, 4, 5, 5, 7): the top-8 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 8 records account for 16 of the box's 187 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 187).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 4, 5, 5, 7), (7,1,13/3←J cap 1/7); (7,2,65/31←J cap 33/70); (7,2,5/3←J cap 33/70); (7,2,65/47←J cap 33/70); (7,3,5/3←J cap 825/1457); (7,3,65/47←J cap 825/1457); (7,3,13/11←J cap 825/1457); (7,3,65/63←J cap 825/1457). -/
noncomputable def compFam_1_3_4_4_5_5_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩,
    ⟨6, 1, 65, 31, [(6, (33 / 70))]⟩,
    ⟨6, 1, 5, 3, [(6, (33 / 70))]⟩,
    ⟨6, 1, 65, 47, [(6, (33 / 70))]⟩,
    ⟨6, 2, 5, 3, [(6, (825 / 1457))]⟩,
    ⟨6, 2, 65, 47, [(6, (825 / 1457))]⟩,
    ⟨6, 2, 13, 11, [(6, (825 / 1457))]⟩,
    ⟨6, 2, 65, 63, [(6, (825 / 1457))]⟩
  ]⟩

theorem compFamData_1_3_4_4_5_5_7 : ComposedFamData compFam_1_3_4_4_5_5_7 := by
  intro e he
  simp only [compFam_1_3_4_4_5_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_4_5_5_7

/-- Box (1, 3, 4, 4, 5, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 508 of the box's 18095 word deaths; the box's honest residual is 184 derived-only deaths (chain-side coverable total: 17911).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 4, 5, 6, 8), (5,1,49/15←J cap 34/161); (5,2,49/31←J cap 357/611); (5,2,49/39←J cap 357/611); (5,2,49/47←J cap 357/611). -/
noncomputable def compFam_1_3_4_4_5_6_8 : ComposedFam :=
  ⟨[
    ⟨4, 0, 49, 15, [(4, (34 / 161))]⟩,
    ⟨4, 1, 49, 31, [(4, (357 / 611))]⟩,
    ⟨4, 1, 49, 39, [(4, (357 / 611))]⟩,
    ⟨4, 1, 49, 47, [(4, (357 / 611))]⟩
  ]⟩

theorem compFamData_1_3_4_4_5_6_8 : ComposedFamData compFam_1_3_4_4_5_6_8 := by
  intro e he
  simp only [compFam_1_3_4_4_5_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_4_5_6_8

/-- Box (1, 3, 4, 4, 5, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 46 of the box's 1934 word deaths; the box's honest residual is 12 derived-only deaths (chain-side coverable total: 1922).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 4, 5, 7, 7), (5,3,1/1←J cap 450/637); (6,3,1/1←J cap 50/91); (7,3,1/1←J cap 25/49); (3,1,41/15←J cap 594/2093). -/
noncomputable def compFam_1_3_4_4_5_7_7 : ComposedFam :=
  ⟨[
    ⟨4, 2, 1, 1, [(4, (450 / 637))]⟩,
    ⟨5, 2, 1, 1, [(5, (50 / 91))]⟩,
    ⟨6, 2, 1, 1, [(6, (25 / 49))]⟩,
    ⟨2, 0, 41, 15, [(2, (594 / 2093))]⟩
  ]⟩

theorem compFamData_1_3_4_4_5_7_7 : ComposedFamData compFam_1_3_4_4_5_7_7 := by
  intro e he
  simp only [compFam_1_3_4_4_5_7_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_4_5_7_7

/-- Box (1, 3, 4, 4, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 605 of the box's 16728 word deaths; the box's honest residual is 54 derived-only deaths (chain-side coverable total: 16674).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 4, 6, 6, 8), (7,6,1/1←J cap 25/31); (6,1,13/3←J cap 102/637); (6,2,65/31←J cap 867/2093); (6,2,5/3←J cap 867/2093). -/
noncomputable def compFam_1_3_4_4_6_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 5, 1, 1, [(6, (25 / 31))]⟩,
    ⟨5, 0, 13, 3, [(5, (102 / 637))]⟩,
    ⟨5, 1, 65, 31, [(5, (867 / 2093))]⟩,
    ⟨5, 1, 5, 3, [(5, (867 / 2093))]⟩
  ]⟩

theorem compFamData_1_3_4_4_6_6_8 : ComposedFamData compFam_1_3_4_4_6_6_8 := by
  intro e he
  simp only [compFam_1_3_4_4_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_4_6_6_8

/-- Box (1, 3, 4, 4, 6, 6, 15): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 48 of the box's 1825 word deaths; the box's honest residual is 4 derived-only deaths (chain-side coverable total: 1821).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 4, 6, 6, 15), (2,1,5/3←J cap 803/2139); (2,3,25/39←J cap 68255/50623); (2,3,25/47←J cap 68255/50623); (2,3,5/11←J cap 68255/50623). -/
noncomputable def compFam_1_3_4_4_6_6_15 : ComposedFam :=
  ⟨[
    ⟨1, 0, 5, 3, [(1, (803 / 2139))]⟩,
    ⟨1, 2, 25, 39, [(1, (68255 / 50623))]⟩,
    ⟨1, 2, 25, 47, [(1, (68255 / 50623))]⟩,
    ⟨1, 2, 5, 11, [(1, (68255 / 50623))]⟩
  ]⟩

theorem compFamData_1_3_4_4_6_6_15 : ComposedFamData compFam_1_3_4_4_6_6_15 := by
  intro e he
  simp only [compFam_1_3_4_4_6_6_15, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_4_6_6_15

/-- Box (1, 3, 4, 5, 5, 5, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 8 of the box's 193 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 193).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 5, 5, 7), (7,1,13/3←J cap 1870/13113); (7,2,65/31←J cap 55/117); (7,2,5/3←J cap 55/117); (7,2,65/47←J cap 55/117). -/
noncomputable def compFam_1_3_4_5_5_5_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩,
    ⟨6, 1, 65, 31, [(6, (55 / 117))]⟩,
    ⟨6, 1, 5, 3, [(6, (55 / 117))]⟩,
    ⟨6, 1, 65, 47, [(6, (55 / 117))]⟩
  ]⟩

theorem compFamData_1_3_4_5_5_5_7 : ComposedFamData compFam_1_3_4_5_5_5_7 := by
  intro e he
  simp only [compFam_1_3_4_5_5_5_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_5_5_7

/-- Box (1, 3, 4, 5, 5, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 2364 of the box's 158746 word deaths; the box's honest residual is 9883 derived-only deaths (chain-side coverable total: 148863).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 5, 6, 7), (7,5,1/1←J cap 1089/1519); (7,4,1/1←J cap 33/49); (6,4,1/1←J cap 8415/10199); (7,1,27/5←J cap 1/7). -/
noncomputable def compFam_1_3_4_5_5_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 4, 1, 1, [(6, (1089 / 1519))]⟩,
    ⟨6, 3, 1, 1, [(6, (33 / 49))]⟩,
    ⟨5, 3, 1, 1, [(5, (8415 / 10199))]⟩,
    ⟨6, 0, 27, 5, [(6, (1 / 7))]⟩
  ]⟩

theorem compFamData_1_3_4_5_5_6_7 : ComposedFamData compFam_1_3_4_5_5_6_7 := by
  intro e he
  simp only [compFam_1_3_4_5_5_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_5_6_7

/-- Box (1, 3, 4, 5, 5, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 20 of the box's 871 word deaths; the box's honest residual is 7 derived-only deaths (chain-side coverable total: 864).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 5, 7, 7), (5,1,49/15←J cap 18/91); (7,1,13/3←J cap 594/4277); (5,2,49/31←J cap 9537/16399); (5,2,49/39←J cap 9537/16399). -/
noncomputable def compFam_1_3_4_5_5_7_7 : ComposedFam :=
  ⟨[
    ⟨4, 0, 49, 15, [(4, (18 / 91))]⟩,
    ⟨6, 0, 13, 3, [(6, (594 / 4277))]⟩,
    ⟨4, 1, 49, 31, [(4, (9537 / 16399))]⟩,
    ⟨4, 1, 49, 39, [(4, (9537 / 16399))]⟩
  ]⟩

theorem compFamData_1_3_4_5_5_7_7 : ComposedFamData compFam_1_3_4_5_5_7_7 := by
  intro e he
  simp only [compFam_1_3_4_5_5_7_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_5_7_7

/-- Box (1, 3, 4, 5, 5, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 1686 of the box's 72915 word deaths; the box's honest residual is 3628 derived-only deaths (chain-side coverable total: 69287).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 5, 7, 8), (7,5,1/1←J cap 33/47); (5,1,13/3←J cap 18/91); (5,2,5/3←J cap 357/611); (5,2,65/47←J cap 357/611). -/
noncomputable def compFam_1_3_4_5_5_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 4, 1, 1, [(6, (33 / 47))]⟩,
    ⟨4, 0, 13, 3, [(4, (18 / 91))]⟩,
    ⟨4, 1, 5, 3, [(4, (357 / 611))]⟩,
    ⟨4, 1, 65, 47, [(4, (357 / 611))]⟩
  ]⟩

theorem compFamData_1_3_4_5_5_7_8 : ComposedFamData compFam_1_3_4_5_5_7_8 := by
  intro e he
  simp only [compFam_1_3_4_5_5_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_5_7_8

/-- Box (1, 3, 4, 5, 5, 7, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 122 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 122).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 5, 7, 9), (5,1,49/15←J cap 32670/173383); (5,2,49/31←J cap 277695/479353); (5,2,49/39←J cap 277695/479353); (5,2,49/47←J cap 277695/479353). -/
noncomputable def compFam_1_3_4_5_5_7_9 : ComposedFam :=
  ⟨[
    ⟨4, 0, 49, 15, [(4, (32670 / 173383))]⟩,
    ⟨4, 1, 49, 31, [(4, (277695 / 479353))]⟩,
    ⟨4, 1, 49, 39, [(4, (277695 / 479353))]⟩,
    ⟨4, 1, 49, 47, [(4, (277695 / 479353))]⟩
  ]⟩

theorem compFamData_1_3_4_5_5_7_9 : ComposedFamData compFam_1_3_4_5_5_7_9 := by
  intro e he
  simp only [compFam_1_3_4_5_5_7_9, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_5_7_9

/-- Box (1, 3, 4, 5, 6, 6, 7): the top-8 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 8 records account for 8 of the box's 110 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 110).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 6, 7), (7,1,13/3←J cap 1/7); (7,2,65/31←J cap 99/235); (7,2,5/3←J cap 99/235); (7,2,65/47←J cap 99/235); (7,3,5/3←J cap 363/611); (7,3,65/47←J cap 363/611); (7,3,13/11←J cap 363/611); (7,3,65/63←J cap 363/611). -/
noncomputable def compFam_1_3_4_5_6_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩,
    ⟨6, 1, 65, 31, [(6, (99 / 235))]⟩,
    ⟨6, 1, 5, 3, [(6, (99 / 235))]⟩,
    ⟨6, 1, 65, 47, [(6, (99 / 235))]⟩,
    ⟨6, 2, 5, 3, [(6, (363 / 611))]⟩,
    ⟨6, 2, 65, 47, [(6, (363 / 611))]⟩,
    ⟨6, 2, 13, 11, [(6, (363 / 611))]⟩,
    ⟨6, 2, 65, 63, [(6, (363 / 611))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_6_7 : ComposedFamData compFam_1_3_4_5_6_6_7 := by
  intro e he
  simp only [compFam_1_3_4_5_6_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_6_7

/-- Box (1, 3, 4, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 7992 of the box's 369531 word deaths; the box's honest residual is 29498 derived-only deaths (chain-side coverable total: 340033).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 6, 8), (6,1,73/15←J cap 54/329); (6,2,73/47←J cap 27/47); (6,3,73/55←J cap 7425/10199); (6,3,73/63←J cap 7425/10199). -/
noncomputable def compFam_1_3_4_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (54 / 329))]⟩,
    ⟨5, 1, 73, 47, [(5, (27 / 47))]⟩,
    ⟨5, 2, 73, 55, [(5, (7425 / 10199))]⟩,
    ⟨5, 2, 73, 63, [(5, (7425 / 10199))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_6_8 : ComposedFamData compFam_1_3_4_5_6_6_8 := by
  intro e he
  simp only [compFam_1_3_4_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_6_8

/-- Box (1, 3, 4, 5, 6, 6, 15): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 48 of the box's 2165 word deaths; the box's honest residual is 12 derived-only deaths (chain-side coverable total: 2153).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 6, 15), (2,1,5/3←J cap 803/2139); (3,1,11/5←J cap 97/345); (2,3,25/39←J cap 68255/50623); (2,3,25/47←J cap 68255/50623). -/
noncomputable def compFam_1_3_4_5_6_6_15 : ComposedFam :=
  ⟨[
    ⟨1, 0, 5, 3, [(1, (803 / 2139))]⟩,
    ⟨2, 0, 11, 5, [(2, (97 / 345))]⟩,
    ⟨1, 2, 25, 39, [(1, (68255 / 50623))]⟩,
    ⟨1, 2, 25, 47, [(1, (68255 / 50623))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_6_15 : ComposedFamData compFam_1_3_4_5_6_6_15 := by
  intro e he
  simp only [compFam_1_3_4_5_6_6_15, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_6_15

/-- Box (1, 3, 4, 5, 6, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 1449 of the box's 86778 word deaths; the box's honest residual is 4270 derived-only deaths (chain-side coverable total: 82508).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 7, 7), (5,3,1/1←J cap 17/23); (6,3,1/1←J cap 25/39); (7,3,1/1←J cap 363/611); (3,1,49/15←J cap 1353/4991). -/
noncomputable def compFam_1_3_4_5_6_7_7 : ComposedFam :=
  ⟨[
    ⟨4, 2, 1, 1, [(4, (17 / 23))]⟩,
    ⟨5, 2, 1, 1, [(5, (25 / 39))]⟩,
    ⟨6, 2, 1, 1, [(6, (363 / 611))]⟩,
    ⟨2, 0, 49, 15, [(2, (1353 / 4991))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_7_7 : ComposedFamData compFam_1_3_4_5_6_7_7 := by
  intro e he
  simp only [compFam_1_3_4_5_6_7_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_7_7

/-- Box (1, 3, 4, 5, 6, 7, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 1741 of the box's 141056 word deaths; the box's honest residual is 8552 derived-only deaths (chain-side coverable total: 132504).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 7, 9), (7,4,1/1←J cap 825/1457); (7,5,1/1←J cap 15895/22103); (6,4,1/1←J cap 18750/25823); (7,1,7/1←J cap 2/17). -/
noncomputable def compFam_1_3_4_5_6_7_9 : ComposedFam :=
  ⟨[
    ⟨6, 3, 1, 1, [(6, (825 / 1457))]⟩,
    ⟨6, 4, 1, 1, [(6, (15895 / 22103))]⟩,
    ⟨5, 3, 1, 1, [(5, (18750 / 25823))]⟩,
    ⟨6, 0, 7, 1, [(6, (2 / 17))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_7_9 : ComposedFamData compFam_1_3_4_5_6_7_9 := by
  intro e he
  simp only [compFam_1_3_4_5_6_7_9, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_7_9

/-- Box (1, 3, 4, 5, 6, 7, 15): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 64 of the box's 4046 word deaths; the box's honest residual is 48 derived-only deaths (chain-side coverable total: 3998).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 7, 15), (2,1,5/3←J cap 110/299); (2,3,25/39←J cap 969/713); (2,3,25/47←J cap 969/713); (2,3,5/11←J cap 969/713). -/
noncomputable def compFam_1_3_4_5_6_7_15 : ComposedFam :=
  ⟨[
    ⟨1, 0, 5, 3, [(1, (110 / 299))]⟩,
    ⟨1, 2, 25, 39, [(1, (969 / 713))]⟩,
    ⟨1, 2, 25, 47, [(1, (969 / 713))]⟩,
    ⟨1, 2, 5, 11, [(1, (969 / 713))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_7_15 : ComposedFamData compFam_1_3_4_5_6_7_15 := by
  intro e he
  simp only [compFam_1_3_4_5_6_7_15, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_7_15

/-- Box (1, 3, 4, 5, 6, 7, 16): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 8 of the box's 343 word deaths; the box's honest residual is 2 derived-only deaths (chain-side coverable total: 341).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 7, 16), (5,1,19/5←J cap 3650/22103); (5,2,57/31←J cap 72270/154721); (5,2,19/13←J cap 72270/154721); (5,2,57/47←J cap 72270/154721). -/
noncomputable def compFam_1_3_4_5_6_7_16 : ComposedFam :=
  ⟨[
    ⟨4, 0, 19, 5, [(4, (3650 / 22103))]⟩,
    ⟨4, 1, 57, 31, [(4, (72270 / 154721))]⟩,
    ⟨4, 1, 19, 13, [(4, (72270 / 154721))]⟩,
    ⟨4, 1, 57, 47, [(4, (72270 / 154721))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_7_16 : ComposedFamData compFam_1_3_4_5_6_7_16 := by
  intro e he
  simp only [compFam_1_3_4_5_6_7_16, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_7_16

/-- Box (1, 3, 4, 5, 6, 8, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 180 of the box's 5005 word deaths; the box's honest residual is 6 derived-only deaths (chain-side coverable total: 4999).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 6, 8, 9), (6,1,73/15←J cap 9826/74865); (6,2,73/31←J cap 17/47); (6,2,73/39←J cap 17/47); (6,2,73/47←J cap 17/47). -/
noncomputable def compFam_1_3_4_5_6_8_9 : ComposedFam :=
  ⟨[
    ⟨5, 0, 73, 15, [(5, (9826 / 74865))]⟩,
    ⟨5, 1, 73, 31, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 39, [(5, (17 / 47))]⟩,
    ⟨5, 1, 73, 47, [(5, (17 / 47))]⟩
  ]⟩

theorem compFamData_1_3_4_5_6_8_9 : ComposedFamData compFam_1_3_4_5_6_8_9 := by
  intro e he
  simp only [compFam_1_3_4_5_6_8_9, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_6_8_9

/-- Box (1, 3, 4, 5, 7, 7, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 223 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 223).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 7, 7, 7), (4,1,49/15←J cap 18/91); (6,1,13/3←J cap 4158/28717); (7,1,13/3←J cap 594/4277); (4,2,49/31←J cap 3/5). -/
noncomputable def compFam_1_3_4_5_7_7_7 : ComposedFam :=
  ⟨[
    ⟨3, 0, 49, 15, [(3, (18 / 91))]⟩,
    ⟨5, 0, 13, 3, [(5, (4158 / 28717))]⟩,
    ⟨6, 0, 13, 3, [(6, (594 / 4277))]⟩,
    ⟨3, 1, 49, 31, [(3, (3 / 5))]⟩
  ]⟩

theorem compFamData_1_3_4_5_7_7_7 : ComposedFamData compFam_1_3_4_5_7_7_7 := by
  intro e he
  simp only [compFam_1_3_4_5_7_7_7, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_7_7_7

/-- Box (1, 3, 4, 5, 7, 7, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 126 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 126).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 4, 5, 7, 7, 9), (6,1,13/3←J cap 594/4277); (6,2,65/31←J cap 99/235); (6,2,5/3←J cap 99/235); (6,2,65/47←J cap 99/235). -/
noncomputable def compFam_1_3_4_5_7_7_9 : ComposedFam :=
  ⟨[
    ⟨5, 0, 13, 3, [(5, (594 / 4277))]⟩,
    ⟨5, 1, 65, 31, [(5, (99 / 235))]⟩,
    ⟨5, 1, 5, 3, [(5, (99 / 235))]⟩,
    ⟨5, 1, 65, 47, [(5, (99 / 235))]⟩
  ]⟩

theorem compFamData_1_3_4_5_7_7_9 : ComposedFamData compFam_1_3_4_5_7_7_9 := by
  intro e he
  simp only [compFam_1_3_4_5_7_7_9, List.mem_cons] at he
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

#print axioms compFamData_1_3_4_5_7_7_9

/-- Box (1, 3, 5, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 48 of the box's 1973 word deaths; the box's honest residual is 1 derived-only deaths (chain-side coverable total: 1972).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 5, 6, 6, 8), (2,1,11/5←J cap 67650/234577); (4,1,49/15←J cap 26950/135501); (2,3,33/47←J cap 304425/234577); (2,3,3/5←J cap 304425/234577). -/
noncomputable def compFam_1_3_5_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨1, 0, 11, 5, [(1, (67650 / 234577))]⟩,
    ⟨3, 0, 49, 15, [(3, (26950 / 135501))]⟩,
    ⟨1, 2, 33, 47, [(1, (304425 / 234577))]⟩,
    ⟨1, 2, 3, 5, [(1, (304425 / 234577))]⟩
  ]⟩

theorem compFamData_1_3_5_5_6_6_8 : ComposedFamData compFam_1_3_5_5_6_6_8 := by
  intro e he
  simp only [compFam_1_3_5_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_5_6_6_8

/-- Box (1, 3, 5, 5, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 44 of the box's 1650 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 1650).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 5, 6, 7, 8), (7,1,73/15←J cap 242/1833); (7,2,73/31←J cap 99/235); (7,2,73/39←J cap 99/235); (7,2,73/47←J cap 99/235). -/
noncomputable def compFam_1_3_5_5_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (242 / 1833))]⟩,
    ⟨6, 1, 73, 31, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 39, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 47, [(6, (99 / 235))]⟩
  ]⟩

theorem compFamData_1_3_5_5_6_7_8 : ComposedFamData compFam_1_3_5_5_6_7_8 := by
  intro e he
  simp only [compFam_1_3_5_5_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_5_6_7_8

/-- Box (1, 3, 5, 6, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 12 of the box's 400 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 400).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 6, 6, 7, 8), (7,1,73/15←J cap 6/47); (7,2,73/31←J cap 99/235); (7,2,73/39←J cap 99/235); (7,2,73/47←J cap 99/235). -/
noncomputable def compFam_1_3_5_6_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩,
    ⟨6, 1, 73, 31, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 39, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 47, [(6, (99 / 235))]⟩
  ]⟩

theorem compFamData_1_3_5_6_6_7_8 : ComposedFamData compFam_1_3_5_6_6_7_8 := by
  intro e he
  simp only [compFam_1_3_5_6_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_6_6_7_8

/-- Box (1, 3, 5, 6, 6, 8, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 128 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 128).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 6, 6, 8, 8), (7,1,73/15←J cap 726/5875); (7,2,73/31←J cap 99/235); (7,2,73/39←J cap 99/235); (7,2,73/47←J cap 99/235). -/
noncomputable def compFam_1_3_5_6_6_8_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (726 / 5875))]⟩,
    ⟨6, 1, 73, 31, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 39, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 47, [(6, (99 / 235))]⟩
  ]⟩

theorem compFamData_1_3_5_6_6_8_8 : ComposedFamData compFam_1_3_5_6_6_8_8 := by
  intro e he
  simp only [compFam_1_3_5_6_6_8_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_6_6_8_8

/-- Box (1, 3, 5, 6, 7, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 128 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 128).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 6, 7, 7, 8), (7,1,73/15←J cap 50/403); (7,2,73/31←J cap 99/235); (7,2,73/39←J cap 99/235); (7,2,73/47←J cap 99/235). -/
noncomputable def compFam_1_3_5_6_7_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (50 / 403))]⟩,
    ⟨6, 1, 73, 31, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 39, [(6, (99 / 235))]⟩,
    ⟨6, 1, 73, 47, [(6, (99 / 235))]⟩
  ]⟩

theorem compFamData_1_3_5_6_7_7_8 : ComposedFamData compFam_1_3_5_6_7_7_8 := by
  intro e he
  simp only [compFam_1_3_5_6_7_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_6_7_7_8

/-- Box (1, 3, 5, 6, 7, 8, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 68 of the box's 2270 word deaths; the box's honest residual is 2 derived-only deaths (chain-side coverable total: 2268).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 3, 5, 6, 7, 8, 8), (3,1,49/15←J cap 98/465); (3,2,49/39←J cap 24255/33511); (3,2,49/47←J cap 24255/33511); (3,4,7/9←J cap 40425/33511). -/
noncomputable def compFam_1_3_5_6_7_8_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (98 / 465))]⟩,
    ⟨2, 1, 49, 39, [(2, (24255 / 33511))]⟩,
    ⟨2, 1, 49, 47, [(2, (24255 / 33511))]⟩,
    ⟨2, 3, 7, 9, [(2, (40425 / 33511))]⟩
  ]⟩

theorem compFamData_1_3_5_6_7_8_8 : ComposedFamData compFam_1_3_5_6_7_8_8 := by
  intro e he
  simp only [compFam_1_3_5_6_7_8_8, List.mem_cons] at he
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

#print axioms compFamData_1_3_5_6_7_8_8

/-- Box (1, 4, 4, 5, 5, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 438 of the box's 19752 word deaths; the box's honest residual is 768 derived-only deaths (chain-side coverable total: 18984).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 4, 5, 5, 6, 7), (6,3,1/1←J cap 7425/10199); (7,3,1/1←J cap 25/39); (3,1,49/15←J cap 578/2415); (3,2,49/47←J cap 6545/7254). -/
noncomputable def compFam_1_4_4_5_5_6_7 : ComposedFam :=
  ⟨[
    ⟨5, 2, 1, 1, [(5, (7425 / 10199))]⟩,
    ⟨6, 2, 1, 1, [(6, (25 / 39))]⟩,
    ⟨2, 0, 49, 15, [(2, (578 / 2415))]⟩,
    ⟨2, 1, 49, 47, [(2, (6545 / 7254))]⟩
  ]⟩

theorem compFamData_1_4_4_5_5_6_7 : ComposedFamData compFam_1_4_4_5_5_6_7 := by
  intro e he
  simp only [compFam_1_4_4_5_5_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_4_4_5_5_6_7

/-- Box (1, 4, 4, 5, 5, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 136 of the box's 6966 word deaths; the box's honest residual is 28 derived-only deaths (chain-side coverable total: 6938).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 4, 5, 5, 6, 8), (7,1,73/15←J cap 2/15); (7,2,73/39←J cap 15895/33511); (7,2,73/47←J cap 15895/33511); (7,2,73/55←J cap 15895/33511). -/
noncomputable def compFam_1_4_4_5_5_6_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (2 / 15))]⟩,
    ⟨6, 1, 73, 39, [(6, (15895 / 33511))]⟩,
    ⟨6, 1, 73, 47, [(6, (15895 / 33511))]⟩,
    ⟨6, 1, 73, 55, [(6, (15895 / 33511))]⟩
  ]⟩

theorem compFamData_1_4_4_5_5_6_8 : ComposedFamData compFam_1_4_4_5_5_6_8 := by
  intro e he
  simp only [compFam_1_4_4_5_5_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_4_4_5_5_6_8

/-- Box (1, 4, 4, 5, 6, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 20 of the box's 522 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 522).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 4, 5, 6, 6, 7), (7,1,13/3←J cap 1/7); (7,2,5/3←J cap 3179/5499); (7,2,65/47←J cap 3179/5499); (7,2,13/11←J cap 3179/5499). -/
noncomputable def compFam_1_4_4_5_6_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩,
    ⟨6, 1, 5, 3, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 65, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 13, 11, [(6, (3179 / 5499))]⟩
  ]⟩

theorem compFamData_1_4_4_5_6_6_7 : ComposedFamData compFam_1_4_4_5_6_6_7 := by
  intro e he
  simp only [compFam_1_4_4_5_6_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_4_4_5_6_6_7

/-- Box (1, 4, 4, 5, 6, 6, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 64 of the box's 4301 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 4301).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 4, 5, 6, 6, 8), (2,1,11/5←J cap 2/7); (3,1,41/15←J cap 1666/7285); (4,1,49/15←J cap 294/1457); (6,1,19/5←J cap 54/329). -/
noncomputable def compFam_1_4_4_5_6_6_8 : ComposedFam :=
  ⟨[
    ⟨1, 0, 11, 5, [(1, (2 / 7))]⟩,
    ⟨2, 0, 41, 15, [(2, (1666 / 7285))]⟩,
    ⟨3, 0, 49, 15, [(3, (294 / 1457))]⟩,
    ⟨5, 0, 19, 5, [(5, (54 / 329))]⟩
  ]⟩

theorem compFamData_1_4_4_5_6_6_8 : ComposedFamData compFam_1_4_4_5_6_6_8 := by
  intro e he
  simp only [compFam_1_4_4_5_6_6_8, List.mem_cons] at he
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

#print axioms compFamData_1_4_4_5_6_6_8

/-- Box (1, 4, 5, 5, 5, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 16 of the box's 417 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 417).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 5, 6, 7), (7,1,13/3←J cap 50/351); (7,2,5/3←J cap 23375/41067); (7,2,65/47←J cap 23375/41067); (7,2,13/11←J cap 23375/41067). -/
noncomputable def compFam_1_4_5_5_5_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (50 / 351))]⟩,
    ⟨6, 1, 5, 3, [(6, (23375 / 41067))]⟩,
    ⟨6, 1, 65, 47, [(6, (23375 / 41067))]⟩,
    ⟨6, 1, 13, 11, [(6, (23375 / 41067))]⟩
  ]⟩

theorem compFamData_1_4_5_5_5_6_7 : ComposedFamData compFam_1_4_5_5_5_6_7 := by
  intro e he
  simp only [compFam_1_4_5_5_5_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_4_5_5_5_6_7

/-- Box (1, 4, 5, 5, 6, 6, 7): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 20 of the box's 538 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 538).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 6, 6, 7), (7,1,13/3←J cap 1870/13113); (7,2,5/3←J cap 3179/5499); (7,2,65/47←J cap 3179/5499); (7,2,13/11←J cap 3179/5499). -/
noncomputable def compFam_1_4_5_5_6_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩,
    ⟨6, 1, 5, 3, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 65, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 13, 11, [(6, (3179 / 5499))]⟩
  ]⟩

theorem compFamData_1_4_5_5_6_6_7 : ComposedFamData compFam_1_4_5_5_6_6_7 := by
  intro e he
  simp only [compFam_1_4_5_5_6_6_7, List.mem_cons] at he
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

#print axioms compFamData_1_4_5_5_6_6_7

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

/-- Box (1, 4, 5, 5, 6, 7, 9): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 134 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 134).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 5, 6, 7, 9), (4,1,49/15←J cap 98/527); (4,2,49/39←J cap 245/341); (4,2,49/47←J cap 245/341); (4,2,49/55←J cap 245/341). -/
noncomputable def compFam_1_4_5_5_6_7_9 : ComposedFam :=
  ⟨[
    ⟨3, 0, 49, 15, [(3, (98 / 527))]⟩,
    ⟨3, 1, 49, 39, [(3, (245 / 341))]⟩,
    ⟨3, 1, 49, 47, [(3, (245 / 341))]⟩,
    ⟨3, 1, 49, 55, [(3, (245 / 341))]⟩
  ]⟩

theorem compFamData_1_4_5_5_6_7_9 : ComposedFamData compFam_1_4_5_5_6_7_9 := by
  intro e he
  simp only [compFam_1_4_5_5_6_7_9, List.mem_cons] at he
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

#print axioms compFamData_1_4_5_5_6_7_9

/-- Box (1, 4, 5, 6, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 40 of the box's 1145 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 1145).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 4, 5, 6, 6, 7, 8), (7,1,73/15←J cap 6/47); (7,2,73/47←J cap 27/47); (7,2,73/55←J cap 27/47); (7,2,73/63←J cap 27/47). -/
noncomputable def compFam_1_4_5_6_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩,
    ⟨6, 1, 73, 47, [(6, (27 / 47))]⟩,
    ⟨6, 1, 73, 55, [(6, (27 / 47))]⟩,
    ⟨6, 1, 73, 63, [(6, (27 / 47))]⟩
  ]⟩

theorem compFamData_1_4_5_6_6_7_8 : ComposedFamData compFam_1_4_5_6_6_7_8 := by
  intro e he
  simp only [compFam_1_4_5_6_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_4_5_6_6_7_8

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

/-- Box (1, 5, 5, 5, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 28 of the box's 861 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 861).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 5, 5, 5, 6, 7, 8), (7,1,73/15←J cap 6358/49491); (7,2,73/47←J cap 3179/5499); (7,2,73/55←J cap 3179/5499); (7,2,73/63←J cap 3179/5499). -/
noncomputable def compFam_1_5_5_5_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6358 / 49491))]⟩,
    ⟨6, 1, 73, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 55, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 63, [(6, (3179 / 5499))]⟩
  ]⟩

theorem compFamData_1_5_5_5_6_7_8 : ComposedFamData compFam_1_5_5_5_6_7_8 := by
  intro e he
  simp only [compFam_1_5_5_5_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_5_5_5_6_7_8

/-- Box (1, 5, 5, 6, 6, 7, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 40 of the box's 1181 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 1181).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 5, 5, 6, 6, 7, 8), (7,1,73/15←J cap 6/47); (7,2,73/47←J cap 3179/5499); (7,2,73/55←J cap 3179/5499); (7,2,73/63←J cap 3179/5499). -/
noncomputable def compFam_1_5_5_6_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩,
    ⟨6, 1, 73, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 55, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 63, [(6, (3179 / 5499))]⟩
  ]⟩

theorem compFamData_1_5_5_6_6_7_8 : ComposedFamData compFam_1_5_5_6_6_7_8 := by
  intro e he
  simp only [compFam_1_5_5_6_6_7_8, List.mem_cons] at he
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

#print axioms compFamData_1_5_5_6_6_7_8

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

/-- Box (1, 5, 5, 6, 7, 8, 8): the top-4 composed family from `joinedge_perbox_v1.jsonl` (by death count, among the demands with a conflicting chain-side cap: J-side caps are implied by every W₀ chain's closed table, box-side caps hold on the whole box).  The family's 4 records account for 4 of the box's 146 word deaths; the box's honest residual is 0 derived-only deaths (chain-side coverable total: 146).  Datum per record: `A·C ≤ B·D` (dump `conflict` flag, kernel-checked by `norm_num` below).  Provenance: `joinedge_perbox_v1.jsonl` BOX (1, 5, 5, 6, 7, 8, 8), (3,1,49/15←J cap 311542/1639125); (3,2,49/47←J cap 155771/170469); (3,2,49/55←J cap 155771/170469); (3,2,7/9←J cap 155771/170469). -/
noncomputable def compFam_1_5_5_6_7_8_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (311542 / 1639125))]⟩,
    ⟨2, 1, 49, 47, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 49, 55, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 7, 9, [(2, (155771 / 170469))]⟩
  ]⟩

theorem compFamData_1_5_5_6_7_8_8 : ComposedFamData compFam_1_5_5_6_7_8_8 := by
  intro e he
  simp only [compFam_1_5_5_6_7_8_8, List.mem_cons] at he
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

#print axioms compFamData_1_5_5_6_7_8_8
/-- The covered set: the 68 one-sided boxes with an instantiated composed family (every box of `joinedge_perbox_v1.jsonl`'s one-sided census that this file instantiates). -/
def coveredSet : Finset (Fin 7 → ℤ) :=
  {![1, 2, 3, 4, 4, 5, 7],
   ![1, 2, 3, 4, 4, 6, 7],
   ![1, 2, 3, 4, 5, 5, 7],
   ![1, 2, 3, 4, 5, 7, 7],
   ![1, 2, 3, 4, 5, 7, 8],
   ![1, 2, 3, 4, 6, 6, 8],
   ![1, 2, 3, 4, 6, 7, 8],
   ![1, 2, 3, 5, 6, 6, 8],
   ![1, 2, 4, 4, 6, 6, 8],
   ![1, 2, 4, 5, 6, 6, 8],
   ![1, 3, 3, 4, 4, 5, 7],
   ![1, 3, 3, 4, 4, 6, 7],
   ![1, 3, 3, 4, 5, 5, 7],
   ![1, 3, 3, 4, 5, 6, 7],
   ![1, 3, 3, 4, 5, 6, 8],
   ![1, 3, 3, 4, 5, 7, 8],
   ![1, 3, 3, 4, 6, 6, 8],
   ![1, 3, 3, 4, 6, 7, 8],
   ![1, 3, 3, 5, 5, 6, 8],
   ![1, 3, 3, 5, 6, 6, 8],
   ![1, 3, 3, 5, 6, 7, 8],
   ![1, 3, 3, 5, 6, 8, 8],
   ![1, 3, 3, 5, 6, 8, 9],
   ![1, 3, 4, 4, 5, 5, 7],
   ![1, 3, 4, 4, 5, 6, 8],
   ![1, 3, 4, 4, 5, 7, 7],
   ![1, 3, 4, 4, 6, 6, 8],
   ![1, 3, 4, 4, 6, 6, 15],
   ![1, 3, 4, 5, 5, 5, 7],
   ![1, 3, 4, 5, 5, 6, 7],
   ![1, 3, 4, 5, 5, 7, 7],
   ![1, 3, 4, 5, 5, 7, 8],
   ![1, 3, 4, 5, 5, 7, 9],
   ![1, 3, 4, 5, 6, 6, 7],
   ![1, 3, 4, 5, 6, 6, 8],
   ![1, 3, 4, 5, 6, 6, 15],
   ![1, 3, 4, 5, 6, 7, 7],
   ![1, 3, 4, 5, 6, 7, 9],
   ![1, 3, 4, 5, 6, 7, 15],
   ![1, 3, 4, 5, 6, 7, 16],
   ![1, 3, 4, 5, 6, 8, 9],
   ![1, 3, 4, 5, 7, 7, 7],
   ![1, 3, 4, 5, 7, 7, 9],
   ![1, 3, 5, 5, 6, 6, 8],
   ![1, 3, 5, 5, 6, 7, 8],
   ![1, 3, 5, 6, 6, 7, 8],
   ![1, 3, 5, 6, 6, 8, 8],
   ![1, 3, 5, 6, 7, 7, 8],
   ![1, 3, 5, 6, 7, 8, 8],
   ![1, 4, 4, 5, 5, 6, 7],
   ![1, 4, 4, 5, 5, 6, 8],
   ![1, 4, 4, 5, 6, 6, 7],
   ![1, 4, 4, 5, 6, 6, 8],
   ![1, 4, 5, 5, 5, 6, 7],
   ![1, 4, 5, 5, 6, 6, 7],
   ![1, 4, 5, 5, 6, 6, 8],
   ![1, 4, 5, 5, 6, 7, 7],
   ![1, 4, 5, 5, 6, 7, 8],
   ![1, 4, 5, 5, 6, 7, 9],
   ![1, 4, 5, 6, 6, 7, 8],
   ![1, 4, 5, 6, 6, 7, 9],
   ![1, 4, 5, 6, 6, 7, 11],
   ![1, 4, 5, 6, 7, 8, 8],
   ![1, 4, 5, 6, 7, 8, 9],
   ![1, 5, 5, 5, 6, 7, 8],
   ![1, 5, 5, 6, 6, 7, 8],
   ![1, 5, 5, 6, 7, 7, 8],
   ![1, 5, 5, 6, 7, 8, 8]}

/-- The per-box family dispatch (definition on the covered set, the empty family off it). -/
noncomputable def compFamOf (b : Fin 7 → ℤ) : ComposedFam :=
  if b = (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) then compFam_1_2_3_4_4_5_7
  else if b = (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) then compFam_1_2_3_4_4_6_7
  else if b = (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) then compFam_1_2_3_4_5_5_7
  else if b = (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) then compFam_1_2_3_4_5_7_7
  else if b = (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) then compFam_1_2_3_4_5_7_8
  else if b = (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_2_3_4_6_6_8
  else if b = (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_2_3_4_6_7_8
  else if b = (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_2_3_5_6_6_8
  else if b = (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_2_4_4_6_6_8
  else if b = (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_2_4_5_6_6_8
  else if b = (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) then compFam_1_3_3_4_4_5_7
  else if b = (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) then compFam_1_3_3_4_4_6_7
  else if b = (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) then compFam_1_3_3_4_5_5_7
  else if b = (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) then compFam_1_3_3_4_5_6_7
  else if b = (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) then compFam_1_3_3_4_5_6_8
  else if b = (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) then compFam_1_3_3_4_5_7_8
  else if b = (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_3_3_4_6_6_8
  else if b = (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_3_3_4_6_7_8
  else if b = (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) then compFam_1_3_3_5_5_6_8
  else if b = (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_3_3_5_6_6_8
  else if b = (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_3_3_5_6_7_8
  else if b = (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) then compFam_1_3_3_5_6_8_8
  else if b = (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) then compFam_1_3_3_5_6_8_9
  else if b = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) then compFam_1_3_4_4_5_5_7
  else if b = (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) then compFam_1_3_4_4_5_6_8
  else if b = (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) then compFam_1_3_4_4_5_7_7
  else if b = (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_3_4_4_6_6_8
  else if b = (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) then compFam_1_3_4_4_6_6_15
  else if b = (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_5_5_7
  else if b = (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_5_6_7
  else if b = (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_5_7_7
  else if b = (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) then compFam_1_3_4_5_5_7_8
  else if b = (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) then compFam_1_3_4_5_5_7_9
  else if b = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_6_6_7
  else if b = (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_3_4_5_6_6_8
  else if b = (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) then compFam_1_3_4_5_6_6_15
  else if b = (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_6_7_7
  else if b = (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) then compFam_1_3_4_5_6_7_9
  else if b = (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) then compFam_1_3_4_5_6_7_15
  else if b = (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) then compFam_1_3_4_5_6_7_16
  else if b = (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) then compFam_1_3_4_5_6_8_9
  else if b = (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) then compFam_1_3_4_5_7_7_7
  else if b = (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) then compFam_1_3_4_5_7_7_9
  else if b = (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_3_5_5_6_6_8
  else if b = (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_3_5_5_6_7_8
  else if b = (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_3_5_6_6_7_8
  else if b = (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) then compFam_1_3_5_6_6_8_8
  else if b = (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) then compFam_1_3_5_6_7_7_8
  else if b = (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then compFam_1_3_5_6_7_8_8
  else if b = (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) then compFam_1_4_4_5_5_6_7
  else if b = (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) then compFam_1_4_4_5_5_6_8
  else if b = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then compFam_1_4_4_5_6_6_7
  else if b = (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_4_4_5_6_6_8
  else if b = (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) then compFam_1_4_5_5_5_6_7
  else if b = (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) then compFam_1_4_5_5_6_6_7
  else if b = (![1, 4, 5, 5, 6, 6, 8] : Fin 7 → ℤ) then compFam_1_4_5_5_6_6_8
  else if b = (![1, 4, 5, 5, 6, 7, 7] : Fin 7 → ℤ) then compFam_1_4_5_5_6_7_7
  else if b = (![1, 4, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_4_5_5_6_7_8
  else if b = (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) then compFam_1_4_5_5_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_4_5_6_6_7_8
  else if b = (![1, 4, 5, 6, 6, 7, 9] : Fin 7 → ℤ) then compFam_1_4_5_6_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 11] : Fin 7 → ℤ) then compFam_1_4_5_6_6_7_11
  else if b = (![1, 4, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then compFam_1_4_5_6_7_8_8
  else if b = (![1, 4, 5, 6, 7, 8, 9] : Fin 7 → ℤ) then compFam_1_4_5_6_7_8_9
  else if b = (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_5_5_5_6_7_8
  else if b = (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then compFam_1_5_5_6_6_7_8
  else if b = (![1, 5, 5, 6, 7, 7, 8] : Fin 7 → ℤ) then compFam_1_5_5_6_7_7_8
  else if b = (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then compFam_1_5_5_6_7_8_8
  else ⟨[]⟩

/-- **The one-sided composed data totality** (deliverable): every box in `coveredSet` carries a valid `ComposedFamData` composed family from the joinedge dump. -/
theorem oneSidedTotalData : ∀ b ∈ coveredSet, ComposedFamData (compFamOf b) := by
  intro b hb
  simp only [coveredSet, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [compFamOf, compFamData_1_2_3_4_4_5_7]
  · simp [compFamOf, compFamData_1_2_3_4_4_6_7]
  · simp [compFamOf, compFamData_1_2_3_4_5_5_7]
  · simp [compFamOf, compFamData_1_2_3_4_5_7_7]
  · simp [compFamOf, compFamData_1_2_3_4_5_7_8]
  · simp [compFamOf, compFamData_1_2_3_4_6_6_8]
  · simp [compFamOf, compFamData_1_2_3_4_6_7_8]
  · simp [compFamOf, compFamData_1_2_3_5_6_6_8]
  · simp [compFamOf, compFamData_1_2_4_4_6_6_8]
  · simp [compFamOf, compFamData_1_2_4_5_6_6_8]
  · simp [compFamOf, compFamData_1_3_3_4_4_5_7]
  · simp [compFamOf, compFamData_1_3_3_4_4_6_7]
  · simp [compFamOf, compFamData_1_3_3_4_5_5_7]
  · simp [compFamOf, compFamData_1_3_3_4_5_6_7]
  · simp [compFamOf, compFamData_1_3_3_4_5_6_8]
  · simp [compFamOf, compFamData_1_3_3_4_5_7_8]
  · simp [compFamOf, compFamData_1_3_3_4_6_6_8]
  · simp [compFamOf, compFamData_1_3_3_4_6_7_8]
  · simp [compFamOf, compFamData_1_3_3_5_5_6_8]
  · simp [compFamOf, compFamData_1_3_3_5_6_6_8]
  · simp [compFamOf, compFamData_1_3_3_5_6_7_8]
  · simp [compFamOf, compFamData_1_3_3_5_6_8_8]
  · simp [compFamOf, compFamData_1_3_3_5_6_8_9]
  · simp [compFamOf, compFamData_1_3_4_4_5_5_7]
  · simp [compFamOf, compFamData_1_3_4_4_5_6_8]
  · simp [compFamOf, compFamData_1_3_4_4_5_7_7]
  · simp [compFamOf, compFamData_1_3_4_4_6_6_8]
  · simp [compFamOf, compFamData_1_3_4_4_6_6_15]
  · simp [compFamOf, compFamData_1_3_4_5_5_5_7]
  · simp [compFamOf, compFamData_1_3_4_5_5_6_7]
  · simp [compFamOf, compFamData_1_3_4_5_5_7_7]
  · simp [compFamOf, compFamData_1_3_4_5_5_7_8]
  · simp [compFamOf, compFamData_1_3_4_5_5_7_9]
  · simp [compFamOf, compFamData_1_3_4_5_6_6_7]
  · simp [compFamOf, compFamData_1_3_4_5_6_6_8]
  · simp [compFamOf, compFamData_1_3_4_5_6_6_15]
  · simp [compFamOf, compFamData_1_3_4_5_6_7_7]
  · simp [compFamOf, compFamData_1_3_4_5_6_7_9]
  · simp [compFamOf, compFamData_1_3_4_5_6_7_15]
  · simp [compFamOf, compFamData_1_3_4_5_6_7_16]
  · simp [compFamOf, compFamData_1_3_4_5_6_8_9]
  · simp [compFamOf, compFamData_1_3_4_5_7_7_7]
  · simp [compFamOf, compFamData_1_3_4_5_7_7_9]
  · simp [compFamOf, compFamData_1_3_5_5_6_6_8]
  · simp [compFamOf, compFamData_1_3_5_5_6_7_8]
  · simp [compFamOf, compFamData_1_3_5_6_6_7_8]
  · simp [compFamOf, compFamData_1_3_5_6_6_8_8]
  · simp [compFamOf, compFamData_1_3_5_6_7_7_8]
  · simp [compFamOf, compFamData_1_3_5_6_7_8_8]
  · simp [compFamOf, compFamData_1_4_4_5_5_6_7]
  · simp [compFamOf, compFamData_1_4_4_5_5_6_8]
  · simp [compFamOf, compFamData_1_4_4_5_6_6_7]
  · simp [compFamOf, compFamData_1_4_4_5_6_6_8]
  · simp [compFamOf, compFamData_1_4_5_5_5_6_7]
  · simp [compFamOf, compFamData_1_4_5_5_6_6_7]
  · simp [compFamOf, compFamData_1_4_5_5_6_6_8]
  · simp [compFamOf, compFamData_1_4_5_5_6_7_7]
  · simp [compFamOf, compFamData_1_4_5_5_6_7_8]
  · simp [compFamOf, compFamData_1_4_5_5_6_7_9]
  · simp [compFamOf, compFamData_1_4_5_6_6_7_8]
  · simp [compFamOf, compFamData_1_4_5_6_6_7_9]
  · simp [compFamOf, compFamData_1_4_5_6_6_7_11]
  · simp [compFamOf, compFamData_1_4_5_6_7_8_8]
  · simp [compFamOf, compFamData_1_4_5_6_7_8_9]
  · simp [compFamOf, compFamData_1_5_5_5_6_7_8]
  · simp [compFamOf, compFamData_1_5_5_6_6_7_8]
  · simp [compFamOf, compFamData_1_5_5_6_7_7_8]
  · simp [compFamOf, compFamData_1_5_5_6_7_8_8]

#print axioms oneSidedTotalData
end Fresh.OneSidedComposed
