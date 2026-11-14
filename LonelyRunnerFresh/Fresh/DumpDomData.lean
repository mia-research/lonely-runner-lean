import Fresh.CapChainsOfCarve

/-!
# DumpDomData: the joinedge2 strict-class families for the 11 strict-complete boxes,
and the honest verdict on `Fresh.CapChainsOfCarve.DumpDom`

Written 2026-11-13.  New file; nothing existing is edited.  Companion data file to
`Fresh.CapChainsOfCarve` (whose `DumpDom` / `CapsDom` / `capChainsRealized_of_dumpDom`
shapes are consumed verbatim) and `Fresh.ComposedFamData` (whose per-box record pattern
is mirrored, whose `compFam_<box>` literals are reused verbatim as the control).  Data:
`experiments/n8/onefast_audit/joinedge2_perbox_v1.jsonl` (73 boxes with domination
witnesses) + `joinedge2_census_v1.out`; the 11 boxes whose EVERY death row carries a
strict-complete (DumpDom-ready) cap are the census section 7 list [T 11/11].

## What the dump certifies (data side)

For each of the 11 boxes: every death row's cap is strict-complete, i.e. EVERY hop of
the cap walk is dominated either by an entry of the box-closure table `U0` (dump tag
`box(face_hi/face_lo/one/ord)`: the bound holds on the whole box) or by an entry of the
join of ALL enumerated W0 chains' closed tables (dump tag `J`: the bound is implied by
every chain; regression flag `join_domination_all_chains` true on all 73 boxes).  The
census controls reproduce the banked records with exact chain-hop witnesses [T 5/5],
and the cross-check performed for THIS file confirmed all 52 banked records reused here
are strict-classified in the joinedge2 dump with agreeing cap values (52/52; the one
row whose joinedge2 PRIMARY cap differs, box (1,5,5,6,6,7,8) demand (7,1,73/15), still
carries the banked cap 6/47 as a strict-complete witness -- witness 5, J-class).

## The verdict: `DumpDom` as defined in `Fresh.CapChainsOfCarve` is NOT instantiable

The construction below is a PROOF, not a report.  `DumpDom n f` quantifies over an
ARBITRARY realized table `U` (`UFine g U`) and an arbitrary realized chain; its J-side
disjunct instantiated at the EMPTY chain (`steps = []`, `chainRun U a Aex [] =
some (U, a, Aex)` definitionally, `ChainRealized g U a Aex []` just the exit bound `1 <
Aex/7`, satisfiable at `Aex = 200`) forces the BOX-side disjunct at that same arbitrary
`U`: `CapsDom U e.y e.caps e.x` for every realized `U`.  But the diagonal table `diagU`
(`diagU i i = some (1, false)`, off-diagonal `none`) is realized by EVERY positive `g`
(`ufine_diagU`), and `CapsDom`'s `cons` needs an entry `diagU e.y z = some ...` at the
FIRST hop pair -- `none` for `z != e.y`.  Every joinedge2 strict witness has
`y != x` (52/52), so `DumpDom` is FALSE for every one of the 11 families
(`not_dumpDom_<box>`, all 11 banked, `not_dumpDomTotalData` for the totality).

Rule-22 residual (honest): the dump's domination datum is real but NARROWER than the
`DumpDom` quantifiers: it is (a) restricted to the CANONICAL box-closure start table
`U0` (`joinedge2`'s `U0_entries`; `dom_box` tags), and (b) quantified over the chains
ENUMERATED from `U0` by the 90-type DFS (which `join_domination_all_chains` exhausts),
not over all `chainRun`-successful traces of all realized chains.  A faithful Lean
restatement needs (1) a variant definition fixing `U := U0` and (2) the DFS
exhaustiveness lemma (every realized chain is an enumerated one) -- (1) is DONE below
(section 4: `DumpDomU0`, the U₀-restricted datum; the U₀ census proved there shows it is
itself FALSE for all 11 strict families -- every one of the 52 records' caps is strictly
TIGHTER than the uMk entry at its pair, so the J-half genuinely lives on the chains'
closed tables, not on U₀), and (2) is the remaining vocabulary: its Lean-consumable form
is `capChainsRealized_of_chainDomU0` (section 4), the consumed chain's own closed-trace
domination at the U₀-fixed start.

Controls: `control_<box>` banked structurally -- each `dumpFam_<box>` contains the
banked `Fresh.OneSidedComposed.compFam_<box>` records verbatim (52 records), so cap
values agree with `Fresh.ComposedFamData.lean` / `Fresh.SpineTotalData.lean` by `rfl`.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every
theorem carries `#print axioms`; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound) -- `sorryAx` is failure.
-/

namespace Fresh.DumpDomData

open Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
  Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly

/-! ## 1. The diagonal table and the empty-chain reduction -/

/-- The diagonal table: identity entry `(1, false)` on the diagonal, unbounded
(`none`) off it.  Realized by every positive reading vector, so it is a legal
instantiation of `DumpDom`'s arbitrary `UFine g U` table. -/
def diagU : UTable := fun i j => if i = j then some ((1 : ℚ), false) else none

/-- `diagU` is realized by every positive `g`: the diagonal `g i / g i = 1` meets
`1 ≤ 1`; the off-diagonal `none` carries nothing. -/
theorem ufine_diagU {g : Fin 7 → ℝ} (hpos : ∀ i, 0 < g i) : UFine g diagU := by
  intro i j
  by_cases hij : i = j
  · subst hij
    have hb : diagU i i = some ((1 : ℚ), false) := by simp [diagU]
    refine bhof_some_of hb ?_
    simp only [BHolds]
    rw [div_self (hpos i).ne']
    norm_num
  · have hd : diagU i j = none := by simp [diagU, hij]
    exact bhof_none_of hd

#print axioms ufine_diagU

/-- The face sandwich for a box with entries ≥ 1 (all 11 strict-complete boxes). -/
theorem faceLo_le_faceHi (n : Fin 7 → ℤ) (hn : ∀ i, 1 ≤ n i) (i : Fin 7) :
    FaceLo n i ≤ FaceHi n i := by
  have hi := hn i
  have hz : (max (2 * n i - 1) 2 : ℤ) ≤ 2 * n i + 1 := max_le (by omega) (by omega)
  unfold FaceLo FaceHi
  gcongr

#print axioms faceLo_le_faceHi

/-- **The empty-chain reduction**: `DumpDom n f` forces the box-side datum at the
ARBITRARY realized table `diagU` for every edge of `f`.  Engine: instantiate `DumpDom`'s
chain at `steps = []`, `a = 0`, `Aex = 200` (the exit bound is `1 < 200/7`, satisfied by
the positivity of `FaceLo n 0`); then `chainRun diagU 0 200 [] = some (diagU, 0, 200)`
is `rfl`, and the J-side disjunct collapses to `CapsDom diagU ...` -- the same
proposition as the box-side disjunct.  So the disjunction is always equivalent to its
`steps = []` instance, and the chain machinery in `DumpDom` is inert. -/
theorem dumpDom_forces {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) {f : ComposedFam}
    (hdd : DumpDom n f) : ∀ e ∈ f.edges, CapsDom diagU e.y e.caps e.x := by
  intro e he
  have hface : ∀ i, FaceLo n i ≤ FaceLo n i ∧ FaceLo n i ≤ FaceHi n i := fun i =>
    ⟨le_refl _, faceLo_le_faceHi n hn i⟩
  have hpos : ∀ i, 0 < FaceLo n i := fun i => faceLo_pos n i
  have hfine : UFine (FaceLo n) diagU := ufine_diagU hpos
  have hchain : ChainRealized (FaceLo n) diagU 0 (200 : ℚ) [] := by
    simp only [ChainRealized, BHolds]
    rw [div_self (hpos 0).ne']
    norm_num
  rcases hdd (FaceLo n) hface diagU 0 (200 : ℚ) [] hfine hchain e he with h | h
  · exact h
  · exact h diagU 0 (200 : ℚ) rfl

#print axioms dumpDom_forces

/-- **The falsity lemma**: if `f` has an edge whose cap walk starts at a pair `e.y → z`
with `z ≠ e.y` (every joinedge2 strict witness: 52/52 have `y ≠ x`), then
`DumpDom n f` is FALSE.  Engine: `dumpDom_forces` hands us `CapsDom diagU e.y e.caps`
e.x`; `CapsDom.cons` needs an entry `diagU e.y z = some ...`, but `diagU` is `none` off
the diagonal. -/
theorem not_dumpDom_of_edge {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) {f : ComposedFam}
    (hedge : ∃ e ∈ f.edges, ∃ z : Fin 7, ∃ c : ℝ, ∃ l : List (Fin 7 × ℝ),
      e.y ≠ z ∧ e.caps = (z, c) :: l) : ¬ DumpDom n f := by
  intro hdd
  obtain ⟨e, he, z, c, l, hyz, hcaps⟩ := hedge
  have h := dumpDom_forces hn hdd e he
  rw [hcaps] at h
  cases h with
  | cons y z' c' l' w' hentry _ =>
    obtain ⟨c₀, s, hV, _⟩ := hentry
    simp [diagU, hyz] at hV

#print axioms not_dumpDom_of_edge

/-! ## 2. The 11 strict-complete boxes: strict-class families, validity, controls, verdicts

(The `not_dumpDom_<box>` verdicts below document why the OLD shape fails; the corrected
U₀-restricted predicate is section 4's `DumpDomU0`, refuted too -- `not_dumpDomU0_<box>`
-- and the honest consumption for these families is `capChainsRealized_of_chainDomU0`.) -/

/-- Box (1, 3, 4, 4, 5, 5, 7): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 8 records are the banked
`Fresh.OneSidedComposed.compFam_1_3_4_4_5_5_7` literals VERBATIM (`control_1_3_4_4_5_5_7`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 8 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_3_4_4_5_5_7` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_3_4_4_5_5_7 : ComposedFam :=
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

theorem dumpFamData_1_3_4_4_5_5_7 : ComposedFamData dumpFam_1_3_4_4_5_5_7 := by
  intro e he
  simp only [dumpFam_1_3_4_4_5_5_7, List.mem_cons] at he
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

#print axioms dumpFamData_1_3_4_4_5_5_7

/-- The CONTROL: the banked `compFam_1_3_4_4_5_5_7` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_3_4_4_5_5_7 : ∀ e ∈ compFam_1_3_4_4_5_5_7.edges, e ∈ dumpFam_1_3_4_4_5_5_7.edges := by
  intro e he
  simp only [compFam_1_3_4_4_5_5_7, dumpFam_1_3_4_4_5_5_7] at he ⊢
  exact he

#print axioms control_1_3_4_4_5_5_7

/-- The VERDICT: `DumpDom` is false for box (1, 3, 4, 4, 5, 5, 7)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 1 / 7). -/
theorem not_dumpDom_1_3_4_4_5_5_7 : ¬ DumpDom (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 13, 3, [(6, (1 / 7))]⟩, by simp [dumpFam_1_3_4_4_5_5_7], (6 : Fin 7), (1 / 7 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_3_4_4_5_5_7

/-- Box (1, 3, 4, 5, 5, 5, 7): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_3_4_5_5_5_7` literals VERBATIM (`control_1_3_4_5_5_5_7`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_3_4_5_5_5_7` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_3_4_5_5_5_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩,
    ⟨6, 1, 65, 31, [(6, (55 / 117))]⟩,
    ⟨6, 1, 5, 3, [(6, (55 / 117))]⟩,
    ⟨6, 1, 65, 47, [(6, (55 / 117))]⟩
  ]⟩

theorem dumpFamData_1_3_4_5_5_5_7 : ComposedFamData dumpFam_1_3_4_5_5_5_7 := by
  intro e he
  simp only [dumpFam_1_3_4_5_5_5_7, List.mem_cons] at he
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

#print axioms dumpFamData_1_3_4_5_5_5_7

/-- The CONTROL: the banked `compFam_1_3_4_5_5_5_7` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_3_4_5_5_5_7 : ∀ e ∈ compFam_1_3_4_5_5_5_7.edges, e ∈ dumpFam_1_3_4_5_5_5_7.edges := by
  intro e he
  simp only [compFam_1_3_4_5_5_5_7, dumpFam_1_3_4_5_5_5_7] at he ⊢
  exact he

#print axioms control_1_3_4_5_5_5_7

/-- The VERDICT: `DumpDom` is false for box (1, 3, 4, 5, 5, 5, 7)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 1870 / 13113). -/
theorem not_dumpDom_1_3_4_5_5_5_7 : ¬ DumpDom (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩, by simp [dumpFam_1_3_4_5_5_5_7], (6 : Fin 7), (1870 / 13113 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_3_4_5_5_5_7

/-- Box (1, 3, 4, 5, 6, 6, 7): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 8 records are the banked
`Fresh.OneSidedComposed.compFam_1_3_4_5_6_6_7` literals VERBATIM (`control_1_3_4_5_6_6_7`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 8 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_3_4_5_6_6_7` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_3_4_5_6_6_7 : ComposedFam :=
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

theorem dumpFamData_1_3_4_5_6_6_7 : ComposedFamData dumpFam_1_3_4_5_6_6_7 := by
  intro e he
  simp only [dumpFam_1_3_4_5_6_6_7, List.mem_cons] at he
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

#print axioms dumpFamData_1_3_4_5_6_6_7

/-- The CONTROL: the banked `compFam_1_3_4_5_6_6_7` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_3_4_5_6_6_7 : ∀ e ∈ compFam_1_3_4_5_6_6_7.edges, e ∈ dumpFam_1_3_4_5_6_6_7.edges := by
  intro e he
  simp only [compFam_1_3_4_5_6_6_7, dumpFam_1_3_4_5_6_6_7] at he ⊢
  exact he

#print axioms control_1_3_4_5_6_6_7

/-- The VERDICT: `DumpDom` is false for box (1, 3, 4, 5, 6, 6, 7)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 1 / 7). -/
theorem not_dumpDom_1_3_4_5_6_6_7 : ¬ DumpDom (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 13, 3, [(6, (1 / 7))]⟩, by simp [dumpFam_1_3_4_5_6_6_7], (6 : Fin 7), (1 / 7 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_3_4_5_6_6_7

/-- Box (1, 3, 4, 5, 7, 7, 9): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_3_4_5_7_7_9` literals VERBATIM (`control_1_3_4_5_7_7_9`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_3_4_5_7_7_9` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 5` has no entry. -/
noncomputable def dumpFam_1_3_4_5_7_7_9 : ComposedFam :=
  ⟨[
    ⟨5, 0, 13, 3, [(5, (594 / 4277))]⟩,
    ⟨5, 1, 65, 31, [(5, (99 / 235))]⟩,
    ⟨5, 1, 5, 3, [(5, (99 / 235))]⟩,
    ⟨5, 1, 65, 47, [(5, (99 / 235))]⟩
  ]⟩

theorem dumpFamData_1_3_4_5_7_7_9 : ComposedFamData dumpFam_1_3_4_5_7_7_9 := by
  intro e he
  simp only [dumpFam_1_3_4_5_7_7_9, List.mem_cons] at he
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

#print axioms dumpFamData_1_3_4_5_7_7_9

/-- The CONTROL: the banked `compFam_1_3_4_5_7_7_9` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_3_4_5_7_7_9 : ∀ e ∈ compFam_1_3_4_5_7_7_9.edges, e ∈ dumpFam_1_3_4_5_7_7_9.edges := by
  intro e he
  simp only [compFam_1_3_4_5_7_7_9, dumpFam_1_3_4_5_7_7_9] at he ⊢
  exact he

#print axioms control_1_3_4_5_7_7_9

/-- The VERDICT: `DumpDom` is false for box (1, 3, 4, 5, 7, 7, 9)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 5`
with cap 594 / 4277). -/
theorem not_dumpDom_1_3_4_5_7_7_9 : ¬ DumpDom (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨5, 0, 13, 3, [(5, (594 / 4277))]⟩, by simp [dumpFam_1_3_4_5_7_7_9], (5 : Fin 7), (594 / 4277 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_3_4_5_7_7_9

/-- Box (1, 4, 4, 5, 6, 6, 7): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_4_4_5_6_6_7` literals VERBATIM (`control_1_4_4_5_6_6_7`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_4_4_5_6_6_7` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_4_4_5_6_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩,
    ⟨6, 1, 5, 3, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 65, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 13, 11, [(6, (3179 / 5499))]⟩
  ]⟩

theorem dumpFamData_1_4_4_5_6_6_7 : ComposedFamData dumpFam_1_4_4_5_6_6_7 := by
  intro e he
  simp only [dumpFam_1_4_4_5_6_6_7, List.mem_cons] at he
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

#print axioms dumpFamData_1_4_4_5_6_6_7

/-- The CONTROL: the banked `compFam_1_4_4_5_6_6_7` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_4_4_5_6_6_7 : ∀ e ∈ compFam_1_4_4_5_6_6_7.edges, e ∈ dumpFam_1_4_4_5_6_6_7.edges := by
  intro e he
  simp only [compFam_1_4_4_5_6_6_7, dumpFam_1_4_4_5_6_6_7] at he ⊢
  exact he

#print axioms control_1_4_4_5_6_6_7

/-- The VERDICT: `DumpDom` is false for box (1, 4, 4, 5, 6, 6, 7)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 1 / 7). -/
theorem not_dumpDom_1_4_4_5_6_6_7 : ¬ DumpDom (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 13, 3, [(6, (1 / 7))]⟩, by simp [dumpFam_1_4_4_5_6_6_7], (6 : Fin 7), (1 / 7 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_4_4_5_6_6_7

/-- Box (1, 4, 5, 5, 5, 6, 7): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_4_5_5_5_6_7` literals VERBATIM (`control_1_4_5_5_5_6_7`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_4_5_5_5_6_7` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_4_5_5_5_6_7 : ComposedFam :=
  ⟨[
    ⟨6, 0, 13, 3, [(6, (50 / 351))]⟩,
    ⟨6, 1, 5, 3, [(6, (23375 / 41067))]⟩,
    ⟨6, 1, 65, 47, [(6, (23375 / 41067))]⟩,
    ⟨6, 1, 13, 11, [(6, (23375 / 41067))]⟩
  ]⟩

theorem dumpFamData_1_4_5_5_5_6_7 : ComposedFamData dumpFam_1_4_5_5_5_6_7 := by
  intro e he
  simp only [dumpFam_1_4_5_5_5_6_7, List.mem_cons] at he
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

#print axioms dumpFamData_1_4_5_5_5_6_7

/-- The CONTROL: the banked `compFam_1_4_5_5_5_6_7` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_4_5_5_5_6_7 : ∀ e ∈ compFam_1_4_5_5_5_6_7.edges, e ∈ dumpFam_1_4_5_5_5_6_7.edges := by
  intro e he
  simp only [compFam_1_4_5_5_5_6_7, dumpFam_1_4_5_5_5_6_7] at he ⊢
  exact he

#print axioms control_1_4_5_5_5_6_7

/-- The VERDICT: `DumpDom` is false for box (1, 4, 5, 5, 5, 6, 7)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 50 / 351). -/
theorem not_dumpDom_1_4_5_5_5_6_7 : ¬ DumpDom (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 13, 3, [(6, (50 / 351))]⟩, by simp [dumpFam_1_4_5_5_5_6_7], (6 : Fin 7), (50 / 351 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_4_5_5_5_6_7

/-- Box (1, 4, 5, 5, 6, 7, 9): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_4_5_5_6_7_9` literals VERBATIM (`control_1_4_5_5_6_7_9`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_4_5_5_6_7_9` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 3` has no entry. -/
noncomputable def dumpFam_1_4_5_5_6_7_9 : ComposedFam :=
  ⟨[
    ⟨3, 0, 49, 15, [(3, (98 / 527))]⟩,
    ⟨3, 1, 49, 39, [(3, (245 / 341))]⟩,
    ⟨3, 1, 49, 47, [(3, (245 / 341))]⟩,
    ⟨3, 1, 49, 55, [(3, (245 / 341))]⟩
  ]⟩

theorem dumpFamData_1_4_5_5_6_7_9 : ComposedFamData dumpFam_1_4_5_5_6_7_9 := by
  intro e he
  simp only [dumpFam_1_4_5_5_6_7_9, List.mem_cons] at he
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

#print axioms dumpFamData_1_4_5_5_6_7_9

/-- The CONTROL: the banked `compFam_1_4_5_5_6_7_9` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_4_5_5_6_7_9 : ∀ e ∈ compFam_1_4_5_5_6_7_9.edges, e ∈ dumpFam_1_4_5_5_6_7_9.edges := by
  intro e he
  simp only [compFam_1_4_5_5_6_7_9, dumpFam_1_4_5_5_6_7_9] at he ⊢
  exact he

#print axioms control_1_4_5_5_6_7_9

/-- The VERDICT: `DumpDom` is false for box (1, 4, 5, 5, 6, 7, 9)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 3`
with cap 98 / 527). -/
theorem not_dumpDom_1_4_5_5_6_7_9 : ¬ DumpDom (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨3, 0, 49, 15, [(3, (98 / 527))]⟩, by simp [dumpFam_1_4_5_5_6_7_9], (3 : Fin 7), (98 / 527 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_4_5_5_6_7_9

/-- Box (1, 4, 5, 6, 6, 7, 8): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_4_5_6_6_7_8` literals VERBATIM (`control_1_4_5_6_6_7_8`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_4_5_6_6_7_8` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_4_5_6_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩,
    ⟨6, 1, 73, 47, [(6, (27 / 47))]⟩,
    ⟨6, 1, 73, 55, [(6, (27 / 47))]⟩,
    ⟨6, 1, 73, 63, [(6, (27 / 47))]⟩
  ]⟩

theorem dumpFamData_1_4_5_6_6_7_8 : ComposedFamData dumpFam_1_4_5_6_6_7_8 := by
  intro e he
  simp only [dumpFam_1_4_5_6_6_7_8, List.mem_cons] at he
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

#print axioms dumpFamData_1_4_5_6_6_7_8

/-- The CONTROL: the banked `compFam_1_4_5_6_6_7_8` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_4_5_6_6_7_8 : ∀ e ∈ compFam_1_4_5_6_6_7_8.edges, e ∈ dumpFam_1_4_5_6_6_7_8.edges := by
  intro e he
  simp only [compFam_1_4_5_6_6_7_8, dumpFam_1_4_5_6_6_7_8] at he ⊢
  exact he

#print axioms control_1_4_5_6_6_7_8

/-- The VERDICT: `DumpDom` is false for box (1, 4, 5, 6, 6, 7, 8)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 6 / 47). -/
theorem not_dumpDom_1_4_5_6_6_7_8 : ¬ DumpDom (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 73, 15, [(6, (6 / 47))]⟩, by simp [dumpFam_1_4_5_6_6_7_8], (6 : Fin 7), (6 / 47 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_4_5_6_6_7_8

/-- Box (1, 5, 5, 5, 6, 7, 8): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_5_5_5_6_7_8` literals VERBATIM (`control_1_5_5_5_6_7_8`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_5_5_5_6_7_8` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_5_5_5_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6358 / 49491))]⟩,
    ⟨6, 1, 73, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 55, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 63, [(6, (3179 / 5499))]⟩
  ]⟩

theorem dumpFamData_1_5_5_5_6_7_8 : ComposedFamData dumpFam_1_5_5_5_6_7_8 := by
  intro e he
  simp only [dumpFam_1_5_5_5_6_7_8, List.mem_cons] at he
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

#print axioms dumpFamData_1_5_5_5_6_7_8

/-- The CONTROL: the banked `compFam_1_5_5_5_6_7_8` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_5_5_5_6_7_8 : ∀ e ∈ compFam_1_5_5_5_6_7_8.edges, e ∈ dumpFam_1_5_5_5_6_7_8.edges := by
  intro e he
  simp only [compFam_1_5_5_5_6_7_8, dumpFam_1_5_5_5_6_7_8] at he ⊢
  exact he

#print axioms control_1_5_5_5_6_7_8

/-- The VERDICT: `DumpDom` is false for box (1, 5, 5, 5, 6, 7, 8)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 6358 / 49491). -/
theorem not_dumpDom_1_5_5_5_6_7_8 : ¬ DumpDom (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 73, 15, [(6, (6358 / 49491))]⟩, by simp [dumpFam_1_5_5_5_6_7_8], (6 : Fin 7), (6358 / 49491 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_5_5_5_6_7_8

/-- Box (1, 5, 5, 6, 6, 7, 8): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_5_5_6_6_7_8` literals VERBATIM (`control_1_5_5_6_6_7_8`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_5_5_6_6_7_8` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 6` has no entry. -/
noncomputable def dumpFam_1_5_5_6_6_7_8 : ComposedFam :=
  ⟨[
    ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩,
    ⟨6, 1, 73, 47, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 55, [(6, (3179 / 5499))]⟩,
    ⟨6, 1, 73, 63, [(6, (3179 / 5499))]⟩
  ]⟩

theorem dumpFamData_1_5_5_6_6_7_8 : ComposedFamData dumpFam_1_5_5_6_6_7_8 := by
  intro e he
  simp only [dumpFam_1_5_5_6_6_7_8, List.mem_cons] at he
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

#print axioms dumpFamData_1_5_5_6_6_7_8

/-- The CONTROL: the banked `compFam_1_5_5_6_6_7_8` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_5_5_6_6_7_8 : ∀ e ∈ compFam_1_5_5_6_6_7_8.edges, e ∈ dumpFam_1_5_5_6_6_7_8.edges := by
  intro e he
  simp only [compFam_1_5_5_6_6_7_8, dumpFam_1_5_5_6_6_7_8] at he ⊢
  exact he

#print axioms control_1_5_5_6_6_7_8

/-- The VERDICT: `DumpDom` is false for box (1, 5, 5, 6, 6, 7, 8)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 6`
with cap 6 / 47). -/
theorem not_dumpDom_1_5_5_6_6_7_8 : ¬ DumpDom (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨6, 0, 73, 15, [(6, (6 / 47))]⟩, by simp [dumpFam_1_5_5_6_6_7_8], (6 : Fin 7), (6 / 47 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_5_5_6_6_7_8

/-- Box (1, 5, 5, 6, 7, 8, 8): the strict-class composed family from
`joinedge2_perbox_v1.jsonl` (every death row of the box is strict-complete there,
census section 7).  The 4 records are the banked
`Fresh.OneSidedComposed.compFam_1_5_5_6_7_8_8` literals VERBATIM (`control_1_5_5_6_7_8_8`), so
cap values agree with `Fresh.ComposedFamData.lean` by construction; the joinedge2
cross-check confirmed all 4 demand rows strict-classified with agreeing cap values.
`not_dumpDom_1_5_5_6_7_8_8` is the honest verdict: `Fresh.CapChainsOfCarve.DumpDom` is
FALSE for this family -- the empty-chain instance of the J-side disjunct collapses
to the box-side at the arbitrary realized table `diagU`, whose first hop `e.y = 0 →`
`z = 2` has no entry. -/
noncomputable def dumpFam_1_5_5_6_7_8_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, (311542 / 1639125))]⟩,
    ⟨2, 1, 49, 47, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 49, 55, [(2, (155771 / 170469))]⟩,
    ⟨2, 1, 7, 9, [(2, (155771 / 170469))]⟩
  ]⟩

theorem dumpFamData_1_5_5_6_7_8_8 : ComposedFamData dumpFam_1_5_5_6_7_8_8 := by
  intro e he
  simp only [dumpFam_1_5_5_6_7_8_8, List.mem_cons] at he
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

#print axioms dumpFamData_1_5_5_6_7_8_8

/-- The CONTROL: the banked `compFam_1_5_5_6_7_8_8` records are members verbatim, so the
cap values agree with `Fresh.ComposedFamData.lean`. -/
theorem control_1_5_5_6_7_8_8 : ∀ e ∈ compFam_1_5_5_6_7_8_8.edges, e ∈ dumpFam_1_5_5_6_7_8_8.edges := by
  intro e he
  simp only [compFam_1_5_5_6_7_8_8, dumpFam_1_5_5_6_7_8_8] at he ⊢
  exact he

#print axioms control_1_5_5_6_7_8_8

/-- The VERDICT: `DumpDom` is false for box (1, 5, 5, 6, 7, 8, 8)'s strict-class family (the
empty-chain reduction + the `diagU` counterexample at the first hop `0 → 2`
with cap 311542 / 1639125). -/
theorem not_dumpDom_1_5_5_6_7_8_8 : ¬ DumpDom (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8 :=
  not_dumpDom_of_edge (by decide)
    ⟨⟨2, 0, 49, 15, [(2, (311542 / 1639125))]⟩, by simp [dumpFam_1_5_5_6_7_8_8], (2 : Fin 7), (311542 / 1639125 : ℝ), [], by decide, rfl⟩

#print axioms not_dumpDom_1_5_5_6_7_8_8

/-! ## 3. The totality: the requested `dumpDomTotalData` statement and its falsity -/

/-- The strict-complete set: the 11 boxes of `joinedge2_census_v1.out` section 7 (every
death row carries a strict-complete cap). -/
def strictBoxes : Finset (Fin 7 → ℤ) :=
  {![1, 3, 4, 4, 5, 5, 7],
   ![1, 3, 4, 5, 5, 5, 7],
   ![1, 3, 4, 5, 6, 6, 7],
   ![1, 3, 4, 5, 7, 7, 9],
   ![1, 4, 4, 5, 6, 6, 7],
   ![1, 4, 5, 5, 5, 6, 7],
   ![1, 4, 5, 5, 6, 7, 9],
   ![1, 4, 5, 6, 6, 7, 8],
   ![1, 5, 5, 5, 6, 7, 8],
   ![1, 5, 5, 6, 6, 7, 8],
   ![1, 5, 5, 6, 7, 8, 8]}

/-- The per-box family dispatch over the strict-complete set (empty family off it),
mirroring `Fresh.OneSidedComposed.compFamOf`. -/
noncomputable def dumpFamOf (b : Fin 7 → ℤ) : ComposedFam :=
  if b = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) then dumpFam_1_3_4_4_5_5_7
  else if b = (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) then dumpFam_1_3_4_5_5_5_7
  else if b = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then dumpFam_1_3_4_5_6_6_7
  else if b = (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) then dumpFam_1_3_4_5_7_7_9
  else if b = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then dumpFam_1_4_4_5_6_6_7
  else if b = (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) then dumpFam_1_4_5_5_5_6_7
  else if b = (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) then dumpFam_1_4_5_5_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then dumpFam_1_4_5_6_6_7_8
  else if b = (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then dumpFam_1_5_5_5_6_7_8
  else if b = (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then dumpFam_1_5_5_6_6_7_8
  else if b = (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then dumpFam_1_5_5_6_7_8_8
  else ⟨[]⟩

/-- **The requested deliverable statement, verbatim** (`strictSet` := `strictBoxes`,
`famOf` := `dumpFamOf`): every strict-complete box carries the `DumpDom` datum.  The
file's honest result is `not_dumpDomTotalData`: this statement is FALSE -- the datum's
arbitrary-table quantifier overshoots what the joinedge2 witnesses certify (see the
module docstring's rule-22 residual for the corrected shape, and section 4's
`DumpDomU0` / `not_dumpDomU0TotalData`: the U₀-restricted correction is false too). -/
-- STANDING: DEFINITION
def dumpDomTotalData : Prop := ∀ b ∈ strictBoxes, DumpDom b (dumpFamOf b)

/-- The CONSTRUCTIVE half that survives: every strict-complete box's strict-class family
is valid (`ComposedFamData`), from the joinedge2 strict-class dump. -/
theorem dumpFamTotalData : ∀ b ∈ strictBoxes, ComposedFamData (dumpFamOf b) := by
  intro b hb
  simp only [strictBoxes, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [dumpFamOf, dumpFamData_1_3_4_4_5_5_7]
  · simp [dumpFamOf, dumpFamData_1_3_4_5_5_5_7]
  · simp [dumpFamOf, dumpFamData_1_3_4_5_6_6_7]
  · simp [dumpFamOf, dumpFamData_1_3_4_5_7_7_9]
  · simp [dumpFamOf, dumpFamData_1_4_4_5_6_6_7]
  · simp [dumpFamOf, dumpFamData_1_4_5_5_5_6_7]
  · simp [dumpFamOf, dumpFamData_1_4_5_5_6_7_9]
  · simp [dumpFamOf, dumpFamData_1_4_5_6_6_7_8]
  · simp [dumpFamOf, dumpFamData_1_5_5_5_6_7_8]
  · simp [dumpFamOf, dumpFamData_1_5_5_6_6_7_8]
  · simp [dumpFamOf, dumpFamData_1_5_5_6_7_8_8]

#print axioms dumpFamTotalData

/-- **The honest verdict**: the requested totality `dumpDomTotalData` is FALSE (already
the first box's family kills it via `not_dumpDom_1_3_4_4_5_5_7`). -/
theorem not_dumpDomTotalData : ¬ dumpDomTotalData := by
  intro h
  have h1 := h (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) (by simp [strictBoxes])
  simp only [dumpFamOf] at h1
  exact not_dumpDom_1_3_4_4_5_5_7 h1

#print axioms not_dumpDomTotalData


/-! ## 4. The corrected predicate `DumpDomU0` (U₀-restricted) and the U₀ census

The bug in `Fresh.CapChainsOfCarve.DumpDom` (proved above: `not_dumpDom_<box>`,
`not_dumpDomTotalData`) is that its J-side disjunct quantifies over an ARBITRARY realized
table: at the empty chain (`steps = []`, `chainRun U a Aex [] = some (U, a, Aex)` by `rfl`)
it collapses to `CapsDom U e.y e.caps e.x` at every realized `U`, which `diagU` refutes.
The corrected datum restricts the J-side to the box's own canonical box-closure table U₀
(the `Fresh.UClosure.uMk` fold on the box tuple): `CapsDom U0 e.y e.caps e.x` -- no table
quantifier, no empty-chain trap.

THE U₀ CENSUS (exact `#eval` of `uMk`, this session): at every pair `(e.y, e.x)` that one
of the 52 banked strict witnesses reads, `uMk`'s entry is STRICTLY LOOSER than the
witness's cap -- e.g. box (1, 3, 4, 4, 5, 5, 7): entry `(2 / 13, false)` at `(0, 6)` vs cap
`1 / 7`, entry `(7 / 13, false)` at `(1, 6)` vs cap `33 / 70`, entry `(9 / 13, true)` at
`(2, 6)` vs cap `825 / 1457`; likewise on all 11 boxes (the per-pair entries are banked as
`u0e_<box>_<i>_<j>` below, and the compile-time `#eval` check re-verifies all of them
against `uMk` live).  So ZERO of the 52 records are U₀-dominated: `DumpDomU0` is FALSE for
every one of the 11 strict families (`not_dumpDomU0_<box>`, `not_dumpDomU0TotalData`).
The joinedge2 census's strict-completeness is a statement about the JOIN of the enumerated
chains' closed tables (the J-half), which no box-only table can capture -- the box face
bounds alone never imply caps as tight as `ρ₀ / ρ₆ < 1 / 7` inside box (1, 3, 4, 4, 5, 5, 7)
(`g 0 / g 6` reaches `3 / 13 > 1 / 7` at the box bottom).  The honest consumption for these
families is therefore `capChainsRealized_of_chainDomU0`: the J-half enters as the consumed
chain's own closed-trace domination, with the chain START fixed at U₀ -- the same
W₀-chain-conditional shape the glue consumes, with both over-quantifiers of the old
`DumpDom` removed.  `capChainsRealized_of_dumpDomU0` consumes the static U₀ datum where a
family carries it.

Table literals: `u0Tab_<box>` transcribes `uMk`'s output AT THE CENSUS PAIRS (the only
pairs the 52 records' singleton walks read -- every record's walk is `[(e.x, c)]`);
elsewhere it carries the identity-diagonal default (`(1, false)` on `i = j`, `none` off),
NOT uMk's propagated entries -- `u0Of` is point-exact on the pairs it is used on, and the
scope is stated here rather than claimed pointwise-global.  (The kernel cannot decide the
uMk fold's entries directly: the fold's ℚ products normalize through `Nat.gcd`, which is
well-founded and kernel-hostile -- `decide` gets stuck even at fold depth 2 -- hence the
transcription route, machine-checked by the kept `#eval`.)
-/

/-- U₀ (the `uMk` fold's output) for box (1, 3, 4, 4, 5, 5, 7), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_3_4_4_5_5_7 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 13 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((7 / 13 : ℚ)), false)
  else if i = (2 : Fin 7) ∧ j = (6 : Fin 7) then some (((9 / 13 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 3, 4, 5, 5, 5, 7), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_3_4_5_5_5_7 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 13 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((7 / 13 : ℚ)), false)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 3, 4, 5, 6, 6, 7), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_3_4_5_6_6_7 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 13 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((7 / 13 : ℚ)), false)
  else if i = (2 : Fin 7) ∧ j = (6 : Fin 7) then some (((9 / 13 : ℚ)), false)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 3, 4, 5, 7, 7, 9), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_3_4_5_7_7_9 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (5 : Fin 7) then some (((2 / 13 : ℚ)), true)
  else if i = (1 : Fin 7) ∧ j = (5 : Fin 7) then some (((7 / 13 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 4, 4, 5, 6, 6, 7), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_4_4_5_6_6_7 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 13 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((9 / 13 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 4, 5, 5, 5, 6, 7), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_4_5_5_5_6_7 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 13 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((9 / 13 : ℚ)), false)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 4, 5, 5, 6, 7, 9), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_4_5_5_6_7_9 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (3 : Fin 7) then some (((2 / 9 : ℚ)), true)
  else if i = (1 : Fin 7) ∧ j = (3 : Fin 7) then some (((1 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 4, 5, 6, 6, 7, 8), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_4_5_6_6_7_8 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 15 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((3 / 5 : ℚ)), false)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 5, 5, 5, 6, 7, 8), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_5_5_5_6_7_8 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 15 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((11 / 15 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 5, 5, 6, 6, 7, 8), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_5_5_6_6_7_8 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (6 : Fin 7) then some (((2 / 15 : ℚ)), false)
  else if i = (1 : Fin 7) ∧ j = (6 : Fin 7) then some (((11 / 15 : ℚ)), true)
  else none

/-- U₀ (the `uMk` fold's output) for box (1, 5, 5, 6, 7, 8, 8), exact at the
record-read pairs; identity-diagonal default elsewhere (see the section census). -/
def u0Tab_1_5_5_6_7_8_8 : UTable := fun i j =>
  if i = j then some ((1 : ℚ), false)
  else if i = (0 : Fin 7) ∧ j = (2 : Fin 7) then some (((2 / 9 : ℚ)), true)
  else if i = (1 : Fin 7) ∧ j = (2 : Fin 7) then some (((1 : ℚ)), true)
  else none

/-- The box-closure table U₀ of a strict-complete box (dispatch over the 11 census boxes;
identity-diagonal default off the list). -/
def u0Of (n : Fin 7 → ℤ) : UTable :=
  if n = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) then u0Tab_1_3_4_4_5_5_7
  else if n = (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) then u0Tab_1_3_4_5_5_5_7
  else if n = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then u0Tab_1_3_4_5_6_6_7
  else if n = (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) then u0Tab_1_3_4_5_7_7_9
  else if n = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then u0Tab_1_4_4_5_6_6_7
  else if n = (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) then u0Tab_1_4_5_5_5_6_7
  else if n = (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) then u0Tab_1_4_5_5_6_7_9
  else if n = (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then u0Tab_1_4_5_6_6_7_8
  else if n = (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then u0Tab_1_5_5_5_6_7_8
  else if n = (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then u0Tab_1_5_5_6_6_7_8
  else if n = (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then u0Tab_1_5_5_6_7_8_8
  else fun i j => if i = j then some ((1 : ℚ), false) else none

/-- `uMk`'s entry at (0, 6) for box (1, 3, 4, 4, 5, 5, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_4_5_5_7_0_6 :
    u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_4_5_5_7]

#print axioms u0e_1_3_4_4_5_5_7_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 3, 4, 4, 5, 5, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_4_5_5_7_1_6 :
    u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((7 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_4_5_5_7]

#print axioms u0e_1_3_4_4_5_5_7_1_6

/-- `uMk`'s entry at (2, 6) for box (1, 3, 4, 4, 5, 5, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_4_5_5_7_2_6 :
    u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) (2 : Fin 7) (6 : Fin 7) = some ((9 / 13 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_3_4_4_5_5_7]

#print axioms u0e_1_3_4_4_5_5_7_2_6

/-- `uMk`'s entry at (0, 6) for box (1, 3, 4, 5, 5, 5, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_5_5_7_0_6 :
    u0Of (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_5_5_5_7]

#print axioms u0e_1_3_4_5_5_5_7_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 3, 4, 5, 5, 5, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_5_5_7_1_6 :
    u0Of (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((7 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_5_5_5_7]

#print axioms u0e_1_3_4_5_5_5_7_1_6

/-- `uMk`'s entry at (0, 6) for box (1, 3, 4, 5, 6, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_6_6_7_0_6 :
    u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_5_6_6_7]

#print axioms u0e_1_3_4_5_6_6_7_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 3, 4, 5, 6, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_6_6_7_1_6 :
    u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((7 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_5_6_6_7]

#print axioms u0e_1_3_4_5_6_6_7_1_6

/-- `uMk`'s entry at (2, 6) for box (1, 3, 4, 5, 6, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_6_6_7_2_6 :
    u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) (2 : Fin 7) (6 : Fin 7) = some ((9 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_3_4_5_6_6_7]

#print axioms u0e_1_3_4_5_6_6_7_2_6

/-- `uMk`'s entry at (0, 5) for box (1, 3, 4, 5, 7, 7, 9): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_7_7_9_0_5 :
    u0Of (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (0 : Fin 7) (5 : Fin 7) = some ((2 / 13 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_3_4_5_7_7_9]

#print axioms u0e_1_3_4_5_7_7_9_0_5

/-- `uMk`'s entry at (1, 5) for box (1, 3, 4, 5, 7, 7, 9): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_3_4_5_7_7_9_1_5 :
    u0Of (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) (1 : Fin 7) (5 : Fin 7) = some ((7 / 13 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_3_4_5_7_7_9]

#print axioms u0e_1_3_4_5_7_7_9_1_5

/-- `uMk`'s entry at (0, 6) for box (1, 4, 4, 5, 6, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_4_5_6_6_7_0_6 :
    u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_4_4_5_6_6_7]

#print axioms u0e_1_4_4_5_6_6_7_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 4, 4, 5, 6, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_4_5_6_6_7_1_6 :
    u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((9 / 13 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_4_4_5_6_6_7]

#print axioms u0e_1_4_4_5_6_6_7_1_6

/-- `uMk`'s entry at (0, 6) for box (1, 4, 5, 5, 5, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_5_5_6_7_0_6 :
    u0Of (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_4_5_5_5_6_7]

#print axioms u0e_1_4_5_5_5_6_7_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 4, 5, 5, 5, 6, 7): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_5_5_6_7_1_6 :
    u0Of (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((9 / 13 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_4_5_5_5_6_7]

#print axioms u0e_1_4_5_5_5_6_7_1_6

/-- `uMk`'s entry at (0, 3) for box (1, 4, 5, 5, 6, 7, 9): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_5_6_7_9_0_3 :
    u0Of (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) (0 : Fin 7) (3 : Fin 7) = some ((2 / 9 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_4_5_5_6_7_9]

#print axioms u0e_1_4_5_5_6_7_9_0_3

/-- `uMk`'s entry at (1, 3) for box (1, 4, 5, 5, 6, 7, 9): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_5_6_7_9_1_3 :
    u0Of (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) (1 : Fin 7) (3 : Fin 7) = some ((1 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_4_5_5_6_7_9]

#print axioms u0e_1_4_5_5_6_7_9_1_3

/-- `uMk`'s entry at (0, 6) for box (1, 4, 5, 6, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_6_6_7_8_0_6 :
    u0Of (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_4_5_6_6_7_8]

#print axioms u0e_1_4_5_6_6_7_8_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 4, 5, 6, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_4_5_6_6_7_8_1_6 :
    u0Of (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((3 / 5 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_4_5_6_6_7_8]

#print axioms u0e_1_4_5_6_6_7_8_1_6

/-- `uMk`'s entry at (0, 6) for box (1, 5, 5, 5, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_5_6_7_8_0_6 :
    u0Of (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_5_5_5_6_7_8]

#print axioms u0e_1_5_5_5_6_7_8_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 5, 5, 5, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_5_6_7_8_1_6 :
    u0Of (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((11 / 15 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_5_5_5_6_7_8]

#print axioms u0e_1_5_5_5_6_7_8_1_6

/-- `uMk`'s entry at (0, 6) for box (1, 5, 5, 6, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_6_6_7_8_0_6 :
    u0Of (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) (0 : Fin 7) (6 : Fin 7) = some ((2 / 15 : ℚ), false) :=
  by simp [u0Of, u0Tab_1_5_5_6_6_7_8]

#print axioms u0e_1_5_5_6_6_7_8_0_6

/-- `uMk`'s entry at (1, 6) for box (1, 5, 5, 6, 6, 7, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_6_6_7_8_1_6 :
    u0Of (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) (1 : Fin 7) (6 : Fin 7) = some ((11 / 15 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_5_5_6_6_7_8]

#print axioms u0e_1_5_5_6_6_7_8_1_6

/-- `uMk`'s entry at (0, 2) for box (1, 5, 5, 6, 7, 8, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_6_7_8_8_0_2 :
    u0Of (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) (0 : Fin 7) (2 : Fin 7) = some ((2 / 9 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_5_5_6_7_8_8]

#print axioms u0e_1_5_5_6_7_8_8_0_2

/-- `uMk`'s entry at (1, 2) for box (1, 5, 5, 6, 7, 8, 8): exact census datum
(`#eval`-checked; the kept compile-time check below re-verifies it live). -/
theorem u0e_1_5_5_6_7_8_8_1_2 :
    u0Of (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) (1 : Fin 7) (2 : Fin 7) = some ((1 : ℚ), true) :=
  by simp [u0Of, u0Tab_1_5_5_6_7_8_8]

#print axioms u0e_1_5_5_6_7_8_8_1_2

/-- **The corrected, faithful datum** (fixes `Fresh.CapChainsOfCarve.DumpDom`'s proved
over-quantification; that def is kept untouched there -- see `not_dumpDom_<box>` above for
why it is uninstantiable, and this section for why the corrected datum is too): every
record's cap walk is dominated by an entry of the box's own canonical box-closure table
`u0Of n` -- the U₀-restricted J-side.  Static: no table quantifier, no chain, hence no
empty-chain collapse. -/
-- STANDING: DEFINITION
def DumpDomU0 (n : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ e ∈ f.edges, CapsDom (u0Of n) e.y e.caps e.x

/-- One stored entry strictly looser than the cap kills the singleton domination: `CapsDom`'s
`cons` reads exactly the entry at `(e.y, e.x)` (the walks here are singletons `[(e.x, c)]`),
and the table's value there is unique. -/
theorem not_capsDomU0_of_entry_lt {V : UTable} {y x : Fin 7} {c : ℝ} {c₀ : ℚ} {s : Bool}
    (hV : V y x = some (c₀, s)) (hlt : c < ((c₀ : ℚ) : ℝ)) :
    ¬ CapsDom V y [(x, c)] x := by
  intro h
  cases h with
  | cons _ _ _ _ _ hentry _ =>
    obtain ⟨c₀', s', hVe, hle⟩ := hentry
    rw [hV] at hVe
    simp only [Option.some.injEq, Prod.mk.injEq] at hVe
    obtain ⟨rfl, -⟩ := hVe
    exact absurd hle (not_le.mpr hlt)

#print axioms not_capsDomU0_of_entry_lt

/-- The U₀ census for box (1, 3, 4, 4, 5, 5, 7): ALL 8 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_3_4_4_5_5_7 :
    ∀ e ∈ dumpFam_1_3_4_4_5_5_7.edges,
      ¬ CapsDom (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_4_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_4_5_5_7_2_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_3_4_4_5_5_7

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 3, 4, 4, 5, 5, 7)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_3_4_4_5_5_7 :
    ¬ DumpDomU0 (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7 :=
  fun h =>
    not_capsDomU0all_1_3_4_4_5_5_7 ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩
      (by simp [dumpFam_1_3_4_4_5_5_7])
      (h ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩ (by simp [dumpFam_1_3_4_4_5_5_7]))

#print axioms not_dumpDomU0_1_3_4_4_5_5_7

/-- The U₀ census for box (1, 3, 4, 5, 5, 5, 7): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_3_4_5_5_5_7 :
    ∀ e ∈ dumpFam_1_3_4_5_5_5_7.edges,
      ¬ CapsDom (u0Of (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_5_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_5_5_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_5_5_7_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_3_4_5_5_5_7

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 3, 4, 5, 5, 5, 7)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_3_4_5_5_5_7 :
    ¬ DumpDomU0 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7 :=
  fun h =>
    not_capsDomU0all_1_3_4_5_5_5_7 ⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩
      (by simp [dumpFam_1_3_4_5_5_5_7])
      (h ⟨6, 0, 13, 3, [(6, (1870 / 13113))]⟩ (by simp [dumpFam_1_3_4_5_5_5_7]))

#print axioms not_dumpDomU0_1_3_4_5_5_5_7

/-- The U₀ census for box (1, 3, 4, 5, 6, 6, 7): ALL 8 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_3_4_5_6_6_7 :
    ∀ e ∈ dumpFam_1_3_4_5_6_6_7.edges,
      ¬ CapsDom (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_5_6_6_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_2_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_6_6_7_2_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_3_4_5_6_6_7

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 3, 4, 5, 6, 6, 7)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_3_4_5_6_6_7 :
    ¬ DumpDomU0 (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7 :=
  fun h =>
    not_capsDomU0all_1_3_4_5_6_6_7 ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩
      (by simp [dumpFam_1_3_4_5_6_6_7])
      (h ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩ (by simp [dumpFam_1_3_4_5_6_6_7]))

#print axioms not_dumpDomU0_1_3_4_5_6_6_7

/-- The U₀ census for box (1, 3, 4, 5, 7, 7, 9): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_3_4_5_7_7_9 :
    ∀ e ∈ dumpFam_1_3_4_5_7_7_9.edges,
      ¬ CapsDom (u0Of (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_3_4_5_7_7_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_7_7_9_0_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_3_4_5_7_7_9_1_5) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_3_4_5_7_7_9

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 3, 4, 5, 7, 7, 9)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_3_4_5_7_7_9 :
    ¬ DumpDomU0 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9 :=
  fun h =>
    not_capsDomU0all_1_3_4_5_7_7_9 ⟨5, 0, 13, 3, [(5, (594 / 4277))]⟩
      (by simp [dumpFam_1_3_4_5_7_7_9])
      (h ⟨5, 0, 13, 3, [(5, (594 / 4277))]⟩ (by simp [dumpFam_1_3_4_5_7_7_9]))

#print axioms not_dumpDomU0_1_3_4_5_7_7_9

/-- The U₀ census for box (1, 4, 4, 5, 6, 6, 7): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_4_4_5_6_6_7 :
    ∀ e ∈ dumpFam_1_4_4_5_6_6_7.edges,
      ¬ CapsDom (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_4_4_5_6_6_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_4_5_6_6_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_4_5_6_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_4_5_6_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_4_5_6_6_7_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_4_4_5_6_6_7

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 4, 4, 5, 6, 6, 7)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_4_4_5_6_6_7 :
    ¬ DumpDomU0 (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7 :=
  fun h =>
    not_capsDomU0all_1_4_4_5_6_6_7 ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩
      (by simp [dumpFam_1_4_4_5_6_6_7])
      (h ⟨6, 0, 13, 3, [(6, (1 / 7))]⟩ (by simp [dumpFam_1_4_4_5_6_6_7]))

#print axioms not_dumpDomU0_1_4_4_5_6_6_7

/-- The U₀ census for box (1, 4, 5, 5, 5, 6, 7): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_4_5_5_5_6_7 :
    ∀ e ∈ dumpFam_1_4_5_5_5_6_7.edges,
      ¬ CapsDom (u0Of (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_4_5_5_5_6_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_5_6_7_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_5_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_5_6_7_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_5_6_7_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_4_5_5_5_6_7

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 4, 5, 5, 5, 6, 7)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_4_5_5_5_6_7 :
    ¬ DumpDomU0 (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7 :=
  fun h =>
    not_capsDomU0all_1_4_5_5_5_6_7 ⟨6, 0, 13, 3, [(6, (50 / 351))]⟩
      (by simp [dumpFam_1_4_5_5_5_6_7])
      (h ⟨6, 0, 13, 3, [(6, (50 / 351))]⟩ (by simp [dumpFam_1_4_5_5_5_6_7]))

#print axioms not_dumpDomU0_1_4_5_5_5_6_7

/-- The U₀ census for box (1, 4, 5, 5, 6, 7, 9): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_4_5_5_6_7_9 :
    ∀ e ∈ dumpFam_1_4_5_5_6_7_9.edges,
      ¬ CapsDom (u0Of (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_4_5_5_6_7_9, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_6_7_9_0_3) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_6_7_9_1_3) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_6_7_9_1_3) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_5_6_7_9_1_3) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_4_5_5_6_7_9

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 4, 5, 5, 6, 7, 9)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_4_5_5_6_7_9 :
    ¬ DumpDomU0 (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9 :=
  fun h =>
    not_capsDomU0all_1_4_5_5_6_7_9 ⟨3, 0, 49, 15, [(3, (98 / 527))]⟩
      (by simp [dumpFam_1_4_5_5_6_7_9])
      (h ⟨3, 0, 49, 15, [(3, (98 / 527))]⟩ (by simp [dumpFam_1_4_5_5_6_7_9]))

#print axioms not_dumpDomU0_1_4_5_5_6_7_9

/-- The U₀ census for box (1, 4, 5, 6, 6, 7, 8): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_4_5_6_6_7_8 :
    ∀ e ∈ dumpFam_1_4_5_6_6_7_8.edges,
      ¬ CapsDom (u0Of (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_4_5_6_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_6_6_7_8_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_6_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_6_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_4_5_6_6_7_8_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_4_5_6_6_7_8

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 4, 5, 6, 6, 7, 8)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_4_5_6_6_7_8 :
    ¬ DumpDomU0 (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8 :=
  fun h =>
    not_capsDomU0all_1_4_5_6_6_7_8 ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩
      (by simp [dumpFam_1_4_5_6_6_7_8])
      (h ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩ (by simp [dumpFam_1_4_5_6_6_7_8]))

#print axioms not_dumpDomU0_1_4_5_6_6_7_8

/-- The U₀ census for box (1, 5, 5, 5, 6, 7, 8): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_5_5_5_6_7_8 :
    ∀ e ∈ dumpFam_1_5_5_5_6_7_8.edges,
      ¬ CapsDom (u0Of (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_5_5_5_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_5_6_7_8_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_5_6_7_8_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_5_5_5_6_7_8

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 5, 5, 5, 6, 7, 8)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_5_5_5_6_7_8 :
    ¬ DumpDomU0 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8 :=
  fun h =>
    not_capsDomU0all_1_5_5_5_6_7_8 ⟨6, 0, 73, 15, [(6, (6358 / 49491))]⟩
      (by simp [dumpFam_1_5_5_5_6_7_8])
      (h ⟨6, 0, 73, 15, [(6, (6358 / 49491))]⟩ (by simp [dumpFam_1_5_5_5_6_7_8]))

#print axioms not_dumpDomU0_1_5_5_5_6_7_8

/-- The U₀ census for box (1, 5, 5, 6, 6, 7, 8): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_5_5_6_6_7_8 :
    ∀ e ∈ dumpFam_1_5_5_6_6_7_8.edges,
      ¬ CapsDom (u0Of (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_5_5_6_6_7_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_6_7_8_0_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_6_7_8_1_6) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_6_7_8_1_6) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_5_5_6_6_7_8

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 5, 5, 6, 6, 7, 8)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_5_5_6_6_7_8 :
    ¬ DumpDomU0 (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8 :=
  fun h =>
    not_capsDomU0all_1_5_5_6_6_7_8 ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩
      (by simp [dumpFam_1_5_5_6_6_7_8])
      (h ⟨6, 0, 73, 15, [(6, (6 / 47))]⟩ (by simp [dumpFam_1_5_5_6_6_7_8]))

#print axioms not_dumpDomU0_1_5_5_6_6_7_8

/-- The U₀ census for box (1, 5, 5, 6, 7, 8, 8): ALL 4 strict witnesses are undominated at
the box-closure table (each cap strictly tighter than the entry at its pair). -/
theorem not_capsDomU0all_1_5_5_6_7_8_8 :
    ∀ e ∈ dumpFam_1_5_5_6_7_8_8.edges,
      ¬ CapsDom (u0Of (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) e.y e.caps e.x := by
  intro e he
  simp only [dumpFam_1_5_5_6_7_8_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | h0
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_7_8_8_0_2) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_7_8_8_1_2) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_7_8_8_1_2) (by norm_num)
  · exact not_capsDomU0_of_entry_lt (u0e_1_5_5_6_7_8_8_1_2) (by norm_num)
  · exact absurd h0 (by simp)

#print axioms not_capsDomU0all_1_5_5_6_7_8_8

/-- The VERDICT for the corrected datum: `DumpDomU0` is FALSE for box (1, 5, 5, 6, 7, 8, 8)'s strict
family (its first record is undominated at U₀, like all of them). -/
theorem not_dumpDomU0_1_5_5_6_7_8_8 :
    ¬ DumpDomU0 (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8 :=
  fun h =>
    not_capsDomU0all_1_5_5_6_7_8_8 ⟨2, 0, 49, 15, [(2, (311542 / 1639125))]⟩
      (by simp [dumpFam_1_5_5_6_7_8_8])
      (h ⟨2, 0, 49, 15, [(2, (311542 / 1639125))]⟩ (by simp [dumpFam_1_5_5_6_7_8_8]))

#print axioms not_dumpDomU0_1_5_5_6_7_8_8

/-- The corrected totality (the section-3 request's U₀-restricted mirror). -/
-- STANDING: DEFINITION
def dumpDomU0TotalData : Prop := ∀ b ∈ strictBoxes, DumpDomU0 b (dumpFamOf b)

/-- **The honest verdict on the corrected datum**: FALSE, already at the first box -- the
strict witnesses' caps are chain-implied bounds, strictly tighter than anything the box
closure stores; the J-half lives on the enumerated chains' closed tables, and its Lean
consumption is `capChainsRealized_of_chainDomU0` (the consumed chain's own trace
domination at the U₀-fixed start). -/
theorem not_dumpDomU0TotalData : ¬ dumpDomU0TotalData := by
  intro h
  have h1 := h (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) (by simp [strictBoxes])
  simp only [dumpFamOf] at h1
  exact not_dumpDomU0_1_3_4_4_5_5_7 h1

#print axioms not_dumpDomU0TotalData

/-- **The corrected consumption, static-datum form** (mirror of
`Fresh.CapChainsOfCarve.capChainsRealized_of_dumpDom` with U fixed at U₀ -- the shape the
glue consumes, both over-quantifiers removed): on a box whose family carries the U₀
domination datum, an arrangement realizing U₀'s bounds has its family's cap chains
realized.  The chain hypotheses are carried for shape compatibility; the datum itself is
static.  (For the 11 strict families the datum is refuted -- `not_dumpDomU0TotalData` --
so this consumes `capChainsRealized_of_chainDomU0`'s hypothesis shape instead.) -/
theorem capChainsRealized_of_dumpDomU0 (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g (u0Of n)) (hchain : ChainRealized g (u0Of n) a Aex steps)
    (hdd : DumpDomU0 n f) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  intro e he
  exact chainReal_of_capsDom hpos hfine0 (hdd e he)

#print axioms capChainsRealized_of_dumpDomU0

/-- **The corrected consumption, J-half form** (the honest home of the joinedge2 strict
witnesses): with the chain START fixed at the box-closure table U₀, every record's cap is
dominated by the consumed chain's own CLOSED TRACE table -- the joinedge2
join-of-all-chains datum, consumed per chain.  Mirror of
`Fresh.CapChainsOfCarve.capChainsRealized_of_chainDom` with U fixed at U₀: no arbitrary
table quantifier (the old bug), no empty-chain collapse (the J-domination is a hypothesis
on the consumed chain, not a ∀-steps claim). -/
theorem capChainsRealized_of_chainDomU0 (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g (u0Of n)) (hchain : ChainRealized g (u0Of n) a Aex steps)
    (hdom : ∀ e ∈ f.edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun (u0Of n) a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x) :
    capChainsRealized g f :=
  capChainsRealized_of_chainDom f hface (u0Of n) a Aex steps hfine0 hchain hdom

#print axioms capChainsRealized_of_chainDomU0

/- Compile-time machine check of the transcription (VM, not kernel): uncomment to re-run.
Verified run 2026-11-13: prints `true`, exit 0 (`/tmp/check_eval3.log`) -- all 22
census-pair entries agree with
`Fresh.UClosure.uMk`'s output exactly (value and strict flag). -/
-- #eval
--   (([
--     ((![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ), [(0, 6), (1, 6), (2, 6)]),
--     ((![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ), [(0, 6), (1, 6), (2, 6)]),
--     ((![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ), [(0, 5), (1, 5)]),
--     ((![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ), [(0, 3), (1, 3)]),
--     ((![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ), [(0, 6), (1, 6)]),
--     ((![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ), [(0, 2), (1, 2)]),
--   ]).all fun (b, ps) =>
--     ps.all fun p =>
--       match (u0Of b) p.1 p.2, (match uMk b with | some T => T p.1 p.2 | none => none) with
--       | some (q₀, s₀), some (q₁, s₁) => q₀ == q₁ && s₀ == s₁
--       | none, none => true
--       | _, _ => false)

/-! ## 5. THE FAITHFUL PREDICATE: `ChainDomPerRecord` (per-record, chain-indexed)

Both falsifications above pin down where the J-half domination actually lives: NOT on an
arbitrary realized table (`not_dumpDomTotalData`), NOT on the box-only closure `u0Of`
(`not_dumpDomU0TotalData` -- every one of the 52 strict caps is strictly tighter than the
U₀ entry at its pair), but on the ATTESTING CHAINS' closed-trace tables: for each record,
the joinedge2 dump v2 computes the set of chains whose closed-trace entry dominates EVERY
hop of the record's cap walk (`compute_att`: the attesting set is the INTERSECTION over
hops -- one chain must dominate every hop, because `CapsDom`'s composition needs a single
realized table across the walk; per-cap ∃-chains would not compose), and certifies the
count is positive for every strict-complete row.  The faithful predicate quantifies over
exactly that: a per-record ∃-attesting-chain datum.

`Attests` is run-conditioned: the empty chain from `u0Of` produces `u0Of` itself, which
provably does not dominate the strict caps (`not_capsDomU0all_*`), so a witness of the
∃ must be a genuine dominating run -- the predicate is neither trivially true nor
table-overshoots.  The per-arrangement form `ChainDomPerRecordG` adds the W₀-admission
half (the arrangement must REALIZE the attesting chain), which is the hypothesis shape
the consumption and the glue actually consume; the static form is the dump-side datum.
-/

/-- One record's attestation by one chain (the dump v2's per-witness `attaining_chains`
datum, `compute_att`): the chain -- run from the box's canonical closure start
`(u0Of n, 0, 1)` -- produces, whenever it succeeds, a closed-trace table dominating the
record's WHOLE cap walk.  Per-record: different records may be attested by different
chains. -/
-- STANDING: DEFINITION
def Attests (n : Fin 7 → ℤ) (e : ComposedEdge) (steps : List Step) : Prop :=
  ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
    chainRun (u0Of n) 0 1 steps = some (V, af, Af) → CapsDom V e.y e.caps e.x

/-- **THE FAITHFUL PREDICATE** (the corrected datum after both falsifications): every
record of the family carries an attesting chain -- the J-half domination is
chain-indexed, per record. -/
-- STANDING: DEFINITION
def ChainDomPerRecord (n : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ e ∈ f.edges, ∃ steps : List Step, Attests n e steps

/-- **The per-arrangement form** (the consumption's hypothesis shape): each record
carries an attesting chain that the arrangement `g` ADMITS (`ChainRealized g (u0Of n)
0 1 steps`) -- different records may use different admitted attesting chains. -/
-- STANDING: DEFINITION
def ChainDomPerRecordG (n : Fin 7 → ℤ) (f : ComposedFam) (g : Fin 7 → ℝ) : Prop :=
  ∀ e ∈ f.edges, ∃ steps : List Step,
    ChainRealized g (u0Of n) 0 1 steps ∧ Attests n e steps

/-- The static datum is the projection of the per-arrangement form (forgetting the
admission half). -/
theorem chainDomPerRecord_of_G {n : Fin 7 → ℤ} {f : ComposedFam} {g : Fin 7 → ℝ}
    (h : ChainDomPerRecordG n f g) : ChainDomPerRecord n f := fun e he =>
  (h e he).elim fun steps hp => ⟨steps, hp.2⟩

#print axioms chainDomPerRecord_of_G

/-- **THE CONSUMPTION** (the faithful predicate's per-arrangement form ⟹
`capChainsRealized`; mirrors `Fresh.CapChainsOfCarve.capChainsRealized_of_chainDom`'s
proof with the per-record ∃-quantifier): for each record, `g` admits an attesting chain;
`chain_fine_of_realized` extracts the admitted chain's closed trace (realized by `g`),
the attestation hands over `CapsDom` on that trace, and `chainReal_of_capsDom` realizes
the record's cap chain. -/
theorem capChainsRealized_of_chainDomPerRecordG (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hfine0 : UFine g (u0Of n)) (hdd : ChainDomPerRecordG n f g) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  intro e he
  obtain ⟨steps, hcr, hatt⟩ := hdd e he
  obtain ⟨Uf, af, Af, hrun, hfine, -⟩ := chain_fine_of_realized hpos hfine0 hcr
  exact chainReal_of_capsDom hpos hfine (hatt Uf af Af hrun)

#print axioms capChainsRealized_of_chainDomPerRecordG

/-- **The glue bridge**: the faithful predicate's per-arrangement form drops into
`Fresh.OneSidedGlue.oneSidedSound_of_composedData` verbatim -- on a covered box, the
per-record attesting-chain datum (with `g` admitting each record's witness chain) gives
the OneSided conclusion shape through the banked kill. -/
theorem oneSidedSound_of_chainDomPerRecordG (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (htotal : ComposedTotalOneSided b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b)) (hdd : ChainDomPerRecordG b (compFamOf b) g)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb htotal g hface
    (capChainsRealized_of_chainDomPerRecordG (compFamOf b) hface hfine0 hdd) hcarve

#print axioms oneSidedSound_of_chainDomPerRecordG

-- ========== section 6: the ChainDomPerRecord instantiation, box (1, 3, 4, 4, 5, 5, 7) ==========

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 4000000

/-- Assembly: a surviving `uAdd` whose keep-cur and back checks are ground-false returns
its propagation, and the propagated table is the transcribed one pointwise.  (Local copy
of `Fresh.ChainDomData.uAdd_eq_some` -- that file imports this one, so it cannot be
re-imported here.  The per-point facts are ground: concrete `Fin 7` pairs, literal ℚ
comparisons.) -/
theorem uAdd_eq_some' {U V : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = false)
    (hpt : ∀ p q, uProp U i j c s p q = V p q) :
    uAdd U i j c s = some V := by
  unfold uAdd
  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]
  exact congrArg some (funext fun p => funext fun q => hpt p q)

#print axioms uAdd_eq_some'

/-- Assembly: a `uStep` on positive numerators is its two `uAdd`s (`uGt_pos`), so the two
per-add facts compose to the step equation (local copy of
`Fresh.ChainDomData.uStep_eq_some`). -/
theorem uStep_eq_some' {U V W : UTable} {a b : Fin 7} {Aex A B : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (h1 : uAdd U a b (Aex / A) true = some V) (h2 : uAdd V b a (B / Aex) true = some W) :
    uStep U a b Aex A B = some W := by
  show (uGt U Aex a A b).bind (fun V => uGt V B b Aex a) = some W
  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]

#print axioms uStep_eq_some'

/-- The attesting-chain PREFIX for box (1, 3, 4, 4, 5, 5, 7): the first 14 steps of the dump's attesting chain (index 94 of the box's enumeration, word length 19).  Entries only tighten along a run (`uTighter` keeps the smaller bound), so the prefix run's closed trace already carries the dominating entries at all three record pairs (0,6), (1,6), (2,6) -- the first dominating propagation for (1,6)/(2,6) is add 27, inside step 14; the (0,6) entry is the chain's very first add. -/
def stepsP_1_3_4_4_5_5_7 : List Step := [
⟨(6 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(6 : Fin 7), (39 : ℚ), (41 : ℚ)⟩
]

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_1 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_1 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_2 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_2 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_3 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_3 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_4 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_4 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_5 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_5 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_6 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_6 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_7 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_7 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_8 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_8 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_9 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_9 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_10 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_10 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_11 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_11 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_12 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_12 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_13 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_13 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_14 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_14 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_15 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_15 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 8575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_16 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_16 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 8575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_17 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_17 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 65 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 65 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 325 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 325 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_18 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_18 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 65 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 65 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 325 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 325 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_19 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_19 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_20 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_20 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_21 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_21 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((75 / 11 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 33 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Transcribed prefix-trace table: T_1_3_4_4_5_5_7_22 (the mirror run's add-end snapshot). -/
def T_1_3_4_4_5_5_7_22 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 67275 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 4485 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((14739 / 2275 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((14739 / 15925 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6825 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_3_4_4_5_5_7 : uAdd (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_1 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, u0Of, u0Tab_1_3_4_4_5_5_7] <;> norm_num) (by simp [uBack, uBackCond, u0Of, u0Tab_1_3_4_4_5_5_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, u0Of, u0Tab_1_3_4_4_5_5_7, T_1_3_4_4_5_5_7_1] <;> norm_num)

/-- Add 2 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_2_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_1 (6 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T_1_3_4_4_5_5_7_2 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_1] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_1, T_1_3_4_4_5_5_7_2] <;> norm_num)

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_2 (6 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_3 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_2] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_2, T_1_3_4_4_5_5_7_3] <;> norm_num)

/-- Add 4 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_4_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_3 (5 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_4 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_3] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_3, T_1_3_4_4_5_5_7_4] <;> norm_num)

/-- Add 5 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_5_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_4 (5 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_5 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_4] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_4, T_1_3_4_4_5_5_7_5] <;> norm_num)

/-- Add 6 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_6_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_5 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_6 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_5] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_5, T_1_3_4_4_5_5_7_6] <;> norm_num)

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_6 (3 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_7 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_6] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_6, T_1_3_4_4_5_5_7_7] <;> norm_num)

/-- Add 8 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_8_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_7 (2 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_8 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_7] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_7, T_1_3_4_4_5_5_7_8] <;> norm_num)

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_8 (2 : Fin 7) (1 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_9 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_8] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_8, T_1_3_4_4_5_5_7_9] <;> norm_num)

/-- Add 10 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_10_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_9 (1 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_10 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_9] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_9, T_1_3_4_4_5_5_7_10] <;> norm_num)

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_10 (1 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_11 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_10] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_10, T_1_3_4_4_5_5_7_11] <;> norm_num)

/-- Add 12 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_12_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_11 (5 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_12 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_11] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_11, T_1_3_4_4_5_5_7_12] <;> norm_num)

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_12 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_13 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_12] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_12, T_1_3_4_4_5_5_7_13] <;> norm_num)

/-- Add 14 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_14_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_13 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_14 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_13] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_13, T_1_3_4_4_5_5_7_14] <;> norm_num)

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_14 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_15 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_14] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_14, T_1_3_4_4_5_5_7_15] <;> norm_num)

/-- Add 16 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_16_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_15 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_16 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_15] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_15, T_1_3_4_4_5_5_7_16] <;> norm_num)

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_16 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_17 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_16] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_16] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_16, T_1_3_4_4_5_5_7_17] <;> norm_num)

/-- Add 18 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_18_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_17 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_17 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_17] <;> norm_num

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_17 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_3_4_4_5_5_7_18 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_17] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_17] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_17, T_1_3_4_4_5_5_7_18] <;> norm_num)

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_18 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_18 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_18] <;> norm_num

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_18 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_4_5_5_7_19 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_18] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_18] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_18, T_1_3_4_4_5_5_7_19] <;> norm_num)

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_19 (6 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_4_5_5_7_19 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_19] <;> norm_num

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_19 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_3_4_4_5_5_7_20 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_19] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_19] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_19, T_1_3_4_4_5_5_7_20] <;> norm_num)

/-- Add 24 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_24_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_20 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_3_4_4_5_5_7_21 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_20] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_20] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_20, T_1_3_4_4_5_5_7_21] <;> norm_num)

/-- Add 25 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_25_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (4 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_21 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_21] <;> norm_num

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (25 : ℚ)) true = some T_1_3_4_4_5_5_7_21 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_21] <;> norm_num

/-- Add 27 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_27_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (1 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (39 : ℚ)) true = some T_1_3_4_4_5_5_7_22 :=
  uAdd_eq_some' (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_21] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_21] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_21, T_1_3_4_4_5_5_7_22] <;> norm_num)

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_22 (6 : Fin 7) (1 : Fin 7) ((41 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_22 := by 
  simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_22] <;> norm_num

/-- Step 1 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_1_1_3_4_4_5_5_7 : uStep (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_2 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_1_1_3_4_4_5_5_7) (addEq_2_1_3_4_4_5_5_7)

/-- Step 2 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_2_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_2 (6 : Fin 7) (5 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_4 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_3_1_3_4_4_5_5_7) (addEq_4_1_3_4_4_5_5_7)

/-- Step 3 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_3_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_4 (5 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_6 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_5_1_3_4_4_5_5_7) (addEq_6_1_3_4_4_5_5_7)

/-- Step 4 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_4_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_6 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_8 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_7_1_3_4_4_5_5_7) (addEq_8_1_3_4_4_5_5_7)

/-- Step 5 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_5_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_8 (2 : Fin 7) (1 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_10 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_9_1_3_4_4_5_5_7) (addEq_10_1_3_4_4_5_5_7)

/-- Step 6 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_6_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_10 (1 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_12 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_11_1_3_4_4_5_5_7) (addEq_12_1_3_4_4_5_5_7)

/-- Step 7 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_7_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_12 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_14 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_13_1_3_4_4_5_5_7) (addEq_14_1_3_4_4_5_5_7)

/-- Step 8 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_8_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_14 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_16 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_15_1_3_4_4_5_5_7) (addEq_16_1_3_4_4_5_5_7)

/-- Step 9 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_9_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_16 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_17 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_17_1_3_4_4_5_5_7) (addEq_18_1_3_4_4_5_5_7)

/-- Step 10 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_10_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_17 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_4_5_5_7_18 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_19_1_3_4_4_5_5_7) (addEq_20_1_3_4_4_5_5_7)

/-- Step 11 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_11_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_18 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_4_5_5_7_19 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_21_1_3_4_4_5_5_7) (addEq_22_1_3_4_4_5_5_7)

/-- Step 12 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_12_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_19 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_4_5_5_7_21 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_23_1_3_4_4_5_5_7) (addEq_24_1_3_4_4_5_5_7)

/-- Step 13 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_13_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_21 (4 : Fin 7) (1 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_21 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_25_1_3_4_4_5_5_7) (addEq_26_1_3_4_4_5_5_7)

/-- Step 14 of the attesting-chain prefix: the two adds compose through `uGt_pos`. -/
theorem stepEq_14_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_21 (1 : Fin 7) (6 : Fin 7) (17 : ℚ) (39 : ℚ) (41 : ℚ) = some T_1_3_4_4_5_5_7_22 :=
  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) (addEq_27_1_3_4_4_5_5_7) (addEq_28_1_3_4_4_5_5_7)

/-- The prefix extraction: whatever table the prefix run produces from `u0Of`, it IS the last transcribed one (the per-step `stepEq` equations pin every intermediate). -/
theorem traceP_1_3_4_4_5_5_7 {V : UTable} {af : Fin 7} {Af : ℚ} 
    (hrun : chainRun (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) 0 1 stepsP_1_3_4_4_5_5_7 = some (V, af, Af)) : 
    V = T_1_3_4_4_5_5_7_22 := by
  simp only [stepsP_1_3_4_4_5_5_7, chainRun] at hrun
  rw [stepEq_1_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_2_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_3_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_4_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_5_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_6_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_7_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_8_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_9_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_10_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_11_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_12_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_13_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_14_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

#print axioms traceP_1_3_4_4_5_5_7

/-- The per-record attestation: the prefix chain's closed-trace entry at (0, 6) is 1/7, dominating the record's cap 1/7. -/
theorem attests_1_3_4_4_5_5_7_p0 : Attests (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 0, 13, 3, [(6, (1/7 : ℝ))]⟩ stepsP_1_3_4_4_5_5_7 := by
  intro V af Af hrun
  have hV := traceP_1_3_4_4_5_5_7 hrun
  rw [hV]
  exact capsDom_single ⟨(1 / 7 : ℚ), true, by simp [T_1_3_4_4_5_5_7_22], by norm_num⟩

#print axioms attests_1_3_4_4_5_5_7_p0

/-- The per-record attestation: the prefix chain's closed-trace entry at (1, 6) is 17/39, dominating the record's cap 33/70. -/
theorem attests_1_3_4_4_5_5_7_p1 : Attests (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 1, 65, 31, [(6, (33/70 : ℝ))]⟩ stepsP_1_3_4_4_5_5_7 := by
  intro V af Af hrun
  have hV := traceP_1_3_4_4_5_5_7 hrun
  rw [hV]
  exact capsDom_single ⟨(17 / 39 : ℚ), true, by simp [T_1_3_4_4_5_5_7_22], by norm_num⟩

#print axioms attests_1_3_4_4_5_5_7_p1

/-- The per-record attestation: the prefix chain's closed-trace entry at (2, 6) is 51/91, dominating the record's cap 825/1457. -/
theorem attests_1_3_4_4_5_5_7_p4 : Attests (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ⟨6, 2, 5, 3, [(6, (825/1457 : ℝ))]⟩ stepsP_1_3_4_4_5_5_7 := by
  intro V af Af hrun
  have hV := traceP_1_3_4_4_5_5_7 hrun
  rw [hV]
  exact capsDom_single ⟨(51 / 91 : ℚ), true, by simp [T_1_3_4_4_5_5_7_22], by norm_num⟩

#print axioms attests_1_3_4_4_5_5_7_p4

/-- **The instantiation** (deliverable, honest count [T 1/11] in this file): box (1, 3, 4, 4, 5, 5, 7)'s strict-class family carries the faithful per-record datum -- every one of its 8 records is attested by the prefix chain (the (1,6)- and (2,6)-pair records share their pair attestations). -/
theorem chainDomPerRecord_1_3_4_4_5_5_7 :
    ChainDomPerRecord (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7 := by
  intro e he
  simp only [dumpFam_1_3_4_4_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p0⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p1⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p1⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p1⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p4⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p4⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p4⟩
  · exact ⟨stepsP_1_3_4_4_5_5_7, attests_1_3_4_4_5_5_7_p4⟩
  · exact absurd h0 (by simp)

#print axioms chainDomPerRecord_1_3_4_4_5_5_7


/-- The covered subset of the strict boxes: the boxes whose attesting chains are
transcribed in THIS file (honest count [T 1/11] here).  Boxes (1, 3, 4, 5, 6, 6, 7) and
(1, 4, 4, 5, 6, 6, 7) carry the same per-record datum in `Fresh.ChainDomData` (whose
`ChainDomData`/`chainDom_<box>` instances are the full-chain form of this section's
prefix-chain form); that file imports this one, so its instances cannot be re-imported
here without a cycle. -/
def chainDomPerRecordBoxes : Finset (Fin 7 → ℤ) :=
  {![1, 3, 4, 4, 5, 5, 7]}

/-- **THE DELIVERABLE** (honest scoping): the faithful per-record datum over the covered
subset.  The full `∀ b ∈ strictBoxes` totality is NOT claimed: the dump v2 certifies
attesting chains for all 11 strict boxes' records DATA-side, but a Lean instantiation
needs each box's attesting-chain trace transcribed (the 22-table transcription above is
one box).  Honest residual: boxes (1,3,4,5,6,6,7) and (1,4,4,5,6,6,7) are instantiated in
`Fresh.ChainDomData` (full-chain form); the other 8 strict boxes have NO single
sparse-start dominating chain (their records are dominated only from the full box closure
`mk n`, whose fold is not kernel-transcribable into the read-only `u0Of`) and need a
richer U₀ vocabulary -- the same rule-22 gap `Fresh.ChainDomData`'s coverage section
names. -/
-- STANDING: DEFINITION
def chainDomPerRecordData : Prop :=
  ∀ b ∈ chainDomPerRecordBoxes, ChainDomPerRecord b (dumpFamOf b)

/-- **The deliverable theorem**: [T 1/11] in this file (3/11 counting the same-side
`Fresh.ChainDomData` instances). -/
theorem chainDomPerRecord_data : chainDomPerRecordData := by
  intro b hb
  simp only [chainDomPerRecordBoxes, Finset.mem_singleton] at hb
  rcases hb with rfl
  simp [dumpFamOf, chainDomPerRecord_1_3_4_4_5_5_7]

#print axioms chainDomPerRecord_data

end Fresh.DumpDomData

