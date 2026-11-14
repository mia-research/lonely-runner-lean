import Fresh.WordCoverSide
import Fresh.ChainDomData

/-!
# SpineTotalProof: THE CONNECTION — ChainDomData + WordCoverSide + JoinFamComposed ⟹ the OneSided assembly shape

Written 2026-11-14.  New file; nothing existing is edited.  This is the composition theorem
of the OneSided branch: the three proved pieces compose to the assembly's `OneSidedSound`
conclusion shape with NO new mathematics — every step is an application of a banked lemma.

## The pieces that compose

1. **The data (per box)**: `Fresh.ChainDomData`'s banked per-box records — for every box
   `b` of the 3-box `chainDomBoxes` (the strict boxes carrying a single sparse-start
   dominator; the banked `chainDom_<box>` records, [T 3/3] instantiated there), a
   `ChainDomData b (compFamOf b)` record (dispatched by this file's
   `chainDomData_of_chainDomBoxes`): the
   attesting `W₀` chain `d.steps` (from the box's dump enumeration) plus the per-record
   J-domination `d.dom` — every banked record's cap walk is dominated by the consumed
   chain's OWN closed-trace table.  This is exactly the missing hypothesis of the corrected
   consumption `Fresh.DumpDomData.capChainsRealized_of_chainDomU0` (the twice-sharpened
   form: chain start fixed at the box-closure table `u0Of b`, the J-domination carried by
   the consumed chain, no arbitrary-table quantifier, no empty-chain collapse —
   `Fresh.DumpDomData` proved both `DumpDom` and `DumpDomU0` uninstantiable for these
   families).
2. **The banked family data**: `Fresh.OneSidedComposed.oneSidedTotalData` — the per-box
   `ComposedFamData (compFamOf b)` [T 68/68], and the engine
   `Fresh.JoinFamComposed.composedFamRefutes` (datum + realized demand + realized chain ⟹
   False, through `composedCap_conflict`).
3. **Direction (b)**: `Fresh.WordCoverSide.wordCover_demands` — a realized `W₁` word's edge
   demand + the realized chains + family exhaustiveness + the banked datum ⟹ False (the
   seam lemma `wordEdge_demand` is its engine), with the two data-side OWEDs it consumes
   (`NoClearPointWordRealized`, `FamilyCoversWordEdges`) carried as hypotheses, NOT assumed.

## The composition (all proved here, each theorem closed)

* `bridge_of_dom` — the corrected consumption at the datum's own `(steps, dom)` shape;
* `composedConflict_of_chainDom` — THE COMPOSED CONFLICT: covered box + `ChainDomData` +
  `g` in the box realizing `u0Of b` and admitting the attesting chain (the W₀-conditional,
  per-chain form) + no `W₁` clear point + family exhaustiveness ⟹ **False** (route:
  `ChainDomData` ⟹ `capChainsRealized` via `capChainsRealized_of_chainDomU0`; no clear
  point ⟹ realized word via `NoClearPointWordRealized`; word edges ⟹ family via
  `FamilyCoversWordEdges`; `wordCover_demands` + `oneSidedTotalData` fire the composed
  conflict);
* `oneSidedSound_of_chainDom` — the assembly shape: same hypotheses minus the no-clear-point
  hypothesis ⟹ the `W₁` clear point exists (`∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1/8 : ℝ) ≤
  distInt (g i * (s/8))`) — verbatim the conclusion of
  `Fresh.FilterAssembly.OneSidedSound`, in the composed-family form the glue consumes;
* `crossCheck_of_dom` — the same shape landed verbatim in
  `Fresh.WordCoverSide.oneSidedSound_of_wordCover` (the banked direction-(b) glue), as a
  shape cross-check;
* `chainDomBoxes_subset_coveredSet` + `chainDomData_of_chainDomBoxes` +
  `spineTotal_of_chainDomBoxes` + the three per-box instances — the totality: for every box
  of `chainDomBoxes`, the composition holds with the datum supplied by the banked
  per-box records;
* `oneSidedSoundAt_of_carveChain` — the carve-conditional consumption: GIVEN the named OWED
  `CarveRealizesChainAt b d.steps`, NO hypothesis on `g` beyond the box + carve remains —
  the OneSided kill exactly as `Fresh.FilterAssembly.OneSidedSound`'s docstring describes
  ("the artifact kill is conditional on a `W₀` chain").

## What is OWED (named, data-side, honestly NOT assumed anywhere here)

* `CarveRealizesChainAt` — carve ⟹ the arrangement realizes `u0Of b` AND admits the
  attesting chain (direction (a)'s remaining piece, per-chain form).  Honest note: the
  `u0Of` realization is NOT derivable from the box interval alone (the `u0Tab` entries at
  the census pairs are tighter than the face ratios — e.g. box (1,3,4,4,5,5,7) entry
  `2/13` at `(0,6)` vs the face maximum `3/13`), which is exactly why it enters as part of
  the W₀-conditional rather than as an interval fact — the form the `Fresh.SpineTotalData`
  no-go lemmas demand.
* `Fresh.WordCoverSide.NoClearPointWordRealized` / `FamilyCoversWordEdges` — direction (b)'s
  two data-side OWEDs (the finite closed-interval covering refinement; the per-box family
  exhaustiveness of the dump), consumed as hypotheses of the composition, per the banked
  files' accounting.
* The verbatim `Fresh.FilterAssembly.OneSidedSound` consumption additionally needs the
  per-box `JoinFam` conversion of the composed records (the `8m±1` numerator bookkeeping on
  raw `C/D` edges that composed cap chains subsume — `Fresh.OneSidedGlue`'s named residual)
  and the corresponding data for the 65 other covered boxes / 8 residual strict boxes —
  outside this file's scope, documented not assumed.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound) — `sorryAx` is failure.
-/

namespace Fresh.SpineTotalProof

open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedComposed
  Fresh.OneSidedGlue Fresh.WordCoverSide Fresh.CapChainsOfCarve Fresh.DumpDomData
  Fresh.UClosure Fresh.ChainDomData Fresh.FrontierFamilyCap

/-! ## 1. The corrected consumption at the datum's own shape -/

/-- **The bridge at the `(steps, dom)` level** (the datum's own shape): the attesting
chain's `dom` field drops into the corrected consumption
`Fresh.DumpDomData.capChainsRealized_of_chainDomU0` verbatim — chain start fixed at the
box-closure table `u0Of b`, the J-domination carried by the consumed chain's closed trace.
This is the KEY CONNECTION (step 2 of the proof route): the family's cap values are
dominated by the W₀ chain's trace entries, so a realized chain realizes the family's
composed cap chains. -/
theorem bridge_of_dom (b : Fin 7 → ℤ) (f : ComposedFam) (steps : List Step)
    (hdom : ∀ e ∈ f.edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun (u0Of b) 0 1 steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b)) (hchain : ChainRealized g (u0Of b) 0 1 steps) :
    capChainsRealized g f :=
  capChainsRealized_of_chainDomU0 f hface 0 1 steps hfine0 hchain hdom

#print axioms bridge_of_dom

/-! ## 2. THE COMPOSED CONFLICT -/

/-- **THE COMPOSED CONFLICT** (the connection theorem, conflict form): on a covered box `b`
carrying its `ChainDomData` (the attesting chain + per-record closed-trace domination), an
arrangement `g` in the box that realizes `u0Of b` and admits the attesting chain (the
W₀-conditional, per-chain form), admits NO `W₁` clear point, and whose realized word edges
the family exhausts — cannot exist.  Route (each step a banked lemma):
`ChainDomData` ⟹ `capChainsRealized` (`capChainsRealized_of_chainDomU0`, through
`chain_fine_of_realized` + `chainReal_of_capsDom`); no clear point ⟹ realized word
(`NoClearPointWordRealized`); word edges ⟹ family records (`FamilyCoversWordEdges`);
`wordCover_demands` + the banked `oneSidedTotalData b hb` fire the composed conflict
(`composedFamRefutes` / `composedCap_conflict`). -/
theorem composedConflict_of_chainDom (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (d : ChainDomData b (compFamOf b))
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b)) (hchain : ChainRealized g (u0Of b) 0 1 d.steps)
    (hnoclear : ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))))
    (hword : NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b)) :
    False := by
  -- step 2: the family's cap records are dominated by the consumed chain's closed trace
  have hchains : capChainsRealized g (compFamOf b) :=
    capChainsRealized_of_chainDomU0 (compFamOf b) hface 0 1 d.steps hfine0 hchain
      (fun e he V af Af hrun => d.dom e he V af Af hrun)
  -- step 3: no W₁ clear point ⟹ a W₁ word is realized on g
  obtain ⟨w, hw⟩ := hword hnoclear
  -- step 4: demand + composed cap-chain with datum ≤ 1 ⟹ the conflict fires
  exact wordCover_demands (oneSidedTotalData b hb) hchains hw (hexh g w hface hw)

#print axioms composedConflict_of_chainDom

/-! ## 3. THE ASSEMBLY SHAPE -/

/-- **THE ASSEMBLY SHAPE** (`oneSidedSound_of_chainDom`): the composed conflict, read in the
contrapositive — for a covered box carrying its `ChainDomData`, an arrangement in the box
that realizes `u0Of b` and admits the attesting chain ADMITS a `W₁` clear point over its
faces.  The conclusion is verbatim `Fresh.FilterAssembly.OneSidedSound`'s conclusion shape,
with the family the banked `compFamOf b` and the W₀-conditional the per-chain form
`ChainDomData` carries (the artifact kill IS conditional on a `W₀` chain — the assembly
hypothesis carries the condition, per `Fresh.FilterAssembly.OneSidedSound`'s docstring). -/
theorem oneSidedSound_of_chainDom (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (d : ChainDomData b (compFamOf b))
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b)) (hchain : ChainRealized g (u0Of b) 0 1 d.steps)
    (_hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  by_contra hnoc
  exact composedConflict_of_chainDom b hb d hface hfine0 hchain hnoc (hword g) hexh

#print axioms oneSidedSound_of_chainDom

/-- **Shape cross-check**: the composition lands verbatim in
`Fresh.WordCoverSide.oneSidedSound_of_wordCover` — the banked direction-(b) glue — with the
bridge supplied by the corrected consumption.  (Same hypotheses, same conclusion; the
banked file's own proof goes through `Fresh.OneSidedGlue.oneSidedSound_of_composedData`.) -/
theorem crossCheck_of_dom (b : Fin 7 → ℤ) (hb : b ∈ coveredSet) (steps : List Step)
    (hdom : ∀ e ∈ (compFamOf b).edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun (u0Of b) 0 1 steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b)) (hchain : ChainRealized g (u0Of b) 0 1 steps)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_wordCover b hb hword hexh g hface
    (bridge_of_dom b (compFamOf b) steps hdom hface hfine0 hchain) hcarve

#print axioms crossCheck_of_dom

/-! ## 4. The chainDomBoxes totality and the coveredSet inclusion -/

/-- coveredSet membership, box (1,3,4,4,5,5,7) (Or-walk over the literal: `simp only`
rewrites membership into the equality chain, the `mem_insert_self`/`mem_insert_of_mem` walk
descends to the matching insert, no decidability needed). -/
theorem covered_1_3_4_4_5_5_7 :
    (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_5_5_7

/-- coveredSet membership, box (1,3,4,5,6,6,7). -/
theorem covered_1_3_4_5_6_6_7 :
    (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_6_7

/-- coveredSet membership, box (1,4,4,5,6,6,7). -/
theorem covered_1_4_4_5_6_6_7 :
    (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_4_5_6_6_7

/-- The datum's boxes are covered boxes (`chainDomBoxes ⊆ coveredSet`): every box carrying
a `ChainDomData` also carries its banked `ComposedFamData` — the composition's two data
sides are available simultaneously on `chainDomBoxes`. -/
theorem chainDomBoxes_subset_coveredSet : ∀ b ∈ chainDomBoxes, b ∈ coveredSet := by
  intro b hb
  simp only [chainDomBoxes, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · exact covered_1_3_4_4_5_5_7
  · exact covered_1_3_4_5_6_6_7
  · exact covered_1_4_4_5_6_6_7

#print axioms chainDomBoxes_subset_coveredSet

/-- **The per-box datum dispatch, decidable form**: for every box of `chainDomBoxes`, the
banked `ChainDomData` record exists at the `compFamOf` dispatch — proven by DECIDABLE case
analysis (`by_cases`/`dite`, legal elimination into the data sort; a `rcases`-on-membership
proof is banned here because `ChainDomData` is a data structure, not a proposition).  Each
branch dispatches to the banked per-box record `chainDom_<box>` with the family defeq
`compFamOf <literal box> = compFam_<box>`.  (A `def`, not a `theorem`: the dispatch
produces data.) -/
def chainDomData_of_chainDomBoxes (b : Fin 7 → ℤ) (hb : b ∈ chainDomBoxes) :
    ChainDomData b (compFamOf b) := by
  by_cases h1 : b = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
  · rw [h1]
    simpa [compFamOf] using chainDom_1_3_4_4_5_5_7
  · by_cases h2 : b = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
    · rw [h2]
      simpa [compFamOf] using chainDom_1_3_4_5_6_6_7
    · by_cases h3 : b = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      · rw [h3]
        simpa [compFamOf] using chainDom_1_4_4_5_6_6_7
      · simp [chainDomBoxes, Finset.mem_insert, Finset.mem_singleton, h1, h2, h3] at hb

#print axioms chainDomData_of_chainDomBoxes

/-- **THE TOTALITY** (`spineTotal_of_chainDomBoxes`): for EVERY box of `chainDomBoxes`, the
three proved pieces compose to the assembly shape — the datum taken at its banked record
shape (`ChainDomData b (compFamOf b)`, discharged by `chainDomData_of_chainDomBoxes` or
verbatim by a banked `chainDom_<box>`), the family the banked `compFamOf` dispatch,
direction (b) the banked word-cover side.  No new mathematics: this is
`oneSidedSound_of_chainDom` with the datum and the coveredSet membership discharged. -/
theorem spineTotal_of_chainDomBoxes (b : Fin 7 → ℤ) (hb : b ∈ chainDomBoxes)
    (d : ChainDomData b (compFamOf b))
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hfine0 : UFine g (u0Of b))
    (hchain : ChainRealized g (u0Of b) 0 1 d.steps)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_chainDom b (chainDomBoxes_subset_coveredSet b hb) d
    hword hexh hface hfine0 hchain hcarve

#print axioms spineTotal_of_chainDomBoxes

/-! ## 5. The per-box instances -/

/-- **Per-box instance, box (1,3,4,4,5,5,7)**: the assembly shape at the box's own attesting
chain `steps_1_3_4_4_5_5_7` — the datum the banked `chainDom_1_3_4_4_5_5_7` record carries
(dispatched directly, no projection through the tactic-proof totality). -/
theorem spineTotal_1_3_4_4_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hfine0 : UFine g (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hchain : ChainRealized g (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) 0 1
      steps_1_3_4_4_5_5_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_chainDom (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) covered_1_3_4_4_5_5_7
    chainDom_1_3_4_4_5_5_7 hword hexh hface hfine0 hchain hcarve

#print axioms spineTotal_1_3_4_4_5_5_7

/-- **Per-box instance, box (1,3,4,5,6,6,7)**: the assembly shape at the box's own attesting
chain `steps_1_3_4_5_6_6_7` — the datum the banked `chainDom_1_3_4_5_6_6_7` record carries. -/
theorem spineTotal_1_3_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hfine0 : UFine g (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hchain : ChainRealized g (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) 0 1
      steps_1_3_4_5_6_6_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_chainDom (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) covered_1_3_4_5_6_6_7
    chainDom_1_3_4_5_6_6_7 hword hexh hface hfine0 hchain hcarve

#print axioms spineTotal_1_3_4_5_6_6_7

/-- **Per-box instance, box (1,4,4,5,6,6,7)**: the assembly shape at the box's own attesting
chain `steps_1_4_4_5_6_6_7` — the datum the banked `chainDom_1_4_4_5_6_6_7` record carries. -/
theorem spineTotal_1_4_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hfine0 : UFine g (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hchain : ChainRealized g (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) 0 1
      steps_1_4_4_5_6_6_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_chainDom (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) covered_1_4_4_5_6_6_7
    chainDom_1_4_4_5_6_6_7 hword hexh hface hfine0 hchain hcarve

#print axioms spineTotal_1_4_4_5_6_6_7

/-! ## 6. The carve-conditional consumption and the named OWED -/

/-- **OWED — the carve-implies-chain direction** (data-side, honestly NOT assumed in the
theorems above; direction (a)'s remaining piece at the per-chain form): for an in-box
arrangement carving `[1,7]`, it realizes the box-closure table `u0Of b` AND admits the
attesting chain.  Without it the kill stays W₀-chain-conditional — which is exactly the
form the artifact's one-sided kill takes (per `Fresh.FilterAssembly.OneSidedSound`'s
docstring).  Honest note: the `u0Of` realization is NOT interval-forced (see the module
docstring), so this OWED is not reducible to face arithmetic — it is the same
data-side machinery the carve/consumption line owes. -/
-- STANDING: OWED
def CarveRealizesChainAt (b : Fin 7 → ℤ) (steps : List Step) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) →
    CarvesOneSeven (Finset.image g Finset.univ) →
    UFine g (u0Of b) ∧ ChainRealized g (u0Of b) 0 1 steps

/-- **The carve-conditional consumption**: on a `chainDomBoxes` box carrying its banked
datum, GIVEN the OWED `CarveRealizesChainAt` at the datum's own attesting chain (plus
direction (b)'s two data-side OWEDs), the assembly shape holds with NO hypothesis on `g`
beyond the box + carve — the OneSided kill exactly as the assembly's soundness hypothesis
consumes it (modulo the `JoinFam` conversion residual, see the module docstring). -/
theorem oneSidedSoundAt_of_carveChain (b : Fin 7 → ℤ) (hb : b ∈ chainDomBoxes)
    (d : ChainDomData b (compFamOf b))
    (hcarvechain : CarveRealizesChainAt b d.steps)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  obtain ⟨hfine0, hchain⟩ := hcarvechain g hface hcarve
  exact spineTotal_of_chainDomBoxes b hb d hword hexh hface hfine0 hchain hcarve

#print axioms oneSidedSoundAt_of_carveChain

end Fresh.SpineTotalProof
