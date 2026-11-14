import Fresh.WordCoverSide
import Fresh.SpineSound
import Fresh.SpineTotalData
import Fresh.DumpDomData

/-!
# TotalityLifts: the mechanical per-box totality lift instantiations — 68 one-sided + 5 pairwise

Written 2026-11-15.  New file; nothing existing is edited.  This file instantiates, box by box,
the per-box totality lifts that feed the assembly chain

  `ComposedFamData → ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`

mirroring the `spineFamData` pattern of `Fresh.SpineTotalData` (per-box banked datum +
per-box consumption theorem).  NO new mathematics: every per-box theorem is a one-line
application of a banked lemma; the box-specific content is (i) the `coveredSet` membership
(the 68-deep insert walk), (ii) the `compFamOf` dispatch, (iii) the wiring.

Per one-sided box `b` (all 68 of `Fresh.OneSidedComposed.coveredSet`), five theorems:

* `covered_<box>` — membership, so the banked data `oneSidedTotalData b hb` is available;
* `spineFamDataOS_<box>` — the `spineFamData` mirror: `InRange17 b ∧ ComposedFamData
  (compFamOf b)`, the two data-side engine hypotheses DISCHARGED (no hypotheses);
* `composedConflict_<box>` — the word-cover KILL at the box: the banked `ComposedFamData`
  record consumed through the composed-cap engine (`wordCover_demands` →
  `composedFamRefutes` → `composedCap_conflict`) — realized word + realized chains +
  family exhaustiveness ⟹ False;
* `totalLift_<box>` — THE TOTALITY INSTANCE: `ComposedTotalOneSided b (compFamOf b)`,
  from the two named data-side OWEDs (`NoClearPointWordRealized` — box-independent, and
  `FamilyCoversWordEdges b (compFamOf b)` — the per-box exhaustiveness datum);
* `oneSidedSound_<box>` — THE CONSUMPTION: the totality instance through THE GLUE
  (`oneSidedSound_of_composedData`) to `Fresh.FilterAssembly.OneSidedSound`'s exact
  conclusion shape (a `W₁` clear point over the faces).

The 11 STRICT boxes (every death row strict-complete in `joinedge2_perbox_v1.jsonl`,
census section 7; the dump v2 data is richest there) additionally get the D-variants
`composedConflictD_/totalLiftD_/oneSidedSoundD_<box>` at the strict-class `dumpFam_<box>`
families of `Fresh.DumpDomData`, through this file's family-general retargetings
(`composedConflict_fam`, `composedTotal_of_wordCover_fam`, `oneSidedSound_of_total_fam`)
— the same lifts at the dump v2 families, consuming `dumpFamData_<box>`.

The 5 pairwise (two-sided) boxes get `pairwiseSound_<box>`: the banked `spineFamData_<id>`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family, `Fresh.SpineTotalData`) is
DISCHARGED — no longer a hypothesis — and `Fresh.FilterAssembly.PairwiseSound`'s exact
conclusion shape reduces to the pairwise totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`).

Totals: `totalLifts_of_exhaustiveness` (all 68 lifts from the two OWEDs),
`oneSidedSounds_of_totals` (all 68 consumptions), `oneSidedSound_of_exhaustiveness`
(the full chain in one theorem), `pairwiseSound_of_total` (the pairwise shape).

OWED (named, data-side, honestly carried as HYPOTHESES, per the banked files' accounting):
* `Fresh.WordCoverSide.NoClearPointWordRealized` — the `W₁`-word covering direction (the
  finite closed-interval covering argument; direction (b)'s word side), box-independent.
  NOTE: `Fin 7` contains `0`, so the probe proposition `∀ i : Fin 7, 1 ≤ i.val` is FALSE —
  the assembly's `InRange17` is about the box tuple's values, not the index.
* `FamilyCoversWordEdges b (compFamOf b)` — the per-box family exhaustiveness (the dump's
  word-edge totality).  Honest residual: the banked `compFam_<box>` families carry the TOP
  records by death count (4, or 8 on the three census-fully-covered boxes), not the full
  dump families (e.g. 551 chain-side family edges for box (1,2,3,4,4,5,7)); the
  exhaustiveness OWED at the banked families is therefore a SHARPENING target (a full-dump
  family instantiation), not a consequence of the banked data.  The D-variants carry the
  same OWED at the strict-class `dumpFam` families (same top-record shape).
* The verbatim `Fresh.FilterAssembly.OneSidedSound` HYPOTHESIS shape additionally needs the
  per-box `JoinFam` conversion of the composed records (the `8m±1` numerator bookkeeping) —
  the named residual of `Fresh.OneSidedGlue`; the consumptions here are in the glue's
  W₀-chain-conditional shape (`capChainsRealized`), with the conclusion shape verbatim.

No-go context (proved in `Fresh.SpineTotalData`): the totality is NOT interval-reducible
(`capDerivedDemand_unsat`, `intervalForcedDemand_capUnsat`, `intervalForcedPair_invalid`),
which is exactly why the lifts enter through the W₀-conditional bridge and the word-cover
side, not through `FaceLo`/`FaceHi` forcing.

All arithmetic is exact (`decide`/banked `norm_num`; floats nowhere).  Every theorem carries
`#print axioms`; the accepted profile is the standard three (propext, Classical.choice,
Quot.sound) — `sorryAx` is failure.
-/

namespace Fresh.TotalityLifts

open Fresh.FilterAssembly Fresh.SpineSound Fresh.SpineTotalData Fresh.JoinFamComposed
  Fresh.OneSidedComposed Fresh.OneSidedGlue Fresh.WordCoverSide Fresh.DumpDomData
  Fresh.FrontierFamilyCap

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

/-! ### Box (1, 3, 4, 4, 5, 5, 7) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 3, 4, 4, 5, 5, 7) carries the banked family
`compFam_1_3_4_4_5_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_4_5_5_7 :
    (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_5_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 4, 5, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_4_5_5_7 :
    InRange17 (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_4_5_5_7⟩

#print axioms spineFamDataOS_1_3_4_4_5_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 4, 5, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_4_5_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_4_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_4_5_5_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_4_5_5_7

/-- **The per-box totality lift, box (1, 3, 4, 4, 5, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_4_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_4_5_5_7 hword hexh

#print axioms totalLift_1_3_4_4_5_5_7

/-- **The per-box consumption, box (1, 3, 4, 4, 5, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_4_5_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_4_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_4_5_5_7

/-- **The strict-class conflict, box (1, 3, 4, 4, 5, 5, 7)**: the word-cover kill at the strict-class
family `dumpFam_1_3_4_4_5_5_7` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_3_4_4_5_5_7` datum. -/
theorem composedConflictD_1_3_4_4_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_4_5_5_7)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_3_4_4_5_5_7 hexh hface hchains hw

#print axioms composedConflictD_1_3_4_4_5_5_7

/-- **The strict-class totality lift, box (1, 3, 4, 4, 5, 5, 7)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_3_4_4_5_5_7` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_3_4_4_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7) :
    ComposedTotalOneSided (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_3_4_4_5_5_7

/-- **The strict-class consumption, box (1, 3, 4, 4, 5, 5, 7)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_3_4_4_5_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_4_5_5_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_4_5_5_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_3_4_4_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_3_4_4_5_5_7

/-! ### Box (1, 3, 4, 5, 5, 5, 7) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 5, 5, 7) carries the banked family
`compFam_1_3_4_5_5_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_5_5_7 :
    (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_5_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 5, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_5_5_7 :
    InRange17 (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_5_5_7⟩

#print axioms spineFamDataOS_1_3_4_5_5_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 5, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_5_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_5_5_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_5_5_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 5, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_5_5_7 hword hexh

#print axioms totalLift_1_3_4_5_5_5_7

/-- **The per-box consumption, box (1, 3, 4, 5, 5, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_5_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_5_5_7

/-- **The strict-class conflict, box (1, 3, 4, 5, 5, 5, 7)**: the word-cover kill at the strict-class
family `dumpFam_1_3_4_5_5_5_7` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_3_4_5_5_5_7` datum. -/
theorem composedConflictD_1_3_4_5_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_5_5_7)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_3_4_5_5_5_7 hexh hface hchains hw

#print axioms composedConflictD_1_3_4_5_5_5_7

/-- **The strict-class totality lift, box (1, 3, 4, 5, 5, 5, 7)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_3_4_5_5_5_7` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_3_4_5_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_3_4_5_5_5_7

/-- **The strict-class consumption, box (1, 3, 4, 5, 5, 5, 7)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_3_4_5_5_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_5_5_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_5_5_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_3_4_5_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_3_4_5_5_5_7

/-! ### Box (1, 3, 4, 5, 6, 6, 7) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 6, 7) carries the banked family
`compFam_1_3_4_5_6_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_6_7 :
    (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_6_7 :
    InRange17 (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_6_7⟩

#print axioms spineFamDataOS_1_3_4_5_6_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_6_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_6_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_6_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_6_7 hword hexh

#print axioms totalLift_1_3_4_5_6_6_7

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_6_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_6_7

/-- **The strict-class conflict, box (1, 3, 4, 5, 6, 6, 7)**: the word-cover kill at the strict-class
family `dumpFam_1_3_4_5_6_6_7` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_3_4_5_6_6_7` datum. -/
theorem composedConflictD_1_3_4_5_6_6_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_6_6_7)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_3_4_5_6_6_7 hexh hface hchains hw

#print axioms composedConflictD_1_3_4_5_6_6_7

/-- **The strict-class totality lift, box (1, 3, 4, 5, 6, 6, 7)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_3_4_5_6_6_7` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_3_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_3_4_5_6_6_7

/-- **The strict-class consumption, box (1, 3, 4, 5, 6, 6, 7)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_3_4_5_6_6_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_3_4_5_6_6_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_6_6_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_3_4_5_6_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_3_4_5_6_6_7

/-! ### Box (1, 3, 4, 5, 7, 7, 9) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 7, 7, 9) carries the banked family
`compFam_1_3_4_5_7_7_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_7_7_9 :
    (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_7_7_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 7, 7, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_7_7_9 :
    InRange17 (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_7_7_9⟩

#print axioms spineFamDataOS_1_3_4_5_7_7_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 7, 7, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_7_7_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_7_7_9
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_7_7_9) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_7_7_9

/-- **The per-box totality lift, box (1, 3, 4, 5, 7, 7, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_7_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_7_7_9 hword hexh

#print axioms totalLift_1_3_4_5_7_7_9

/-- **The per-box consumption, box (1, 3, 4, 5, 7, 7, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_7_7_9
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_7_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_7_7_9

/-- **The strict-class conflict, box (1, 3, 4, 5, 7, 7, 9)**: the word-cover kill at the strict-class
family `dumpFam_1_3_4_5_7_7_9` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_3_4_5_7_7_9` datum. -/
theorem composedConflictD_1_3_4_5_7_7_9
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_7_7_9)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_3_4_5_7_7_9 hexh hface hchains hw

#print axioms composedConflictD_1_3_4_5_7_7_9

/-- **The strict-class totality lift, box (1, 3, 4, 5, 7, 7, 9)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_3_4_5_7_7_9` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_3_4_5_7_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9) :
    ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_3_4_5_7_7_9

/-- **The strict-class consumption, box (1, 3, 4, 5, 7, 7, 9)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_3_4_5_7_7_9
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) dumpFam_1_3_4_5_7_7_9)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_3_4_5_7_7_9)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_3_4_5_7_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_3_4_5_7_7_9

/-! ### Box (1, 4, 4, 5, 6, 6, 7) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 4, 4, 5, 6, 6, 7) carries the banked family
`compFam_1_4_4_5_6_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_4_5_6_6_7 :
    (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_4_5_6_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 4, 5, 6, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_4_5_6_6_7 :
    InRange17 (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_4_5_6_6_7⟩

#print axioms spineFamDataOS_1_4_4_5_6_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 4, 5, 6, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_4_5_6_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_4_5_6_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_4_5_6_6_7) hexh hface hchains hw

#print axioms composedConflict_1_4_4_5_6_6_7

/-- **The per-box totality lift, box (1, 4, 4, 5, 6, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_4_5_6_6_7 hword hexh

#print axioms totalLift_1_4_4_5_6_6_7

/-- **The per-box consumption, box (1, 4, 4, 5, 6, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_4_5_6_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_4_5_6_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_4_5_6_6_7

/-- **The strict-class conflict, box (1, 4, 4, 5, 6, 6, 7)**: the word-cover kill at the strict-class
family `dumpFam_1_4_4_5_6_6_7` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_4_4_5_6_6_7` datum. -/
theorem composedConflictD_1_4_4_5_6_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_4_5_6_6_7)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_4_4_5_6_6_7 hexh hface hchains hw

#print axioms composedConflictD_1_4_4_5_6_6_7

/-- **The strict-class totality lift, box (1, 4, 4, 5, 6, 6, 7)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_4_4_5_6_6_7` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_4_4_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7) :
    ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_4_4_5_6_6_7

/-- **The strict-class consumption, box (1, 4, 4, 5, 6, 6, 7)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_4_4_5_6_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_4_5_6_6_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_4_5_6_6_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_4_4_5_6_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_4_4_5_6_6_7

/-! ### Box (1, 4, 5, 5, 5, 6, 7) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 4, 5, 5, 5, 6, 7) carries the banked family
`compFam_1_4_5_5_5_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_5_6_7 :
    (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_5_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 5, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_5_6_7 :
    InRange17 (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_5_6_7⟩

#print axioms spineFamDataOS_1_4_5_5_5_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 5, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_5_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_5_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_5_6_7) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_5_6_7

/-- **The per-box totality lift, box (1, 4, 5, 5, 5, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_5_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_5_6_7 hword hexh

#print axioms totalLift_1_4_5_5_5_6_7

/-- **The per-box consumption, box (1, 4, 5, 5, 5, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_5_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_5_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_5_6_7

/-- **The strict-class conflict, box (1, 4, 5, 5, 5, 6, 7)**: the word-cover kill at the strict-class
family `dumpFam_1_4_5_5_5_6_7` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_4_5_5_5_6_7` datum. -/
theorem composedConflictD_1_4_5_5_5_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_5_5_6_7)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_4_5_5_5_6_7 hexh hface hchains hw

#print axioms composedConflictD_1_4_5_5_5_6_7

/-- **The strict-class totality lift, box (1, 4, 5, 5, 5, 6, 7)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_4_5_5_5_6_7` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_4_5_5_5_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7) :
    ComposedTotalOneSided (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_4_5_5_5_6_7

/-- **The strict-class consumption, box (1, 4, 5, 5, 5, 6, 7)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_4_5_5_5_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) dumpFam_1_4_5_5_5_6_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_5_5_6_7)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_4_5_5_5_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_4_5_5_5_6_7

/-! ### Box (1, 4, 5, 5, 6, 7, 9) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 4, 5, 5, 6, 7, 9) carries the banked family
`compFam_1_4_5_5_6_7_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_6_7_9 :
    (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_6_7_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 6, 7, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_6_7_9 :
    InRange17 (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_6_7_9⟩

#print axioms spineFamDataOS_1_4_5_5_6_7_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 6, 7, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_6_7_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_6_7_9
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_6_7_9) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_6_7_9

/-- **The per-box totality lift, box (1, 4, 5, 5, 6, 7, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_6_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_6_7_9 hword hexh

#print axioms totalLift_1_4_5_5_6_7_9

/-- **The per-box consumption, box (1, 4, 5, 5, 6, 7, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_6_7_9
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_6_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_6_7_9

/-- **The strict-class conflict, box (1, 4, 5, 5, 6, 7, 9)**: the word-cover kill at the strict-class
family `dumpFam_1_4_5_5_6_7_9` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_4_5_5_6_7_9` datum. -/
theorem composedConflictD_1_4_5_5_6_7_9
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_5_6_7_9)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_4_5_5_6_7_9 hexh hface hchains hw

#print axioms composedConflictD_1_4_5_5_6_7_9

/-- **The strict-class totality lift, box (1, 4, 5, 5, 6, 7, 9)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_4_5_5_6_7_9` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_4_5_5_6_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_4_5_5_6_7_9

/-- **The strict-class consumption, box (1, 4, 5, 5, 6, 7, 9)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_4_5_5_6_7_9
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) dumpFam_1_4_5_5_6_7_9)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_5_6_7_9)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_4_5_5_6_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_4_5_5_6_7_9

/-! ### Box (1, 4, 5, 6, 6, 7, 8) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 4, 5, 6, 6, 7, 8) carries the banked family
`compFam_1_4_5_6_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_6_6_7_8 :
    (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_6_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 6, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_6_6_7_8 :
    InRange17 (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_6_6_7_8⟩

#print axioms spineFamDataOS_1_4_5_6_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 6, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_6_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_6_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_6_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_4_5_6_6_7_8

/-- **The per-box totality lift, box (1, 4, 5, 6, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_6_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_6_6_7_8 hword hexh

#print axioms totalLift_1_4_5_6_6_7_8

/-- **The per-box consumption, box (1, 4, 5, 6, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_6_6_7_8
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_6_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_6_6_7_8

/-- **The strict-class conflict, box (1, 4, 5, 6, 6, 7, 8)**: the word-cover kill at the strict-class
family `dumpFam_1_4_5_6_6_7_8` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_4_5_6_6_7_8` datum. -/
theorem composedConflictD_1_4_5_6_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_6_6_7_8)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_4_5_6_6_7_8 hexh hface hchains hw

#print axioms composedConflictD_1_4_5_6_6_7_8

/-- **The strict-class totality lift, box (1, 4, 5, 6, 6, 7, 8)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_4_5_6_6_7_8` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_4_5_6_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8) :
    ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_4_5_6_6_7_8

/-- **The strict-class consumption, box (1, 4, 5, 6, 6, 7, 8)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_4_5_6_6_7_8
    (htotal : ComposedTotalOneSided (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_4_5_6_6_7_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_4_5_6_6_7_8)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_4_5_6_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_4_5_6_6_7_8

/-! ### Box (1, 5, 5, 5, 6, 7, 8) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 5, 5, 5, 6, 7, 8) carries the banked family
`compFam_1_5_5_5_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_5_5_5_6_7_8 :
    (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_5_5_5_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 5, 5, 5, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_5_5_5_6_7_8 :
    InRange17 (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_5_5_5_6_7_8⟩

#print axioms spineFamDataOS_1_5_5_5_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 5, 5, 5, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_5_5_5_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_5_5_5_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_5_5_5_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_5_5_5_6_7_8

/-- **The per-box totality lift, box (1, 5, 5, 5, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_5_5_5_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_5_5_5_6_7_8 hword hexh

#print axioms totalLift_1_5_5_5_6_7_8

/-- **The per-box consumption, box (1, 5, 5, 5, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_5_5_5_6_7_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_5_5_5_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_5_5_5_6_7_8

/-- **The strict-class conflict, box (1, 5, 5, 5, 6, 7, 8)**: the word-cover kill at the strict-class
family `dumpFam_1_5_5_5_6_7_8` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_5_5_5_6_7_8` datum. -/
theorem composedConflictD_1_5_5_5_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_5_6_7_8)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_5_5_5_6_7_8 hexh hface hchains hw

#print axioms composedConflictD_1_5_5_5_6_7_8

/-- **The strict-class totality lift, box (1, 5, 5, 5, 6, 7, 8)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_5_5_5_6_7_8` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_5_5_5_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8) :
    ComposedTotalOneSided (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_5_5_5_6_7_8

/-- **The strict-class consumption, box (1, 5, 5, 5, 6, 7, 8)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_5_5_5_6_7_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_5_6_7_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_5_6_7_8)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_5_5_5_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_5_5_5_6_7_8

/-! ### Box (1, 5, 5, 6, 6, 7, 8) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 5, 5, 6, 6, 7, 8) carries the banked family
`compFam_1_5_5_6_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_5_5_6_6_7_8 :
    (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_5_5_6_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 5, 5, 6, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_5_5_6_6_7_8 :
    InRange17 (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_5_5_6_6_7_8⟩

#print axioms spineFamDataOS_1_5_5_6_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 5, 5, 6, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_5_5_6_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_5_5_6_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_5_5_6_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_5_5_6_6_7_8

/-- **The per-box totality lift, box (1, 5, 5, 6, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_5_5_6_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_5_5_6_6_7_8 hword hexh

#print axioms totalLift_1_5_5_6_6_7_8

/-- **The per-box consumption, box (1, 5, 5, 6, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_5_5_6_6_7_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_5_5_6_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_5_5_6_6_7_8

/-- **The strict-class conflict, box (1, 5, 5, 6, 6, 7, 8)**: the word-cover kill at the strict-class
family `dumpFam_1_5_5_6_6_7_8` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_5_5_6_6_7_8` datum. -/
theorem composedConflictD_1_5_5_6_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_6_6_7_8)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_5_5_6_6_7_8 hexh hface hchains hw

#print axioms composedConflictD_1_5_5_6_6_7_8

/-- **The strict-class totality lift, box (1, 5, 5, 6, 6, 7, 8)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_5_5_6_6_7_8` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_5_5_6_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8) :
    ComposedTotalOneSided (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_5_5_6_6_7_8

/-- **The strict-class consumption, box (1, 5, 5, 6, 6, 7, 8)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_5_5_6_6_7_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_6_7_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_6_6_7_8)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_5_5_6_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_5_5_6_6_7_8

/-! ### Box (1, 5, 5, 6, 7, 8, 8) — strict-complete (joinedge2 census §7) -/

/-- coveredSet membership: box (1, 5, 5, 6, 7, 8, 8) carries the banked family
`compFam_1_5_5_6_7_8_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_5_5_6_7_8_8 :
    (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem
  exact Finset.mem_singleton.mpr rfl

#print axioms covered_1_5_5_6_7_8_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 5, 5, 6, 7, 8, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_5_5_6_7_8_8 :
    InRange17 (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_5_5_6_7_8_8⟩

#print axioms spineFamDataOS_1_5_5_6_7_8_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 5, 5, 6, 7, 8, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_5_5_6_7_8_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_5_5_6_7_8_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_5_5_6_7_8_8) hexh hface hchains hw

#print axioms composedConflict_1_5_5_6_7_8_8

/-- **The per-box totality lift, box (1, 5, 5, 6, 7, 8, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_5_5_6_7_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_5_5_6_7_8_8 hword hexh

#print axioms totalLift_1_5_5_6_7_8_8

/-- **The per-box consumption, box (1, 5, 5, 6, 7, 8, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_5_5_6_7_8_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_5_5_6_7_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_5_5_6_7_8_8

/-- **The strict-class conflict, box (1, 5, 5, 6, 7, 8, 8)**: the word-cover kill at the strict-class
family `dumpFam_1_5_5_6_7_8_8` (`Fresh.DumpDomData`; every death row of the box is
strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked
`dumpFamData_1_5_5_6_7_8_8` datum. -/
theorem composedConflictD_1_5_5_6_7_8_8
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8)
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_6_7_8_8)
    (hw : WordRealized g w) : False :=
  composedConflict_fam dumpFamData_1_5_5_6_7_8_8 hexh hface hchains hw

#print axioms composedConflictD_1_5_5_6_7_8_8

/-- **The strict-class totality lift, box (1, 5, 5, 6, 7, 8, 8)**: `ComposedTotalOneSided` at the strict-class
family `dumpFam_1_5_5_6_7_8_8` — the same reduction at the dump v2 family, through the
family-general retargeting. -/
theorem totalLiftD_1_5_5_6_7_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8) :
    ComposedTotalOneSided (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8 :=
  composedTotal_of_wordCover_fam hword hexh

#print axioms totalLiftD_1_5_5_6_7_8_8

/-- **The strict-class consumption, box (1, 5, 5, 6, 7, 8, 8)**: the strict-class totality instance through
the family-general glue — the same conclusion shape at the dump v2 family. -/
theorem oneSidedSoundD_1_5_5_6_7_8_8
    (htotal : ComposedTotalOneSided (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) dumpFam_1_5_5_6_7_8_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g dumpFam_1_5_5_6_7_8_8)
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_total_fam dumpFamData_1_5_5_6_7_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSoundD_1_5_5_6_7_8_8

/-! ### Box (1, 2, 3, 4, 4, 5, 7) -/

/-- coveredSet membership: box (1, 2, 3, 4, 4, 5, 7) carries the banked family
`compFam_1_2_3_4_4_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_4_5_7 :
    (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_4_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 4, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_4_5_7 :
    InRange17 (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_4_5_7⟩

#print axioms spineFamDataOS_1_2_3_4_4_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 4, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_4_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_4_5_7
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_4_5_7) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_4_5_7

/-- **The per-box totality lift, box (1, 2, 3, 4, 4, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_4_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_4_5_7 hword hexh

#print axioms totalLift_1_2_3_4_4_5_7

/-- **The per-box consumption, box (1, 2, 3, 4, 4, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_4_5_7
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_4_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_4_5_7

/-! ### Box (1, 2, 3, 4, 4, 6, 7) -/

/-- coveredSet membership: box (1, 2, 3, 4, 4, 6, 7) carries the banked family
`compFam_1_2_3_4_4_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_4_6_7 :
    (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_4_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 4, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_4_6_7 :
    InRange17 (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_4_6_7⟩

#print axioms spineFamDataOS_1_2_3_4_4_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 4, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_4_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_4_6_7
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_4_6_7) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_4_6_7

/-- **The per-box totality lift, box (1, 2, 3, 4, 4, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_4_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_4_6_7 hword hexh

#print axioms totalLift_1_2_3_4_4_6_7

/-- **The per-box consumption, box (1, 2, 3, 4, 4, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_4_6_7
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_4_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_4_6_7

/-! ### Box (1, 2, 3, 4, 5, 5, 7) -/

/-- coveredSet membership: box (1, 2, 3, 4, 5, 5, 7) carries the banked family
`compFam_1_2_3_4_5_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_5_5_7 :
    (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_5_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 5, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_5_5_7 :
    InRange17 (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_5_5_7⟩

#print axioms spineFamDataOS_1_2_3_4_5_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 5, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_5_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_5_5_7) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_5_5_7

/-- **The per-box totality lift, box (1, 2, 3, 4, 5, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_5_5_7 hword hexh

#print axioms totalLift_1_2_3_4_5_5_7

/-- **The per-box consumption, box (1, 2, 3, 4, 5, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_5_5_7
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_5_5_7

/-! ### Box (1, 2, 3, 4, 5, 7, 7) -/

/-- coveredSet membership: box (1, 2, 3, 4, 5, 7, 7) carries the banked family
`compFam_1_2_3_4_5_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_5_7_7 :
    (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_5_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 5, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_5_7_7 :
    InRange17 (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_5_7_7⟩

#print axioms spineFamDataOS_1_2_3_4_5_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 5, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_5_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_5_7_7
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_5_7_7) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_5_7_7

/-- **The per-box totality lift, box (1, 2, 3, 4, 5, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_5_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_5_7_7 hword hexh

#print axioms totalLift_1_2_3_4_5_7_7

/-- **The per-box consumption, box (1, 2, 3, 4, 5, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_5_7_7
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_5_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_5_7_7

/-! ### Box (1, 2, 3, 4, 5, 7, 8) -/

/-- coveredSet membership: box (1, 2, 3, 4, 5, 7, 8) carries the banked family
`compFam_1_2_3_4_5_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_5_7_8 :
    (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_5_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 5, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_5_7_8 :
    InRange17 (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_5_7_8⟩

#print axioms spineFamDataOS_1_2_3_4_5_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 5, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_5_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_5_7_8
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_5_7_8) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_5_7_8

/-- **The per-box totality lift, box (1, 2, 3, 4, 5, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_5_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_5_7_8 hword hexh

#print axioms totalLift_1_2_3_4_5_7_8

/-- **The per-box consumption, box (1, 2, 3, 4, 5, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_5_7_8
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_5_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_5_7_8

/-! ### Box (1, 2, 3, 4, 6, 6, 8) -/

/-- coveredSet membership: box (1, 2, 3, 4, 6, 6, 8) carries the banked family
`compFam_1_2_3_4_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_6_6_8 :
    (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_6_6_8 :
    InRange17 (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_6_6_8⟩

#print axioms spineFamDataOS_1_2_3_4_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_6_6_8

/-- **The per-box totality lift, box (1, 2, 3, 4, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_6_6_8 hword hexh

#print axioms totalLift_1_2_3_4_6_6_8

/-- **The per-box consumption, box (1, 2, 3, 4, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_6_6_8
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_6_6_8

/-! ### Box (1, 2, 3, 4, 6, 7, 8) -/

/-- coveredSet membership: box (1, 2, 3, 4, 6, 7, 8) carries the banked family
`compFam_1_2_3_4_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_4_6_7_8 :
    (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_4_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 4, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_4_6_7_8 :
    InRange17 (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_4_6_7_8⟩

#print axioms spineFamDataOS_1_2_3_4_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 4, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_4_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_4_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_4_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_2_3_4_6_7_8

/-- **The per-box totality lift, box (1, 2, 3, 4, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_4_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_4_6_7_8 hword hexh

#print axioms totalLift_1_2_3_4_6_7_8

/-- **The per-box consumption, box (1, 2, 3, 4, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_4_6_7_8
    (htotal : ComposedTotalOneSided (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_4_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_4_6_7_8

/-! ### Box (1, 2, 3, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 2, 3, 5, 6, 6, 8) carries the banked family
`compFam_1_2_3_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_3_5_6_6_8 :
    (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_3_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 3, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_3_5_6_6_8 :
    InRange17 (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_3_5_6_6_8⟩

#print axioms spineFamDataOS_1_2_3_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 3, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_3_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_3_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_3_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_2_3_5_6_6_8

/-- **The per-box totality lift, box (1, 2, 3, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_3_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_3_5_6_6_8 hword hexh

#print axioms totalLift_1_2_3_5_6_6_8

/-- **The per-box consumption, box (1, 2, 3, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_3_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_3_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_3_5_6_6_8

/-! ### Box (1, 2, 4, 4, 6, 6, 8) -/

/-- coveredSet membership: box (1, 2, 4, 4, 6, 6, 8) carries the banked family
`compFam_1_2_4_4_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_4_4_6_6_8 :
    (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_4_4_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 4, 4, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_4_4_6_6_8 :
    InRange17 (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_4_4_6_6_8⟩

#print axioms spineFamDataOS_1_2_4_4_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 4, 4, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_4_4_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_4_4_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_4_4_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_2_4_4_6_6_8

/-- **The per-box totality lift, box (1, 2, 4, 4, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_4_4_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_4_4_6_6_8 hword hexh

#print axioms totalLift_1_2_4_4_6_6_8

/-- **The per-box consumption, box (1, 2, 4, 4, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_4_4_6_6_8
    (htotal : ComposedTotalOneSided (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_4_4_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_4_4_6_6_8

/-! ### Box (1, 2, 4, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 2, 4, 5, 6, 6, 8) carries the banked family
`compFam_1_2_4_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_2_4_5_6_6_8 :
    (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_2_4_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 2, 4, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_2_4_5_6_6_8 :
    InRange17 (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_2_4_5_6_6_8⟩

#print axioms spineFamDataOS_1_2_4_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 2, 4, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_2_4_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_2_4_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_2_4_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_2_4_5_6_6_8

/-- **The per-box totality lift, box (1, 2, 4, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_2_4_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_2_4_5_6_6_8 hword hexh

#print axioms totalLift_1_2_4_5_6_6_8

/-- **The per-box consumption, box (1, 2, 4, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_2_4_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 2, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_2_4_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_2_4_5_6_6_8

/-! ### Box (1, 3, 3, 4, 4, 5, 7) -/

/-- coveredSet membership: box (1, 3, 3, 4, 4, 5, 7) carries the banked family
`compFam_1_3_3_4_4_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_4_5_7 :
    (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_4_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 4, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_4_5_7 :
    InRange17 (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_4_5_7⟩

#print axioms spineFamDataOS_1_3_3_4_4_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 4, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_4_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_4_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_4_5_7) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_4_5_7

/-- **The per-box totality lift, box (1, 3, 3, 4, 4, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_4_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_4_5_7 hword hexh

#print axioms totalLift_1_3_3_4_4_5_7

/-- **The per-box consumption, box (1, 3, 3, 4, 4, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_4_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 4, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_4_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_4_5_7

/-! ### Box (1, 3, 3, 4, 4, 6, 7) -/

/-- coveredSet membership: box (1, 3, 3, 4, 4, 6, 7) carries the banked family
`compFam_1_3_3_4_4_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_4_6_7 :
    (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_4_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 4, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_4_6_7 :
    InRange17 (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_4_6_7⟩

#print axioms spineFamDataOS_1_3_3_4_4_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 4, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_4_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_4_6_7
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_4_6_7) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_4_6_7

/-- **The per-box totality lift, box (1, 3, 3, 4, 4, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_4_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_4_6_7 hword hexh

#print axioms totalLift_1_3_3_4_4_6_7

/-- **The per-box consumption, box (1, 3, 3, 4, 4, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_4_6_7
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 4, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_4_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_4_6_7

/-! ### Box (1, 3, 3, 4, 5, 5, 7) -/

/-- coveredSet membership: box (1, 3, 3, 4, 5, 5, 7) carries the banked family
`compFam_1_3_3_4_5_5_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_5_5_7 :
    (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_5_5_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 5, 5, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_5_5_7 :
    InRange17 (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_5_5_7⟩

#print axioms spineFamDataOS_1_3_3_4_5_5_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 5, 5, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_5_5_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_5_5_7
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_5_5_7) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_5_5_7

/-- **The per-box totality lift, box (1, 3, 3, 4, 5, 5, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_5_5_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_5_5_7 hword hexh

#print axioms totalLift_1_3_3_4_5_5_7

/-- **The per-box consumption, box (1, 3, 3, 4, 5, 5, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_5_5_7
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 5, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_5_5_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_5_5_7

/-! ### Box (1, 3, 3, 4, 5, 6, 7) -/

/-- coveredSet membership: box (1, 3, 3, 4, 5, 6, 7) carries the banked family
`compFam_1_3_3_4_5_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_5_6_7 :
    (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_5_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 5, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_5_6_7 :
    InRange17 (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_5_6_7⟩

#print axioms spineFamDataOS_1_3_3_4_5_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 5, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_5_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_5_6_7
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_5_6_7) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_5_6_7

/-- **The per-box totality lift, box (1, 3, 3, 4, 5, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_5_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_5_6_7 hword hexh

#print axioms totalLift_1_3_3_4_5_6_7

/-- **The per-box consumption, box (1, 3, 3, 4, 5, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_5_6_7
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_5_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_5_6_7

/-! ### Box (1, 3, 3, 4, 5, 6, 8) -/

/-- coveredSet membership: box (1, 3, 3, 4, 5, 6, 8) carries the banked family
`compFam_1_3_3_4_5_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_5_6_8 :
    (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_5_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 5, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_5_6_8 :
    InRange17 (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_5_6_8⟩

#print axioms spineFamDataOS_1_3_3_4_5_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 5, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_5_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_5_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_5_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_5_6_8

/-- **The per-box totality lift, box (1, 3, 3, 4, 5, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_5_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_5_6_8 hword hexh

#print axioms totalLift_1_3_3_4_5_6_8

/-- **The per-box consumption, box (1, 3, 3, 4, 5, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_5_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_5_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_5_6_8

/-! ### Box (1, 3, 3, 4, 5, 7, 8) -/

/-- coveredSet membership: box (1, 3, 3, 4, 5, 7, 8) carries the banked family
`compFam_1_3_3_4_5_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_5_7_8 :
    (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_5_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 5, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_5_7_8 :
    InRange17 (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_5_7_8⟩

#print axioms spineFamDataOS_1_3_3_4_5_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 5, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_5_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_5_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_5_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_5_7_8

/-- **The per-box totality lift, box (1, 3, 3, 4, 5, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_5_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_5_7_8 hword hexh

#print axioms totalLift_1_3_3_4_5_7_8

/-- **The per-box consumption, box (1, 3, 3, 4, 5, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_5_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 5, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_5_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_5_7_8

/-! ### Box (1, 3, 3, 4, 6, 6, 8) -/

/-- coveredSet membership: box (1, 3, 3, 4, 6, 6, 8) carries the banked family
`compFam_1_3_3_4_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_6_6_8 :
    (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_6_6_8 :
    InRange17 (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_6_6_8⟩

#print axioms spineFamDataOS_1_3_3_4_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_6_6_8

/-- **The per-box totality lift, box (1, 3, 3, 4, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_6_6_8 hword hexh

#print axioms totalLift_1_3_3_4_6_6_8

/-- **The per-box consumption, box (1, 3, 3, 4, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_6_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_6_6_8

/-! ### Box (1, 3, 3, 4, 6, 7, 8) -/

/-- coveredSet membership: box (1, 3, 3, 4, 6, 7, 8) carries the banked family
`compFam_1_3_3_4_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_4_6_7_8 :
    (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_4_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 4, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_4_6_7_8 :
    InRange17 (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_4_6_7_8⟩

#print axioms spineFamDataOS_1_3_3_4_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 4, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_4_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_4_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_4_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_4_6_7_8

/-- **The per-box totality lift, box (1, 3, 3, 4, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_4_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_4_6_7_8 hword hexh

#print axioms totalLift_1_3_3_4_6_7_8

/-- **The per-box consumption, box (1, 3, 3, 4, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_4_6_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 4, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_4_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_4_6_7_8

/-! ### Box (1, 3, 3, 5, 5, 6, 8) -/

/-- coveredSet membership: box (1, 3, 3, 5, 5, 6, 8) carries the banked family
`compFam_1_3_3_5_5_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_5_5_6_8 :
    (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_5_5_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 5, 5, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_5_5_6_8 :
    InRange17 (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_5_5_6_8⟩

#print axioms spineFamDataOS_1_3_3_5_5_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 5, 5, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_5_5_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_5_5_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_5_5_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_5_5_6_8

/-- **The per-box totality lift, box (1, 3, 3, 5, 5, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_5_5_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_5_5_6_8 hword hexh

#print axioms totalLift_1_3_3_5_5_6_8

/-- **The per-box consumption, box (1, 3, 3, 5, 5, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_5_5_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_5_5_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_5_5_6_8

/-! ### Box (1, 3, 3, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 3, 3, 5, 6, 6, 8) carries the banked family
`compFam_1_3_3_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_5_6_6_8 :
    (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_5_6_6_8 :
    InRange17 (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_5_6_6_8⟩

#print axioms spineFamDataOS_1_3_3_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_5_6_6_8

/-- **The per-box totality lift, box (1, 3, 3, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_5_6_6_8 hword hexh

#print axioms totalLift_1_3_3_5_6_6_8

/-- **The per-box consumption, box (1, 3, 3, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_5_6_6_8

/-! ### Box (1, 3, 3, 5, 6, 7, 8) -/

/-- coveredSet membership: box (1, 3, 3, 5, 6, 7, 8) carries the banked family
`compFam_1_3_3_5_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_5_6_7_8 :
    (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_5_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 5, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_5_6_7_8 :
    InRange17 (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_5_6_7_8⟩

#print axioms spineFamDataOS_1_3_3_5_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 5, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_5_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_5_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_5_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_5_6_7_8

/-- **The per-box totality lift, box (1, 3, 3, 5, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_5_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_5_6_7_8 hword hexh

#print axioms totalLift_1_3_3_5_6_7_8

/-- **The per-box consumption, box (1, 3, 3, 5, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_5_6_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_5_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_5_6_7_8

/-! ### Box (1, 3, 3, 5, 6, 8, 8) -/

/-- coveredSet membership: box (1, 3, 3, 5, 6, 8, 8) carries the banked family
`compFam_1_3_3_5_6_8_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_5_6_8_8 :
    (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_5_6_8_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 5, 6, 8, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_5_6_8_8 :
    InRange17 (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_5_6_8_8⟩

#print axioms spineFamDataOS_1_3_3_5_6_8_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 5, 6, 8, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_5_6_8_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_5_6_8_8
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_5_6_8_8) hexh hface hchains hw

#print axioms composedConflict_1_3_3_5_6_8_8

/-- **The per-box totality lift, box (1, 3, 3, 5, 6, 8, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_5_6_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_5_6_8_8 hword hexh

#print axioms totalLift_1_3_3_5_6_8_8

/-- **The per-box consumption, box (1, 3, 3, 5, 6, 8, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_5_6_8_8
    (htotal : ComposedTotalOneSided (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 8, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_5_6_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_5_6_8_8

/-! ### Box (1, 3, 3, 5, 6, 8, 9) -/

/-- coveredSet membership: box (1, 3, 3, 5, 6, 8, 9) carries the banked family
`compFam_1_3_3_5_6_8_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_3_5_6_8_9 :
    (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_3_5_6_8_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 3, 5, 6, 8, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_3_5_6_8_9 :
    InRange17 (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_3_5_6_8_9⟩

#print axioms spineFamDataOS_1_3_3_5_6_8_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 3, 5, 6, 8, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_3_5_6_8_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_3_5_6_8_9
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_3_5_6_8_9) hexh hface hchains hw

#print axioms composedConflict_1_3_3_5_6_8_9

/-- **The per-box totality lift, box (1, 3, 3, 5, 6, 8, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_3_5_6_8_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_3_5_6_8_9 hword hexh

#print axioms totalLift_1_3_3_5_6_8_9

/-- **The per-box consumption, box (1, 3, 3, 5, 6, 8, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_3_5_6_8_9
    (htotal : ComposedTotalOneSided (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 3, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_3_5_6_8_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_3_5_6_8_9

/-! ### Box (1, 3, 4, 4, 5, 6, 8) -/

/-- coveredSet membership: box (1, 3, 4, 4, 5, 6, 8) carries the banked family
`compFam_1_3_4_4_5_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_4_5_6_8 :
    (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_5_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 4, 5, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_4_5_6_8 :
    InRange17 (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_4_5_6_8⟩

#print axioms spineFamDataOS_1_3_4_4_5_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 4, 5, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_4_5_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_4_5_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_4_5_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_4_4_5_6_8

/-- **The per-box totality lift, box (1, 3, 4, 4, 5, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_4_5_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_4_5_6_8 hword hexh

#print axioms totalLift_1_3_4_4_5_6_8

/-- **The per-box consumption, box (1, 3, 4, 4, 5, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_4_5_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_4_5_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_4_5_6_8

/-! ### Box (1, 3, 4, 4, 5, 7, 7) -/

/-- coveredSet membership: box (1, 3, 4, 4, 5, 7, 7) carries the banked family
`compFam_1_3_4_4_5_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_4_5_7_7 :
    (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_5_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 4, 5, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_4_5_7_7 :
    InRange17 (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_4_5_7_7⟩

#print axioms spineFamDataOS_1_3_4_4_5_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 4, 5, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_4_5_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_4_5_7_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_4_5_7_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_4_5_7_7

/-- **The per-box totality lift, box (1, 3, 4, 4, 5, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_4_5_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_4_5_7_7 hword hexh

#print axioms totalLift_1_3_4_4_5_7_7

/-- **The per-box consumption, box (1, 3, 4, 4, 5, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_4_5_7_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 5, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_4_5_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_4_5_7_7

/-! ### Box (1, 3, 4, 4, 6, 6, 8) -/

/-- coveredSet membership: box (1, 3, 4, 4, 6, 6, 8) carries the banked family
`compFam_1_3_4_4_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_4_6_6_8 :
    (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 4, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_4_6_6_8 :
    InRange17 (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_4_6_6_8⟩

#print axioms spineFamDataOS_1_3_4_4_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 4, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_4_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_4_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_4_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_4_4_6_6_8

/-- **The per-box totality lift, box (1, 3, 4, 4, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_4_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_4_6_6_8 hword hexh

#print axioms totalLift_1_3_4_4_6_6_8

/-- **The per-box consumption, box (1, 3, 4, 4, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_4_6_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_4_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_4_6_6_8

/-! ### Box (1, 3, 4, 4, 6, 6, 15) -/

/-- coveredSet membership: box (1, 3, 4, 4, 6, 6, 15) carries the banked family
`compFam_1_3_4_4_6_6_15` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_4_6_6_15 :
    (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_4_6_6_15

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 4, 6, 6, 15)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_4_6_6_15 :
    InRange17 (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_4_6_6_15⟩

#print axioms spineFamDataOS_1_3_4_4_6_6_15

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 4, 6, 6, 15)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_4_6_6_15`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_4_6_6_15
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_4_6_6_15) hexh hface hchains hw

#print axioms composedConflict_1_3_4_4_6_6_15

/-- **The per-box totality lift, box (1, 3, 4, 4, 6, 6, 15)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_4_6_6_15
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_4_6_6_15 hword hexh

#print axioms totalLift_1_3_4_4_6_6_15

/-- **The per-box consumption, box (1, 3, 4, 4, 6, 6, 15)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_4_6_6_15
    (htotal : ComposedTotalOneSided (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 4, 6, 6, 15] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_4_6_6_15 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_4_6_6_15

/-! ### Box (1, 3, 4, 5, 5, 6, 7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 5, 6, 7) carries the banked family
`compFam_1_3_4_5_5_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_5_6_7 :
    (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_5_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 5, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_5_6_7 :
    InRange17 (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_5_6_7⟩

#print axioms spineFamDataOS_1_3_4_5_5_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 5, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_5_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_5_6_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_5_6_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_5_6_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 5, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_5_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_5_6_7 hword hexh

#print axioms totalLift_1_3_4_5_5_6_7

/-- **The per-box consumption, box (1, 3, 4, 5, 5, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_5_6_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_5_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_5_6_7

/-! ### Box (1, 3, 4, 5, 5, 7, 7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 5, 7, 7) carries the banked family
`compFam_1_3_4_5_5_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_5_7_7 :
    (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_5_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 5, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_5_7_7 :
    InRange17 (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_5_7_7⟩

#print axioms spineFamDataOS_1_3_4_5_5_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 5, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_5_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_5_7_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_5_7_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_5_7_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 5, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_5_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_5_7_7 hword hexh

#print axioms totalLift_1_3_4_5_5_7_7

/-- **The per-box consumption, box (1, 3, 4, 5, 5, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_5_7_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_5_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_5_7_7

/-! ### Box (1, 3, 4, 5, 5, 7, 8) -/

/-- coveredSet membership: box (1, 3, 4, 5, 5, 7, 8) carries the banked family
`compFam_1_3_4_5_5_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_5_7_8 :
    (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_5_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 5, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_5_7_8 :
    InRange17 (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_5_7_8⟩

#print axioms spineFamDataOS_1_3_4_5_5_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 5, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_5_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_5_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_5_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_5_7_8

/-- **The per-box totality lift, box (1, 3, 4, 5, 5, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_5_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_5_7_8 hword hexh

#print axioms totalLift_1_3_4_5_5_7_8

/-- **The per-box consumption, box (1, 3, 4, 5, 5, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_5_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_5_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_5_7_8

/-! ### Box (1, 3, 4, 5, 5, 7, 9) -/

/-- coveredSet membership: box (1, 3, 4, 5, 5, 7, 9) carries the banked family
`compFam_1_3_4_5_5_7_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_5_7_9 :
    (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_5_7_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 5, 7, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_5_7_9 :
    InRange17 (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_5_7_9⟩

#print axioms spineFamDataOS_1_3_4_5_5_7_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 5, 7, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_5_7_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_5_7_9
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_5_7_9) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_5_7_9

/-- **The per-box totality lift, box (1, 3, 4, 5, 5, 7, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_5_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_5_7_9 hword hexh

#print axioms totalLift_1_3_4_5_5_7_9

/-- **The per-box consumption, box (1, 3, 4, 5, 5, 7, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_5_7_9
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 5, 7, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_5_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_5_7_9

/-! ### Box (1, 3, 4, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 6, 8) carries the banked family
`compFam_1_3_4_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_6_8 :
    (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_6_8 :
    InRange17 (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_6_8⟩

#print axioms spineFamDataOS_1_3_4_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_6_8

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_6_8 hword hexh

#print axioms totalLift_1_3_4_5_6_6_8

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_6_8

/-! ### Box (1, 3, 4, 5, 6, 6, 15) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 6, 15) carries the banked family
`compFam_1_3_4_5_6_6_15` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_6_15 :
    (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_6_15

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 6, 15)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_6_15 :
    InRange17 (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_6_15⟩

#print axioms spineFamDataOS_1_3_4_5_6_6_15

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 6, 15)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_6_15`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_6_15
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_6_15) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_6_15

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 6, 15)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_6_15
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_6_15 hword hexh

#print axioms totalLift_1_3_4_5_6_6_15

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 6, 15)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_6_15
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 6, 15] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_6_15 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_6_15

/-! ### Box (1, 3, 4, 5, 6, 7, 7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 7, 7) carries the banked family
`compFam_1_3_4_5_6_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_7_7 :
    (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_7_7 :
    InRange17 (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_7_7⟩

#print axioms spineFamDataOS_1_3_4_5_6_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_7_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_7_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_7_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_7_7 hword hexh

#print axioms totalLift_1_3_4_5_6_7_7

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_7_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_7_7

/-! ### Box (1, 3, 4, 5, 6, 7, 9) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 7, 9) carries the banked family
`compFam_1_3_4_5_6_7_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_7_9 :
    (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_7_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 7, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_7_9 :
    InRange17 (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_7_9⟩

#print axioms spineFamDataOS_1_3_4_5_6_7_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 7, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_7_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_7_9
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_7_9) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_7_9

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 7, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_7_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_7_9 hword hexh

#print axioms totalLift_1_3_4_5_6_7_9

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 7, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_7_9
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_7_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_7_9

/-! ### Box (1, 3, 4, 5, 6, 7, 15) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 7, 15) carries the banked family
`compFam_1_3_4_5_6_7_15` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_7_15 :
    (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_7_15

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 7, 15)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_7_15 :
    InRange17 (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_7_15⟩

#print axioms spineFamDataOS_1_3_4_5_6_7_15

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 7, 15)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_7_15`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_7_15
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_7_15) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_7_15

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 7, 15)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_7_15
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_7_15 hword hexh

#print axioms totalLift_1_3_4_5_6_7_15

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 7, 15)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_7_15
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 15] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_7_15 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_7_15

/-! ### Box (1, 3, 4, 5, 6, 7, 16) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 7, 16) carries the banked family
`compFam_1_3_4_5_6_7_16` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_7_16 :
    (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_7_16

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 7, 16)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_7_16 :
    InRange17 (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_7_16⟩

#print axioms spineFamDataOS_1_3_4_5_6_7_16

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 7, 16)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_7_16`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_7_16
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_7_16) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_7_16

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 7, 16)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_7_16
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_7_16 hword hexh

#print axioms totalLift_1_3_4_5_6_7_16

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 7, 16)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_7_16
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 7, 16] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_7_16 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_7_16

/-! ### Box (1, 3, 4, 5, 6, 8, 9) -/

/-- coveredSet membership: box (1, 3, 4, 5, 6, 8, 9) carries the banked family
`compFam_1_3_4_5_6_8_9` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_6_8_9 :
    (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_6_8_9

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 6, 8, 9)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_6_8_9 :
    InRange17 (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_6_8_9⟩

#print axioms spineFamDataOS_1_3_4_5_6_8_9

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 6, 8, 9)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_6_8_9`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_6_8_9
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_6_8_9) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_6_8_9

/-- **The per-box totality lift, box (1, 3, 4, 5, 6, 8, 9)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_6_8_9
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_6_8_9 hword hexh

#print axioms totalLift_1_3_4_5_6_8_9

/-- **The per-box consumption, box (1, 3, 4, 5, 6, 8, 9)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_6_8_9
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 6, 8, 9] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_6_8_9 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_6_8_9

/-! ### Box (1, 3, 4, 5, 7, 7, 7) -/

/-- coveredSet membership: box (1, 3, 4, 5, 7, 7, 7) carries the banked family
`compFam_1_3_4_5_7_7_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_4_5_7_7_7 :
    (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_4_5_7_7_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 4, 5, 7, 7, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_4_5_7_7_7 :
    InRange17 (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_4_5_7_7_7⟩

#print axioms spineFamDataOS_1_3_4_5_7_7_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 4, 5, 7, 7, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_4_5_7_7_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_4_5_7_7_7
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_4_5_7_7_7) hexh hface hchains hw

#print axioms composedConflict_1_3_4_5_7_7_7

/-- **The per-box totality lift, box (1, 3, 4, 5, 7, 7, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_4_5_7_7_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_4_5_7_7_7 hword hexh

#print axioms totalLift_1_3_4_5_7_7_7

/-- **The per-box consumption, box (1, 3, 4, 5, 7, 7, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_4_5_7_7_7
    (htotal : ComposedTotalOneSided (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 4, 5, 7, 7, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_4_5_7_7_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_4_5_7_7_7

/-! ### Box (1, 3, 5, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 3, 5, 5, 6, 6, 8) carries the banked family
`compFam_1_3_5_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_5_6_6_8 :
    (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_5_6_6_8 :
    InRange17 (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_5_6_6_8⟩

#print axioms spineFamDataOS_1_3_5_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_5_6_6_8

/-- **The per-box totality lift, box (1, 3, 5, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_5_6_6_8 hword hexh

#print axioms totalLift_1_3_5_5_6_6_8

/-- **The per-box consumption, box (1, 3, 5, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_5_6_6_8

/-! ### Box (1, 3, 5, 5, 6, 7, 8) -/

/-- coveredSet membership: box (1, 3, 5, 5, 6, 7, 8) carries the banked family
`compFam_1_3_5_5_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_5_6_7_8 :
    (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_5_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 5, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_5_6_7_8 :
    InRange17 (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_5_6_7_8⟩

#print axioms spineFamDataOS_1_3_5_5_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 5, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_5_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_5_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_5_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_5_6_7_8

/-- **The per-box totality lift, box (1, 3, 5, 5, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_5_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_5_6_7_8 hword hexh

#print axioms totalLift_1_3_5_5_6_7_8

/-- **The per-box consumption, box (1, 3, 5, 5, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_5_6_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 5, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_5_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_5_6_7_8

/-! ### Box (1, 3, 5, 6, 6, 7, 8) -/

/-- coveredSet membership: box (1, 3, 5, 6, 6, 7, 8) carries the banked family
`compFam_1_3_5_6_6_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_6_6_7_8 :
    (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_6_6_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 6, 6, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_6_6_7_8 :
    InRange17 (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_6_6_7_8⟩

#print axioms spineFamDataOS_1_3_5_6_6_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 6, 6, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_6_6_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_6_6_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_6_6_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_6_6_7_8

/-- **The per-box totality lift, box (1, 3, 5, 6, 6, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_6_6_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_6_6_7_8 hword hexh

#print axioms totalLift_1_3_5_6_6_7_8

/-- **The per-box consumption, box (1, 3, 5, 6, 6, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_6_6_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 6, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_6_6_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_6_6_7_8

/-! ### Box (1, 3, 5, 6, 6, 8, 8) -/

/-- coveredSet membership: box (1, 3, 5, 6, 6, 8, 8) carries the banked family
`compFam_1_3_5_6_6_8_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_6_6_8_8 :
    (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_6_6_8_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 6, 6, 8, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_6_6_8_8 :
    InRange17 (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_6_6_8_8⟩

#print axioms spineFamDataOS_1_3_5_6_6_8_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 6, 6, 8, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_6_6_8_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_6_6_8_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_6_6_8_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_6_6_8_8

/-- **The per-box totality lift, box (1, 3, 5, 6, 6, 8, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_6_6_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_6_6_8_8 hword hexh

#print axioms totalLift_1_3_5_6_6_8_8

/-- **The per-box consumption, box (1, 3, 5, 6, 6, 8, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_6_6_8_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 6, 8, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_6_6_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_6_6_8_8

/-! ### Box (1, 3, 5, 6, 7, 7, 8) -/

/-- coveredSet membership: box (1, 3, 5, 6, 7, 7, 8) carries the banked family
`compFam_1_3_5_6_7_7_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_6_7_7_8 :
    (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_6_7_7_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 6, 7, 7, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_6_7_7_8 :
    InRange17 (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_6_7_7_8⟩

#print axioms spineFamDataOS_1_3_5_6_7_7_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 6, 7, 7, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_6_7_7_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_6_7_7_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_6_7_7_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_6_7_7_8

/-- **The per-box totality lift, box (1, 3, 5, 6, 7, 7, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_6_7_7_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_6_7_7_8 hword hexh

#print axioms totalLift_1_3_5_6_7_7_8

/-- **The per-box consumption, box (1, 3, 5, 6, 7, 7, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_6_7_7_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 7, 7, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_6_7_7_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_6_7_7_8

/-! ### Box (1, 3, 5, 6, 7, 8, 8) -/

/-- coveredSet membership: box (1, 3, 5, 6, 7, 8, 8) carries the banked family
`compFam_1_3_5_6_7_8_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_3_5_6_7_8_8 :
    (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_3_5_6_7_8_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 3, 5, 6, 7, 8, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_3_5_6_7_8_8 :
    InRange17 (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_3_5_6_7_8_8⟩

#print axioms spineFamDataOS_1_3_5_6_7_8_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 3, 5, 6, 7, 8, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_3_5_6_7_8_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_3_5_6_7_8_8
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_3_5_6_7_8_8) hexh hface hchains hw

#print axioms composedConflict_1_3_5_6_7_8_8

/-- **The per-box totality lift, box (1, 3, 5, 6, 7, 8, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_3_5_6_7_8_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_3_5_6_7_8_8 hword hexh

#print axioms totalLift_1_3_5_6_7_8_8

/-- **The per-box consumption, box (1, 3, 5, 6, 7, 8, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_3_5_6_7_8_8
    (htotal : ComposedTotalOneSided (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 3, 5, 6, 7, 8, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_3_5_6_7_8_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_3_5_6_7_8_8

/-! ### Box (1, 4, 4, 5, 5, 6, 7) -/

/-- coveredSet membership: box (1, 4, 4, 5, 5, 6, 7) carries the banked family
`compFam_1_4_4_5_5_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_4_5_5_6_7 :
    (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_4_5_5_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 4, 5, 5, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_4_5_5_6_7 :
    InRange17 (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_4_5_5_6_7⟩

#print axioms spineFamDataOS_1_4_4_5_5_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 4, 5, 5, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_4_5_5_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_4_5_5_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_4_5_5_6_7) hexh hface hchains hw

#print axioms composedConflict_1_4_4_5_5_6_7

/-- **The per-box totality lift, box (1, 4, 4, 5, 5, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_4_5_5_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_4_5_5_6_7 hword hexh

#print axioms totalLift_1_4_4_5_5_6_7

/-- **The per-box consumption, box (1, 4, 4, 5, 5, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_4_5_5_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 5, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_4_5_5_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_4_5_5_6_7

/-! ### Box (1, 4, 4, 5, 5, 6, 8) -/

/-- coveredSet membership: box (1, 4, 4, 5, 5, 6, 8) carries the banked family
`compFam_1_4_4_5_5_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_4_5_5_6_8 :
    (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_4_5_5_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 4, 5, 5, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_4_5_5_6_8 :
    InRange17 (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_4_5_5_6_8⟩

#print axioms spineFamDataOS_1_4_4_5_5_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 4, 5, 5, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_4_5_5_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_4_5_5_6_8
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_4_5_5_6_8) hexh hface hchains hw

#print axioms composedConflict_1_4_4_5_5_6_8

/-- **The per-box totality lift, box (1, 4, 4, 5, 5, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_4_5_5_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_4_5_5_6_8 hword hexh

#print axioms totalLift_1_4_4_5_5_6_8

/-- **The per-box consumption, box (1, 4, 4, 5, 5, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_4_5_5_6_8
    (htotal : ComposedTotalOneSided (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 5, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_4_5_5_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_4_5_5_6_8

/-! ### Box (1, 4, 4, 5, 6, 6, 8) -/

/-- coveredSet membership: box (1, 4, 4, 5, 6, 6, 8) carries the banked family
`compFam_1_4_4_5_6_6_8` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_4_5_6_6_8 :
    (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_4_5_6_6_8

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 4, 5, 6, 6, 8)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_4_5_6_6_8 :
    InRange17 (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_4_5_6_6_8⟩

#print axioms spineFamDataOS_1_4_4_5_6_6_8

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 4, 5, 6, 6, 8)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_4_5_6_6_8`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_4_5_6_6_8
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_4_5_6_6_8) hexh hface hchains hw

#print axioms composedConflict_1_4_4_5_6_6_8

/-- **The per-box totality lift, box (1, 4, 4, 5, 6, 6, 8)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_4_5_6_6_8
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_4_5_6_6_8 hword hexh

#print axioms totalLift_1_4_4_5_6_6_8

/-- **The per-box consumption, box (1, 4, 4, 5, 6, 6, 8)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_4_5_6_6_8
    (htotal : ComposedTotalOneSided (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 4, 5, 6, 6, 8] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_4_5_6_6_8 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_4_5_6_6_8

/-! ### Box (1, 4, 5, 5, 6, 6, 7) -/

/-- coveredSet membership: box (1, 4, 5, 5, 6, 6, 7) carries the banked family
`compFam_1_4_5_5_6_6_7` of `Fresh.ComposedFamData` ([T 68/68]). -/
theorem covered_1_4_5_5_6_6_7 :
    (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) ∈ coveredSet := by
  rw [coveredSet]
  repeat' first
    | apply Finset.mem_insert_self
    | apply Finset.mem_insert_of_mem

#print axioms covered_1_4_5_5_6_6_7

/-- **The per-box data datum (the `spineFamData` mirror), box (1, 4, 5, 5, 6, 6, 7)**: `InRange17`
and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side
engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/
theorem spineFamDataOS_1_4_5_5_6_6_7 :
    InRange17 (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) ∧
      ComposedFamData (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  ⟨by decide, oneSidedTotalData _ covered_1_4_5_5_6_6_7⟩

#print axioms spineFamDataOS_1_4_5_5_6_6_7

/-- **The per-box composed conflict (the word-cover kill), box (1, 4, 5, 5, 6, 6, 7)**: the banked
datum `oneSidedTotalData` (the record `compFamData_1_4_5_5_6_6_7`) consumed through the
composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):
a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the
family-exhaustiveness OWED ⟹ False. -/
theorem composedConflict_1_4_5_5_6_6_7
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)))
    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hw : WordRealized g w) : False :=
  composedConflict_fam (oneSidedTotalData _ covered_1_4_5_5_6_6_7) hexh hface hchains hw

#print axioms composedConflict_1_4_5_5_6_6_7

/-- **The per-box totality lift, box (1, 4, 5, 5, 6, 6, 7)**: `ComposedTotalOneSided` at the box's
banked family — the two data-side OWEDs (`NoClearPointWordRealized`,
`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →
ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/
theorem totalLift_1_4_5_5_6_6_7
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ))) :
    ComposedTotalOneSided (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)) :=
  composedTotal_of_wordCover _ covered_1_4_5_5_6_6_7 hword hexh

#print axioms totalLift_1_4_5_5_6_6_7

/-- **The per-box consumption, box (1, 4, 5, 5, 6, 6, 7)**: the totality instance through THE GLUE
(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`'s exact
conclusion shape: an arrangement in the box whose chains are realized (the
W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/
theorem oneSidedSound_1_4_5_5_6_6_7
    (htotal : ComposedTotalOneSided (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)
      (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ) i)
    (hchains : capChainsRealized g (compFamOf (![1, 4, 5, 5, 6, 6, 7] : Fin 7 → ℤ)))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData _ covered_1_4_5_5_6_6_7 htotal g hface hchains hcarve

#print axioms oneSidedSound_1_4_5_5_6_6_7

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

/-! ## 3. The 5 pairwise (two-sided) boxes: the banked `spineFamData` datum discharged -/


/-- **The per-box pairwise consumption, box (1, 2, 3, 4, 5, 6, 8)**: the banked `spineFamData_12568`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `fam12568`,
`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and
`Fresh.FilterAssembly.PairwiseSound`'s exact conclusion shape reduces to the pairwise
totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/
theorem pairwiseSound_1_2_3_4_5_6_8
    (htotal : SpineTotalPairwise (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) fam12568)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ spineFamData_12568.1 spineFamData_12568.2 htotal g hface

#print axioms pairwiseSound_1_2_3_4_5_6_8

/-- **The per-box pairwise consumption, box (1, 3, 4, 5, 5, 6, 8)**: the banked `spineFamData_134556_8`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `fam134556_8`,
`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and
`Fresh.FilterAssembly.PairwiseSound`'s exact conclusion shape reduces to the pairwise
totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/
theorem pairwiseSound_1_3_4_5_5_6_8
    (htotal : SpineTotalPairwise (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) fam134556_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ spineFamData_134556_8.1 spineFamData_134556_8.2 htotal g hface

#print axioms pairwiseSound_1_3_4_5_5_6_8

/-- **The per-box pairwise consumption, box (1, 3, 4, 4, 5, 6, 7)**: the banked `spineFamData_134456_7`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `fam134456_7`,
`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and
`Fresh.FilterAssembly.PairwiseSound`'s exact conclusion shape reduces to the pairwise
totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/
theorem pairwiseSound_1_3_4_4_5_6_7
    (htotal : SpineTotalPairwise (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) fam134456_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ spineFamData_134456_7.1 spineFamData_134456_7.2 htotal g hface

#print axioms pairwiseSound_1_3_4_4_5_6_7

/-- **The per-box pairwise consumption, box (1, 3, 4, 5, 6, 7, 8)**: the banked `spineFamData_134567_8`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `fam134567_8`,
`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and
`Fresh.FilterAssembly.PairwiseSound`'s exact conclusion shape reduces to the pairwise
totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/
theorem pairwiseSound_1_3_4_5_6_7_8
    (htotal : SpineTotalPairwise (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) fam134567_8)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ spineFamData_134567_8.1 spineFamData_134567_8.2 htotal g hface

#print axioms pairwiseSound_1_3_4_5_6_7_8

/-- **The per-box pairwise consumption, box (1, 2, 3, 4, 5, 6, 7)**: the banked `spineFamData_123456_7`
datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `fam123456_7`,
`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and
`Fresh.FilterAssembly.PairwiseSound`'s exact conclusion shape reduces to the pairwise
totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/
theorem pairwiseSound_1_2_3_4_5_6_7
    (htotal : SpineTotalPairwise (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) fam123456_7)
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ spineFamData_123456_7.1 spineFamData_123456_7.2 htotal g hface

#print axioms pairwiseSound_1_2_3_4_5_6_7

/-! ## 4. The totals -/

/-- **THE TOTAL (the one-sided lift)**: for EVERY covered box, the two data-side OWEDs give
the composed totality — the per-box instances `totalLift_<box>` are this theorem's per-box
unfoldings (each of whose downstream kills consumed the banked `ComposedFamData` record
through the composed-cap engine). -/
theorem totalLifts_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b)) :
    ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b) :=
  fun b hb => composedTotal_of_wordCover b hb hword (hexh b hb)

#print axioms totalLifts_of_exhaustiveness

/-- **THE TOTAL (the consumption)**: the per-box totality through the glue to
`Fresh.FilterAssembly.OneSidedSound`'s conclusion shape, for every covered box. -/
theorem oneSidedSounds_of_totals
    (htotal : ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b))
    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb (htotal b hb) g hface hchains hcarve

#print axioms oneSidedSounds_of_totals

/-- **THE TOTAL (the full chain in one theorem)**: `ComposedFamData → ComposedTotalOneSided
→ oneSidedSound_of_composedData → OneSidedSound`, per covered box, with the two data-side
OWEDs the only hypotheses.  (Composes this file's two totals; equals the banked
`Fresh.WordCoverSide.oneSidedSound_of_wordCover` shape.) -/
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

/-- **THE TOTAL (pairwise)**: the pairwise consumption shape at general box/family — the
five per-box instances `pairwiseSound_<box>` instantiate it with the banked data
discharged. -/
theorem pairwiseSound_of_total (n : Fin 7 → ℤ) (fam : Finset JoinEdge)
    (hrange : InRange17 n) (hfam : JoinFam n fam) (htotal : SpineTotalPairwise n fam)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at n fam hrange hfam htotal g hface

#print axioms pairwiseSound_of_total

end Fresh.TotalityLifts
