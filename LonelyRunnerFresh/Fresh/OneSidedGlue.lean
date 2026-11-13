import Fresh.ComposedFamData
import Fresh.SpineSound

/-!
# The OneSided composition glue: banked composed data -> the assembly hypothesis

Written 2026-11-13.  New file; nothing existing is edited.  This file composes the two banked
pieces into the OneSided spine lift that `Fresh.FilterAssembly.OneSidedSound`'s conclusion
shape consumes:

* the DATA: `Fresh.OneSidedComposed.oneSidedTotalData` — every box `b` of the 68-box
  `coveredSet` carries a valid composed family `compFamOf b` (`ComposedFamData`), each record
  bundling a `(x, y, A, B)` word demand with its composed cap chain and the conflict datum
  `A·∏caps ≤ B` (the `composedCap_conflict` product form, E813 item 7);
* the ENGINE: `Fresh.JoinFamComposed.composedFamRefutes` — datum + realized demand + realized
  chain ⟹ False.

The bridge between the pieces and the arrangement is `capChainsRealized`: the composed chains
of the box's family are REALIZED on the readings `g` (`ChainReal g e.y e.caps e.x` per
record).  Per the dump semantics (`joinedge_perbox_v1.jsonl`, cf. the module docstring of
`Fresh.ComposedFamData`), every banked record's chain is a SINGLETON cap chain
`[(e.x, c)]` carrying the transposed-pair J-side cap — implied by every W₀ chain's closed
table (and the box-side caps hold on the whole box) — so `capChainsRealized` is exactly the
one-sided hypothesis at the level of the pieces: W₀-chain-conditional, vacuous on chainless
arrangements, and NOT an interval statement (which is why the `Fresh.SpineTotalData` no-go
lemmas do not apply to it — the caps enter as realized chain steps, not as forced intervals;
the datum-level conflicts are banked, not derived from the box interval).

Contents (all PROVED; every theorem closed):
* `capChainsRealized` — the bridge def (STANDING: DEFINITION);
* `chainReal_singleton` — the singleton-chain builder (the banked records' chain shape);
* `capChainsRealized_of_rawCaps` — per-record raw J-caps ⟹ the bridge (the census's
  realized-cap form lifted to composed chains);
* `composedEdge_kill` — the per-record kill: data + bridge + realized demand ⟹ False;
* `oneSidedKill_of_composedData` / `oneSidedKill_allEdges` — the banked-data kills: on a
  covered box, chains realized + (some / every) record's demand realized ⟹ the OneSided
  conclusion shape (the W₁ clear point exists, via False);
* `oneSidedSound_of_composedData` — THE GLUE (assembly shape, mirroring
  `Fresh.SpineSound.oneSidedSound_at`): for `b ∈ coveredSet`, the banked data
  (`oneSidedTotalData`, no longer a hypothesis) + the W₀-chain-conditional bridge
  (`capChainsRealized`) + the composed totality datum `ComposedTotalOneSided b` ⟹
  `Fresh.FilterAssembly.OneSidedSound`'s exact conclusion shape for `g`.

OWED (named, data-side, NOT assumed here — the glue takes them as hypotheses):
* `ComposedTotalOneSided b (compFamOf b)` — the census word-cover side: carve + chains + no
  W₁ clear point ⟹ some record's demand realized on `g`.  This is `Fresh.SpineTotalData`'s
  acknowledged direction (b) (the finite closed-interval covering argument over the W₁ words;
  `no-raw-kill pairs 0` is its artifact law), composed-form.
* `capChainsRealized` itself as a THEOREM from the carve — `Fresh.SpineTotalData` direction
  (a) (carve ⟹ the J caps realized on `g`), here in composed-chain form; the one-sided
  conditional.  At the pieces' level it is the hypothesis `capChainsRealized`, which is why
  the glue is vacuous on chainless arrangements by design.
* the per-box conversion of the composed records into a verbatim `JoinFam` family (the 8m±1
  numerator bookkeeping the dump subsumes), IF the exact
  `Fresh.FilterAssembly.OneSidedSound` hypothesis shape (quantified over `JoinFam` families)
  is to be consumed by `Fresh.FilterAssembly.filterAssembly` without restatement.

Chain-form note: the W₀ chain enters in the `Fresh.JoinFamComposed.ChainReal` form (the
composed engine's realized cap chain through the readings) — the SpineSound/JoinFamComposed
form, which is what the banked `ComposedFamData` chains and `composedCap_conflict` consume.
`Fresh.UClosureKill`'s `ChainRealized`/`chainRun` is the separate UTable-closure
formalization of the box theorem and is not the carrier here.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound) — `sorryAx` is failure.
-/

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

/-- The singleton-chain builder: one realized cap `ρ_y/ρ_x ≤ c` with positive endpoints is
the realized chain from `y` to `x` carrying the single cap `c` on node `x` — the chain shape
of every banked record (`⟨x, y, A, B, [(x, c)]⟩`, cf. `Fresh.ComposedFamData`). -/
theorem chainReal_singleton {g : Fin 7 → ℝ} {y x : Fin 7} {c : ℝ}
    (hcap : g y / g x ≤ c) (hypos : 0 < g y) (hxpos : 0 < g x) :
    ChainReal g y [(x, c)] x :=
  ChainReal.cons y x c [] x hcap hypos hxpos (ChainReal.nil x hxpos)

#print axioms chainReal_singleton

/-- The census's realized-cap form lifts to the bridge: if every record's chain is a
singleton cap chain `[(e.x, c)]` (the banked shape) and every record's raw J-cap
`ρ_y/ρ_x ≤ c` is realized on `g` (with positive endpoints), then `capChainsRealized` holds. -/
theorem capChainsRealized_of_rawCaps {f : ComposedFam} {g : Fin 7 → ℝ}
    (h : ∀ e ∈ f.edges, ∃ c : ℝ, e.caps = [(e.x, c)] ∧
      0 < g e.x ∧ 0 < g e.y ∧ g e.y / g e.x ≤ c) :
    capChainsRealized g f := by
  intro e he
  obtain ⟨c, hc, hxpos, hypos, hcap⟩ := h e he
  rw [hc]
  exact chainReal_singleton hcap hypos hxpos

#print axioms capChainsRealized_of_rawCaps

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

/-- The readings in a box have positive endpoints for every record (via
`Fresh.SpineSound.face_pos`: every `FaceLo ≥ 1`). -/
theorem composedEdge_pos {b : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) (e : ComposedEdge) :
    0 < g e.x ∧ 0 < g e.y := ⟨face_pos hface e.x, face_pos hface e.y⟩

#print axioms composedEdge_pos

/-! ## 3. The banked-data kills on a covered box -/

/-- **The banked kill (existential demand form)**: on a covered box `b`, the W₀-chain-
conditional bridge holds on `g` and SOME record's word demand is realized — then the OneSided
conclusion shape holds (the W₁ clear point exists): the demanded record dies through the
banked datum, so anything follows.  This is the maximal shape the banked pieces compose to
without the word-cover totality. -/
theorem oneSidedKill_of_composedData (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    {g : Fin 7 → ℝ} (hchains : capChainsRealized g (compFamOf b))
    (hdemand : ∃ e ∈ (compFamOf b).edges,
      0 < g e.x ∧ 0 < g e.y ∧ g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  exfalso
  obtain ⟨e, he, hxpos, hypos, hdem⟩ := hdemand
  exact composedEdge_kill (oneSidedTotalData b hb) hchains he hxpos hypos hdem

#print axioms oneSidedKill_of_composedData

/-- **The banked kill (all-edges demand form)** — the "word cover of [9,15] forces its
edges; every edge dies ⟹ no word" shape: on a covered box `b`, chains realized + EVERY
record's demand realized (the family nonempty — each covered box's family is a nonempty
record list) ⟹ the OneSided conclusion shape.  Positivity is carried by the box faces, so
the demand form may drop it. -/
theorem oneSidedKill_allEdges (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hne : (compFamOf b).edges ≠ [])
    (hdemands : ∀ e ∈ (compFamOf b).edges, g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  exfalso
  cases hl : (compFamOf b).edges with
  | nil => exact absurd hl hne
  | cons e es =>
    have he : e ∈ (compFamOf b).edges := by rw [hl]; simp
    have hpos := composedEdge_pos hface e
    exact composedEdge_kill (oneSidedTotalData b hb) hchains he hpos.1 hpos.2
      (hdemands e he)

#print axioms oneSidedKill_allEdges

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

/-- The glue in the demand-side totality form: the per-box totality datum may equivalently
be supplied demand-realized (with the positivity carried by the box faces). -/
theorem oneSidedSound_of_composedData' (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (htotal : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) →
      capChainsRealized g (compFamOf b) →
      Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
      ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
      ∃ e ∈ (compFamOf b).edges, g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  refine oneSidedSound_of_composedData b hb (fun g' hface' hch hcv hnc => ?_) g hface hchains
    hcarve
  obtain ⟨e, he, hdem⟩ := htotal g' hface' hch hcv hnc
  exact ⟨e, he, composedEdge_pos hface' e |>.1, composedEdge_pos hface' e |>.2, hdem⟩

#print axioms oneSidedSound_of_composedData'

/-- **The assembly connection, stated**: the glue's conclusion is verbatim
`Fresh.FilterAssembly.OneSidedSound`'s conclusion shape; consuming it inside
`Fresh.FilterAssembly.filterAssembly` verbatim additionally needs, per covered box `b`, the
two OWED directions named above (`ComposedTotalOneSided b (compFamOf b)`; carve ⟹
`capChainsRealized`) and the per-box `JoinFam` conversion of the composed records — all
data-side, none assumed here. -/
theorem glue_conclusion_shape (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (htotal : ComposedTotalOneSided b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb htotal g hface hchains hcarve

#print axioms glue_conclusion_shape

end Fresh.OneSidedGlue
