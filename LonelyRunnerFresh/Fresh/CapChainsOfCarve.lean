import Fresh.OneSidedGlue
import Fresh.UClosureKill

/-!
# CapChainsOfCarve: the OneSided conditional — a realized W₀ chain realizes the family's cap chains

Written 2026-11-13.  New file; nothing existing is edited.  This proves the load-bearing
conditional of the OneSided glue (`Fresh.OneSidedGlue.oneSidedSound_of_composedData`'s named
OWED direction (a)): IF the arrangement `g` admits a W₀ chain — given in
`Fresh.UClosure`'s `ChainRealized` form, each step's two seam bounds strictly satisfied by
`g` itself — THEN `capChainsRealized g f` holds for the box's composed family `f` (every
record's composed cap chain is realized on `g`, `Fresh.JoinFamComposed.ChainReal g e.y
e.caps e.x`), provided the records' caps are DOMINATED: each cap of each record's walk is
bounded below by a stored table entry of a table that `g`'s readings realize.

The two domination routes mirror the dump semantics (`joinedge_perbox_v1.jsonl`, cf.
`Fresh.ComposedFamData`'s module docstring) exactly:

* BOX-side caps — "the `box` side is the box closure `U0`, hence holds on the whole box":
  the cap is dominated by an entry of the box's opening table `U` (`uMk`'s output), which
  is realized on every in-box arrangement; no chain needed (`capChainsRealized_of_boxDom`);
* J-side caps — "the `J` side is the join of ALL W₀ chains' closed tables, hence implied by
  every chain": the cap is dominated by an entry of `g`'s own chain's CLOSED TRACE table
  (the final `UTable` of `chainRun`); the trace stays realized by `g`
  (`Fresh.UClosure.chain_fine_of_realized`), so the entry's value holds on `g`'s readings,
  and domination transfers it to the cap (`capChainsRealized_of_chainDom`).

Per-cap domination is carried by `CapsDom` (the walk-shaped domination predicate mirroring
`ChainReal`'s constructors); `chainReal_of_capsDom` is the domination-augmented variant of
`Fresh.UClosureKill`'s trace-realization induction, building the realized walk step by step
(`ChainReal.cons`) from realized table entries (`UFine` + `bhof_eq_some` + the value
domination — a strict stored bound `ρ < c₀ ≤ c` still yields `ρ ≤ c`).  The per-step
engine `chainReal_of_stepDom` shows the rawest route: a cap dominating one seam bound of
`g`'s own chain is realized outright.

OWED (named, data-side — the dump-v2 refinement, honestly NOT assumed in the theorems):
`DumpDom` — the per-record identification datum pairing every banked record's caps with
the table entries (box-side or J-side) that dominate them.  Dump v1 records the caps as
VALUES only (the transposed-pair entries of the join, per record); which entry of the
closed table realizes which banked cap — and, for the 5.7% derived-only deaths, the
path decomposition of the word's accumulated products — is exactly the dump-v2 detail the
`Fresh.ComposedFamData` honest residual names.  Everything downstream composes: the glue
consumes `capChainsRealized` verbatim (`oneSided_of_dumpDom`).

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound) — `sorryAx` is failure.
-/

namespace Fresh.CapChainsOfCarve

open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedGlue
  Fresh.OneSidedComposed Fresh.UClosure

/-! ## 1. Table-entry domination of a cap walk -/

/-- The walk-shaped domination predicate (the `ChainReal` mirror): every cap `c` of the
walk `y → (z₁, c₁) → … → x` is dominated by a stored table entry — the table `V` has, on
the corresponding consecutive pair `(prev, zᵢ)`, a bound `(c₀, s)` with VALUE `c₀ ≤ c`
(the strict flag is irrelevant: a strict bound `ρ < c₀ ≤ c` still gives `ρ ≤ c`).  The
table is the box closure `U₀` (box-side caps) or a W₀ chain's closed trace table (J-side
caps). -/
inductive CapsDom (V : UTable) : Fin 7 → List (Fin 7 × ℝ) → Fin 7 → Prop
  | nil (x : Fin 7) : CapsDom V x [] x
  | cons (y z : Fin 7) (c : ℝ) (l : List (Fin 7 × ℝ)) (w : Fin 7)
      (hentry : ∃ c₀ : ℚ, ∃ s : Bool, V y z = some (c₀, s) ∧ ((c₀ : ℚ) : ℝ) ≤ c)
      (hrest : CapsDom V z l w) : CapsDom V y ((z, c) :: l) w

/-- The singleton domination builder: one table entry dominating the one cap. -/
theorem capsDom_single {V : UTable} {y z : Fin 7} {c : ℝ}
    (hentry : ∃ c₀ : ℚ, ∃ s : Bool, V y z = some (c₀, s) ∧ ((c₀ : ℚ) : ℝ) ≤ c) :
    CapsDom V y [(z, c)] z :=
  CapsDom.cons y z c [] z hentry (CapsDom.nil z)

#print axioms capsDom_single

/-- **The domination-augmented trace-realization induction**: if `g` realizes the table
`V` (`UFine`) and every cap of the walk is dominated by `V`'s entries, the walk is a
realized cap chain on `g` (`ChainReal`).  Each step is `ChainReal.cons` on a realized
table entry (`bhof_eq_some`) shrunk by the value domination; the strict flag is handled
by cases (strict `ρ < c₀ ≤ c`, non-strict `ρ ≤ c₀ ≤ c`). -/
theorem chainReal_of_capsDom {g : Fin 7 → ℝ} (hpos : ∀ k, 0 < g k)
    {V : UTable} (hfine : UFine g V) {y x : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : CapsDom V y caps x) : ChainReal g y caps x := by
  induction h with
  | nil x => exact ChainReal.nil x (hpos x)
  | cons y z c l w hentry hrest ih =>
    obtain ⟨c₀, s, hV, hcle⟩ := hentry
    have hholds : BHolds s (g y / g z) c₀ := bhof_eq_some (hfine y z) hV
    have hcap : g y / g z ≤ ((c₀ : ℚ) : ℝ) := by
      cases s with
      | false => simpa only [BHolds] using hholds
      | true => exact le_of_lt (by simpa only [BHolds] using hholds)
    exact ChainReal.cons y z c l w (le_trans hcap hcle) (hpos y) (hpos z) ih

#print axioms chainReal_of_capsDom

/-! ## 2. The per-step domination engine -/

/-- A chain step's seam bounds, extracted from `ChainRealized`'s step record — the two
strict bounds each step of `g`'s own W₀ chain asserts on consecutive readings
(`Fresh.UClosure.ChainRealized`'s `BHolds` pair). -/
theorem stepBounds_of_realized {g : Fin 7 → ℝ} {U : UTable} {a : Fin 7} {Aex : ℚ}
    {st : Step} {rest : List Step}
    (h : ChainRealized g U a Aex (st :: rest)) :
    BHolds true (g a / g st.b) (Aex / st.A) ∧ BHolds true (g st.b / g a) (st.B / Aex) := by
  simp only [ChainRealized] at h
  obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := h
  exact ⟨sat1, sat2⟩

#print axioms stepBounds_of_realized

/-- The rawest domination route: a cap `c` dominating ONE seam bound of `g`'s own chain
(`ρ_y/ρ_x < B/Aex ≤ c`) realizes the singleton cap chain `[(x, c)]` from `y` — the
`ChainReal` shape of every banked record (`Fresh.ComposedFamData`). -/
theorem chainReal_of_stepDom {g : Fin 7 → ℝ} {y x : Fin 7} {c : ℝ} {Aex B : ℚ}
    (hypos : 0 < g y) (hxpos : 0 < g x)
    (hbound : BHolds true (g y / g x) (B / Aex))
    (hdom : ((B / Aex : ℚ) : ℝ) ≤ c) :
    ChainReal g y [(x, c)] x := by
  simp only [BHolds] at hbound
  exact chainReal_singleton (le_of_lt (lt_of_lt_of_le hbound hdom)) hypos hxpos

#print axioms chainReal_of_stepDom

/-! ## 3. The box-side half (no chain needed) -/

/-- **BOX-side caps** (the dump's `box` side: "the box closure `U0`, hence holds on the
whole box"): if every record's walk is dominated by entries of the box's opening table
`U` and `U` is realized on `g` (the box-side datum), the family's chains are realized on
`g` with NO chain hypothesis. -/
theorem capChainsRealized_of_boxDom (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (U : UTable) (hfine0 : UFine g U)
    (hdom : ∀ e ∈ f.edges, CapsDom U e.y e.caps e.x) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  intro e he
  exact chainReal_of_capsDom hpos hfine0 (hdom e he)

#print axioms capChainsRealized_of_boxDom

/-! ## 4. THE CONDITIONAL (direction (a)): W₀ chain realized ⟹ cap chains realized -/

/-- **THE CONDITIONAL** (the OneSided glue's OWED direction (a), proved): if `g` (in the
box) admits a W₀ chain in the `Fresh.UClosure.ChainRealized` form — each step's two seam
bounds strictly satisfied by `g` itself, starting on the realized opening table `U` —
and every record's cap walk is dominated by entries of the chain's CLOSED TRACE table
(the final `UTable` of `chainRun`; the join-of-chains table semantics), then
`capChainsRealized g f`: every record's composed cap chain is realized on `g`.
Engine: the trace stays realized by `g` (`chain_fine_of_realized`), and domination
transfers the realized entries through `chainReal_of_capsDom`. -/
theorem capChainsRealized_of_chainDom (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g U) (hchain : ChainRealized g U a Aex steps)
    (hdom : ∀ e ∈ f.edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  obtain ⟨Uf, af, Af, hrun, hfine, -⟩ := chain_fine_of_realized hpos hfine0 hchain
  intro e he
  exact chainReal_of_capsDom hpos hfine (hdom e he Uf af Af hrun)

#print axioms capChainsRealized_of_chainDom

/-- The faithful two-sided form (the dump's per-record semantics: each banked cap is
box-side or J-side): box-side caps dominated by the opening table, J-side caps dominated
by the closed trace table — EITHER suffices per record. -/
theorem capChainsRealized_of_domData (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g U) (hchain : ChainRealized g U a Aex steps)
    (hdom : ∀ e ∈ f.edges,
      CapsDom U e.y e.caps e.x ∨
        (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
          chainRun U a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  obtain ⟨Uf, af, Af, hrun, hfine, -⟩ := chain_fine_of_realized hpos hfine0 hchain
  intro e he
  rcases hdom e he with hU | hV
  · exact chainReal_of_capsDom hpos hfine0 hU
  · exact chainReal_of_capsDom hpos hfine (hV Uf af Af hrun)

#print axioms capChainsRealized_of_domData

/-! ## 5. The dump-v2 OWED and the glue consumption -/

/-- **OWED — the dump-v2 data refinement** (data-side, honestly not assumed in the
theorems above; exactly the `Fresh.ComposedFamData` honest residual): the per-record
IDENTIFICATION datum — for every in-box arrangement admitting a W₀ chain, every record's
caps are dominated (each cap by an entry of the box closure, or by an entry of the
chain's closed trace table).  Dump v1 records the caps as values only; pairing each
banked cap with its dominating entry — and, for the derived-only deaths, the path
decomposition of the word's accumulated products — is the dump-v2 detail. -/
-- STANDING: OWED
def DumpDom (n : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    ∀ (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step),
      UFine g U → ChainRealized g U a Aex steps →
      ∀ e ∈ f.edges,
        CapsDom U e.y e.caps e.x ∨
          (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
            chainRun U a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)

/-- The OWED discharges the conditional verbatim. -/
theorem capChainsRealized_of_dumpDom (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g U) (hchain : ChainRealized g U a Aex steps)
    (hdd : DumpDom n f) :
    capChainsRealized g f :=
  capChainsRealized_of_domData f hface U a Aex steps hfine0 hchain
    (hdd g hface U a Aex steps hfine0 hchain)

#print axioms capChainsRealized_of_dumpDom

/-- **The glue consumption**: the conditional drops into
`Fresh.OneSidedGlue.oneSidedSound_of_composedData` verbatim — on a covered box, the OWED
dump-v2 datum + `g`'s own realized W₀ chain give the OneSided conclusion shape (the W₁
clear point exists) through the banked kill. -/
theorem oneSided_of_dumpDom (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (htotal : ComposedTotalOneSided b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g U) (hchain : ChainRealized g U a Aex steps)
    (hdd : DumpDom b (compFamOf b))
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb htotal g hface
    (capChainsRealized_of_dumpDom (compFamOf b) hface U a Aex steps hfine0 hchain hdd)
    hcarve

#print axioms oneSided_of_dumpDom

end Fresh.CapChainsOfCarve
