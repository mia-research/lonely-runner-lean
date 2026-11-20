import Fresh.UClosureKill
import Fresh.MechDataBatch

/-!
# M4CertSound: the DFS-soundness engine (pruned-tree domination for the M4 residual boxes)

Written 2026-11-14.  New file; nothing existing is edited.  This formalizes the DFS-soundness
engine of `j2_admit_cert_v2.py` (the M4 certificate search, `j2_admit_cert2_checkpoint.jsonl`,
[T 2329/2329] banked as `Fresh.MechDataBatch.m4res_*` / `m4resData_*`): the tree the DFS builds
over the comb-zone chain space, its per-leaf killing conditions, and the domination theorem

  closed tree + child-filter completeness + per-prune-leaf domination + root admissibility
    ⟹ no real W₀ chain (the `M4CertSound` shape) ⟹ clear point per arrangement.

The engine MIRRORS `Fresh.UClosureKill`'s proved kill chain, with the DFS tree replacing the
fixpoint: `dfsWalk` is the `FixCoversChains` analogue (a real chain's path is never filtered
away — its steps are seam-feasible on the node tables it realizes, `uAdd_none_of_fine_sat` +
`uAdd_fine_some`, so it descends through `DfsEnum`-matching children), the node completion
check (`uExitOK`) plays the direct-exit role (`uExitOK_of_fine` fires it at the real chain's
terminal node, contradicting `DfsClosed`), and `chainRealized_tableMono` (a chain realized
from ANY table realized by ρ is realized from any other such table) discharges the
"any realized opening" quantifier of `M4CertSound`.

Division of labour, honestly recorded:
* PROVED here, fully general, no data hypotheses: **the tree-domination lemma** `dfsWalk`
  (closed + enum + prune-dom + soft-admissibility ⟹ False, by induction over the chain),
  the **conversion lemma** `chainRealized_tableMono`, the **forest/no-chain composition**
  `noChain_of_forest` + `m4CertSound_of_forest` (delivers `Fresh.MechDataBatch.M4CertSound`
  verbatim), the **compositions** `killExcl_of_m4cert` (M4 certificate ⟹ the exact
  chain-exclusion shape `Fresh.UClosure.kill_sound` concludes, so M4 certificates substitute
  the C3 fixpoint kill wherever that conclusion is consumed) and `boxAdmit_of_m4cert`
  (M4 certificate + link 1 ⟹ clear point per arrangement, `boxAdmit_of_kill`'s proof shape
  with the fixpoint kill replaced by the DFS certificate), and the **data connection**
  `boxN` + `leafKeys_env90` + `m4CertSound_of_data` + `m4boxClear_of_data` (the banked
  `m4resData_<box>` consumed: the box tuple becomes the census function `boxN`, every
  distinct leaf key embeds in the 90-type key space `Fin 6 × Fin 15` of the C3 fixpoint
  via `leafKey_in_env90`, and the soundness + envelope bridge deliver together).
* OWED (named, data-side, per box): **(a)** `DfsRootAdm` — the E810 side of the child-filter
  completeness [P]: every real chain's opening matches a tree root whose table it realizes
  (the W₀ chain's first zone straddles 1, so the start-zone enumeration covers it) and the
  chain's steps pass the soft filters along the induced path (entry below the frontier sup
  and zone-freshness: the strict-monotone reading of E810's covering chains, the same status
  as `EnvChain`'s envelope conditions in `E810ChainCover`); **(b)** the discharge of
  `DfsPruneDom`'s per-prune-leaf condition FROM the artifact's `reach_utc` verdicts — the
  state-graph projection [P] of `reach_utc` (every real chain prefix projects into the
  (frontier-sup, reading) state graph and a real completing chain yields a completing
  state); **(c)** the transcription of each box's checkpoint tree into the `DfsCert` data.
  The dead-end leaf condition and the node completion verdicts need NO separate OWED: they
  are exactly what `DfsEnum` (at dead ends: no filter-passing step) and `DfsClosed` (no
  node fires) assert, and the DFS computes them by construction.
* The banked instance `m4cert_1_4_6_7_10_16_16` consumes `m4resData_1_4_6_7_10_16_16` (the
  biggest residual tree: nodes=51748, leaves=15622, 18 distinct leaf keys, all in the
  90-type envelope) and carries the per-box domination certificate as the named OWED
  `DfsCert_1_4_6_7_10_16_16`; `hn17_1_4_6_7_10_16_16` (the census envelope n ≤ 17) is
  DISCHARGED from the record itself.
-/

namespace Fresh.M4Cert

open Fresh.FilterAssembly Fresh.UClosure Fresh.MechDataBatch

/-! ## 1. The DFS certificate tree (node state and shape, verbatim `j2_admit_cert_v2.py`)

A node state is the DFS state `(U, a, Aex, P, seen)`: the bound table (box opening table +
the prefix's start and seam bounds), the last reading row and its exit numerator, the
frontier supremum `P` (the exit sup `B/lo'_b` of the tightened ranges), and the set of
already-expanded zones `(row, exit)` (the `seen` freshness set).  The tree has three node
kinds: internal nodes (expanded: one child per filter-passing zone step), closure-prune
leaves (the `reach_utc` abstraction found no completing state — LEAF kind `reach` of the
checkpoint), and dead-end leaves (no child passed the filters — LEAF kind `deadend`).  The
completion check is a property of the node state (`uExitOK`), not a node kind: a node where
it fires is a control stop ('chain'), and a closed tree has none (`DfsClosed`). -/

/-- One DFS node state, verbatim the `dfs(U, a, Aex, seen, depth, P)` state of
`j2_admit_cert_v2.py`. -/
structure DfsNode where
  /-- the bound table carried at the node (box opening + prefix bounds) -/
  U : UTable
  /-- the last reading row -/
  a : Fin 7
  /-- the last zone's exit numerator -/
  Aex : ℚ
  /-- the frontier supremum (`P = B/lo'_b` from the tightened ranges) -/
  P : ℚ
  /-- the expanded-zone set `(row, exit)` (the `seen` freshness set) -/
  seen : Finset (Fin 7 × ℚ)

/-- One DFS certificate tree: internal node with children, closure-prune leaf, or dead-end
leaf.  A node whose completion check fires is a control stop and cannot occur in a closed
tree (`DfsClosed` demands `uExitOK = false` at every node). -/
inductive DfsCert where
  /-- expanded node: one child per filter-passing zone step -/
  | node (st : DfsNode) (children : List DfsCert) : DfsCert
  /-- closure-prune leaf: `reach_utc` found no completing state (checkpoint kind `reach`) -/
  | prune (st : DfsNode) : DfsCert
  /-- dead-end leaf: no child zone passed the filters (checkpoint kind `deadend`) -/
  | deadend (st : DfsNode) : DfsCert

/-- The root state of a tree. -/
def DfsCert.root : DfsCert → DfsNode
  | .node st _ => st
  | .prune st => st
  | .deadend st => st

/-- The tightened range hi of reading row `b` at table `U`: `min((2n_b+1)/2, U[b][0])`,
verbatim `tranges` (flags ignored = generous = sound). -/
-- Fixed 2026-11-20: rows ≥ 1 previously dropped the /2 (code said 2n±1 where the
-- docstring and the reconstruction's `tranges` say (2n±1)/2); concrete `childEq`
-- transcription caught it (17/11 ≠ 34/11).  Row 0 keeps [1, 3] unhalved, verbatim.
def dfsHi (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) : ℚ :=
  if 0 < b.val then
    match U b 0 with
    | some (c, _) => min (((2 * n b + 1 : ℤ) : ℚ) / 2) c
    | none => ((2 * n b + 1 : ℤ) : ℚ) / 2
  else ((2 * n 0 + 1 : ℤ) : ℚ)

/-- The tightened range lo of reading row `b` at table `U`: `max((2n_b−1)/2, 1, 1/U[0][b])`,
verbatim `tranges` (row 0 unused). -/
-- Fixed 2026-11-20: rows ≥ 1 previously dropped the /2 (see `dfsHi`).
def dfsLo (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) : ℚ :=
  if 0 < b.val then
    let lo := max (((2 * n b - 1 : ℤ) : ℚ) / 2) 1
    match U 0 b with
    | some (c, _) => max lo (1 / c)
    | none => lo
  else 1

/-- The tightened tooth family of reading row `b` at table `U` (verbatim `tzones`): the
teeth `8j−1, 8j+1` (`j ≥ 1`) whose window entry `(8j−1)/hi'_b` is below 7 (the loop-break
condition). -/
-- STANDING: DEFINITION
def dfsZone (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) (A B : ℚ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ A = ((8 * j - 1 : ℕ) : ℚ) ∧ B = ((8 * j + 1 : ℕ) : ℚ) ∧
    ((A : ℝ) / (dfsHi n U b : ℝ)) < 7

/-- The soft filters of a candidate child step at a node (verbatim: zone of the tightened
family, entry below the frontier sup `P`, zone fresh) — the part the E810 monotone side
supplies for real chains; the seam-feasibility part is derived from the machinery. -/
-- STANDING: DEFINITION
def DfsSoft (n : Fin 7 → ℤ) (st : DfsNode) (b : Fin 7) (A B : ℚ) : Prop :=
  dfsZone n st.U b A B ∧ ((A : ℝ) / (dfsHi n st.U b : ℝ)) < (st.P : ℝ) ∧
    (b, B) ∉ st.seen

/-- The full child filters at a node (verbatim): soft filters + both seam bounds feasible on
the node table (the two `gt` calls = `uStep` surviving). -/
-- STANDING: DEFINITION
def DfsFilters (n : Fin 7 → ℤ) (st : DfsNode) (b : Fin 7) (A B : ℚ) : Prop :=
  DfsSoft n st b A B ∧ uStep st.U st.a b st.Aex A B ≠ none

/-- The child state produced by expanding step `(b, B)` with surviving table `V` (verbatim):
row/exit updated, frontier sup `B/lo'_b` from the PARENT's tightened ranges, zone marked
seen. -/
def childState (n : Fin 7 → ℤ) (st : DfsNode) (b : Fin 7) (B : ℚ) (V : UTable) : DfsNode :=
  ⟨V, b, B, B / dfsLo n st.U b, st.seen ∪ {(b, B)}⟩

/-- A child tree MATCHES a step at node `st` when it was produced by the DFS expansion rule:
its root state is the `childState` of the step's surviving table. -/
-- STANDING: DEFINITION
def DfsMatch (n : Fin 7 → ℤ) (st : DfsNode) (b : Fin 7) (A B : ℚ) (c : DfsCert) : Prop :=
  ∃ V : UTable, uStep st.U st.a b st.Aex A B = some V ∧
    childState n st b B V = c.root

/-! ## 2. The certificate predicates (what the DFS run's closed tree certifies) -/

/-- The node completion check FAILS (verbatim `add(U, a, 0, Aex/7, True)` infeasible). -/
-- STANDING: DEFINITION
def DfsNodeOK (st : DfsNode) : Prop := uExitOK st.U st.a st.Aex = false

/-- The tree is CLOSED: the completion check fails at every node (no control stop fired). -/
-- STANDING: DEFINITION
def DfsClosed : DfsCert → Prop
  | .node st ch => DfsNodeOK st ∧ ∀ c ∈ ch, DfsClosed c
  | .prune st => DfsNodeOK st
  | .deadend st => DfsNodeOK st

/-- The tree ENUMERATES the filter-passing steps: at every internal node the children
include a match for EVERY filter-passing step (the DFS expanded all of them), recursively;
at every dead-end leaf NO step passes the filters (the DFS verified the dead end).  At
closure-prune leaves no requirement — their domination is `DfsPruneDom`. -/
-- STANDING: DEFINITION
def DfsEnum (n : Fin 7 → ℤ) : DfsCert → Prop
  | .node st ch =>
    (∀ b : Fin 7, ∀ A B : ℚ, DfsFilters n st b A B → ∃ c ∈ ch, DfsMatch n st b A B c) ∧
      ∀ c ∈ ch, DfsEnum n c
  | .prune _ => True
  | .deadend st => ∀ b : Fin 7, ∀ A B : ℚ, ¬ DfsFilters n st b A B

/-- The per-prune-leaf domination (the leaf-level killing inequality): at every
closure-prune leaf, NO completing real chain passes through the node — no positive readings
realizing the node table realize a `ChainRealized` continuation (this is exactly the [P]
conclusion of the `reach_utc` abstraction; its discharge from the artifact's verdicts is the
named OWED (b) of the header). -/
-- STANDING: DEFINITION
def DfsPruneDom : DfsCert → Prop
  | .node _ ch => ∀ c ∈ ch, DfsPruneDom c
  | .prune st =>
    ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → UFine ρ st.U →
      ∀ steps : List Step, ¬ ChainRealized ρ st.U st.a st.Aex steps
  | .deadend _ => True

/-- The soft admissibility of a step list from a node state: each step passes the soft
filters at its (inductively constructed) node state — the E810-side condition on real chains
(named OWED (a) of the header). -/
-- STANDING: DEFINITION
def DfsSoftAdm (n : Fin 7 → ℤ) : DfsNode → List Step → Prop
  | _, [] => True
  | st, s :: rest =>
    DfsSoft n st s.b s.A s.B ∧
      ∀ V : UTable, uStep st.U st.a s.b st.Aex s.A s.B = some V →
        DfsSoftAdm n (childState n st s.b s.B V) rest

/-- **OWED — the root-admissibility closure (the E810 side of the DFS enumeration).**  Every
real chain's opening matches a tree root whose table it realizes, and the chain's steps pass
the soft filters along the induced path.  Discharges from: the start-zone enumeration of the
DFS roots (a W₀ chain's first zone straddles 1, so it is a start zone the DFS tried) + the
strict-monotone reading of E810's covering chains (entry below the frontier sup, zones
fresh).  Same hypothesis status as `EnvChain`'s envelope conditions inside
`Fresh.UClosure.E810ChainCover`. -/
-- STANDING: OWED
def DfsRootAdm (n : Fin 7 → ℤ) (T : List DfsCert) : Prop :=
  ∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
    (∀ k, 0 < ρ k) → UFine ρ U0 → ChainRealized ρ U0 a0 Aex0 steps →
      ∃ t ∈ T, t.root.a = a0 ∧ t.root.Aex = Aex0 ∧ UFine ρ t.root.U ∧
        DfsSoftAdm n t.root steps

/-! ## 3. The conversion lemma (the "any realized opening" quantifier) -/

/-- A chain realized from ANY opening table is realized from ANY OTHER table realized by the
same readings: each step's two seam bounds are satisfied by `ρ` (carried by `ChainRealized`,
table-independent), so the step's two `add`s survive on the new table
(`uAdd_none_of_fine_sat`) and propagate it realized (`uAdd_fine_some`), and the continuation
re-projects onto the reconstructed table (the induction re-bases the target per step). -/
theorem chainRealized_tableMono {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) :
    ∀ (steps : List Step) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ),
      ChainRealized ρ U0 a0 Aex0 steps →
      ∀ U' : UTable, UFine ρ U' → ChainRealized ρ U' a0 Aex0 steps := by
  intro steps
  induction steps with
  | nil => intro U0 a0 Aex0 h U' _; exact h
  | cons s rest ih =>
    intro U0 a0 Aex0 h U' hfine'
    simp only [ChainRealized] at h ⊢
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := h
    have hc1 : 0 < (Aex0 / s.A : ℚ) := bpos_of_holds (div_pos (hpos a0) (hpos s.b)) sat1
    have hAex' : 0 < Aex0 := by
      have h1 : Aex0 = (Aex0 / s.A) * s.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    -- the step's two adds survive on U' (the seam bounds are satisfied by the same ρ) and
    -- propagate it realized; the continuation re-projects onto the reconstructed table
    have hsat1 : BHolds true (ρ a0 / ρ s.b) (Aex0 / s.A) := sat1
    have hsat2 : BHolds true (ρ s.b / ρ a0) (s.B / Aex0) := sat2
    have hsurv1 : uAdd U' a0 s.b (Aex0 / s.A) true ≠ none :=
      uAdd_none_of_fine_sat hpos hfine' hsat1
    have hsurv2 (W1 : UTable) (hf1 : UFine ρ W1) : uAdd W1 s.b a0 (s.B / Aex0) true ≠ none :=
      uAdd_none_of_fine_sat hpos hf1 hsat2
    obtain ⟨W1, hh1⟩ : ∃ W1, uAdd U' a0 s.b (Aex0 / s.A) true = some W1 :=
      Option.ne_none_iff_exists'.mp hsurv1
    have hf1 : UFine ρ W1 := uAdd_fine_some hpos hfine' hsat1 hh1
    obtain ⟨W2, hh2⟩ : ∃ W2, uAdd W1 s.b a0 (s.B / Aex0) true = some W2 :=
      Option.ne_none_iff_exists'.mp (hsurv2 W1 hf1)
    have hf2 : UFine ρ W2 := uAdd_fine_some hpos hf1 hsat2 hh2
    have hstep : uStep U' a0 s.b Aex0 s.A s.B = some W2 := by
      unfold uStep
      rw [uGt_pos U' a0 s.b hAex' hA, hh1]
      show uGt W1 s.B s.b Aex0 a0 = some W2
      rw [uGt_pos W1 s.b a0 hB hAex', hh2]
    exact ⟨W2, hstep, hA, hB, sat1, sat2, ih V s.b s.B hrest W2 hf2⟩

#print axioms chainRealized_tableMono

/-! ## 4. The tree-domination lemma (the engine) -/

/-- **The tree-domination lemma (the `FixCoversChains` analogue for the DFS tree).**  A real
chain whose opening matches a closed, enumerating, prune-dominated tree root and whose steps
are soft-admissible along the induced path cannot exist: while steps remain it descends
through a matching child (the seam bounds are satisfied by its own readings, so the step
survives the node table — `uAdd_none_of_fine_sat` — and the table stays realized —
`uAdd_fine_some`; the soft filters are the chain-side hypothesis), and when the steps are
exhausted the terminal node's completion check fires (`uExitOK_of_fine`), contradicting
`DfsClosed`.  At a dead-end leaf the real step's filters contradict `DfsEnum`'s
no-filter-passing-step verdict; at a closure-prune leaf the chain contradicts the leaf's
domination. -/
theorem dfsWalk (n : Fin 7 → ℤ) (steps : List Step) :
    ∀ (T : DfsCert) (st : DfsNode), T.root = st → DfsClosed T → DfsEnum n T → DfsPruneDom T →
      ∀ ρ : Fin 7 → ℝ, (∀ k, 0 < ρ k) → UFine ρ st.U →
        ChainRealized ρ st.U st.a st.Aex steps → DfsSoftAdm n st steps → False := by
  induction steps with
  | nil =>
    intro T st hroot hclosed _ _ ρ hpos hfine hchain _
    simp only [ChainRealized] at hchain
    have h1 : uExitOK st.U st.a st.Aex = true := uExitOK_of_fine hpos hfine hchain
    rcases T with ⟨m, ch⟩ | ⟨m⟩ | ⟨m⟩ <;>
      simp only [DfsCert.root, DfsClosed, DfsNodeOK] at hroot hclosed
    · obtain ⟨hOK, -⟩ := hclosed
      rw [hroot, h1] at hOK
      exact Bool.noConfusion hOK
    · rw [hroot, h1] at hclosed
      exact Bool.noConfusion hclosed
    · rw [hroot, h1] at hclosed
      exact Bool.noConfusion hclosed
  | cons s rest ih =>
    intro T st hroot hclosed henum hprune ρ hpos hfine hchain hadm
    simp only [ChainRealized] at hchain
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hchain
    simp only [DfsSoftAdm] at hadm
    obtain ⟨hsoft, hrec⟩ := hadm
    -- the step's table machinery: the trace stays realized by ρ
    have hc1 : 0 < (st.Aex / s.A : ℚ) := bpos_of_holds (div_pos (hpos st.a) (hpos s.b)) sat1
    have hAex' : 0 < st.Aex := by
      have h1 : st.Aex = (st.Aex / s.A) * s.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    obtain ⟨V1, hadd1, hadd2⟩ := uStep_some_add hAex' hA hB hV
    have hf1 : UFine ρ V1 := uAdd_fine_some hpos hfine sat1 hadd1
    have hfV : UFine ρ V := uAdd_fine_some hpos hf1 sat2 hadd2
    -- the full filters hold for the real step
    have hseam : uStep st.U st.a s.b st.Aex s.A s.B ≠ none := by
      rw [hV]
      exact Option.some_ne_none V
    have hfilt : DfsFilters n st s.b s.A s.B := ⟨hsoft, hseam⟩
    rcases T with ⟨m, ch⟩ | ⟨m⟩ | ⟨m⟩ <;>
      simp only [DfsCert.root] at hroot <;> rw [hroot] at hclosed henum hprune
    · -- internal node: descend through the matching child
      simp only [DfsClosed, DfsEnum, DfsPruneDom] at hclosed henum hprune
      obtain ⟨-, hch⟩ := hclosed
      obtain ⟨hcE, hcEch⟩ := henum
      obtain ⟨c, hcch, hM⟩ := hcE s.b s.A s.B hfilt
      simp only [DfsMatch] at hM
      obtain ⟨V', hV', hchild⟩ := hM
      have hVV : V = V' := Option.some.inj (hV.symm.trans hV')
      rw [← hVV] at hchild
      rcases c with ⟨m2, ch2⟩ | ⟨m2⟩ | ⟨m2⟩ <;> simp only [DfsCert.root] at hchild
      · exact ih (DfsCert.node m2 ch2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
      · exact ih (DfsCert.prune m2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
      · exact ih (DfsCert.deadend m2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
    · -- closure-prune leaf: the leaf's domination kills the chain through it
      simp only [DfsPruneDom] at hprune
      exact hprune ρ hpos hfine (s :: rest) ⟨V, hV, hA, hB, sat1, sat2, hrest⟩
    · -- dead-end leaf: the real step passes the filters, contradicting the dead end
      simp only [DfsEnum] at henum
      exact henum s.b s.A s.B hfilt

#print axioms dfsWalk

/-- The forest form: a real chain from ANY realized opening whose root matches one of the
forest's trees and whose steps are soft-admissible cannot exist. -/
theorem noChain_of_forest (n : Fin 7 → ℤ) (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum n t)
    (hprune : ∀ t ∈ T, DfsPruneDom t)
    (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step)
    (hpos : ∀ k, 0 < ρ k) (_hfine : UFine ρ U0)
    (hchain : ChainRealized ρ U0 a0 Aex0 steps)
    (hadm : ∃ t ∈ T, t.root.a = a0 ∧ t.root.Aex = Aex0 ∧ UFine ρ t.root.U ∧
      DfsSoftAdm n t.root steps) : False := by
  obtain ⟨t, htm, ⟨ha, hAx, hfineR, hadmR⟩⟩ := hadm
  have hchain' : ChainRealized ρ t.root.U a0 Aex0 steps :=
    chainRealized_tableMono hpos steps U0 a0 Aex0 hchain t.root.U hfineR
  rw [← ha, ← hAx] at hchain'
  exact dfsWalk n steps t t.root rfl (hclosed t htm) (henum t htm) (hprune t htm) ρ hpos
    hfineR hchain' hadmR

#print axioms noChain_of_forest

/-- **The DFS-soundness theorem (box form).**  A closed, enumerating, prune-dominated
certificate forest with the root-admissibility closure kills the box: NO real W₀ chain
exists — the exact `Fresh.MechDataBatch.M4CertSound` conclusion. -/
theorem m4CertSound_of_forest (n : Fin 7 → ℤ) (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum n t)
    (hprune : ∀ t ∈ T, DfsPruneDom t) (hcadm : DfsRootAdm n T) : M4CertSound n :=
  fun ρ U0 a0 Aex0 steps hpos hfine hchain =>
    noChain_of_forest n T hclosed henum hprune ρ U0 a0 Aex0 steps hpos hfine hchain
      (hcadm ρ U0 a0 Aex0 steps hpos hfine hchain)

#print axioms m4CertSound_of_forest

/-! ## 5. The compositions (clear point per arrangement; substitution for the C3 kill) -/

/-- **Substitution for the C3 kill.**  An M4 certificate implies the exact chain-exclusion
conclusion `Fresh.UClosure.kill_sound` delivers (no seeded envelope chain of length ≤ T) —
so wherever `kill_sound`'s conclusion is consumed (e.g. inside `boxAdmit_of_kill`'s proof
shape), the M4 certificate substitutes for the fixpoint kill. -/
theorem killExcl_of_m4cert {n : Fin 7 → ℤ} (hcert : M4CertSound n)
    (seed : Fresh.UClosure.Fixpoint) (T : ℕ) :
    ¬ ∃ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) ∧ UFine ρ U0 ∧ ChainRealized ρ U0 a0 Aex0 steps ∧
      Fresh.UClosure.EnvChain a0 Aex0 steps ∧ steps.length ≤ T ∧
      (∃ c0 : Fin 15, Aex0 = Fresh.UClosure.envB c0 ∧
        Fresh.UClosure.keyOf a0 c0 ∈ seed.states) :=
  fun ⟨ρ, U0, a0, Aex0, steps, hpos, hfine, hchain, _, _, _⟩ =>
  hcert ρ U0 a0 Aex0 steps hpos hfine hchain

#print axioms killExcl_of_m4cert

/-- **The box theorem (M4 form of `boxAdmit_of_kill`).**  For a box in the killing-bound
census envelope whose DFS certificate forest killed (this file's engine), every arrangement
in the box admits a clear point `R₀ ∈ [1,7]` — link 1 (`E810ChainCover`) supplies the chain
from the no-clear-point assumption, the M4 certificate excludes it. -/
theorem boxAdmit_of_m4cert (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17)
    (hE810 : Fresh.UClosure.E810ChainCover n hn17) (hcert : M4CertSound n)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨ρ, U0, a0, Aex0, steps, hpos, hfine0, hchain, henv, hlen⟩ := hE810 g hface hnoc
  exact hcert ρ U0 a0 Aex0 steps hpos hfine0 hchain

#print axioms boxAdmit_of_m4cert

/-! ## 6. The data connection (the banked `m4resData_<box>` consumed) -/

/-- The box's census tuple as the face function `Fin 7 → ℤ` (leading entry = the base row). -/
def boxN (r : M4Res) : Fin 7 → ℤ := fun i => ((r.box.getD i.val 0 : ℕ) : ℤ)

/-- **The M4 leaf-key bridge (data side).**  Every distinct leaf key `(rank, exit-numerator)`
of a data-valid residual tree embeds in the 90-type key space of the C3 fixpoint: the rank
index `b` with `b.val + 2 = rank`, the exit numerator `envB c`, and the fixpoint key
`keyOf (rowOf b) c = (b, c)` — the M4 leaf certificates and the C3 merge classes key the
same closed comb envelope (`Fresh.MechDataBatch.leafKey_in_env90` + `keyOf`/`rowOf`). -/
theorem leafKeys_env90 (r : M4Res) (hdata : M4ResData r) :
    ∀ k ∈ r.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
      Fresh.UClosure.envB c = (k.2 : ℚ) ∧
      Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) := by
  intro k hk
  obtain ⟨-, -, -, -, -, -, -, -, -, hlz, -⟩ := hdata
  have h1 : InLeafEnvB k = true := List.all_eq_true.mp hlz k hk
  obtain ⟨b, c, hb, hc⟩ := leafKey_in_env90 (InLeafEnvB_of k |>.mp h1)
  refine ⟨b, c, hb, hc, ?_⟩
  have hkey : Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) := by
    unfold Fresh.UClosure.keyOf Fresh.UClosure.rowOf
    congr 1
  exact hkey

#print axioms leafKeys_env90

/-- **The data-facing soundness theorem.**  The banked record's validity (`M4ResData r`) plus
the per-box domination certificate (the closed, enumerating, prune-dominated forest with the
root-admissibility closure) deliver TOGETHER: the box kills (`M4CertSound (boxN r)`) AND
every distinct leaf key embeds in the C3 90-type key space (the composed-kill bridge: the
M4-fired residual boxes and the aA-killed boxes key the same envelope). -/
theorem m4CertSound_of_data (r : M4Res) (hdata : M4ResData r)
    (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum (boxN r) t)
    (hprune : ∀ t ∈ T, DfsPruneDom t) (hcadm : DfsRootAdm (boxN r) T) :
    M4CertSound (boxN r) ∧
      ∀ k ∈ r.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  ⟨m4CertSound_of_forest _ T hclosed henum hprune hcadm, leafKeys_env90 r hdata⟩

#print axioms m4CertSound_of_data

/-- **The M4 admission consumption (data form).**  The banked record + the domination
certificate + link 5 (`Fresh.UClosure.ChainlessClear`) give every arrangement in the box a
clear point `R₀ ∈ [1,7]` — through `Fresh.MechDataBatch.m4boxClear_of_cert`. -/
theorem m4boxClear_of_data (r : M4Res) (hn17 : ∀ i, boxN r i ≤ 17)
    (hcc : Fresh.UClosure.ChainlessClear (boxN r) hn17)
    (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum (boxN r) t)
    (hprune : ∀ t ∈ T, DfsPruneDom t) (hcadm : DfsRootAdm (boxN r) T)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN r) i ≤ g i ∧ g i ≤ FaceHi (boxN r) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_cert hn17 hcc
    (m4CertSound_of_forest (boxN r) T hclosed henum hprune hcadm) g hface

#print axioms m4boxClear_of_data

/-! ## 7. The banked instance (box (1, 4, 6, 7, 10, 16, 16), the biggest residual tree) -/

/-- **OWED — the per-box domination certificate** for box (1, 4, 6, 7, 10, 16, 16): the
checkpoint tree of `m4comp_cert_ckpt_v1.jsonl` (nodes=51748, leaves=15622, maxdepth=30,
3 start zones; leaf kinds 2137 reach + 13485 dead-end + 0 start-infeasible), transcribed as
a `DfsCert` forest with its census properties: closed (no node's completion check fired),
child-filter complete (every filter-passing step expanded; every dead-end verified),
per-prune-leaf domination (the `reach_utc` verdicts), and the root-admissibility closure.
Discharge: OWED (a)+(b)+(c) of the header. -/
-- STANDING: OWED
def DfsCert_1_4_6_7_10_16_16 (T : List DfsCert) : Prop :=
  (∀ t ∈ T, DfsClosed t) ∧ (∀ t ∈ T, DfsEnum (boxN m4res_1_4_6_7_10_16_16) t) ∧
    (∀ t ∈ T, DfsPruneDom t) ∧ DfsRootAdm (boxN m4res_1_4_6_7_10_16_16) T

/-- The census envelope of the banked box tuple (all seven entries ≤ 17), discharged from
the record itself. -/
theorem hn17_1_4_6_7_10_16_16 : ∀ i : Fin 7, boxN m4res_1_4_6_7_10_16_16 i ≤ 17 := by
  intro i
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
    i.val = 6 := by
    have := i.isLt
    omega
  rcases hv with h | h | h | h | h | h | h
  · have e : i = ⟨0, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨1, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨2, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨3, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨4, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨5, by decide⟩ := Fin.ext h; subst e; decide
  · have e : i = ⟨6, by decide⟩ := Fin.ext h; subst e; decide

#print axioms hn17_1_4_6_7_10_16_16

/-- **The banked instance.**  `m4resData_1_4_6_7_10_16_16` [T 2329/2329] + the per-box
domination certificate deliver: the box (1, 4, 6, 7, 10, 16, 16) kills (no real W₀ chain in
the `ChainRealized` form from any realized opening) AND its 18 distinct leaf keys embed in
the C3 90-type key space. -/
theorem m4cert_1_4_6_7_10_16_16 (T : List DfsCert) (hcert : DfsCert_1_4_6_7_10_16_16 T) :
    M4CertSound (boxN m4res_1_4_6_7_10_16_16) ∧
      ∀ k ∈ m4res_1_4_6_7_10_16_16.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧
        Fresh.UClosure.envB c = (k.2 : ℚ) ∧
        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=
  m4CertSound_of_data m4res_1_4_6_7_10_16_16 m4resData_1_4_6_7_10_16_16 T
    hcert.1 hcert.2.1 hcert.2.2.1 hcert.2.2.2

#print axioms m4cert_1_4_6_7_10_16_16

/-- **The banked admission instance.**  The record + the domination certificate + link 5
(`ChainlessClear`, hypothesis) give every arrangement in the box a clear point `R₀ ∈ [1,7]`. -/
theorem m4boxClear_1_4_6_7_10_16_16 (T : List DfsCert) (hcert : DfsCert_1_4_6_7_10_16_16 T)
    (hcc : Fresh.UClosure.ChainlessClear (boxN m4res_1_4_6_7_10_16_16) hn17_1_4_6_7_10_16_16)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo (boxN m4res_1_4_6_7_10_16_16) i ≤ g i ∧
      g i ≤ FaceHi (boxN m4res_1_4_6_7_10_16_16) i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  m4boxClear_of_data m4res_1_4_6_7_10_16_16 hn17_1_4_6_7_10_16_16 hcc T
    hcert.1 hcert.2.1 hcert.2.2.1 hcert.2.2.2 g hface

#print axioms m4boxClear_1_4_6_7_10_16_16

end Fresh.M4Cert
