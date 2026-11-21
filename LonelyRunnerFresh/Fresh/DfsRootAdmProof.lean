import Fresh.M4CertSound
import Fresh.SelectRung1Data

/-!
# DfsRootAdmProof: the forced-opening lemma for box b1 and the `DfsRootAdm` reduction

New file (2026-11-21); nothing existing is edited.

## What is forced and what is owed

`Fresh.M4CertSound.DfsRootAdm` (OWED (a) of its header) is the E810 side of the DFS child
filter completeness: every real chain's opening matches a tree root whose table it realizes,
and the chain's steps pass the soft filters along the induced path.  This file isolates the
two halves of that OWED and discharges the cover half as far as the banked data supports,
for the select-rung box `b1 = ![1, 3, 4, 5, 5, 5, 7]`.

**The def-forced shape of a first step.**  `ChainRealized`'s def carries two strict seam
bounds per step, `BHolds true (ρ a / ρ st.b) (Aex / st.A)` and
`BHolds true (ρ st.b / ρ a) (st.B / Aex)`, with `BHolds true x c := x < c`; `Step.A` is the
entry edge `8j−1` and `Step.B` the exit edge `8j+1`.  For the pinned window start
`(a₀, Aex₀) = (0, 1)` with `g 0 = 1` the seams force, for the FIRST step,
`zEntry j < g i < zExit j`: the first zone straddles `R = 1` with the reading `g i`
strictly inside the open tooth `(8j−1, 8j+1)`.  In b1's faces only row 6 can exceed 7
(`FaceHi` caps rows 0..5 at `11/2`, row 6 at `15/2`), and `8j−1 < 15/2` with `j ≥ 1` forces
`j = 1`.  So ANY envelope first step of a realized pinned chain in b1 is
`⟨6, zEntry 1, zExit 1⟩` — the tooth `(6, 1)`.

1. **Forced opening (proved):** `b1_forced_tooth` (tooth-level classification, no chain
   hypothesis), `forced_opening_b1` (classification of the first step of a realized pinned
   chain), `forced_opening_b1_extract` (the def-forced extraction for the pinned literal
   first step: surviving step equation, realized continuation, `7 < g 6 < 9`).
2. **Root membership (reduced to one root record):** `b1ForcedRoots` is the literal
   singleton `[(6, 1)]`, exactly the forced-openings set (`b1ForcedRoots_iff` +
   `b1_forced_key_feasible`).  No `M4CertRung2` transcription exists for box
   `(1, 3, 4, 5, 5, 5, 7)` (the rung-2 files cover other boxes; rung 1's forest is box
   `(1, 4, 6, 7, 10, 16, 16)` with only its crown subtree transcribed), so membership is
   stated as the cover condition it will consume: `b1_cover_singleton` shows one tree
   rooted at `(row 6, exit numerator zExit 1 = 9)` covers the forced-opening half.  The
   opening is ACHIEVED (`b1_forced_opening_achieved`): the banked counterexample walk
   `walk19` of `Fresh.SelectRung1Data` opens with exactly this tooth and is realized at
   the exact in-box arrangement `g19` — the root record is not vacuous.
3. **Soft-filter half (STANDING: OWED, made precise).**  `DfsSoft n st b A B =
   dfsZone n st.U b A B ∧ (A:ℝ)/dfsHi n st.U b < st.P ∧ (b, B) ∉ st.seen` is NOT implied by
   `ChainRealized`'s strict seams alone.  What IS implied is banked:
   `chainStep_strictIncrease` — the upper seam forces the window position `Aex/ρ a` to
   strictly increase past the tooth exit `B/ρ b`, so a realized chain never REPEATS a tooth
   it consumed (the seed of zone freshness).  The residual datum of OWED (a) is precisely
   three conjuncts the seams do not carry: (i) the envelope form of the steps with the
   `dfsZone` loop-break bound `A/dfsHi < 7` (the E810 covering-chain form, the same status
   as `EnvChain`'s envelope conditions), (ii) entry below the frontier sup `A/dfsHi < st.P`
   (the strict-monotone E810 reading), and (iii) the root's banked `seen` set avoiding the
   chain's steps (start-zone-enumeration bookkeeping; the path-added zones are covered by
   the strict increase).
4. **Unrestricted-quantifier caveat (proved):** `chainRealized_nil_of_gt7` — for every
   rational `Aex₀ > 7` the empty chain at row 0 is realized, so `DfsRootAdm`'s cover half
   cannot collapse to the forced openings alone; the reduction `dfsRootAdm_of_cover_soft`
   keeps the halves separate so neither is silently over-claimed.

All arithmetic exact; every theorem carries `#print axioms`; accepted profile is the
standard three (`propext`, `Classical.choice`, `Quot.sound`) — `sorryAx` is failure.
-/

namespace Fresh.M4Cert

open Fresh FilterAssembly UClosure
open Fresh.SelectRung1Data Fresh.ChainDomPerRec8

/-! ## 0. General seam arithmetic (no box data) -/

/-- **Strict position increase from the upper seam (general, box-free).**  A realized
step's upper seam `ρ b / ρ a < B / Aex` says exactly that consuming the step moves the
window position from `Aex / ρ a` strictly past the tooth exit `B / ρ b`.  So a realized
chain's position strictly increases at every step, and no tooth `(b, B)` can be consumed
twice: after the first consumption the position already equals `B / ρ b`. -/
theorem chainStep_strictIncrease {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) {U : UTable}
    {a b : Fin 7} {Aex : ℚ} (hAex : 0 < Aex) {A B : ℚ}
    (hsat2 : BHolds true (ρ b / ρ a) (B / Aex)) :
    (Aex : ℝ) / ρ a < (B : ℝ) / ρ b := by
  simp only [BHolds, Rat.cast_div, Rat.cast_ofNat] at hsat2
  rw [div_lt_div_iff₀ (hpos a) (hpos b)]
  rw [div_lt_div_iff₀ (hpos a) (Rat.cast_pos.mpr hAex)] at hsat2
  rw [mul_comm (Aex : ℝ) (ρ b)]
  exact hsat2

/-- **The trivial-empty-chain datum.**  For any positive `ρ` and ANY exit numerator past 7,
the empty chain at row 0 is realized: `ChainRealized ρ U0 0 Aex0 []` unfolds to
`1 < Aex0 / 7`.  Consequently the unrestricted start quantifier of `DfsRootAdm` demands,
for each rational `Aex₀ > 7`, a root `(a = 0, Aex = Aex₀)` — the cover half of OWED (a)
cannot collapse to the forced openings alone. -/
theorem chainRealized_nil_of_gt7 {ρ : Fin 7 → ℝ} (hpos : 0 < ρ 0) (U0 : UTable) (Aex0 : ℚ)
    (h7 : (7 : ℚ) < Aex0) : ChainRealized ρ U0 0 Aex0 [] := by
  show BHolds true (ρ 0 / ρ 0) (Aex0 / 7)
  simp only [BHolds, Rat.cast_div, Rat.cast_ofNat, div_self (ne_of_gt hpos)]
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)]
  exact_mod_cast h7

/-! ## 1. The b1 face caps (literal arithmetic) -/

/-- The face caps of box b1: row 6 is the only reading whose face interval can reach above
`11/2` (rows 0..5 are capped at `11/2`; row 6 at `15/2`). -/
theorem b1_faceHi_caps :
    ∀ k : Fin 7, k = 6 ∨ (FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k : ℝ) ≤ (11 / 2 : ℝ) := by
  intro k
  fin_cases k
  · right; simp [FaceHi] <;> norm_num
  · right; simp [FaceHi] <;> norm_num
  · right; simp [FaceHi] <;> norm_num
  · right; simp [FaceHi] <;> norm_num
  · right; simp [FaceHi] <;> norm_num
  · right; simp [FaceHi] <;> norm_num
  · left; rfl

theorem b1_faceHi_6 :
    (FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) 6 : ℝ) = (15 / 2 : ℝ) := by
  simp [FaceHi]

theorem b1_faceLo_6 :
    (FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) 6 : ℝ) = (13 / 2 : ℝ) := by
  simp [FaceLo]

/-! ## 2. The forced opening of box b1 -/

/-- The tooth entry edge in ℚ (valid for all `j`, including `j = 0` where it is `-1`).
All tooth arithmetic below is done in ℚ over this form: `linarith` over ℝ does not fold
`Nat.cast` numerals into constants, so ℕ-cast atoms are avoided. -/
theorem zEntry_q (j : Fin 16) : (zEntry j : ℚ) = (8 : ℚ) * (j.val : ℚ) - 1 := by
  have h1 : zEntry j = (zExit j : ℚ) - 2 := rfl
  have h2 : (zExit j : ℚ) = ((8 * j.val + 1 : ℕ) : ℚ) := rfl
  rw [h1, h2]
  push_cast
  ring

/-- **The forced opening of box b1 (tooth-level, no chain hypothesis).**  The only tooth
`(i, j)` with `j ≥ 1` whose open window `(8j−1, 8j+1)` can meet a face interval of b1 —
i.e. `8j−1 < FaceHi b1 i` and `FaceLo b1 i < 8j+1` — is the tooth `(6, 1)`: rows 0..5 are
face-capped at `11/2 < 7 ≤ 8j−1`, and `8j−1 < 15/2` forces `j = 1`.  This is the
forced-openings set of OWED (a), b1 instance.  (`hlo'` states the full filter shape; the
forcing itself only needs the entry side plus `j ≥ 1`.) -/
theorem b1_forced_tooth {i : Fin 7} {j : Fin 16} (hj : 0 < j.val)
    (hlo' : (FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i : ℝ) < (zExit j : ℝ))
    (hhi' : (zEntry j : ℝ) < (FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i : ℝ)) :
    i = 6 ∧ j = 1 := by
  rcases b1_faceHi_caps i with heq | hc5
  · subst heq
    rw [b1_faceHi_6] at hhi'
    -- hhi' : (zEntry j : ℝ) < 15/2; bridge to ℚ and force j = 1
    have h2 : ((15 / 2 : ℚ) : ℝ) = (15 / 2 : ℝ) := by norm_num
    rw [← h2] at hhi'
    have hq : (zEntry j : ℚ) < (15 / 2 : ℚ) := Rat.cast_lt.mp hhi'
    have hzq : (zEntry j : ℚ) = (8 : ℚ) * (j.val : ℚ) - 1 := zEntry_q j
    rw [hzq] at hq
    have hjlt : (j.val : ℚ) < 2 := by linarith
    have hjn : j.val < 2 := by exact_mod_cast hjlt
    have hj1 : j.val = 1 := by omega
    exact ⟨rfl, Fin.ext hj1⟩
  · exfalso
    -- 7 ≤ zEntry j < FaceHi i ≤ 11/2 in ℝ (the 7-bound carried at ℚ and folded up)
    have h7q : (7 : ℚ) ≤ (zEntry j : ℚ) := by
      have hzq : (zEntry j : ℚ) = (8 : ℚ) * (j.val : ℚ) - 1 := zEntry_q j
      rw [hzq]
      have hjn1 : (1 : ℕ) ≤ j.val := by omega
      have hjq : (1 : ℚ) ≤ (j.val : ℚ) := by exact_mod_cast hjn1
      linarith
    have h7r : ((7 : ℚ) : ℝ) ≤ (zEntry j : ℝ) := Rat.cast_le.mpr h7q
    have h7c : ((7 : ℚ) : ℝ) = (7 : ℝ) := by norm_num
    rw [h7c] at h7r
    linarith [h7r, hhi', hc5]

/-- **The forced opening of box b1 (chain-level).**  ANY envelope first step `⟨i, zEntry j,
zExit j⟩` of a `ChainRealized` chain from the pinned window start `(a₀, Aex₀) = (0, 1)` in
b1 — rows in the faces, `g 0 = 1` — is the tooth `(6, 1)`: the two strict seams force
`zEntry j < g i < zExit j` (the first zone straddles `R = 1` with `g i` strictly inside the
tooth), `j = 0` is excluded because the exit edge `1` cannot exceed the face floor
`FaceLo ≥ 1`, and `b1_forced_tooth` finishes.  (`hord` is carried for the downstream
composition with the closure-start strict orderings; it is not needed for the forcing
itself.) -/
theorem forced_opening_b1 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hord : g 1 < g 2 ∧ g 2 < g 3 ∧ g 3 < g 4 ∧ g 4 < g 5 ∧ g 5 < g 6)
    (hpin : g 0 = 1)
    {U : UTable} {rest : List Step} {i : Fin 7} {j : Fin 16}
    (hcr : ChainRealized g U 0 1 (⟨i, zEntry j, zExit j⟩ :: rest)) :
    i = 6 ∧ j = 1 := by
  have hlo (k : Fin 7) : (1 : ℝ) ≤ g k :=
    (faceLo_ge_one (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k).trans (hface k).1
  have hpos (k : Fin 7) : (0 : ℝ) < g k := lt_of_lt_of_le zero_lt_one (hlo k)
  simp only [ChainRealized] at hcr
  obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
  -- the two strict seams, multiplied out to the tooth window
  have s1 := sat1
  simp only [BHolds] at s1
  rw [Rat.cast_div, Rat.cast_one, hpin,
    div_lt_div_iff₀ (hpos i) (Rat.cast_pos.mpr hA)] at s1
  have hentry : (zEntry j : ℝ) < g i := by simpa using s1
  have s2 := sat2
  simp only [BHolds] at s2
  rw [Rat.cast_div, Rat.cast_one, hpin] at s2
  have hexit : g i < (zExit j : ℝ) := by simpa using s2
  -- `j = 0` is excluded: the exit edge of tooth 0 is `1`, below every face floor
  have hj0 : 0 < j.val := by
    by_contra hc
    have hj0' : j = 0 := Fin.ext (by omega)
    subst hj0'
    rw [zExit_real] at hexit
    norm_num at hexit
    linarith [hexit, hlo i]
  exact b1_forced_tooth hj0 (lt_of_le_of_lt (hface i).1 hexit)
    (lt_of_lt_of_le hentry (hface i).2)

/-- **The pinned extraction (the def-forced shape at the forced tooth).**  For a realized
chain whose first step is the forced opening `⟨6, zEntry 1, zExit 1⟩`, `ChainRealized`'s
def forces: the step equation survives on the chain's own table (`uStep = some V`), the
continuation is realized from the new state `(6, zExit 1)`, and the seams pin the reading
into the tooth: `7 < g 6 < 9`. -/
theorem forced_opening_b1_extract {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hord : g 1 < g 2 ∧ g 2 < g 3 ∧ g 3 < g 4 ∧ g 4 < g 5 ∧ g 5 < g 6)
    (hpin : g 0 = 1)
    {U : UTable} {rest : List Step}
    (hcr : ChainRealized g U 0 1 (⟨(6 : Fin 7), zEntry 1, zExit 1⟩ :: rest)) :
    ∃ V : UTable,
      uStep U 0 6 1 (zEntry 1) (zExit 1) = some V ∧
      ChainRealized g V 6 (zExit 1) rest ∧
      ((7 : ℝ) < g 6 ∧ g 6 < 9) := by
  have hpos (k : Fin 7) : (0 : ℝ) < g k :=
    lt_of_lt_of_le zero_lt_one
      ((faceLo_ge_one (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k).trans (hface k).1)
  simp only [ChainRealized] at hcr
  obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
  refine ⟨V, hV, hrest, ?_, ?_⟩
  · -- lower seam: `g 0 / g 6 < 1/7` with `g 0 = 1` gives `7 < g 6`
    have s1 := sat1
    simp only [BHolds] at s1
    rw [Rat.cast_div, Rat.cast_one, hpin,
      div_lt_div_iff₀ (hpos 6) (Rat.cast_pos.mpr hA)] at s1
    have hze : ((zEntry 1 : ℚ) : ℝ) = (7 : ℝ) := by simp [zEntry, zExit] <;> norm_num
    rw [hze] at s1
    simpa using s1
  · -- upper seam: `g 6 / g 0 < 9` gives `g 6 < 9`
    have s2 := sat2
    simp only [BHolds] at s2
    rw [Rat.cast_div, Rat.cast_one, hpin] at s2
    have hze : ((zExit 1 : ℚ) : ℝ) = (9 : ℝ) := by simp [zExit, zEntry] <;> norm_num
    rw [hze] at s2
    simpa using s2

/-! ## 3. Root membership: the forced-openings set is the singleton `(6, 1)` -/

/-- The forced-openings root list of box b1, as the literal extracted from
`b1_forced_tooth`: the singleton tooth class (row 6, tooth 1 — exit numerator
`zExit 1 = 9`). -/
def b1ForcedRoots : List (Fin 7 × Fin 16) := [((6 : Fin 7), (1 : Fin 16))]

theorem b1ForcedRoots_iff (i : Fin 7) (j : Fin 16) :
    (i, j) ∈ b1ForcedRoots ↔ i = 6 ∧ j.val = 1 := by
  unfold b1ForcedRoots
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, hj1⟩
    exact ⟨rfl, Fin.ext hj1⟩

theorem mem_b1ForcedRoots : ((6 : Fin 7), (1 : Fin 16)) ∈ b1ForcedRoots := by
  simp [b1ForcedRoots]

/-- The key tooth satisfies the forced-opening filter: the set is nonempty, not vacuous
(the zone `(7, 9)` really does meet row 6's face interval `[13/2, 15/2]`). -/
theorem b1_forced_key_feasible :
    ((zEntry 1 : ℝ) < (FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) 6 : ℝ)) ∧
      ((FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) 6 : ℝ) < (zExit 1 : ℝ)) := by
  rw [b1_faceHi_6, b1_faceLo_6]
  have h7 : ((zEntry 1 : ℚ) : ℝ) = (7 : ℝ) := by simp [zEntry, zExit] <;> norm_num
  have h9 : ((zExit 1 : ℚ) : ℝ) = (9 : ℝ) := by simp [zExit, zEntry] <;> norm_num
  rw [h7, h9]
  norm_num

/-- **The forced opening of b1 is ACHIEVED (non-vacuous).**  The banked counterexample walk
`walk19` of `Fresh.SelectRung1Data` — realized at the exact in-box arrangement `g19` by
`walk19_realized` — opens with exactly the tooth `(6, 1)`. -/
theorem b1_forced_opening_achieved :
    ChainRealized g19 mkTab_1_3_4_5_5_5_7 0 1
      (⟨(6 : Fin 7), zEntry 1, zExit 1⟩ :: walk19.tail) :=
  walk19_realized

/-- **Root membership, b1 (the cover half of OWED (a), collapsed to one record).**  Every
envelope first step of a realized pinned chain in b1 is the tooth `(6, 1)`
(`forced_opening_b1`), so a forest containing a tree rooted at `(row 6, exit numerator
zExit 1)` covers the forced-opening half: for each realized pinned chain the matching root
exists.  The remaining data-side OWED for box b1 is exactly this record — the b1 DFS
enumerated the start zone `(6, zExit 1)` — plus the soft half below. -/
theorem b1_cover_singleton {g : Fin 7 → ℝ} {T : List DfsCert} {U0 : UTable}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) i)
    (hord : g 1 < g 2 ∧ g 2 < g 3 ∧ g 3 < g 4 ∧ g 4 < g 5 ∧ g 5 < g 6)
    (hpin : g 0 = 1)
    (t0 : DfsCert) (ht0 : t0 ∈ T)
    (hroot : t0.root.a = 6 ∧ t0.root.Aex = zExit 1)
    {rest : List Step} {i : Fin 7} {j : Fin 16}
    (hcr : ChainRealized g U0 0 1 (⟨i, zEntry j, zExit j⟩ :: rest)) :
    ∃ t ∈ T, t.root.a = i ∧ t.root.Aex = zExit j := by
  obtain ⟨rfl, rfl⟩ := forced_opening_b1 hface hord hpin hcr
  exact ⟨t0, ht0, hroot.1, hroot.2⟩

/-! ## 4. The general reduction of `DfsRootAdm` to the two halves -/

/-- **The general reduction of OWED (a) to two precise halves** (the def, unfolded
honestly): `DfsRootAdm n T` is exactly (cover: every realized start has a root with
matching row/exit and a table the readings realize) ∧ (soft: every covered chain's steps
pass the soft filters along the induced path).  The soft half is the STANDING OWED; its
residual datum is documented at `DfsSoft` precision in the module header — the envelope
form with the `dfsZone` loop-break bound, entry below the frontier sup, and the root's
`seen` set avoiding the chain's steps; none is implied by the strict seams alone (the
implied part, strict position increase, is banked as `chainStep_strictIncrease`).  Note
also `chainRealized_nil_of_gt7`: the cover half must additionally reach the trivial exits
`(0, Aex₀)` for every `Aex₀ > 7`, so it cannot collapse to the forced openings alone —
`firstWindow_of_pinned_forest` does not need it (its `hadmit` covers pinned-window
continuations only), and the pinned-scope shape is `b1_pinned_cover_of_single` below. -/
theorem dfsRootAdm_of_cover_soft {n : Fin 7 → ℤ} {T : List DfsCert}
    (hcover : ∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) → UFine ρ U0 → ChainRealized ρ U0 a0 Aex0 steps →
      ∃ t ∈ T, t.root.a = a0 ∧ t.root.Aex = Aex0 ∧ UFine ρ t.root.U)
    (hsoft : ∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step)
      (t : DfsCert), (∀ k, 0 < ρ k) → UFine ρ U0 →
      ChainRealized ρ U0 a0 Aex0 steps → t ∈ T →
      t.root.a = a0 → t.root.Aex = Aex0 → UFine ρ t.root.U →
      DfsSoftAdm n t.root steps) :
    DfsRootAdm n T := by
  intro ρ U0 a0 Aex0 steps hpos hfine hcr
  obtain ⟨t, ht, ha, hAex, hf⟩ := hcover ρ U0 a0 Aex0 steps hpos hfine hcr
  exact ⟨t, ht, ha, hAex, hf, hsoft ρ U0 a0 Aex0 steps t hpos hfine hcr ht ha hAex hf⟩

/-- **The pinned OWED (a) shape for box b1 in one statement**: the single root record
`(6, zExit 1)` + the root's table realized by the arrangement + the soft half along covered
pinned chains ⟹ the pinned chain's continuation is covered with a realized table and
soft-admissible steps — the datum `firstWindow_of_pinned_forest`'s `hadmit` consumes for
the opening `(6, 1)` (its other openings are vacuous here: `forced_opening_b1` forces the
first step).  `hfroot` is the "whose table it realizes" half of OWED (a): the root record's
table is realized by the readings — a per-root, per-arrangement datum, discharged from the
root transcription (`chainRealized_tableMono` re-bases the chain onto it inside
`noChain_of_forest`). -/
theorem b1_pinned_cover_of_single {T : List DfsCert}
    (t0 : DfsCert) (ht0 : t0 ∈ T)
    (hroot : t0.root.a = 6 ∧ t0.root.Aex = zExit 1)
    (hsoft : ∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (rest : List Step) (t : DfsCert),
      (∀ k, 0 < ρ k) →
      (∀ k, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k ≤ ρ k ∧
        ρ k ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k) →
      ρ 0 = 1 → UFine ρ U0 →
      ChainRealized ρ U0 0 1 (⟨(6 : Fin 7), zEntry 1, zExit 1⟩ :: rest) → t ∈ T →
      t.root.a = 6 → t.root.Aex = zExit 1 → UFine ρ t.root.U →
      DfsSoftAdm (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) t.root rest)
    (ρ : Fin 7 → ℝ) (U0 : UTable) (rest : List Step)
    (hpos : ∀ k, 0 < ρ k)
    (hface : ∀ k, FaceLo (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k ≤ ρ k ∧
      ρ k ≤ FaceHi (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) k)
    (hpin : ρ 0 = 1) (hfine : UFine ρ U0)
    (hfroot : UFine ρ t0.root.U)
    (hcr : ChainRealized ρ U0 0 1 (⟨(6 : Fin 7), zEntry 1, zExit 1⟩ :: rest)) :
    ∃ t ∈ T, t.root.a = 6 ∧ t.root.Aex = zExit 1 ∧ UFine ρ t.root.U ∧
      DfsSoftAdm (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) t.root rest :=
  ⟨t0, ht0, hroot.1, hroot.2, hfroot,
    hsoft ρ U0 rest t0 hpos hface hpin hfine hcr ht0 hroot.1 hroot.2 hfroot⟩

#print axioms chainStep_strictIncrease
#print axioms chainRealized_nil_of_gt7
#print axioms b1_faceHi_caps
#print axioms b1_faceHi_6
#print axioms b1_faceLo_6
#print axioms b1_forced_tooth
#print axioms forced_opening_b1
#print axioms forced_opening_b1_extract
#print axioms b1ForcedRoots_iff
#print axioms mem_b1ForcedRoots
#print axioms b1_forced_key_feasible
#print axioms b1_forced_opening_achieved
#print axioms b1_cover_singleton
#print axioms dfsRootAdm_of_cover_soft
#print axioms b1_pinned_cover_of_single

end Fresh.M4Cert
