import Fresh.DfsRootAdmProof
import Fresh.M4CertRung1

/-!
# DfsSoftProof: the soft half of `DfsRootAdm` — three conjuncts, composition, worked cases

New file (2026-11-21); nothing existing is edited.

## What is discharged and what is owed

`Fresh.M4CertSound.DfsSoft n st b A B =
  dfsZone n st.U b A B ∧ (A:ℝ)/dfsHi n st.U b < st.P ∧ (b, B) ∉ st.seen`
decomposes into the three conjuncts of OWED (a)'s soft half (E901 / the `DfsRootAdmProof`
header): (i) envelope form + loop-break `A/dfsHi < 7`, (ii) entry below the frontier sup
`A/dfsHi < st.P`, (iii) seen-set avoidance.  For a realized chain's steps along the induced
tree path, at the pinned scope (ρ 0 = 1, in-box face bounds, node table realized):

* **(iii) PROVED unconditionally:** `soft_seen_of_chainRealized` — `chainStep_strictIncrease`
  extended to the seen-set form: a realized chain never consumes a tooth already in the
  accumulated list (each accumulated pair's exit position is ≤ the current node's position,
  and the upper seam forces the position to strictly increase past it).
* **(ii) PROVED from one named datum:** `soft_frontier_of_chainRealized` — the frontier
  datum `(st.Aex : ℝ)/ρ st.a ≤ st.P`.  `DfsSoft`'s `st.P` semantics: `childState` banks
  `P = B/dfsLo n (parent U) b` — the PREVIOUS EXIT over the consumed row's tightened lo —
  so for tree-internal nodes the frontier sup IS the previous exit (scaled) and the datum
  is DERIVED (`dfsLo_le_read`); only the tree root's banked `P` is a record datum
  (`crown_root_frontier_of_face` discharges it for the rung-1 crown root from the face
  bounds; `walk19Root`'s is an equality by the childState convention).
* **(i) PROVED from two named data:** `soft_env_of_chainRealized` — the step's tooth form
  `∃ c : Fin 15, s.A = envA c ∧ s.B = envB c` (the `EnvChain` per-step envelope datum, the
  same status as E810's envelope conditions) + the node's window position
  `(st.Aex : ℝ)/ρ st.a < 7` (the E810 covering-chain window datum — the raw seams do NOT
  forbid an intermediate position past 7, so this is genuinely carried, `WinBelow7`).

Composition: `soft_of_chainRealized` — `ChainRealized` + pinned in-box + the three named
data (root seen-avoidance, per-step tooth form, window form, root frontier datum) ⟹
`DfsSoftAdm n st steps`, the per-step soft filters along the induced path.  The induction
maintains every transferable datum along the realized trace: `UFine` via
`uAdd_fine_some`, the frontier datum via `childState` + `dfsLo_le_read` (at every row, no
row-0 side condition), the seen datum via the parent's + no-repeat, the window datum by
`WinBelow7`'s recursion.

Worked cases:
* box b1 = `(1, 3, 4, 5, 5, 5, 7)`: the banked counterexample walk `walk19`
  (`SelectRung1Data.walk19_realized`) at the constructed induced root state `walk19Root`
  (closure-start table, pinned start `(0, 1)`, frontier sup `1/dfsLo = 1`, empty seen):
  `walk19_soft : DfsSoftAdm box1 walk19Root walk19` — all 19 steps × 3 conjuncts checked;
  `walk19_step1_soft` extracts step 1's `DfsSoft` literally.  The path's first child state
  is row 6 exit 9 — exactly the b1 forced-opening root of `DfsRootAdmProof`.
* rung 1's crown root `nodeRoot` (`M4CertRung1`): the root frontier datum discharged from
  the face bounds, and the two banked filter-passing steps' soft conditions as literal
  theorems `crown_c0_soft` / `crown_c1_soft` — exactly the two steps `enumMatch_root`
  matches to children.

Compiler quirks (from `DfsRootAdmProof`'s header, all hit here): tooth arithmetic in ℚ
(ℝ-linarith does not fold Nat.cast numerals); ℚ-literals in ℝ statements rewritten
explicitly before `Rat.cast_lt`; a cast of a ℚ-division must be written
`Rat.cast (x / y)` (an ascription `(x / y : ℝ)` elaborates as ℝ-division instead); and
`DfsSoft`/`dfsZone` must BOTH be unfolded before a `dfsHi` rewrite can fire under the
∃-binder.  All arithmetic exact; every theorem carries `#print axioms`; accepted profile
is the standard three (`propext`, `Classical.choice`, `Quot.sound`) — `sorryAx` is
failure.  The OWED data are named hypotheses, never sorry'd.
-/

namespace Fresh.M4Cert

open Fresh FilterAssembly UClosure
open Fresh.SelectRung1Data Fresh.ChainDomPerRec8 Fresh.MechDataBatch
open Fresh.M4CertRung1

/-! ## 0. The tightened ranges bound the readings at the pinned scope -/

/-- The ℝ-bridge for the census part of `dfsHi` (row ≥ 1 form) and `FaceHi` (note the
`Rat.cast` form: an ascription `(x / 2 : ℝ)` would elaborate as ℝ-division). -/
theorem faceHi_q (n : Fin 7 → ℤ) (b : Fin 7) :
    (FaceHi n b : ℝ) = Rat.cast (((2 * n b + 1 : ℤ) : ℚ) / 2) := by
  norm_num [FaceHi, Rat.cast_div, Rat.cast_intCast]

/-- At the pinned scope, the tightened hi of row `b` bounds the reading `ρ b` from above
(the `dfsZone` entry/loop-break arithmetic works against `dfsHi`). -/
theorem dfsHi_ge_read (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) (ρ : Fin 7 → ℝ)
    (hpos : ∀ k, 0 < ρ k) (hpin : ρ 0 = 1)
    (hface : ∀ i, FaceLo n i ≤ ρ i ∧ ρ i ≤ FaceHi n i) (hn0 : (0 : ℤ) < n 0)
    (hfine : UFine ρ U) : (ρ b : ℝ) ≤ (dfsHi n U b : ℝ) := by
  unfold dfsHi
  by_cases hb : 0 < b.val
  · rw [if_pos hb]
    cases hU : U b 0 with
    | none =>
      simp only [hU]
      rw [← faceHi_q]
      exact (hface b).2
    | some p =>
      obtain ⟨c, s⟩ := p
      simp only [hU]
      have hF : (ρ b : ℝ) ≤ Rat.cast (((2 * n b + 1 : ℤ) : ℚ) / 2) := by
        rw [← faceHi_q]
        exact (hface b).2
      have h2 : (ρ b : ℝ) ≤ (c : ℝ) := by
        have h := bhof_eq_some (hfine b 0) hU
        rw [hpin, div_one] at h
        cases s <;> simp only [BHolds] at h
        · exact h
        · exact le_of_lt h
      rw [Rat.cast_min]
      exact le_min hF h2
  · rw [if_neg hb]
    have hb0 : b = 0 := Fin.ext (by have := b.isLt; omega)
    subst hb0
    have hge : ((3 : ℤ) : ℚ) ≤ ((2 * n 0 + 1 : ℤ) : ℚ) := by
      have h2 : (3 : ℤ) ≤ 2 * n 0 + 1 := by omega
      exact_mod_cast h2
    rw [hpin]
    exact le_trans (by norm_num : (1 : ℝ) ≤ Rat.cast ((3 : ℤ) : ℚ)) (Rat.cast_le.mpr hge)

/-- At the pinned scope, the tightened lo of row `b` is bounded by the reading `ρ b` (the
frontier-sup arithmetic works against `dfsLo`; holds at EVERY row, no row-0 datum). -/
theorem dfsLo_le_read (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) (ρ : Fin 7 → ℝ)
    (hpos : ∀ k, 0 < ρ k) (hpin : ρ 0 = 1)
    (hface : ∀ i, FaceLo n i ≤ ρ i ∧ ρ i ≤ FaceHi n i)
    (hfine : UFine ρ U) : (dfsLo n U b : ℝ) ≤ (ρ b : ℝ) := by
  have hc2 : Rat.cast (((2 * n b - 1 : ℤ) : ℚ) / 2) ≤ (ρ b : ℝ) := by
    have hc : Rat.cast (((2 * n b - 1 : ℤ) : ℚ) / 2) ≤ FaceLo n b := by
      have hcast : Rat.cast (((2 * n b - 1 : ℤ) : ℚ) / 2) = ((2 * n b - 1 : ℤ) : ℝ) / 2 := by
        rw [Rat.cast_div, Rat.cast_intCast]
        norm_num
      rw [hcast]
      simp only [FaceLo, Int.cast_max]
      exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
    exact hc.trans (hface b).1
  have h1 : (1 : ℝ) ≤ (ρ b : ℝ) := (faceLo_ge_one n b).trans (hface b).1
  unfold dfsLo
  by_cases hb : 0 < b.val
  · rw [if_pos hb]
    cases hU : U 0 b with
    | none =>
      show Rat.cast (max (((2 * n b - 1 : ℤ) : ℚ) / 2) 1) ≤ (ρ b : ℝ)
      rw [Rat.cast_max, Rat.cast_one]
      exact max_le hc2 h1
    | some p =>
      obtain ⟨c, s⟩ := p
      show Rat.cast (max (max (((2 * n b - 1 : ℤ) : ℚ) / 2) 1) (1 / c)) ≤ (ρ b : ℝ)
      rw [Rat.cast_max, Rat.cast_max, Rat.cast_one]
      refine max_le (max_le hc2 h1) ?_
      have h := bhof_eq_some (hfine 0 b) hU
      have hcpos : (0 : ℝ) < (c : ℝ) := by
        exact_mod_cast bpos_of_holds (div_pos (hpos 0) (hpos b)) h
      rw [hpin] at h
      cases s <;> simp only [BHolds] at h
      · rw [show Rat.cast (1 / c) = (1 : ℝ) / (c : ℝ) from by rw [Rat.cast_div, Rat.cast_one]]
        exact (div_le_iff₀ hcpos).mpr (by
          have h2 : (1 : ℝ) ≤ ρ b * (c : ℝ) := by
            rw [mul_comm]
            exact div_le_iff₀ (hpos b) |>.mp h
          exact h2)
      · rw [show Rat.cast (1 / c) = (1 : ℝ) / (c : ℝ) from by rw [Rat.cast_div, Rat.cast_one]]
        exact (div_le_iff₀ hcpos).mpr (by
          have h2 : (1 : ℝ) < ρ b * (c : ℝ) := by
            rw [mul_comm]
            exact div_lt_iff₀ (hpos b) |>.mp h
          exact le_of_lt h2)
  · rw [if_neg hb]
    have hb0 : b = 0 := Fin.ext (by have := b.isLt; omega)
    subst hb0
    rw [hpin]
    norm_num

/-- `dfsLo` is positive (it carries a `max … 1`), so it can serve as a division bound. -/
theorem dfsLo_pos (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) : (0 : ℚ) < dfsLo n U b := by
  unfold dfsLo
  by_cases hb : 0 < b.val
  · rw [if_pos hb]
    cases hU : U 0 b with
    | none =>
      show (0 : ℚ) < max (((2 * n b - 1 : ℤ) : ℚ) / 2) 1
      exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    | some p =>
      obtain ⟨c, s⟩ := p
      show (0 : ℚ) < max (max (((2 * n b - 1 : ℤ) : ℚ) / 2) 1) (1 / c)
      exact lt_of_lt_of_le (by norm_num)
        (le_trans (le_max_right _ _) (le_max_left _ _))
  · rw [if_neg hb]
    norm_num

/-! ## 1. Seam arithmetic: the entry sits below the running position -/

/-- **Entry below the running position (general, box-free).**  A realized step's lower seam
`ρ a / ρ b < Aex / A` says the step's entry edge over the new reading sits strictly below
the current node's position `Aex / ρ a` — the position is INSIDE the new tooth window. -/
theorem chainStep_entryBelow {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) {a b : Fin 7} {Aex A : ℚ}
    (hA : 0 < A) (hsat1 : BHolds true (ρ a / ρ b) (Aex / A)) :
    (A : ℝ) / ρ b < (Aex : ℝ) / ρ a := by
  simp only [BHolds, Rat.cast_div] at hsat1
  rw [div_lt_div_iff₀ (hpos b) (Rat.cast_pos.mpr hA)] at hsat1
  rw [div_lt_div_iff₀ (hpos b) (hpos a)]
  have hcomm : (A : ℝ) * ρ a = ρ a * (A : ℝ) := by ring
  rw [hcomm]
  exact hsat1

/-! ## 2. The window datum and the seen-set extension of the strict-increase seed -/

/-- **The window datum (the E810 covering-chain form, conjunct (i)'s loop-break side).**
Every non-terminal node position `Aex / ρ a` of the chain is below 7 — the raw seams do not
forbid an intermediate position past 7 (the chain could jump out of the window and keep
going), so this is genuinely carried data, the same status as `EnvChain`'s envelope
conditions (it is what `chainWalk`'s window guard supplies at each node). -/
def WinBelow7 (ρ : Fin 7 → ℝ) (a : Fin 7) (Aex : ℚ) : List Step → Prop
  | [] => True
  | s :: rest => ((Aex : ℝ) / ρ a < 7) ∧ WinBelow7 ρ s.b s.B rest

/-- **Conjunct (iii): the seen-set form of `chainStep_strictIncrease`.**  A realized chain
never consumes a tooth already in the accumulated list `S`: each accumulated pair's exit
position is at most the current node's position (the invariant), while the upper seam
forces the position to strictly increase past every step it consumes — so a repeat would
push the position strictly past itself. -/
theorem soft_seen_of_chainRealized {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) :
    ∀ (rest : List Step) (U : UTable) (a : Fin 7) (Aex : ℚ) (S : List (Fin 7 × ℚ)),
      ChainRealized ρ U a Aex rest →
      (∀ p ∈ S, ((p.2 : ℝ) / ρ p.1 ≤ (Aex : ℝ) / ρ a)) →
      ∀ q ∈ rest, (q.b, q.B) ∉ S := by
  intro rest
  induction rest with
  | nil => intro U a Aex S _ _ q hq; exact absurd hq (by simp)
  | cons t rest' ih =>
    intro U a Aex S hcr hinv q hq
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
    have hc1 : 0 < (Aex / t.A : ℚ) := bpos_of_holds (div_pos (hpos a) (hpos t.b)) sat1
    have hAex : 0 < Aex := by
      have h1 : Aex = (Aex / t.A) * t.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    have hinc := chainStep_strictIncrease (U := U) (A := t.A) hpos hAex sat2
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq'
    · intro hmem
      exact lt_irrefl _ (lt_of_lt_of_le hinc (hinv _ hmem))
    · intro hmem
      exact ih V t.b t.B ((t.b, t.B) :: S) hrest
        (by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact le_rfl
          · exact le_trans (hinv p hp') hinc.le)
        q hq' (List.mem_cons_of_mem _ hmem)

/-! ## 3. The three conjuncts (per-step, from `ChainRealized`'s own conditions) -/

/-- The tooth form delivers `dfsZone`'s envelope conjuncts (ℚ arithmetic, `j = c.val + 1`). -/
theorem dfsZone_of_tooth {n : Fin 7 → ℤ} {U : UTable} {b : Fin 7} {A B : ℚ} {c : Fin 15}
    (hA : A = envA c) (hB : B = envB c) (hbreak : (A : ℝ) / (dfsHi n U b : ℝ) < 7) :
    dfsZone n U b A B := by
  unfold dfsZone
  refine ⟨c.val + 1, by omega, ?_, ?_, hbreak⟩
  · rw [hA]
    fin_cases c <;> simp only [envA, exitNum] <;> norm_num
  · rw [hB]
    fin_cases c <;> simp only [envB, exitNum] <;> norm_num

/-- **Conjunct (i): envelope form + loop-break.**  A realized step (the cons case of
`ChainRealized` — the two strict seams + positivity are `ChainRealized`'s own conditions)
whose tooth form is given (the `EnvChain` per-step datum, OWED) at a node whose window
position is below 7 (the covering-chain window datum, OWED) satisfies `dfsZone`:
`s.A/dfsHi ≤ s.A/ρ s.b < st.Aex/ρ st.a < 7`. -/
theorem soft_env_of_chainRealized {n : Fin 7 → ℤ} {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k)
    (hpin : ρ 0 = 1) (hface : ∀ i, FaceLo n i ≤ ρ i ∧ ρ i ≤ FaceHi n i) (hn0 : (0 : ℤ) < n 0)
    {st : DfsNode} {s : Step} {rest : List Step} (hfine : UFine ρ st.U)
    (hcr : ChainRealized ρ st.U st.a st.Aex (s :: rest))
    (htooth : ∃ c : Fin 15, s.A = envA c ∧ s.B = envB c)
    (hwin : (st.Aex : ℝ) / ρ st.a < 7) :
    dfsZone n st.U s.b s.A s.B := by
  obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
  have hentry := chainStep_entryBelow hpos hA sat1
  have hread := dfsHi_ge_read n st.U s.b ρ hpos hpin hface hn0 hfine
  obtain ⟨c, hAeq, hBeq⟩ := htooth
  refine dfsZone_of_tooth hAeq hBeq ?_
  calc (s.A : ℝ) / (dfsHi n st.U s.b : ℝ)
      ≤ (s.A : ℝ) / ρ s.b :=
        div_le_div_of_nonneg_left (le_of_lt (Rat.cast_pos.mpr hA)) (hpos s.b) hread
    _ < (st.Aex : ℝ) / ρ st.a := hentry
    _ < 7 := hwin

/-- **Conjunct (ii): entry below the frontier sup.**  A realized step at a node whose
frontier datum `(st.Aex : ℝ)/ρ st.a ≤ st.P` holds satisfies `A/dfsHi < st.P`.  The datum's
status: `childState` banks `P = B/dfsLo n (parent U) b` — the previous exit over the
consumed row's tightened lo — so at tree-internal nodes the frontier sup IS the previous
exit (scaled) and the datum follows from `dfsLo_le_read`; only the tree ROOT's banked `P`
is a record datum. -/
theorem soft_frontier_of_chainRealized {n : Fin 7 → ℤ} {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k)
    (hpin : ρ 0 = 1) (hface : ∀ i, FaceLo n i ≤ ρ i ∧ ρ i ≤ FaceHi n i) (hn0 : (0 : ℤ) < n 0)
    {st : DfsNode} {s : Step} {rest : List Step} (hfine : UFine ρ st.U)
    (hcr : ChainRealized ρ st.U st.a st.Aex (s :: rest))
    (hfr : (st.Aex : ℝ) / ρ st.a ≤ (st.P : ℝ)) :
    ((s.A : ℝ) / (dfsHi n st.U s.b : ℝ)) < (st.P : ℝ) := by
  obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
  have hentry := chainStep_entryBelow hpos hA sat1
  have hread := dfsHi_ge_read n st.U s.b ρ hpos hpin hface hn0 hfine
  calc (s.A : ℝ) / (dfsHi n st.U s.b : ℝ)
      ≤ (s.A : ℝ) / ρ s.b :=
        div_le_div_of_nonneg_left (le_of_lt (Rat.cast_pos.mpr hA)) (hpos s.b) hread
    _ < (st.Aex : ℝ) / ρ st.a := hentry
    _ ≤ (st.P : ℝ) := hfr

/-! Conjunct (iii) at the root's banked seen set is the named OWED datum the composition
consumes: the root's `seen` avoids the chain's steps (start-zone enumeration bookkeeping;
the path-added zones are covered by `soft_seen_of_chainRealized`).  It appears as the
hypothesis `hseen` of `soft_of_chainRealized`. -/

/-! ## 4. The composition: `ChainRealized` ⟹ `DfsSoftAdm` along the induced path -/

/-- **The composition theorem the consumption needs.**  A realized chain from a realized
node state (pinned scope, in-box) whose root record carries the three named data —
seen-avoidance, the per-step tooth form, the window form, and the root frontier datum —
has every step soft-admissible along the induced path. -/
theorem soft_of_chainRealized {n : Fin 7 → ℤ} {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k)
    (hpin : ρ 0 = 1) (hface : ∀ i, FaceLo n i ≤ ρ i ∧ ρ i ≤ FaceHi n i) (hn0 : (0 : ℤ) < n 0) :
    ∀ (steps : List Step) (st : DfsNode),
      UFine ρ st.U →
      ((st.Aex : ℝ) / ρ st.a ≤ (st.P : ℝ)) →
      ChainRealized ρ st.U st.a st.Aex steps →
      (∀ q ∈ steps, (q.b, q.B) ∉ st.seen) →
      (∀ q ∈ steps, ∃ c : Fin 15, q.A = envA c ∧ q.B = envB c) →
      WinBelow7 ρ st.a st.Aex steps →
      DfsSoftAdm n st steps := by
  intro steps
  induction steps with
  | nil => intro st _ _ _ _ _ _; exact True.intro
  | cons s rest ih =>
    intro st hfine hfr hcr hseen htooth hwin
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hcr
    simp only [WinBelow7] at hwin
    obtain ⟨hwin1, hwin2⟩ := hwin
    have hentry := chainStep_entryBelow hpos hA sat1
    have hread := dfsHi_ge_read n st.U s.b ρ hpos hpin hface hn0 hfine
    have hstepDiv : (s.A : ℝ) / (dfsHi n st.U s.b : ℝ) ≤ (s.A : ℝ) / ρ s.b :=
      div_le_div_of_nonneg_left (le_of_lt (Rat.cast_pos.mpr hA)) (hpos s.b) hread
    obtain ⟨c, hAeq, hBeq⟩ := htooth s List.mem_cons_self
    have hzone : dfsZone n st.U s.b s.A s.B :=
      dfsZone_of_tooth hAeq hBeq (by
        calc (s.A : ℝ) / (dfsHi n st.U s.b : ℝ)
            ≤ (s.A : ℝ) / ρ s.b := hstepDiv
          _ < (st.Aex : ℝ) / ρ st.a := hentry
          _ < 7 := hwin1)
    have hfront : ((s.A : ℝ) / (dfsHi n st.U s.b : ℝ)) < (st.P : ℝ) :=
      calc (s.A : ℝ) / (dfsHi n st.U s.b : ℝ)
          ≤ (s.A : ℝ) / ρ s.b := hstepDiv
        _ < (st.Aex : ℝ) / ρ st.a := hentry
        _ ≤ (st.P : ℝ) := hfr
    have hfresh : (s.b, s.B) ∉ st.seen := hseen s List.mem_cons_self
    -- the trace machinery: the child table stays realized (as in `dfsWalk`)
    have hc1 : 0 < (st.Aex / s.A : ℚ) := bpos_of_holds (div_pos (hpos st.a) (hpos s.b)) sat1
    have hAex : 0 < st.Aex := by
      have h1 : st.Aex = (st.Aex / s.A) * s.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    obtain ⟨V1, hadd1, hadd2⟩ := uStep_some_add hAex hA hB hV
    have hf1 : UFine ρ V1 := uAdd_fine_some hpos hfine sat1 hadd1
    have hfV : UFine ρ V := uAdd_fine_some hpos hf1 sat2 hadd2
    -- the child's frontier datum: derived (the frontier sup IS the previous exit)
    have hchildfr : ((s.B : ℝ) / ρ s.b) ≤ (((childState n st s.b s.B V).P : ℚ) : ℝ) := by
      show (s.B : ℝ) / ρ s.b ≤ Rat.cast (s.B / dfsLo n st.U s.b)
      rw [Rat.cast_div]
      exact (div_le_div_iff₀ (hpos s.b) (Rat.cast_pos.mpr (dfsLo_pos n st.U s.b))).mpr
        (mul_le_mul_of_nonneg_left (dfsLo_le_read n st.U s.b ρ hpos hpin hface hfine)
          (le_of_lt (Rat.cast_pos.mpr hB)))
    -- the child's seen datum: the parent's + no-repeat (strict increase)
    have hchildseen : ∀ q ∈ rest, (q.b, q.B) ∉ (childState n st s.b s.B V).seen := by
      intro q hq
      have h1 := hseen q (List.mem_cons_of_mem _ hq)
      have h2 : (q.b, q.B) ≠ (s.b, s.B) := by
        intro heq
        exact soft_seen_of_chainRealized hpos rest V s.b s.B [(s.b, s.B)] hrest
          (by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact le_rfl
            · exact absurd hp' (by simp))
          q hq (by rw [heq]; exact List.mem_cons_self)
      simp only [childState, Finset.mem_union, Finset.mem_singleton]
      intro hmem
      rcases hmem with hmem | hmem
      · exact h1 hmem
      · exact h2 hmem
    simp only [DfsSoftAdm]
    refine ⟨⟨hzone, hfront, hfresh⟩, fun W hW => ?_⟩
    have hVW : V = W := Option.some.inj (hV.symm.trans hW)
    subst hVW
    exact ih (childState n st s.b s.B V) hfV hchildfr hrest hchildseen
      (fun q hq => htooth q (List.mem_cons_of_mem _ hq)) hwin2

/-! ## 5. Worked case A: box b1's banked walk19 -/

/-- The b1 census (the box of `DfsRootAdmProof`). -/
def box1 : Fin 7 → ℤ := (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ)

theorem box1_pos0 : (0 : ℤ) < box1 0 := by decide

theorem box1_pos : ∀ i, (0 : ℤ) < box1 i := by
  intro i
  fin_cases i <;> decide

theorem g19_box1_face : ∀ i, FaceLo box1 i ≤ g19 i ∧ g19 i ≤ FaceHi box1 i := g19_face

theorem g19_pin : g19 0 = 1 := by simp [g19]

theorem g19_pos : ∀ k, 0 < g19 k := fun k =>
  lt_of_lt_of_le zero_lt_one ((faceLo_ge_one box1 k).trans (g19_box1_face k).1)

/-- The induced root state of the pinned b1 start: the closure-start table, row 0, exit
numerator 1, frontier sup `1/dfsLo` (the `childState` convention at the virtual start —
`dfsLo` at row 0 is 1 verbatim), empty seen set. -/
def walk19Root : DfsNode :=
  ⟨mkTab_1_3_4_5_5_5_7, (0 : Fin 7), (1 : ℚ), (1 : ℚ) / dfsLo box1 mkTab_1_3_4_5_5_5_7 0, ∅⟩

theorem dfsLo_box1_0 : dfsLo box1 mkTab_1_3_4_5_5_5_7 0 = 1 := rfl

theorem walk19_root_frontier :
    ((walk19Root.Aex : ℝ)) / g19 walk19Root.a ≤ ((walk19Root.P : ℝ)) := by
  simp [walk19Root, dfsLo_box1_0, g19]

theorem walk19_root_seen : ∀ q ∈ walk19, (q.b, q.B) ∉ walk19Root.seen := by
  intro q _
  simp [walk19Root]

/-- The banked walk's tooth form (head step `(6, zEntry 1, zExit 1)` = tooth 1; the tail
from the banked `walk19_env`). -/
theorem walk19_tooth : ∀ q ∈ walk19, ∃ c : Fin 15, q.A = envA c ∧ q.B = envB c := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact ⟨0, rfl, rfl⟩
  · obtain ⟨-, ⟨c, h1, h2⟩⟩ := walk19_env.2.2 q hq'
    exact ⟨c, h1, h2⟩

/-- The banked walk's window datum: all 19 non-terminal node positions `B/ρ b` are below 7
(the walk blocks inside the window and exits only at the last step, where `WinBelow7` is
vacuous). -/
theorem walk19_win : WinBelow7 g19 0 1 walk19 := by
  rw [walk19_lit]
  simp only [WinBelow7]
  simp [g19]
  norm_num

/-- **The worked case (b1).**  The banked counterexample walk is soft-admissible along its
induced path from the constructed root state: all 19 steps pass the three soft conjuncts
(the envelope `dfsZone` with the loop-break, the frontier sup, the seen freshness). -/
theorem walk19_soft : DfsSoftAdm box1 walk19Root walk19 :=
  soft_of_chainRealized (n := box1) (ρ := g19) g19_pos g19_pin g19_box1_face box1_pos0
    walk19 walk19Root g19_fine walk19_root_frontier walk19_realized walk19_root_seen
    walk19_tooth walk19_win

/-- Step 1 of the walk, literally: the tooth `(6, 1)`'s step passes the full soft filter at
the constructed root (whose first child state is row 6 exit 9 — the b1 forced-opening root
of `DfsRootAdmProof`). -/
theorem walk19_step1_soft : DfsSoft box1 walk19Root (6 : Fin 7) 7 9 := by
  have h := walk19_soft
  simp only [DfsSoftAdm, walk19] at h
  have hz : zEntry 1 = (7 : ℚ) := by simp [zEntry, zExit] <;> norm_num
  have hx : zExit 1 = (9 : ℚ) := by simp [zEntry, zExit] <;> norm_num
  rw [← hz, ← hx]
  exact h.1

/-! ## 6. Worked case B: rung 1's crown root -/

/-- **The crown root's frontier datum, discharged from the face bounds.**  The banked root
record has `P = 82/31 = 41/(31/2)` (the start zone's exit over the OPENING table's
tightened lo — the ancestor's `U 0 5`, looser than the node table's `17/273`); any in-box
pinned arrangement has `ρ 5 ≥ 31/2 = FaceLo` (census 16), so the datum holds for every
realizing arrangement. -/
theorem crown_root_frontier_of_face (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k)
    (hface : ∀ i, FaceLo (boxN m4res_1_4_6_7_10_16_16) i ≤ ρ i ∧
      ρ i ≤ FaceHi (boxN m4res_1_4_6_7_10_16_16) i) :
    ((41 : ℚ) : ℝ) / ρ 5 ≤ ((82 / 31 : ℚ) : ℝ) := by
  have h5 : (FaceLo (boxN m4res_1_4_6_7_10_16_16) 5 : ℝ) = (31 / 2 : ℝ) := by
    simp only [FaceLo, boxN]
    norm_num [m4res_1_4_6_7_10_16_16]
  have h55 := (hface 5).1
  rw [h5] at h55
  have h7 : ((82 / 31 : ℚ) : ℝ) * (31 / 2 : ℝ) ≤ ((82 / 31 : ℚ) : ℝ) * ρ 5 :=
    mul_le_mul_of_nonneg_left h55 (by norm_num)
  rw [div_le_iff₀ (hpos 5)]
  have h6 : ((82 / 31 : ℚ) : ℝ) * (31 / 2 : ℝ) = ((41 : ℚ) : ℝ) := by norm_num
  rw [← h6]
  exact h7

/-- **Worked case B, step c0** (the reach-prune child's step, banked as `stepEq_c0`):
the full soft filter at the crown root, checked literally — tooth `(2, 15, 17)` = tooth 2,
loop-break `15/(28611/4550) < 7`, frontier `15/(28611/4550) < 82/31`, fresh
`(2, 17) ∉ nodeRoot.seen`. -/
theorem crown_c0_soft : DfsSoft (boxN m4res_1_4_6_7_10_16_16) nodeRoot (2 : Fin 7) 15 17 := by
  have hv : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (2 : Fin 7) = (28611 / 4550 : ℚ) :=
    by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_2_0]
  simp only [DfsSoft, dfsZone, nodeRoot, hv]
  refine ⟨⟨2, by norm_num, rfl, rfl, by norm_num⟩, by norm_num, by decide⟩

/-- **Worked case B, step c1** (the dead-end child's step, banked as `stepEq_c1`):
the full soft filter at the crown root, checked literally — tooth `(4, 23, 25)` = tooth 3,
loop-break `23/(9537/910) < 7`, frontier `23/(9537/910) < 82/31`, fresh
`(4, 25) ∉ nodeRoot.seen`. -/
theorem crown_c1_soft : DfsSoft (boxN m4res_1_4_6_7_10_16_16) nodeRoot (4 : Fin 7) 23 25 := by
  have hv : dfsHi (boxN m4res_1_4_6_7_10_16_16) tblRoot (4 : Fin 7) = (9537 / 910 : ℚ) :=
    by norm_num [dfsHi, boxN, m4res_1_4_6_7_10_16_16, tblRoot_c_4_0]
  simp only [DfsSoft, dfsZone, nodeRoot, hv]
  refine ⟨⟨3, by norm_num, rfl, rfl, by norm_num⟩, by norm_num, by decide⟩

#print axioms faceHi_q
#print axioms dfsHi_ge_read
#print axioms dfsLo_le_read
#print axioms dfsLo_pos
#print axioms chainStep_entryBelow
#print axioms soft_seen_of_chainRealized
#print axioms dfsZone_of_tooth
#print axioms soft_env_of_chainRealized
#print axioms soft_frontier_of_chainRealized
#print axioms soft_of_chainRealized
#print axioms box1_pos0
#print axioms box1_pos
#print axioms g19_box1_face
#print axioms g19_pin
#print axioms g19_pos
#print axioms dfsLo_box1_0
#print axioms walk19_root_frontier
#print axioms walk19_root_seen
#print axioms walk19_tooth
#print axioms walk19_win
#print axioms walk19_soft
#print axioms walk19_step1_soft
#print axioms crown_root_frontier_of_face
#print axioms crown_c0_soft
#print axioms crown_c1_soft

end Fresh.M4Cert
