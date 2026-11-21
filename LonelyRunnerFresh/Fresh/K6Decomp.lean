import Mathlib.Tactic

/-!
# K6Decomp: the K6 component decomposition of the tooth-blocked window [1, 7]

New file (2026-11-21); nothing existing is edited.

## Provenance and mirror target

This file mirrors `k6_components` of `experiments/n8/conjT3_enum_v1.py` (which composes
`taillemma_lib_v1.zones_of` with clipping to `[1, 7]`, a sort, a touching-merge, and a
component walk) as the Lean definition `K6Comps`, together with the covered/lonely
characterisation of its members.  Tooth arithmetic is in ℚ throughout; the readings are
the five reals `rho : Fin 5 → ℚ` (`ρ₂..ρ₆`).

Pipeline (each stage mirrors the Python exactly):
* `ZonesOf r` — the tooth zones `((8j-1)/r, (8j+1)/r)`, laps `j = 1..15` (here `j = k+1`,
  endpoints `(8k+7)/r, (8k+9)/r`), each clipped to `[1, 7]` (`max a 1, min b 7`) and kept
  iff the clipped interval is nondegenerate.  Lap bound provenance: a zone can meet
  `[1, 7]` only if `(8j-1)/r < 7`, i.e. `j < (7r+1)/8`; for readings `r ≤ 17` that forces
  `8j - 1 < 119`, hence `j ≤ 14 ⊆ 1..15`.  So for `r ≤ 17` the laps `1..15` exhaust all
  zones meeting `[1, 7]` (for `r > 17` higher laps would exist; the general lemmas below
  do not need the bound — only the bridge lemma `zone_open_unbounded_iff` does).
* `zonesAll rho` — the five readings' clipped zones concatenated, reading order preserved
  (Python's `ivs` before sorting).
* `sortIv` — insertion sort by left endpoint (Python `ivs.sort()`; ties in the left
  endpoint do not affect the merged union, and the worked instance has no ties).
* `mergeAcc` / `Merged` — the touching-merge fold `a ≤ last.2 → extend` (Python `merged`).
* `K6Walk` / `K6Comps` — the component walk from `cur = 1`: emit `[cur, a]` when `a > cur`,
  `cur = max(cur, b)`, final `[cur, 7]` when `cur < 7`.

## What is proved here, honestly

* **Step 1** — the defs and the worked instance `rhoEx = ![2, 3, 4, 6, 8]`, each stage's
  value pinned to the Python-computed list literal by `decide`.
* **Step 2, direction ⟹** (`comps_lonely`): every component point of `[1, 7]` lies in NO
  open tooth zone of any reading.  Fully general, no hypotheses on `rho` (clipping makes
  every list entry satisfy `Vld` by the filter alone).
* **Step 2, direction ⟸** (`lonely_comp_or_artifact`): a point of `[1, 7]` in no open
  zone of the *merged* union is in a component, EXCEPT possibly the two boundary
  artifacts `x = 1` (when some merged block starts exactly at 1) and `x = 7` (when some
  merged block ends exactly at 7).  The bare iff "in some component ⟺ in no open zone of
  any reading" is FALSE at three kinds of points:
  1. touching boundaries: two zones of different readings meeting end-to-start, e.g.
     readings 3 and 5 give zones `(7/3, 3)` and `(3, 17/5)`; the point 3 is in no open
     zone, yet the merged block `(7/3, 17/5)` absorbs it and the walk emits nothing
     there.  Such points are open-interior points of merged blocks and endpoints of
     zones (`blocked_or_touching`).
  2. `x = 1` when the first merged block starts exactly at 1 (the worked instance does:
     reading 8 has tooth `(7/8, 9/8)` clipped to `(1, 9/8)`).
  3. `x = 7` when a merged block ends exactly at 7 (the worked instance does: reading 8's
     lap-7 tooth `(55/8, 57/8)` clipped to `(55/8, 7)`).
* **Step 3** (`blocked_witness_bounded`, task shape): under the honest extra band
  hypothesis that `x` lies in no open zone of the MERGED union (which excludes the
  touching boundaries), a non-component point of `[1, 7]` with `x ≠ 1 ≠ 7` cannot exist,
  so the blocked-witness conclusion `∃ i j, (8j-1)/ρᵢ < x < (8j+1)/ρᵢ` follows in the
  bounded `1 ≤ j ≤ 15` form.  The honest content of Step 3 is `blocked_or_touching`: a
  non-component point of `[1, 7]` with `x ≠ 1 ≠ 7` in no open zone of any reading is a
  TOUCHING BOUNDARY — an open-interior point of a merged block and an endpoint of some
  clipped zone.

## Bridge β (band-union lemma) input spec

β consumes, per the results landed here:
* `merged_valid` — `Merged (zonesAll rho)` is strictly separated (pairwise `p.2 < q.1`)
  and every block is a clipped interval (`Vld`: `1 ≤ .1 < .2 ≤ 7`); no hypotheses on rho.
* `merged_contain` — every clipped zone is contained in some merged block (closed hulls).
* `comps_lonely` / `lonely_comp_or_artifact` / `blocked_or_touching` — the component
  union equals `[1,7] \ (open tooth bands)` up to the finite artifact set
  `{1, 7} ∪ {touching boundaries}`, all of which are endpoints of clipped zones.
* `zone_open_iff` / `zone_open_unbounded_iff` — membership in an open zone of reading
  `r` as a `ZonesOf` entry ↔ the tooth predicate `∃ j, 1 ≤ j ≤ 15` (resp. unbounded `j`,
  needing `r ≤ 17`), `(8j-1)/r < x < (8j+1)/r`.  NOTE the clipped blind spots: these
  equivalences hold for `1 < x < 7` only; at `x = 1` (resp. `x = 7`) a tooth may
  strictly contain the point while the clipped entry starts (resp. ends) exactly there.
  Positivity of the readings is never assumed as a hypothesis; it is forced at the point
  of use by `x ≥ 1` together with the tooth predicate.

## Compiler quirks used (recorded)

* Core `Rat.mul`/`Rat.inv` are `@[irreducible]`, so `decide`/`rfl` cannot evaluate ℚ
  division.  This file sets `allowUnsafeReducibility` and makes `Rat.mul`/`Rat.inv`
  LOCALLY reducible (elaboration-level only; soundness and the axiom footprint are
  unaffected, and no other file is touched).  With that, `decide` evaluates the whole
  pipeline on the worked instance.
* All tooth comparisons reduce through `Rat.blt` on constructor-level ℚ values.
-/

set_option allowUnsafeReducibility true
attribute [local reducible] Rat.mul Rat.inv

/-! ## §1 Definitions (mirror of conjT3_enum_v1.py) -/

/-- Clipped-zone validity: `p` is a nondegenerate interval inside `[1, 7]`. -/
def Vld (p : ℚ × ℚ) : Prop := 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 7

/-- The tooth zones of reading `r`: open intervals `((8j-1)/r, (8j+1)/r)` for laps
`j = 1..15` (here `j = k+1`, so the endpoints are `(8k+7)/r, (8k+9)/r`), clipped to
`[1, 7]` and kept iff the clipped interval is nondegenerate.  Mirrors `taillemma_lib_v1`
`zones_of` plus the clip step of `k6_components`. -/
def ZonesOf (r : ℚ) : List (ℚ × ℚ) :=
  (List.range 15).filterMap (fun k =>
    if max (((8 * k + 7 : ℕ) : ℚ) / r) 1 < min (((8 * k + 9 : ℕ) : ℚ) / r) 7 then
      some (max (((8 * k + 7 : ℕ) : ℚ) / r) 1, min (((8 * k + 9 : ℕ) : ℚ) / r) 7)
    else none)

/-- The five readings' clipped zones concatenated, reading order preserved
(Python's `ivs` list before sorting). -/
def zonesAll (rho : Fin 5 → ℚ) : List (ℚ × ℚ) :=
  ZonesOf (rho 0) ++ ZonesOf (rho 1) ++ ZonesOf (rho 2) ++ ZonesOf (rho 3) ++ ZonesOf (rho 4)

/-- Insertion of one interval into a list sorted by left endpoint. -/
def insIv (p : ℚ × ℚ) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => [p]
  | q :: t => if p.1 ≤ q.1 then p :: q :: t else q :: insIv p t

theorem insIv_nil (p : ℚ × ℚ) : insIv p [] = [p] := rfl
theorem insIv_cons (q : ℚ × ℚ) (t : List (ℚ × ℚ)) (p : ℚ × ℚ) :
    insIv p (q :: t) = if p.1 ≤ q.1 then p :: q :: t else q :: insIv p t := rfl

/-- Insertion sort by left endpoint (Python `ivs.sort()`). -/
def sortIv : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => []
  | p :: t => insIv p (sortIv t)

theorem sortIv_nil : sortIv [] = [] := rfl
theorem sortIv_cons (p : ℚ × ℚ) (t : List (ℚ × ℚ)) : sortIv (p :: t) = insIv p (sortIv t) := rfl

/-- One merge step: fold interval `p` into the running accumulator, newest block first,
merging on contact (`p.1 ≤ newest.2` extends the block to the max).  Mirrors
`if merged and a <= merged[-1][1]: merged[-1][1] = max(...)` of `k6_components`. -/
def mergeStep (acc : List (ℚ × ℚ)) (p : ℚ × ℚ) : List (ℚ × ℚ) :=
  match acc with
  | [] => [p]
  | q :: accT => if p.1 ≤ q.2 then (q.1, max q.2 p.2) :: accT else p :: acc

theorem mergeStep_nil (p : ℚ × ℚ) : mergeStep [] p = [p] := rfl
theorem mergeStep_cons (q : ℚ × ℚ) (accT : List (ℚ × ℚ)) (p : ℚ × ℚ) :
    mergeStep (q :: accT) p =
      if p.1 ≤ q.2 then (q.1, max q.2 p.2) :: accT else p :: q :: accT := rfl

/-- The touching-merge fold (Python's `merged` construction). -/
def mergeAcc (acc : List (ℚ × ℚ)) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => acc.reverse
  | p :: rest => mergeAcc (mergeStep acc p) rest

theorem mergeAcc_nil (acc : List (ℚ × ℚ)) : mergeAcc acc [] = acc.reverse := rfl
theorem mergeAcc_cons (acc : List (ℚ × ℚ)) (p : ℚ × ℚ) (rest : List (ℚ × ℚ)) :
    mergeAcc acc (p :: rest) = mergeAcc (mergeStep acc p) rest := rfl

/-- Sort by left endpoint, then merge touching intervals (Python `merged`). -/
def Merged (l : List (ℚ × ℚ)) : List (ℚ × ℚ) := mergeAcc [] (sortIv l)

/-- The component walk over a merged list (Python's `comps` loop): emit `[cur, a]` when
`a > cur`, `cur = max(cur, b)`, final `[cur, 7]` when `cur < 7`. -/
def K6Walk (cur : ℚ) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => if cur < 7 then [(cur, 7)] else []
  | p :: rest => (if p.1 > cur then [(cur, p.1)] else []) ++ K6Walk (max cur p.2) rest

theorem K6Walk_nil (cur : ℚ) : K6Walk cur [] = if cur < 7 then [(cur, 7)] else [] := rfl
theorem K6Walk_cons (cur : ℚ) (p : ℚ × ℚ) (rest : List (ℚ × ℚ)) :
    K6Walk cur (p :: rest) =
      (if p.1 > cur then [(cur, p.1)] else []) ++ K6Walk (max cur p.2) rest := rfl

/-- The K6 components of five readings: the mirror of `k6_components rho`
(conjT3_enum_v1.py). -/
def K6Comps (rho : Fin 5 → ℚ) : List (ℚ × ℚ) := K6Walk 1 (Merged (zonesAll rho))

/-- `x` lies in some closed interval of the list (component membership). -/
def MemComp (x : ℚ) (l : List (ℚ × ℚ)) : Prop := ∃ p ∈ l, p.1 ≤ x ∧ x ≤ p.2

/-- `x` lies strictly inside some interval of the list (open-zone membership). -/
def MemZone (x : ℚ) (l : List (ℚ × ℚ)) : Prop := ∃ p ∈ l, p.1 < x ∧ x < p.2

/-! ## §2 Step 1 — the worked instance `rhoEx = ![2, 3, 4, 6, 8]` -/

/-- The worked instance: readings 2, 3, 4, 6, 8 (Python `rho_small = [2, 3, 4, 6, 8]`). -/
def rhoEx : Fin 5 → ℚ := ![2, 3, 4, 6, 8]

theorem zonesEx_2 : ZonesOf 2 = [(7 / 2, 9 / 2)] := by decide
theorem zonesEx_3 : ZonesOf 3 = [(7 / 3, 3), (5, 17 / 3)] := by decide
theorem zonesEx_4 : ZonesOf 4 = [(7 / 4, 9 / 4), (15 / 4, 17 / 4), (23 / 4, 25 / 4)] := by decide
theorem zonesEx_6 : ZonesOf 6 =
    [(7 / 6, 3 / 2), (5 / 2, 17 / 6), (23 / 6, 25 / 6), (31 / 6, 11 / 2), (13 / 2, 41 / 6)] := by
  decide
theorem zonesEx_8 : ZonesOf 8 =
    [(1, 9 / 8), (15 / 8, 17 / 8), (23 / 8, 25 / 8), (31 / 8, 33 / 8), (39 / 8, 41 / 8),
      (47 / 8, 49 / 8), (55 / 8, 7)] := by
  decide

/-- The merged union for the worked instance — exactly Python's `merged` list.  Note it
EXHIBITS both boundary artifacts: the first block starts exactly at `1` (reading 8's
tooth `(7/8, 9/8)` clipped) and the last ends exactly at `7` (reading 8's lap-7 tooth
`(55/8, 57/8)` clipped). -/
theorem mergedEx : Merged (zonesAll rhoEx) =
    [(1, 9 / 8), (7 / 6, 3 / 2), (7 / 4, 9 / 4), (7 / 3, 25 / 8), (7 / 2, 9 / 2),
      (39 / 8, 17 / 3), (23 / 4, 25 / 4), (13 / 2, 41 / 6), (55 / 8, 7)] := by
  decide

/-- The K6 components for the worked instance — exactly Python's
`k6_components([2, 3, 4, 6, 8])`; the walk ends with `cur = 7`, so no final component. -/
theorem compsEx : K6Comps rhoEx =
    [(9 / 8, 7 / 6), (3 / 2, 7 / 4), (9 / 4, 7 / 3), (25 / 8, 7 / 2), (9 / 2, 39 / 8),
      (17 / 3, 23 / 4), (25 / 4, 13 / 2), (41 / 6, 55 / 8)] := by
  decide

/-! ## §3 Sort/merge infrastructure -/

theorem zonesOf_valid (r : ℚ) (p : ℚ × ℚ) (h : p ∈ ZonesOf r) : Vld p := by
  simp only [ZonesOf, List.mem_filterMap, List.mem_range] at h
  obtain ⟨k, hk, hk'⟩ := h
  by_cases hC : max (((8 * k + 7 : ℕ) : ℚ) / r) 1 < min (((8 * k + 9 : ℕ) : ℚ) / r) 7
  · rw [if_pos hC] at hk'
    injection hk' with hk'
    show 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 7
    rw [congrArg Prod.fst hk'.symm, congrArg Prod.snd hk'.symm]
    exact ⟨le_max_right _ _, hC, min_le_right _ _⟩
  · rw [if_neg hC] at hk'
    simp at hk'

theorem zonesAll_valid (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (h : p ∈ zonesAll rho) : Vld p := by
  rw [zonesAll] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact zonesOf_valid _ _ h
        · exact zonesOf_valid _ _ h
      · exact zonesOf_valid _ _ h
    · exact zonesOf_valid _ _ h
  · exact zonesOf_valid _ _ h

theorem insIv_mem (p : ℚ × ℚ) : ∀ (t : List (ℚ × ℚ)) (y : ℚ × ℚ),
    y ∈ insIv p t ↔ y = p ∨ y ∈ t := by
  intro t
  induction t with
  | nil => intro y; rw [insIv_nil]; simp
  | cons q t ih =>
    intro y
    rw [insIv_cons]
    by_cases h : p.1 ≤ q.1
    · simp only [if_pos h, List.mem_cons]
    · simp only [if_neg h, List.mem_cons, ih]
      tauto

theorem sortIv_mem : ∀ (l : List (ℚ × ℚ)) (y : ℚ × ℚ), y ∈ sortIv l ↔ y ∈ l := by
  intro l
  induction l with
  | nil => intro y; rw [sortIv_nil]
  | cons p t ih =>
    intro y
    simp only [sortIv_cons, insIv_mem, ih, List.mem_cons]

theorem insIv_sorted : ∀ (t : List (ℚ × ℚ)), t.Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) →
    ∀ p : ℚ × ℚ, (insIv p t).Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) := by
  intro t
  induction t with
  | nil =>
    intro _ p
    rw [insIv_nil]
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons q t ih =>
    intro hs p
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rw [insIv_cons]
    by_cases h : p.1 ≤ q.1
    · rw [if_pos h]
      exact List.Pairwise.cons
        (by intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact h
            · exact le_trans h (hhead y hy))
        (List.Pairwise.cons hhead htail)
    · rw [if_neg h]
      refine List.Pairwise.cons ?_ (ih htail p)
      intro y hy
      rcases (insIv_mem p t y).mp hy with rfl | hy'
      · linarith
      · exact hhead y hy'

theorem sortIv_sorted (l : List (ℚ × ℚ)) :
    (sortIv l).Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p t ih => rw [sortIv_cons]; exact insIv_sorted (sortIv t) ih p

/-- Accumulator invariant of the merge fold: newest block first, every older block ends
strictly before the newer block starts. -/
def AccSep (l : List (ℚ × ℚ)) : Prop := l.Pairwise (fun p q => q.2 < p.1)

theorem mergeStep_vld (acc : List (ℚ × ℚ)) (p : ℚ × ℚ)
    (hacc : ∀ q ∈ acc, Vld q) (hp : Vld p) : ∀ s ∈ mergeStep acc p, Vld s := by
  rcases acc with _ | ⟨u, accU⟩
  · rw [mergeStep_nil]
    intro s hs
    simp at hs
    rw [hs]
    exact hp
  · rw [mergeStep_cons]
    by_cases h : p.1 ≤ u.2
    · rw [if_pos h]
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨(hacc u (by simp)).1,
          lt_of_lt_of_le (hacc u (by simp)).2.1 (le_max_left _ _),
          max_le (hacc u (by simp)).2.2 hp.2.2⟩
      · exact hacc s (List.mem_cons_of_mem _ hs)
    · rw [if_neg h]
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with h1 | h2 | hs
      · rw [h1]; exact hp
      · rw [h2]; exact hacc u (by simp)
      · exact hacc s (List.mem_cons_of_mem _ hs)

theorem mergeStep_accsep (acc : List (ℚ × ℚ)) (p : ℚ × ℚ)
    (hacc : ∀ q ∈ acc, Vld q) (hsep : AccSep acc) : AccSep (mergeStep acc p) := by
  rcases acc with _ | ⟨u, accU⟩
  · rw [mergeStep_nil]
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  · obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsep
    rw [mergeStep_cons]
    by_cases h : p.1 ≤ u.2
    · rw [if_pos h]
      exact List.Pairwise.cons (by intro y hy; exact hhead y hy) htail
    · rw [if_neg h]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hhead htail)
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact lt_of_not_ge (fun hge => h (ge_iff_le.mp hge))
      · linarith [hhead y hy, (hacc u (by simp)).2.1,
          lt_of_not_ge (fun hge : u.2 ≥ p.1 => h (ge_iff_le.mp hge))]

theorem mergeStep_order (acc : List (ℚ × ℚ)) (p : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (hacc : ∀ q ∈ acc, ∀ p' ∈ rest, q.1 ≤ p'.1) (hhead : ∀ p' ∈ rest, p.1 ≤ p'.1) :
    ∀ s ∈ mergeStep acc p, ∀ p' ∈ rest, s.1 ≤ p'.1 := by
  rcases acc with _ | ⟨u, accU⟩
  · rw [mergeStep_nil]
    intro s hs p'
    simp at hs
    rw [hs]
    exact hhead p'
  · rw [mergeStep_cons]
    by_cases h : p.1 ≤ u.2
    · rw [if_pos h]
      intro s hs p'
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hacc u (by simp) p'
      · exact hacc s (List.mem_cons_of_mem _ hs) p'
    · rw [if_neg h]
      intro s hs p'
      simp only [List.mem_cons] at hs
      rcases hs with h1 | h2 | hs
      · rw [h1]; exact hhead p'
      · rw [h2]; exact hacc u (by simp) p'
      · exact hacc s (List.mem_cons_of_mem _ hs) p'

theorem mergeStep_contain_p (acc : List (ℚ × ℚ)) (p : ℚ × ℚ) (hacc : ∀ q ∈ acc, q.1 ≤ p.1) :
    ∃ s ∈ mergeStep acc p, s.1 ≤ p.1 ∧ p.2 ≤ s.2 := by
  rcases acc with _ | ⟨u, accU⟩
  · rw [mergeStep_nil]
    exact ⟨p, by simp, le_refl _, le_refl _⟩
  · rw [mergeStep_cons]
    by_cases h : p.1 ≤ u.2
    · rw [if_pos h]
      exact ⟨(u.1, max u.2 p.2), by simp, hacc u (by simp), le_max_right _ _⟩
    · rw [if_neg h]
      exact ⟨p, by simp, le_refl _, le_refl _⟩

theorem mergeStep_contain_acc (acc : List (ℚ × ℚ)) (p : ℚ × ℚ) (hacc : ∀ q ∈ acc, q.1 ≤ p.1)
    (r : ℚ × ℚ) (hr : r ∈ acc) : ∃ s ∈ mergeStep acc p, s.1 ≤ r.1 ∧ r.2 ≤ s.2 := by
  rcases acc with _ | ⟨u, accU⟩
  · exact absurd hr (by simp)
  · rw [mergeStep_cons]
    by_cases h : p.1 ≤ u.2
    · rw [if_pos h]
      rcases List.mem_cons.mp hr with h1 | hr'
      · rw [h1]
        exact ⟨(u.1, max u.2 p.2), by simp, le_refl _, le_max_left _ _⟩
      · exact ⟨r, List.mem_cons_of_mem _ hr', le_refl _, le_refl _⟩
    · rw [if_neg h]
      exact ⟨r, List.mem_cons_of_mem _ hr, le_refl _, le_refl _⟩

theorem mergeAcc_vld : ∀ (L : List (ℚ × ℚ)) (acc : List (ℚ × ℚ)),
    (∀ q ∈ acc, Vld q) → (∀ p ∈ L, Vld p) → ∀ s ∈ mergeAcc acc L, Vld s := by
  intro L
  induction L with
  | nil =>
    intro acc hacc _ s hs
    rw [mergeAcc_nil, List.mem_reverse] at hs
    exact hacc s hs
  | cons p rest ih =>
    intro acc hacc hv s hs
    rw [mergeAcc_cons] at hs
    exact ih (mergeStep acc p)
      (fun y hy => mergeStep_vld acc p hacc (hv p (List.mem_cons_self)) y hy)
      (fun y hy => hv y (List.mem_cons_of_mem _ hy)) s hs

theorem mergeAcc_accsep : ∀ (L : List (ℚ × ℚ)) (acc : List (ℚ × ℚ)),
    AccSep acc → (∀ q ∈ acc, ∀ p ∈ L, q.1 ≤ p.1) →
    L.Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) →
    (∀ q ∈ acc, Vld q) → (∀ p ∈ L, Vld p) →
    (mergeAcc acc L).Pairwise (fun p q : ℚ × ℚ => p.2 < q.1) := by
  intro L
  induction L with
  | nil =>
    intro acc hsep _ _ _ _
    rw [mergeAcc_nil]
    exact List.Pairwise.reverse hsep
  | cons p rest ih =>
    intro acc hsep hord hpair hacc hv
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    rw [mergeAcc_cons]
    exact ih (mergeStep acc p)
      (mergeStep_accsep acc p hacc hsep)
      (mergeStep_order acc p rest (fun q hq p' hp' => hord q hq p' (List.mem_cons_of_mem _ hp')) hhead)
      htail
      (fun y hy => mergeStep_vld acc p hacc (hv p (List.mem_cons_self)) y hy)
      (fun y hy => hv y (List.mem_cons_of_mem _ hy))

/-- Every interval of `acc ++ L` is contained (closed hull) in some interval of the
merged fold.  Requires the input sorted by left endpoint (for the pushed-block case). -/
theorem mergeAcc_contain : ∀ (L : List (ℚ × ℚ)) (acc : List (ℚ × ℚ)),
    (∀ q ∈ acc, ∀ p ∈ L, q.1 ≤ p.1) → L.Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) →
    ∀ r : ℚ × ℚ, r ∈ acc ++ L → ∃ s ∈ mergeAcc acc L, s.1 ≤ r.1 ∧ r.2 ≤ s.2 := by
  intro L
  induction L with
  | nil =>
    intro acc _ _ r hr
    rw [List.append_nil] at hr
    rw [mergeAcc_nil]
    exact ⟨r, List.mem_reverse.mpr hr, le_refl _, le_refl _⟩
  | cons p rest ih =>
    intro acc hacc hpair r hr
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hr | hreq | hr
    · obtain ⟨s, hs, h1, h2⟩ :=
        mergeStep_contain_acc acc p (fun q hq => hacc q hq p (List.mem_cons_self)) r hr
      obtain ⟨t, ht, h3, h4⟩ :=
        ih (mergeStep acc p) (mergeStep_order acc p rest (fun q hq p' hp' => hacc q hq p' (List.mem_cons_of_mem _ hp')) hhead) htail s
          (List.mem_append_left rest hs)
      exact ⟨t, ht, le_trans h3 h1, le_trans h2 h4⟩
    · rw [hreq]
      obtain ⟨s, hs, h1, h2⟩ :=
        mergeStep_contain_p acc p (fun q hq => hacc q hq p (List.mem_cons_self))
      obtain ⟨t, ht, h3, h4⟩ :=
        ih (mergeStep acc p) (mergeStep_order acc p rest (fun q hq p' hp' => hacc q hq p' (List.mem_cons_of_mem _ hp')) hhead) htail s
          (List.mem_append_left rest hs)
      exact ⟨t, ht, le_trans h3 h1, le_trans h2 h4⟩
    · exact ih (mergeStep acc p) (mergeStep_order acc p rest (fun q hq p' hp' => hacc q hq p' (List.mem_cons_of_mem _ hp')) hhead) htail r
        (List.mem_append_right _ hr)

theorem merged_valid (l : List (ℚ × ℚ)) (hv : ∀ p ∈ l, Vld p) :
    (Merged l).Pairwise (fun p q : ℚ × ℚ => p.2 < q.1) ∧ ∀ p ∈ Merged l, Vld p := by
  have hv' : ∀ p ∈ sortIv l, Vld p := fun p hp => hv p ((sortIv_mem l p).mp hp)
  exact ⟨mergeAcc_accsep (sortIv l) [] List.Pairwise.nil (by simp) (sortIv_sorted l)
      (by simp) hv',
    mergeAcc_vld (sortIv l) [] (by simp) hv'⟩

/-- Every interval of `l` is contained (closed hull) in some merged block of `Merged l`. -/
theorem merged_contain (l : List (ℚ × ℚ)) (r : ℚ × ℚ) (hr : r ∈ l) :
    ∃ s ∈ Merged l, s.1 ≤ r.1 ∧ r.2 ≤ s.2 :=
  mergeAcc_contain (sortIv l) [] (by simp) (sortIv_sorted l) r
    (by rw [List.nil_append]; exact (sortIv_mem l r).mpr hr)

/-- Every point of a merged block's closed hull lies in the closed hull of some input
interval (the reverse containment; needs no sortedness). -/
theorem mergeAcc_hullcover : ∀ (L : List (ℚ × ℚ)) (acc : List (ℚ × ℚ)) (x : ℚ),
    (∃ s ∈ mergeAcc acc L, s.1 ≤ x ∧ x ≤ s.2) →
      ∃ q ∈ acc ++ L, q.1 ≤ x ∧ x ≤ q.2 := by
  intro L
  induction L with
  | nil =>
    intro acc x hx
    obtain ⟨s, hs, h1, h2⟩ := hx
    rw [mergeAcc_nil, List.mem_reverse] at hs
    exact ⟨s, by rw [List.append_nil]; exact hs, h1, h2⟩
  | cons p rest ih =>
    intro acc x hx
    obtain ⟨t, ht, h1, h2⟩ := hx
    rw [mergeAcc_cons] at ht
    obtain ⟨q, hq, h3, h4⟩ := ih (mergeStep acc p) x ⟨t, ht, h1, h2⟩
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · -- q ∈ mergeStep acc p: find the source interval in acc ++ (p :: rest)
      rcases acc with _ | ⟨u, accU⟩
      · rw [mergeStep_nil] at hq
        simp at hq
        rw [show q = p from hq] at h3 h4
        exact ⟨p, List.mem_append_right _ List.mem_cons_self, h3, h4⟩
      · rw [mergeStep_cons] at hq
        by_cases hmrg : p.1 ≤ u.2
        · rw [if_pos hmrg] at hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq'
          · -- q = (u.1, max u.2 p.2): x ∈ [u.1, max u.2 p.2] lies in [u.1, u.2] or [p.1, p.2]
            by_cases hx' : x ≤ u.2
            · exact ⟨u, List.mem_append_left _ List.mem_cons_self, h3, hx'⟩
            · have hx'2 : u.2 < x := by linarith
              have hxmax : x ≤ max u.2 p.2 := h4
              have hmax : max u.2 p.2 = p.2 := by
                by_cases hle : p.2 ≤ u.2
                · rw [max_eq_left hle] at hxmax
                  exact absurd hxmax (by linarith)
                · exact max_eq_right (le_of_lt (by linarith : u.2 < p.2))
              exact ⟨p, List.mem_append_right _ List.mem_cons_self,
                le_trans hmrg (le_of_lt hx'2), le_trans hxmax hmax.le⟩
          · -- q ∈ accU ⊆ acc
            exact ⟨q, List.mem_append_left _ (List.mem_cons_of_mem _ hq'), h3, h4⟩
        · rw [if_neg hmrg] at hq
          simp only [List.mem_cons] at hq
          rcases hq with h1 | h2 | hq'
          · rw [h1] at h3 h4
            exact ⟨p, List.mem_append_right _ List.mem_cons_self, h3, h4⟩
          · rw [h2] at h3 h4
            exact ⟨u, List.mem_append_left _ List.mem_cons_self, h3, h4⟩
          · exact ⟨q, List.mem_append_left _ (List.mem_cons_of_mem _ hq'), h3, h4⟩
    · exact ⟨q, List.mem_append_right _ (List.mem_cons_of_mem _ hq), h3, h4⟩

/-- Endpoint extraction: a hull point of `acc ++ L` lying in no open interval of
`acc ++ L` is an endpoint of some interval of `acc ++ L`. -/
theorem mergeAcc_endpoints : ∀ (L : List (ℚ × ℚ)) (acc : List (ℚ × ℚ)),
    (∀ q ∈ acc, ∀ p ∈ L, q.1 ≤ p.1) → L.Pairwise (fun a b : ℚ × ℚ => a.1 ≤ b.1) →
    ∀ x : ℚ, (∃ q ∈ acc ++ L, q.1 ≤ x ∧ x ≤ q.2) →
      (∀ r ∈ acc ++ L, ¬ (r.1 < x ∧ x < r.2)) →
      ∃ q ∈ acc ++ L, x = q.1 ∨ x = q.2 := by
  intro L
  induction L with
  | nil =>
    intro acc _ _ x hx hz
    rw [List.append_nil] at hx hz ⊢
    obtain ⟨q, hq, h1, h2⟩ := hx
    by_cases hlt : q.1 < x
    · refine ⟨q, hq, Or.inr ?_⟩
      by_cases hlt2 : x < q.2
      · exact absurd ⟨hlt, hlt2⟩ (hz q hq)
      · exact le_antisymm h2 (not_lt.mp hlt2)
    · exact ⟨q, hq, Or.inl (le_antisymm (not_lt.mp hlt) h1)⟩
  | cons p rest ih =>
    intro acc hacc hpair x hx hz
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    have hord' : ∀ s ∈ mergeStep acc p, ∀ p' ∈ rest, s.1 ≤ p'.1 :=
      mergeStep_order acc p rest (fun q hq p' hp' => hacc q hq p' (List.mem_cons_of_mem _ hp')) hhead
    have hhull : ∃ s ∈ mergeStep acc p ++ rest, s.1 ≤ x ∧ x ≤ s.2 := by
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      obtain ⟨w, hw, hw1, hw2⟩ := hx
      rcases hw with hw | hwp | hw
      · obtain ⟨s, hs, h1, h2⟩ :=
          mergeStep_contain_acc acc p (fun q hq => hacc q hq p List.mem_cons_self) w hw
        exact ⟨s, Or.inl hs, le_trans h1 hw1, le_trans hw2 h2⟩
      · rw [hwp] at hw1 hw2
        obtain ⟨s, hs, h1, h2⟩ :=
          mergeStep_contain_p acc p (fun q hq => hacc q hq p List.mem_cons_self)
        exact ⟨s, Or.inl hs, le_trans h1 hw1, le_trans hw2 h2⟩
      · exact ⟨w, Or.inr hw, hw1, hw2⟩
    by_cases hz'' : ∀ r ∈ mergeStep acc p ++ rest, ¬ (r.1 < x ∧ x < r.2)
    · -- the recursive call applies; transport the endpoint witness back
      obtain ⟨t, ht, hw⟩ := ih (mergeStep acc p) hord' htail x hhull hz''
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · rcases acc with _ | ⟨u, accU⟩
        · rw [mergeStep_nil] at ht
          simp at ht
          rw [show t = p from ht] at hw
          exact ⟨p, by simp, hw⟩
        · rw [mergeStep_cons] at ht
          by_cases hmrg : p.1 ≤ u.2
          · rw [if_pos hmrg] at ht
            simp only [List.mem_cons] at ht
            rcases ht with rfl | ht'
            · rcases hw with hw | hw
              · exact ⟨u, List.mem_append_left _ List.mem_cons_self, Or.inl hw⟩
              · by_cases hle : p.2 ≤ u.2
                · have hxe : x = max u.2 p.2 := hw
                  rw [hxe, max_eq_left hle]
                  exact ⟨u, List.mem_append_left _ List.mem_cons_self, Or.inr rfl⟩
                · have hxe : x = max u.2 p.2 := hw
                  rw [hxe, max_eq_right (le_of_lt (by linarith : u.2 < p.2))]
                  exact ⟨p, List.mem_append_right _ List.mem_cons_self, Or.inr rfl⟩
            · exact ⟨t, List.mem_append_left _ (List.mem_cons_of_mem _ ht'), hw⟩
          · rw [if_neg hmrg] at ht
            simp only [List.mem_cons] at ht
            rcases ht with h1 | h2 | ht'
            · rw [h1] at hw
              exact ⟨p, List.mem_append_right _ List.mem_cons_self, hw⟩
            · rw [h2] at hw
              exact ⟨u, List.mem_append_left _ List.mem_cons_self, hw⟩
            · exact ⟨t, List.mem_append_left _ (List.mem_cons_of_mem _ ht'), hw⟩
      · exact ⟨t, List.mem_append_right _ (List.mem_cons_of_mem _ ht), hw⟩
    · -- x lies in some open interval of the folded list: push back through the merge.
      -- A kept block or `p` contradicts `hz`; the merged block forces x = u.2, the
      -- touching boundary, which is an endpoint of u.
      simp only [not_forall, not_imp_not, not_not] at hz''
      obtain ⟨r, hr, hc1, hc2⟩ := hz''
      simp only [List.mem_append, List.mem_cons] at hr
      rcases hr with hr | hr
      · rcases acc with _ | ⟨u, accU⟩
        · rw [mergeStep_nil] at hr
          simp at hr
          rw [hr] at hc1 hc2
          exact absurd ⟨hc1, hc2⟩ (hz p (by simp))
        · rw [mergeStep_cons] at hr
          by_cases hmrg : p.1 ≤ u.2
          · rw [if_pos hmrg] at hr
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr'
            · -- r = (u.1, max u.2 p.2): touching-boundary analysis forces x = u.2
              by_cases hxc : x ≤ u.2
              · have hu' := hz u (by simp)
                have hx2 : x = u.2 := by
                  by_cases hx2' : x < u.2
                  · exact absurd ⟨hc1, hx2'⟩ hu'
                  · exact le_antisymm hxc (not_lt.mp hx2')
                exact ⟨u, by simp, Or.inr hx2⟩
              · have hx'2 : u.2 < x := by linarith
                have hp' := hz p (by simp)
                have hxlt : x < max u.2 p.2 := hc2
                by_cases hle : p.2 ≤ u.2
                · have hmax : max u.2 p.2 = u.2 := max_eq_left hle
                  rw [hmax] at hxlt
                  linarith
                · have hmax : max u.2 p.2 = p.2 := max_eq_right (le_of_lt (by linarith : u.2 < p.2))
                  rw [hmax] at hxlt
                  exact absurd ⟨lt_of_le_of_lt hmrg hx'2, hxlt⟩ hp'
            · exact absurd ⟨hc1, hc2⟩
                (hz r (by simp only [List.mem_append]; exact Or.inl (List.mem_cons_of_mem _ hr')))
          · rw [if_neg hmrg] at hr
            simp only [List.mem_cons] at hr
            rcases hr with h1 | h2 | hr'
            · rw [h1] at hc1 hc2
              exact absurd ⟨hc1, hc2⟩ (hz p (by simp))
            · rw [h2] at hc1 hc2
              exact absurd ⟨hc1, hc2⟩ (hz u (by simp))
            · exact absurd ⟨hc1, hc2⟩
                (hz r (by simp only [List.mem_append]; exact Or.inl (List.mem_cons_of_mem _ hr')))
      · exact absurd ⟨hc1, hc2⟩ (hz r (by simp only [List.mem_append]; exact Or.inr (List.mem_cons_of_mem _ hr)))

/-! ## §4 The walk lemmas -/

theorem walk_ge : ∀ (L : List (ℚ × ℚ)) (cur : ℚ) (s : ℚ × ℚ), s ∈ K6Walk cur L → cur ≤ s.1 := by
  intro L
  induction L with
  | nil =>
    intro cur s hs
    rw [K6Walk_nil] at hs
    split at hs
    · simp at hs
      subst hs
      exact le_refl _
    · simp at hs
  | cons q rest ih =>
    intro cur s hs
    rw [K6Walk_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · split at hs
      · simp at hs
        subst hs
        exact le_refl _
      · simp at hs
    · exact le_trans (le_max_left cur q.2) (ih (max cur q.2) s hs)

theorem walk_final : ∀ (L : List (ℚ × ℚ)) (cur : ℚ), (∀ p ∈ L, p.2 < 7) → cur < 7 →
    ∃ s ∈ K6Walk cur L, s.1 ≤ 7 ∧ 7 ≤ s.2 := by
  intro L
  induction L with
  | nil =>
    intro cur _ hcur
    rw [K6Walk_nil, if_pos hcur]
    exact ⟨(cur, 7), List.mem_cons_self, hcur.le, le_refl _⟩
  | cons q rest ih =>
    intro cur hL hcur
    obtain ⟨s, hs, h1, h2⟩ :=
      ih (max cur q.2)
        (fun p hp => hL p (List.mem_cons_of_mem _ hp))
        (max_lt hcur (hL q List.mem_cons_self))
    exact ⟨s, by rw [K6Walk_cons]; exact List.mem_append_right _ hs, h1, h2⟩

/-- **W2 (components are lonely).**  For a strictly separated list of clipped intervals,
every point of a walked component is ≥ cur, ≤ 7, and lies in no open interval of the
list. -/
theorem walk_lonely : ∀ (L : List (ℚ × ℚ)), L.Pairwise (fun p q : ℚ × ℚ => p.2 < q.1) →
    (∀ p ∈ L, Vld p) → ∀ (cur x : ℚ) (s : ℚ × ℚ), s ∈ K6Walk cur L → s.1 ≤ x ∧ x ≤ s.2 →
    cur ≤ x ∧ x ≤ 7 ∧ ¬ MemZone x L := by
  intro L
  induction L with
  | nil =>
    intro _ _ cur x s hs hmem
    rw [K6Walk_nil] at hs
    split at hs
    · simp at hs
      subst hs
      exact ⟨hmem.1, hmem.2, by simp [MemZone]⟩
    · simp at hs
  | cons q rest ih =>
    intro hsep hv cur x s hs hmem
    obtain ⟨hsephead, hseptail⟩ := List.pairwise_cons.mp hsep
    rw [K6Walk_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · split at hs
      · simp at hs
        subst hs
        have h1 : cur ≤ x := hmem.1
        have h2 : x ≤ q.1 := hmem.2
        refine ⟨h1, ?_, ?_⟩
        · have hq := hv q List.mem_cons_self
          exact le_trans (le_trans h2 (le_of_lt hq.2.1)) hq.2.2
        · intro hz
          simp only [MemZone, List.mem_cons] at hz
          obtain ⟨p, hp, h4, h5⟩ := hz
          rcases hp with hp1 | hp
          · rw [hp1] at h4 h5
            linarith
          · linarith [hsephead p hp, h2, (hv q List.mem_cons_self).2.1]
      · simp at hs
    · obtain ⟨h1, h2, h3⟩ :=
        ih hseptail (fun p hp => hv p (List.mem_cons_of_mem _ hp)) (max cur q.2) x s hs hmem
      refine ⟨le_trans (le_max_left cur q.2) h1, h2, ?_⟩
      intro hz
      simp only [MemZone, List.mem_cons] at hz
      obtain ⟨p, hp, h4, h5⟩ := hz
      rcases hp with hp1 | hp
      · rw [hp1] at h4 h5
        linarith [le_max_right cur q.2]
      · exact h3 ⟨p, hp, h4, h5⟩

/-- **W1'' (the walk covers the lonely set).**  For a strictly separated list of clipped
intervals: a point `x` with `cur ≤ x < 7` in no open interval of the list is either in a
walked component, or is the artifact `x = cur` with some interval starting exactly at
`x` (at `cur = 1` this is the `x = 1` boundary artifact). -/
theorem walk_cover : ∀ (L : List (ℚ × ℚ)), L.Pairwise (fun p q : ℚ × ℚ => p.2 < q.1) →
    (∀ p ∈ L, Vld p) → ∀ (cur x : ℚ), cur ≤ x → x < 7 → ¬ MemZone x L →
    MemComp x (K6Walk cur L) ∨ (x = cur ∧ ∃ q ∈ L, q.1 = x) := by
  intro L
  induction L with
  | nil =>
    intro _ _ cur x hle hlt7 _
    refine Or.inl ⟨(cur, 7), ?_, hle, le_of_lt hlt7⟩
    rw [K6Walk_nil, if_pos (lt_of_le_of_lt hle hlt7)]
    exact List.mem_cons_self
  | cons q rest ih =>
    intro hsep hv cur x hle hlt7 hz
    obtain ⟨hsephead, hseptail⟩ := List.pairwise_cons.mp hsep
    have hzq : ¬ (q.1 < x ∧ x < q.2) := fun hc => hz ⟨q, List.mem_cons_self, hc.1, hc.2⟩
    rw [K6Walk_cons]
    simp only [MemComp, List.mem_append]
    by_cases hxq : x ≤ q.1
    · by_cases hcq : q.1 > cur
      · refine Or.inl ⟨(cur, q.1), ?_, hle, hxq⟩
        rw [if_pos hcq]
        exact Or.inl List.mem_cons_self
      · refine Or.inr ⟨?_, q, List.mem_cons_self, ?_⟩
        · exact le_antisymm (le_trans hxq (le_of_not_gt hcq)) hle
        · exact le_antisymm (le_trans (le_of_not_gt hcq) hle) hxq
    · have hq1lt : q.1 < x := by linarith
      have hxq2 : q.2 ≤ x := le_of_not_gt (fun hlt : x < q.2 => hzq ⟨hq1lt, hlt⟩)
      have hcur' : max cur q.2 ≤ x := max_le hle hxq2
      have hzrest : ¬ MemZone x rest := by
        rintro ⟨p, hp, h4, h5⟩
        exact hz ⟨p, List.mem_cons_of_mem _ hp, h4, h5⟩
      rcases ih hseptail (fun p hp => hv p (List.mem_cons_of_mem _ hp))
        (max cur q.2) x hcur' hlt7 hzrest with hres | ⟨hxc, t, ht, htx⟩
      · obtain ⟨s, hs, h1, h2⟩ := hres
        exact Or.inl ⟨s, Or.inr hs, h1, h2⟩
      · refine Or.inr ⟨?_, t, List.mem_cons_of_mem _ ht, htx⟩
        by_cases hc2 : cur ≤ q.2
        · exfalso
          have hmax : max cur q.2 = q.2 := max_eq_right hc2
          have htx' : t.1 = x := htx
          rw [hxc, hmax] at htx'
          have := hsephead t ht
          rw [htx'] at this
          exact lt_irrefl _ this
        · exact hxc.trans (max_eq_left (le_of_lt (by linarith : q.2 < cur)))

/-! ## §5 Main theorems -/

/-- **Step 2, direction ⟹ (components are lonely).**  Every point of a K6 component of
`[1, 7]` is `≥ 1`, `≤ 7`, and lies in NO open tooth zone of any of the five readings.
No hypotheses on the readings (clipping makes every list entry valid by the filter). -/
theorem comps_lonely (rho : Fin 5 → ℚ) (x : ℚ) (h : MemComp x (K6Comps rho)) :
    1 ≤ x ∧ x ≤ 7 ∧ ¬ MemZone x (zonesAll rho) := by
  obtain ⟨hsep, hvld⟩ := merged_valid (zonesAll rho) (zonesAll_valid rho)
  obtain ⟨s, hs, h1, h2⟩ := h
  obtain ⟨h3, h4, h5⟩ :=
    walk_lonely _ hsep hvld 1 x s (by simpa only [K6Comps] using hs) ⟨h1, h2⟩
  refine ⟨h3, h4, ?_⟩
  rintro ⟨p, hp, h6, h7⟩
  obtain ⟨t, ht, h8, h9⟩ := merged_contain (zonesAll rho) p hp
  exact h5 ⟨t, ht, lt_of_le_of_lt h8 h6, lt_of_lt_of_le h7 h9⟩

/-- **Step 2, direction ⟸ (lonely ⟹ component, up to the two boundary artifacts).**
For `x ∈ [1, 7]` in no open zone of the merged union: `x` is in a component, or `x = 1`
with a merged block starting exactly at 1, or `x = 7` with a merged block ending exactly
at 7. -/
theorem lonely_comp_or_artifact (rho : Fin 5 → ℚ) (x : ℚ) (h1 : 1 ≤ x) (h7 : x ≤ 7)
    (hz : ¬ MemZone x (Merged (zonesAll rho))) :
    MemComp x (K6Comps rho)
      ∨ (x = 1 ∧ ∃ p ∈ Merged (zonesAll rho), p.1 = 1)
      ∨ (x = 7 ∧ ∃ p ∈ Merged (zonesAll rho), p.2 = 7) := by
  obtain ⟨hsep, hvld⟩ := merged_valid (zonesAll rho) (zonesAll_valid rho)
  by_cases hx7 : x < 7
  · rcases walk_cover _ hsep hvld 1 x h1 hx7 hz with hres | ⟨hxc, t, ht, htx⟩
    · exact Or.inl hres
    · exact Or.inr (Or.inl ⟨hxc, t, ht, htx.trans hxc⟩)
  · have hx7' : x = 7 := le_antisymm h7 (not_lt.mp hx7)
    subst hx7'
    by_cases hmax7 : ∃ p ∈ Merged (zonesAll rho), p.2 = 7
    · exact Or.inr (Or.inr ⟨rfl, hmax7⟩)
    · have hall : ∀ p ∈ Merged (zonesAll rho), p.2 < 7 := fun p hp =>
        lt_of_le_of_ne (hvld p hp).2.2 (fun hpe => hmax7 ⟨p, hp, hpe⟩)
      obtain ⟨s, hs, h1', h2'⟩ := walk_final _ 1 hall (by norm_num)
      exact Or.inl ⟨s, hs, h1', h2'⟩

/-- Step 2, direction ⟸, against the raw five-reading zone list: the symmetric difference
between "component" and "in no open zone of any reading" is contained in `{1, 7}` plus
the touching boundaries (which ARE open-interior points of merged blocks). -/
theorem lonely_comp_or_artifact' (rho : Fin 5 → ℚ) (x : ℚ) (h1 : 1 ≤ x) (h7 : x ≤ 7)
    (hz : ¬ MemZone x (zonesAll rho)) :
    MemComp x (K6Comps rho) ∨ x = 1 ∨ x = 7 ∨ MemZone x (Merged (zonesAll rho)) := by
  by_cases hm : MemZone x (Merged (zonesAll rho))
  · exact Or.inr (Or.inr (Or.inr hm))
  · rcases lonely_comp_or_artifact rho x h1 h7 hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr (Or.inl h.1))

/-- **Step 3 (task shape, blocked-witness form).**  Under the honest extra band
hypothesis that `x` lies in no open zone of the MERGED union (this excludes the touching
boundaries), a non-component point of `[1, 7]` with `x ≠ 1 ≠ 7` cannot exist, so the
witness conclusion follows in the bounded tooth form
`∃ i j, 1 ≤ j ≤ 15 ∧ (8j-1)/ρᵢ < x < (8j+1)/ρᵢ`. -/
theorem blocked_witness_bounded (rho : Fin 5 → ℚ) (x : ℚ) (h1 : 1 ≤ x) (h7 : x ≤ 7)
    (hc : ¬ MemComp x (K6Comps rho)) (hx1 : x ≠ 1) (hx7 : x ≠ 7)
    (hm : ¬ MemZone x (Merged (zonesAll rho))) :
    ∃ (i : Fin 5) (j : ℕ), 1 ≤ j ∧ j ≤ 15 ∧
      (8 * j - 1 : ℚ) / rho i < x ∧ x < (8 * j + 1 : ℚ) / rho i := by
  rcases lonely_comp_or_artifact rho x h1 h7 hm with h | ⟨hxc, _, _⟩ | ⟨hx77, _, _⟩
  · exact absurd h hc
  · exact absurd hxc hx1
  · exact absurd hx77 hx7

/-- **Step 3 (honest form).**  A non-component point of `[1, 7]` with `x ≠ 1 ≠ 7` that
lies in no open zone of any reading is a TOUCHING BOUNDARY: it is an open-interior point
of some merged block AND an endpoint of some clipped zone. -/
theorem blocked_or_touching (rho : Fin 5 → ℚ) (x : ℚ) (h1 : 1 ≤ x) (h7 : x ≤ 7)
    (hc : ¬ MemComp x (K6Comps rho)) (hx1 : x ≠ 1) (hx7 : x ≠ 7)
    (hz : ¬ MemZone x (zonesAll rho)) :
    (∃ s ∈ Merged (zonesAll rho), s.1 < x ∧ x < s.2) ∧
      (∃ q ∈ zonesAll rho, x = q.1 ∨ x = q.2) := by
  by_cases hm : MemZone x (Merged (zonesAll rho))
  · refine ⟨hm, ?_⟩
    obtain ⟨s, hs, h4, h5⟩ := hm
    -- x is in the closed hull of the merged block s; hullcover pulls it into a zone hull
    have hxhull : ∃ q ∈ sortIv (zonesAll rho), q.1 ≤ x ∧ x ≤ q.2 := by
      have hstep := mergeAcc_hullcover (sortIv (zonesAll rho)) [] x
        ⟨s, hs, le_of_lt h4, le_of_lt h5⟩
      simpa using hstep
    have hstep := mergeAcc_endpoints (sortIv (zonesAll rho)) [] (by simp) (sortIv_sorted _) x
      hxhull
      (by
        intro r hr
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact absurd hr (by simp)
        · intro hc
          exact hz ⟨r, (sortIv_mem (zonesAll rho) r).mp hr, hc.1, hc.2⟩)
    obtain ⟨q, hq, hwe⟩ := hstep
    exact ⟨q, (sortIv_mem (zonesAll rho) q).mp (by simpa using hq), hwe⟩
  · rcases lonely_comp_or_artifact rho x h1 h7 hm with h | ⟨hxc, _, _⟩ | ⟨hx77, _, _⟩
    · exact absurd h hc
    · exact absurd hxc hx1
    · exact absurd hx77 hx7

/-! ### Bridge lemmas for β (tooth predicate ↔ ZonesOf membership) -/

/-- Bridge lemma: membership in an open zone of reading `r` as a `ZonesOf` entry ↔ the
tooth predicate with lap bound `1 ≤ j ≤ 15`.  Requires `1 < x < 7` (the clipped blind
spots are exactly the endpoints 1 and 7).  No hypotheses on `r`. -/
theorem zone_open_iff (r : ℚ) (x : ℚ) (hx1 : 1 < x) (hx7 : x < 7) :
    (∃ p ∈ ZonesOf r, p.1 < x ∧ x < p.2) ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ 15 ∧ (8 * j - 1 : ℚ) / r < x ∧ x < (8 * j + 1 : ℚ) / r := by
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    simp only [ZonesOf, List.mem_filterMap, List.mem_range] at hp
    obtain ⟨k, hk, hk'⟩ := hp
    by_cases hC : max (((8 * k + 7 : ℕ) : ℚ) / r) 1 < min (((8 * k + 9 : ℕ) : ℚ) / r) 7
    · rw [if_pos hC] at hk'
      injection hk' with hk'
      subst hk'
      refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
      · simp only [Nat.cast_add, Nat.cast_one]
        have hid : (8 * (↑k + 1) - 1 : ℚ) = ((8 * k + 7 : ℕ) : ℚ) := by push_cast; ring
        rw [hid]
        exact lt_of_le_of_lt (le_max_left _ _) h1
      · simp only [Nat.cast_add, Nat.cast_one]
        have hid : (8 * (↑k + 1) + 1 : ℚ) = ((8 * k + 9 : ℕ) : ℚ) := by push_cast; ring
        rw [hid]
        exact lt_of_lt_of_le h2 (min_le_left _ _)
    · rw [if_neg hC] at hk'
      exact absurd hk' (by simp)
  · rintro ⟨j, hj1, hj15, h1, h2⟩
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    subst hk
    have hA : ((8 * k + 7 : ℕ) : ℚ) / r < x := by
      have hid : (8 * (↑k + 1) - 1 : ℚ) = ((8 * k + 7 : ℕ) : ℚ) := by push_cast; ring
      simp only [Nat.cast_add, Nat.cast_one] at h1
      rw [hid] at h1
      exact h1
    have hB : x < ((8 * k + 9 : ℕ) : ℚ) / r := by
      have hid : (8 * (↑k + 1) + 1 : ℚ) = ((8 * k + 9 : ℕ) : ℚ) := by push_cast; ring
      simp only [Nat.cast_add, Nat.cast_one] at h2
      rw [hid] at h2
      exact h2
    refine ⟨(max (((8 * k + 7 : ℕ) : ℚ) / r) 1, min (((8 * k + 9 : ℕ) : ℚ) / r) 7), ?_, ?_, ?_⟩
    · simp only [ZonesOf, List.mem_filterMap, List.mem_range]
      refine ⟨k, by omega, ?_⟩
      rw [if_pos (max_lt (lt_min (lt_trans hA hB) (lt_of_lt_of_le hA (le_of_lt hx7)))
        (lt_min (lt_of_le_of_lt (le_of_lt hx1) hB) (by norm_num)))]
    · exact max_lt hA hx1
    · exact lt_min hB hx7

/-- Bridge lemma, unbounded-lap form: the raw tooth predicate `∃ j ≥ 1,
(8j-1)/r < x < (8j+1)/r` matches `ZonesOf r` membership for `1 < x < 7` provided
`r ≤ 17` (then any tooth meeting `[1, 7]` has `8j - 1 < 7r ≤ 119`, i.e. `j ≤ 14`). -/
theorem zone_open_unbounded_iff (r : ℚ) (hr : r ≤ 17) (x : ℚ) (hx1 : 1 < x) (hx7 : x < 7) :
    (∃ j : ℕ, 1 ≤ j ∧ (8 * j - 1 : ℚ) / r < x ∧ x < (8 * j + 1 : ℚ) / r) ↔
      ∃ p ∈ ZonesOf r, p.1 < x ∧ x < p.2 := by
  constructor
  · rintro ⟨j, hj1, h1, h2⟩
    have hxpos : (0 : ℚ) < x := lt_of_le_of_lt (by norm_num) hx1
    have hBpos : (0 : ℚ) < (8 * j + 1 : ℚ) := by
      have hjq : (0 : ℚ) < (j : ℚ) := Nat.cast_pos.mpr (by omega)
      linarith
    have hr0 : 0 < r := by
      have h1' : (0 : ℚ) < (8 * j + 1 : ℚ) / r :=
        lt_trans (show (0 : ℚ) < 1 by norm_num) (lt_trans hx1 h2)
      rcases (div_pos_iff (a := (8 * j + 1 : ℚ)) (b := r)).mp h1' with ⟨_, hb⟩ | ⟨hn, _⟩
      · exact hb
      · linarith [hBpos]
    have hj15 : j ≤ 15 := by
      have hlt : (8 * j - 1 : ℚ) / r < 7 := lt_of_lt_of_le h1 (le_of_lt hx7)
      have hc : (8 * j - 1 : ℚ) < 7 * r := by
        have h2 := mul_lt_mul_of_pos_right hlt hr0
        rwa [div_mul_cancel₀ _ (ne_of_gt hr0)] at h2
      have h7r : (7 : ℚ) * r ≤ 119 := by
        have h2 := mul_le_mul_of_nonneg_left hr (show (0 : ℚ) ≤ 7 by norm_num)
        norm_num at h2
        exact h2
      have hjq : (j : ℚ) < 15 := by linarith
      have hnat : j < 15 := Nat.cast_lt.mp hjq
      omega
    exact (zone_open_iff r x hx1 hx7).mpr ⟨j, hj1, hj15, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩
    obtain ⟨j, hj1, hj15, h1', h2'⟩ := (zone_open_iff r x hx1 hx7).mp ⟨p, hp, h1, h2⟩
    exact ⟨j, hj1, h1', h2'⟩

/-! ## §6 Axiom footprints -/

#print axioms zonesEx_2
#print axioms zonesEx_3
#print axioms zonesEx_4
#print axioms zonesEx_6
#print axioms zonesEx_8
#print axioms mergedEx
#print axioms compsEx
#print axioms comps_lonely
#print axioms lonely_comp_or_artifact
#print axioms lonely_comp_or_artifact'
#print axioms blocked_witness_bounded
#print axioms blocked_or_touching
#print axioms zone_open_iff
#print axioms zone_open_unbounded_iff
