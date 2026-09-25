import LonelyRunner.LRC.Spec.OrderEightCasesN

/-!
# Order eight: the skeleton of the proof, with every hole named

2026-09-25.  Scale invariance fixes the scale up to one factor, so a whole-number disparity set is
its ratios.  Split on **separation of scale** with threshold `T`:

* **separated** (`Separated8 T S`): the set splits into a slow core `C` and a fast block `F` with
  `T·c ≤ x` for every `c ∈ C`, `x ∈ F`;
* **scale-free**: otherwise.  Every consecutive ratio is then below `T`.

Every set is one or the other, so the split cannot leak.  The proof then asks, for each block size
`f`, that every separated set with a block of `f` runners be lonely (`BlockRule8 f T`), and that
every scale-free set be lonely (`BoundedCovered8 T`).  `lonelyRunnerAt8_of_skeleton` proves that
these give the conjecture.  At `T = 9` the block sizes 1 and 2 are **discharged**: R8 carries a
block of one (`blockRule8_one`) and the fast pair a block of two (`blockRule8_two`).  So the
conjecture at eight runners follows from exactly five named statements (`lonelyRunnerAt8_of_holes`):

| hole | what is in hand toward it |
|---|---|
| `BlockRule8 3 9`, `BlockRule8 4 9` | block split (common factor), synchronised block at the seventh; window constants measured, not proved |
| `BlockRule8 5 9`, `BlockRule8 6 9` | block split; synchronised block at the seventh (cores not divisible by 7); general R owed; unsynchronised blocks: none |
| `BoundedCovered8 9` | the case list of `OrderEightCasesN`; the two-pinner lemma at tight points; the finite cover not built |

These are **OWED**: asserted nowhere, used only as hypotheses.  None of them adds a requirement to
the conjecture: each is a family of instances of it.

**The cascade's own route** is recorded beside this one, not replaced by it: `LRC.Spec.DoorFAM`
(each runner is in the way at only finitely many cascade steps) is equivalent to loneliness at every
subject (`LRC.Spec.doors_agree`).  The rules above are proofs that the cascade arrives for whole
families at once; they name a scale no later than the one the cascade finds.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.Order8Skeleton

open LRC.OrderEightN

/-- Lonely at `1/8`, for a whole-number disparity set. -/
def Lonely8 (S : Finset ℕ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)

/-- **Separated at ratio `T`**: some threshold `m` splits the set into a nonempty slow part
`{d ≤ m}` and a nonempty fast part `{d > m}` with `T·c ≤ x` across the split. -/
def Separated8 (T : ℕ) (S : Finset ℕ) : Prop :=
  ∃ m : ℕ, (S.filter (· ≤ m)).Nonempty ∧ (S.filter (m < ·)).Nonempty ∧
    ∀ c ∈ S.filter (· ≤ m), ∀ x ∈ S.filter (m < ·), T * c ≤ x

/-- **The block rule for blocks of `f` runners** (OWED for `f ≥ 3`): a nonempty core `C` below a
block `F` of `f` runners, `T·c ≤ x` across, at most seven in all, is lonely. -/
def BlockRule8 (f T : ℕ) : Prop :=
  ∀ C F : Finset ℕ, (∀ d ∈ C, 0 < d) → (∀ d ∈ F, 0 < d) → F.card = f → C.card + F.card ≤ 7 →
    C.Nonempty → (∀ c ∈ C, ∀ x ∈ F, T * c ≤ x) → Lonely8 (C ∪ F)

/-- **The bounded region** (OWED): every scale-free set of at most seven is lonely. -/
def BoundedCovered8 (T : ℕ) : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ 7 → ¬ Separated8 T S → Lonely8 S

/-- **The skeleton.**  Block rules for every block size `1 … 6` and the bounded region give every
whole-number set of at most seven. -/
theorem lonely8_of_skeleton {T : ℕ} (hblock : ∀ f, 1 ≤ f → f ≤ 6 → BlockRule8 f T)
    (hbounded : BoundedCovered8 T) (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7) :
    Lonely8 S := by
  classical
  by_cases hsep : Separated8 T S
  · obtain ⟨m, hCne, hFne, hsplit⟩ := hsep
    set C := S.filter (· ≤ m)
    set F := S.filter (m < ·)
    have hunion : C ∪ F = S := by
      ext d; simp only [C, F, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h; by_cases hd : d ≤ m
        · exact Or.inl ⟨h, hd⟩
        · exact Or.inr ⟨h, by omega⟩
    have hcardsum : C.card + F.card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · rw [hunion]
      · rw [Finset.disjoint_left]; intro d hd hd'
        simp only [C, F, Finset.mem_filter] at hd hd'; omega
    have hF1 : 1 ≤ F.card := Finset.card_pos.mpr hFne
    have hC1 : 1 ≤ C.card := Finset.card_pos.mpr hCne
    have hl := hblock F.card hF1 (by omega) C F
      (fun d hd => hpos d (Finset.mem_of_mem_filter d hd))
      (fun d hd => hpos d (Finset.mem_of_mem_filter d hd)) rfl (by omega) hCne hsplit
    rwa [hunion] at hl
  · exact hbounded S hpos hcard hsep

/-- **The conjecture at eight runners from the skeleton.** -/
theorem lonelyRunnerAt8_of_skeleton {T : ℕ} (hblock : ∀ f, 1 ≤ f → f ≤ 6 → BlockRule8 f T)
    (hbounded : BoundedCovered8 T) : LRC.Spec.LonelyRunnerAt8 :=
  LRC.Spec.lonelyRunnerAt8_of_existence
    (existenceAt8_of_nat fun S hpos hcard => lonely8_of_skeleton hblock hbounded S hpos hcard)

/-- **Block of one, discharged** at `T = 9`: R8. -/
theorem blockRule8_one : BlockRule8 1 9 := by
  classical
  intro C F hC hF hFc hcard _ hsep
  obtain ⟨V, rfl⟩ := Finset.card_eq_one.mp hFc
  have hVpos := hF V (Finset.mem_singleton_self V)
  refine lonely_eight_of_fast (S := C ∪ {V}) ?_ (le_trans (Finset.card_union_le _ _) (by simpa using hcard))
    (Finset.mem_union_right _ (Finset.mem_singleton_self V)) ?_
  · intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact hC d h
    · exact hF d h
  · intro s hs hsV
    rcases Finset.mem_union.mp hs with h | h
    · have := hsep s h V (Finset.mem_singleton_self V); have := hC s h; omega
    · exact absurd (Finset.mem_singleton.mp h) hsV

/-- **Block of two, discharged** at `T = 9`: the fast pair. -/
theorem blockRule8_two : BlockRule8 2 9 := by
  classical
  intro C F hC hF hFc hcard hCne hsep
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hFc
  -- order the pair
  wlog hlt : a < b generalizing a b
  · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
    have := this b a (Ne.symm hab) (by rwa [Finset.pair_comm] at hF)
      (by rwa [Finset.pair_comm] at hFc) (by rwa [Finset.pair_comm] at hcard)
      (by intro c hc x hx; rw [Finset.pair_comm] at hx; exact hsep c hc x hx) hba
    rwa [Finset.pair_comm] at this
  have ha := hsep
  have hCm : ∀ c ∈ C, c ≤ a / 9 := by
    intro c hc; rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := hsep c hc a (by simp); omega
  have hCcard : C.card ≤ 5 := by
    have : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
    omega
  obtain ⟨t, ht, hCl, hal, hbl⟩ := LRC.FastPairEight.lonely_eight_of_fast_pair hC hCcard hCne hCm
    hlt.le (Nat.mul_div_le a 9)
  refine ⟨t, ht, fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with h | h
  · exact hCl d h
  · rcases Finset.mem_insert.mp h with h | h
    · rw [h]; exact hal
    · rw [Finset.mem_singleton.mp h]; exact hbl

/-- **The conjecture at eight runners from exactly five named holes.** -/
theorem lonelyRunnerAt8_of_holes (h3 : BlockRule8 3 9) (h4 : BlockRule8 4 9) (h5 : BlockRule8 5 9)
    (h6 : BlockRule8 6 9) (hB : BoundedCovered8 9) : LRC.Spec.LonelyRunnerAt8 := by
  refine lonelyRunnerAt8_of_skeleton (T := 9) (fun f hf1 hf6 => ?_) hB
  interval_cases f
  · exact blockRule8_one
  · exact blockRule8_two
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end LRC.Order8Skeleton
