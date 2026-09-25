import LonelyRunner.LRC.Spec.OrderEightCasesN

/-!
# Order eight: the skeleton of the proof, with every hole named

2026-09-25.  Scale invariance fixes the scale up to one factor, so a whole-number disparity set is
its ratios.  Split on **separation of scale** with threshold `T`:

* **separated** (`Separated8 T S`): a runner's readings split into a slow core `C` and a fast block
  `F` with `T·c ≤ x` for every `c ∈ C`, `x ∈ F`;
* **scale-free**: otherwise.  Every consecutive ratio is then below `T`.

**Frame (restated 2026-09-25, `MANUSCRIPT_v21` §1.1).**  The owed statements quantify over
**arrangements** of eight distinct positive speeds and over **every runner** `k`, and apply the split
to that runner's own readings `readingsOf v k` (`|v_j − v_k|`, what "`k` is lonely" means).  No runner
is held at rest: a set of seven readings is realised as the readings of the runner at speed `1` in the
arrangement `(1, 1 + s₁, …, 1 + s₇)` (`readingsOf_cons`).  The earlier statement over bare difference
sets is withdrawn.

Every set is one or the other, so the split cannot leak.  The proof then asks, for each block size
`f`, that every runner whose readings are separated with a block of `f` be lonely (`ArrBlockRule8 f T`), and
that every runner whose readings are scale-free be lonely (`ArrBoundedCovered8 T`).  At `T = 9` the
block sizes 1 and 2 are **discharged** as lemmas about a runner's readings: R8 carries a block of one
(`blockRule8_one`) and the fast pair a block of two (`blockRule8_two`).  So the conjecture at eight
runners follows from exactly five named statements (`lonelyRunnerAt8_of_arrangement_holes`):

| hole | what is in hand toward it |
|---|---|
| `ArrBlockRule8 3 9`, `ArrBlockRule8 4 9` | block split (common factor), synchronised block at the seventh; window constants measured, not proved |
| `ArrBlockRule8 5 9`, `ArrBlockRule8 6 9` | block split; synchronised block at the seventh (cores not divisible by 7); general R owed; unsynchronised blocks: none |
| `ArrBoundedCovered8 9` | the case list of `OrderEightCasesN`; the two-pinner lemma at tight points; the finite cover not built |

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

/-- **The block rule, as a lemma about one runner's readings**: a nonempty core `C` below a block `F`
of `f` readings, `T·c ≤ x` across, at most seven in all, is lonely.  Proved for `f = 1, 2` at `T = 9`. -/
def BlockRule8 (f T : ℕ) : Prop :=
  ∀ C F : Finset ℕ, (∀ d ∈ C, 0 < d) → (∀ d ∈ F, 0 < d) → F.card = f → C.card + F.card ≤ 7 →
    C.Nonempty → (∀ c ∈ C, ∀ x ∈ F, T * c ≤ x) → Lonely8 (C ∪ F)

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

/-- A runner's own readings in an arrangement: `|v_j − v_k|` for the other seven. -/
def readingsOf (v : Fin 8 → ℕ) (k : Fin 8) : Finset ℕ :=
  (Finset.univ.erase k).image (fun i => Nat.dist (v i) (v k))

/-- An arrangement: eight distinct positive speeds.  No runner is at rest. -/
def Arr8 (v : Fin 8 → ℕ) : Prop := (∀ i, 0 < v i) ∧ Function.Injective v

/-- **The block rule on arrangements** (OWED for `f ≥ 3`): every runner of every arrangement whose
readings split at `m` into a nonempty core below and a block of `f` above, `T·c ≤ x` across, is lonely. -/
def ArrBlockRule8 (f T : ℕ) : Prop :=
  ∀ v : Fin 8 → ℕ, Arr8 v → ∀ k : Fin 8, ∀ m : ℕ,
    ((readingsOf v k).filter (· ≤ m)).Nonempty → ((readingsOf v k).filter (m < ·)).card = f →
    (∀ c ∈ (readingsOf v k).filter (· ≤ m), ∀ x ∈ (readingsOf v k).filter (m < ·), T * c ≤ x) →
    Lonely8 (readingsOf v k)

/-- **The bounded region on arrangements** (OWED): every runner of every arrangement whose readings
are scale-free is lonely. -/
def ArrBoundedCovered8 (T : ℕ) : Prop :=
  ∀ v : Fin 8 → ℕ, Arr8 v → ∀ k : Fin 8, ¬ Separated8 T (readingsOf v k) → Lonely8 (readingsOf v k)

/-- The arrangement `(1, 1 + s₁, …, 1 + s₇)`: every speed positive, all distinct. -/
theorem arr8_cons (S : Finset ℕ) (hS : S.card = 7) (hpos : ∀ d ∈ S, 0 < d) :
    Arr8 (Fin.cons 1 (fun i : Fin 7 => 1 + S.orderEmbOfFin hS i)) := by
  refine ⟨fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ]; omega
  · refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨j, hj⟩
      simp only at hj
      have := hpos _ (Finset.orderEmbOfFin_mem S hS j); omega
    · intro a b hab
      exact (S.orderEmbOfFin hS).injective (by simpa using hab)

/-- **The runner at speed `1` reads exactly `S`.** -/
theorem readingsOf_cons (S : Finset ℕ) (hS : S.card = 7) :
    readingsOf (Fin.cons 1 (fun i : Fin 7 => 1 + S.orderEmbOfFin hS i)) 0 = S := by
  classical
  ext d
  simp only [readingsOf, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨i, hi0, rfl⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi0
    simp only [Fin.cons_succ, Fin.cons_zero, Nat.dist]
    have hm := Finset.orderEmbOfFin_mem S hS j
    have : 1 + S.orderEmbOfFin hS j - 1 + (1 - (1 + S.orderEmbOfFin hS j)) =
        S.orderEmbOfFin hS j := by omega
    rwa [this]
  · intro hd
    obtain ⟨j, hj⟩ : ∃ j, S.orderEmbOfFin hS j = d := by
      have : d ∈ Set.range (S.orderEmbOfFin hS) := by rw [Finset.range_orderEmbOfFin]; exact hd
      exact this
    refine ⟨j.succ, Fin.succ_ne_zero j, ?_⟩
    simp only [Fin.cons_succ, Fin.cons_zero, Nat.dist]
    omega

/-- **The skeleton on arrangements.**  Every whole-number set of at most seven readings is lonely,
given the owed arrangement statements for blocks of `3 … 6` and the bounded region. -/
theorem lonely8_of_arrangement_holes (h : ∀ f, 3 ≤ f → f ≤ 6 → ArrBlockRule8 f 9)
    (hB : ArrBoundedCovered8 9) (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7) :
    Lonely8 S := by
  classical
  by_cases h6 : S.card ≤ 6
  · exact lonely_eight_of_card_le_six hpos h6
  have hS : S.card = 7 := by omega
  have hR := readingsOf_cons S hS
  have harr := arr8_cons S hS hpos
  set v : Fin 8 → ℕ := Fin.cons 1 (fun i : Fin 7 => 1 + S.orderEmbOfFin hS i) with hv
  by_cases hsep : Separated8 9 S
  · obtain ⟨m, hCne, hFne, hsplit⟩ := hsep
    set C := S.filter (· ≤ m)
    set F := S.filter (m < ·)
    have hunion : C ∪ F = S := by
      ext d; simp only [C, F, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hd, -⟩ | ⟨hd, -⟩) <;> exact hd
      · intro hd; by_cases hdm : d ≤ m
        · exact Or.inl ⟨hd, hdm⟩
        · exact Or.inr ⟨hd, by omega⟩
    have hcardsum : C.card + F.card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · rw [hunion]
      · rw [Finset.disjoint_left]; intro d hd hd'
        simp only [C, F, Finset.mem_filter] at hd hd'; omega
    have hF1 : 1 ≤ F.card := Finset.card_pos.mpr hFne
    have hC1 : 1 ≤ C.card := Finset.card_pos.mpr hCne
    have hCpos : ∀ d ∈ C, 0 < d := fun d hd => hpos d (Finset.mem_of_mem_filter d hd)
    have hFpos : ∀ d ∈ F, 0 < d := fun d hd => hpos d (Finset.mem_of_mem_filter d hd)
    by_cases hf1 : F.card = 1
    · have := blockRule8_one C F hCpos hFpos hf1 (by omega) hCne hsplit; rwa [hunion] at this
    by_cases hf2 : F.card = 2
    · have := blockRule8_two C F hCpos hFpos hf2 (by omega) hCne hsplit; rwa [hunion] at this
    have hrule := h F.card (by omega) (by omega) v harr 0 m
    rw [hR] at hrule
    exact hrule hCne rfl hsplit
  · have := hB v harr 0 (by rw [hR]; exact hsep)
    rwa [hR] at this

/-- **The conjecture at eight runners from exactly five named holes, stated on arrangements.** -/
theorem lonelyRunnerAt8_of_arrangement_holes (h3 : ArrBlockRule8 3 9) (h4 : ArrBlockRule8 4 9)
    (h5 : ArrBlockRule8 5 9) (h6 : ArrBlockRule8 6 9) (hB : ArrBoundedCovered8 9) :
    LRC.Spec.LonelyRunnerAt8 := by
  refine LRC.Spec.lonelyRunnerAt8_of_existence (existenceAt8_of_nat fun S hpos hcard => ?_)
  refine lonely8_of_arrangement_holes (fun f hf3 hf6 => ?_) hB S hpos hcard
  interval_cases f
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end LRC.Order8Skeleton
