import LonelyRunner.LRC.SmallN.IntLRC_5
import LonelyRunner.LRC.Spec.DoorsN

/-!
# Order five, closed for whole-number arrangements

2026-09-21.  `intLRC_five` is axiom-clean in this tree but is stated for a strictly monotone
`Fin 4 → ℕ` with gcd one.  A subject of a five-runner arrangement presents an unordered
`Finset` of **at most** four disparities, whose gcd need not be one, so the two do not meet.
This file builds the bridge and closes order five on arrangements of whole numbers.

The route is deliberate.  `DoorLargestFlank` at `n = 5` (`docs/nN/OVERLAP_BOUND_v1.md`) would
close order five *natively*, but it is unproved and three routes to it are measured shut.  This
uses `intLRC_five` as a **tool** while the target stays native — `LRC.SpecN.LonelyAt` on an
arrangement — which is what the author's 2026-09-15 ruling permits.

**What this does not do.**  It is confined to whole-number arrangements.  The reduction to real
speeds is `Theorem121_Main.theorem121_LRC_real`, still `sorry`, so `LonelyRunnerAtN 5` over the
reals does **not** follow from anything here.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LRC.FiveInt

open Finset Flanks MomentIterationN LRC.SpecN

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩

/-! ## 1. padding a small set up to four members -/

noncomputable def padTo (S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  S ∪ (Finset.range (m - S.card)).image (fun i => (S.sup id) + 1 + i)

theorem padTo_subset (S : Finset ℕ) (m : ℕ) : S ⊆ padTo S m := Finset.subset_union_left

theorem padTo_card {S : Finset ℕ} {m : ℕ} (h : S.card ≤ m) : (padTo S m).card = m := by
  classical
  unfold padTo
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]; omega
  · rw [Finset.disjoint_right]
    intro a ha haS
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    have := Finset.le_sup (f := id) haS
    simp only [id] at this; omega

theorem padTo_pos {S : Finset ℕ} {m : ℕ} (hS : ∀ d ∈ S, 0 < d) : ∀ d ∈ padTo S m, 0 < d := by
  classical
  intro d hd
  rcases Finset.mem_union.mp hd with h | h
  · exact hS d h
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h; omega

theorem padTo_gcd {S : Finset ℕ} {m : ℕ} (h : S.gcd id = 1) : (padTo S m).gcd id = 1 := by
  classical
  have hdvd : (padTo S m).gcd id ∣ S.gcd id :=
    Finset.dvd_gcd (fun b hb => Finset.gcd_dvd (padTo_subset S m hb))
  rw [h] at hdvd; exact Nat.eq_one_of_dvd_one hdvd

theorem oif_strictMono (T : Finset ℕ) {k : ℕ} (h : T.card = k) :
    StrictMono (fun i : Fin k => ((T.orderIsoOfFin h i : ℕ))) :=
  fun a b hab => (T.orderIsoOfFin h).strictMono hab

theorem oif_image (T : Finset ℕ) {k : ℕ} (h : T.card = k) :
    Finset.univ.image (fun i : Fin k => ((T.orderIsoOfFin h i : ℕ))) = T := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact (T.orderIsoOfFin h i).2
  · rw [h, Finset.card_image_of_injective _ (oif_strictMono T h).injective, Finset.card_univ,
      Fintype.card_fin]

theorem oif_gcd (T : Finset ℕ) {k : ℕ} (h : T.card = k) :
    Finset.univ.gcd (fun i : Fin k => ((T.orderIsoOfFin h i : ℕ))) = T.gcd id := by
  classical
  conv_rhs => rw [← oif_image T h]
  rw [Finset.gcd_image]; rfl

/-- **The bridge.**  `intLRC_five` gives a lonely instant for any whole-number difference set of
at most four members with gcd one. -/
theorem exists_lonely_of_intLRC_five {S : Finset ℕ} (hne : S.Nonempty) (hcard : S.card ≤ 4)
    (hpos : ∀ d ∈ S, 0 < d) (hgcd : S.gcd id = 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set T := padTo S 4 with hT
  have hT4 : T.card = 4 := padTo_card hcard
  set sp : Fin 4 → ℕ := fun i => ((T.orderIsoOfFin hT4 i : ℕ)) with hsp
  have hmono : StrictMono sp := oif_strictMono T hT4
  have hspos : ∀ i, 0 < sp i := fun i => padTo_pos hpos _ (T.orderIsoOfFin hT4 i).2
  have hsgcd : Finset.univ.gcd sp = 1 := by rw [hsp, oif_gcd T hT4]; exact padTo_gcd hgcd
  obtain ⟨t, ht⟩ := intLRC_five sp hmono hspos hsgcd
  -- every member of S is some sp i
  have hmem : ∀ d ∈ S, ∃ i, sp i = d := by
    intro d hd
    have : d ∈ Finset.univ.image sp := by rw [hsp, oif_image T hT4]; exact padTo_subset S 4 hd
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
    exact ⟨i, hi⟩
  have hclear : ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
    intro d hd
    obtain ⟨i, rfl⟩ := hmem d hd
    have := ht i
    rw [show (1 : ℝ) / (5 : ℕ) = (5 : ℝ)⁻¹ by norm_num] at this
    exact this
  -- t ≠ 0, and |t| works by evenness
  obtain ⟨d, hd⟩ := hne
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hpos d hd
  have htne : t ≠ 0 := by
    intro h0
    have := hclear d hd
    rw [h0, mul_zero] at this
    simp [circDist] at this
    norm_num at this
  refine ⟨|t|, abs_pos.mpr htne, fun d' hd' => ?_⟩
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; exact hclear d' hd'
  · rw [h, mul_neg, circDist_neg]; exact hclear d' hd'

/-- **The bridge without the gcd hypothesis.**  Divide by the gcd and scale the witness back. -/
theorem exists_lonely_of_int_five {S : Finset ℕ} (hne : S.Nonempty) (hcard : S.card ≤ 4)
    (hpos : ∀ d ∈ S, 0 < d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨d0, hd0⟩ := hne
  set g := S.gcd id with hg
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · exfalso
      have hdvd0 : g ∣ d0 := Finset.gcd_dvd hd0
      rw [h] at hdvd0
      have hz : d0 = 0 := Nat.eq_zero_of_zero_dvd hdvd0
      have := hpos d0 hd0
      omega
    · exact h
  set S' : Finset ℕ := S.image (fun d => d / g) with hS'
  have hdvd : ∀ d ∈ S, g ∣ d := fun d hd => Finset.gcd_dvd hd
  have hS'pos : ∀ d ∈ S', 0 < d := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.div_pos (Nat.le_of_dvd (hpos x hx) (hdvd x hx)) hgpos
  have hS'card : S'.card ≤ 4 := le_trans Finset.card_image_le hcard
  have hS'ne : S'.Nonempty := ⟨d0 / g, Finset.mem_image_of_mem _ hd0⟩
  have hS'gcd : S'.gcd id = 1 := by
    rw [hS', Finset.gcd_image]
    have hd0ne : d0 ≠ 0 := (hpos d0 hd0).ne'
    exact Finset.gcd_div_id_eq_one hd0 hd0ne
  obtain ⟨t, htpos, ht⟩ := exists_lonely_of_intLRC_five hS'ne hS'card hS'pos hS'gcd
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
  refine ⟨t / g, div_pos htpos hgR, fun d hd => ?_⟩
  have hmem : d / g ∈ S' := Finset.mem_image_of_mem _ hd
  have := ht _ hmem
  have heq : ((d / g : ℕ) : ℝ) * t = (d : ℝ) * (t / g) := by
    have : ((d / g : ℕ) : ℝ) = (d : ℝ) / (g : ℝ) := by
      rw [Nat.cast_div (hdvd d hd) (by exact_mod_cast hgpos.ne')]
    rw [this]; field_simp
  rwa [heq] at this

open LRC.SpecN in
/-- **Order five is closed for whole-number arrangements.**  For every injective
`v : Fin 5 → ℤ` and every subject `k`, some positive instant has every other runner at circle
distance at least `1/5`. -/
theorem lonelyAtFive_int (v : Fin 5 → ℤ) (hv : Function.Injective v) (k : Fin 5) :
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin 5, i ≠ k → (5 : ℝ)⁻¹ ≤ circDist (((v i : ℝ) - (v k : ℝ)) * t) := by
  classical
  set S : Finset ℕ := (Finset.univ.erase k).image (fun i => (v i - v k).natAbs) with hS
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    have : v i - v k ≠ 0 := sub_ne_zero.mpr fun h => hik (hv h)
    exact Int.natAbs_pos.mpr this
  have hne : S.Nonempty := by
    have hu : (Finset.univ.erase k).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
      simp
    obtain ⟨i, hi⟩ := hu
    exact ⟨_, Finset.mem_image_of_mem _ hi⟩
  have hcard : S.card ≤ 4 := by
    refine le_trans Finset.card_image_le ?_
    simp [Finset.card_erase_of_mem]
  obtain ⟨t, htpos, ht⟩ := exists_lonely_of_int_five hne hcard hpos
  refine ⟨t, htpos, fun i hik => ?_⟩
  have hmem : (v i - v k).natAbs ∈ S :=
    Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
  have hkey := ht _ hmem
  have hcast : (((v i - v k).natAbs : ℕ) : ℝ) = |((v i : ℝ) - (v k : ℝ))| := by
    rw [Nat.cast_natAbs]; push_cast; ring_nf
  rw [hcast] at hkey
  rcases abs_cases ((v i : ℝ) - (v k : ℝ)) with ⟨h, -⟩ | ⟨h, -⟩
  · rwa [h] at hkey
  · rw [h, neg_mul, circDist_neg] at hkey; exact hkey

/-! ## 2. the arrangement forms, and the doors -/

/-- **The subject's obligation, discharged**, for a whole-number arrangement. -/
theorem lonelyForSubject_five_int (v : Fin 5 → ℤ) (hv : Function.Injective v) (k : Fin 5) :
    LonelyForSubject (fun i => ((v i : ℝ))) k := by
  obtain ⟨t, htpos, ht⟩ := lonelyAtFive_int v hv k
  refine ⟨t, htpos, fun i hik => ?_⟩
  rw [sep_eq]
  exact ht i hik

/-- **All four doors hold at every subject of every whole-number five-runner arrangement.**
By `LRC.SpecN.doors_agree`, which is an equivalence, so this is not a weaker statement. -/
theorem doors_five_int (v : Fin 5 → ℤ) (hv : Function.Injective v) (k : Fin 5) :
    DoorFlank (fun i => ((v i : ℝ))) k ∧ DoorArrives (fun i => ((v i : ℝ))) k ∧
    DoorCapped (fun i => ((v i : ℝ))) k ∧ DoorFAM (fun i => ((v i : ℝ))) k := by
  have hinj : Function.Injective (fun i => ((v i : ℝ))) := by
    intro a b hab
    exact hv (Int.cast_injective hab)
  obtain ⟨h1, h2, h3, h4⟩ := doors_agree (n := 5) hinj k
  have hL := lonelyForSubject_five_int v hv k
  exact ⟨h1.mpr hL, h2.mpr hL, h3.mpr hL, h4.mpr hL⟩

/-- **The cascade arrives**, for every subject of every whole-number five-runner arrangement.
This is the framework's Existence statement at order five, discharged — for whole numbers. -/
theorem cascade_arrives_five_int (v : Fin 5 → ℤ) (hv : Function.Injective v) (k : Fin 5) :
    DoorArrives (fun i => ((v i : ℝ))) k := (doors_five_int v hv k).2.1

/-! ## 3. the commensurable case -/

/-- **Order five, closed for every commensurable arrangement.**  If the subject's disparities are
all integer multiples of one positive real `c` — which is exactly the commensurable case, and
covers every rational arrangement after clearing denominators — the subject has a lonely instant.
No integrality of the speeds themselves is required, and nothing is pinned at `0`. -/
theorem lonelyForSubject_five_commensurable {v : Fin 5 → ℝ} (hv : Function.Injective v)
    (k : Fin 5) {c : ℝ} (hc : 0 < c) (a : Fin 5 → ℤ) (ha : ∀ i, v i - v k = c * (a i : ℝ)) :
    LonelyForSubject v k := by
  have hainj : Function.Injective a := by
    intro i j hij
    apply hv
    have : v i - v k = v j - v k := by rw [ha i, ha j, hij]
    linarith
  obtain ⟨t, htpos, ht⟩ := lonelyAtFive_int a hainj k
  refine ⟨t / c, div_pos htpos hc, fun i hik => ?_⟩
  rw [sep_eq, ha i]
  -- a k = 0, because v k - v k = c * a k
  have hk0 : a k = 0 := by
    have := ha k
    simp at this
    rcases this with h | h
    · linarith [hc]
    · exact_mod_cast h
  rw [show c * (a i : ℝ) * (t / c) = (a i : ℝ) * t by field_simp]
  have := ht i hik
  rw [hk0] at this
  simpa using this

end LRC.FiveInt
