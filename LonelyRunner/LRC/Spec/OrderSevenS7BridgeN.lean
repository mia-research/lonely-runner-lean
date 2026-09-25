import LonelyRunner.LRC.Spec.OrderSevenS7Stage2AllN
import LonelyRunner.LRC.Spec.OrderSevenS7Stage2OddN
import LonelyRunner.LRC.Spec.OrderSevenS7SmallN
import LonelyRunner.LRC.Spec.OrderSevenFilterN

/-!
# n = 7 (Barajas–Serra) — §7 bridge: the `|A| = 5`, `m = 1` witness

Turns the finite searches of `Section7_M1*` into the statement the `m = 1` case
of Barajas–Serra needs: five level-`0` speeds with residue class in `{1,2,4}`
mod `7`, plus one level-`1` speed `d₆`, always admit a modulus `P` and a
multiplier `lam` placing all six in the band `[P, 6P]` mod `7P`.
-/

namespace LRC.OrderSevenN

open Section7M1

/-! ## Transfer between `ℤ`-arithmetic and the `Nat` searches -/

/-- If `x ≡ r (mod M)` with `r < M`, the band condition for `lam * x` at modulus
`M` over `ℤ` is exactly the `Nat` band condition for `lam * r`. -/
theorem band_transfer (M lam r : ℕ) (x : ℤ) (hr : r < M)
    (hx : x % (M : ℤ) = (r : ℤ)) (lo hi : ℕ)
    (h1 : lo ≤ lam * r % M) (h2 : lam * r % M ≤ hi) :
    (lo : ℤ) ≤ ((lam : ℤ) * x) % (M : ℤ) ∧ ((lam : ℤ) * x) % (M : ℤ) ≤ (hi : ℤ) := by
  have hrM : ((r : ℤ)) % (M : ℤ) = (r : ℤ) := by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)]
  have hmod : ((lam : ℤ) * x) % (M : ℤ) = (((lam * r) % M : ℕ) : ℤ) := by
    have hxr : x % (M : ℤ) = (r : ℤ) % (M : ℤ) := by rw [hx, hrM]
    have := Int.ModEq.mul_left (lam : ℤ) hxr
    rw [this]
    push_cast
    ring_nf
  rw [hmod]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## Membership in the search universes -/

/-- A residue `< 49` whose class mod `7` lies in `{1,2,4}` is in `S21`. -/
theorem mem_S21 (n : ℕ) (h1 : n < 49) (h2 : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4) : n ∈ S21 := by
  simp only [S21, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  exact ⟨h1, by tauto⟩

theorem mem_subs4 {a b c d : ℕ} (ha : a ∈ S21) (hb : b ∈ S21) (hc : c ∈ S21) (hd : d ∈ S21)
    (h1 : a < b) (h2 : b < c) (h3 : c < d) : [a, b, c, d] ∈ subs4 := by
  simp only [subs4, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨a, ha, b, ⟨hb, h1⟩, c, ⟨hc, h2⟩, d, ⟨hd, h3⟩, rfl⟩

theorem mem_subs5 {a b c d e : ℕ} (ha : a ∈ S21) (hb : b ∈ S21) (hc : c ∈ S21) (hd : d ∈ S21)
    (he : e ∈ S21) (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) :
    [a, b, c, d, e] ∈ subs5 := by
  simp only [subs5, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨a, ha, b, ⟨hb, h1⟩, c, ⟨hc, h2⟩, d, ⟨hd, h3⟩, e, ⟨he, h4⟩, rfl⟩

/-! ## From a `Finset` of residues to a member of the search universe -/

/-- A strictly increasing list of four `S21` residues is one of the `subs4`. -/
theorem mem_subs4_of_sorted (T : List ℕ) (hp : T.Pairwise (· < ·)) (hl : T.length = 4)
    (hm : ∀ x ∈ T, x ∈ S21) : T ∈ subs4 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, T = [a, b, c, d] := by
    match T, hl with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hm
  exact mem_subs4 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 (by tauto) (by tauto) (by tauto)

/-- A strictly increasing list of five `S21` residues is one of the `subs5`. -/
theorem mem_subs5_of_sorted (T : List ℕ) (hp : T.Pairwise (· < ·)) (hl : T.length = 5)
    (hm : ∀ x ∈ T, x ∈ S21) : T ∈ subs5 := by
  obtain ⟨a, b, c, d, e, rfl⟩ : ∃ a b c d e, T = [a, b, c, d, e] := by
    match T, hl with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hm
  exact mem_subs5 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2
    (by tauto) (by tauto) (by tauto) (by tauto)

/-- The residues of the five level-`0` speeds are covered either by a four-element
`S21`-subset (when two of them coincide mod `49`) or, when they are distinct, by
the five-element `S21`-subset they form. -/
theorem residue_cover (r : Fin 5 → ℕ) (hr : ∀ i, r i ∈ S21) :
    (∃ T ∈ subs4, ∀ i, r i ∈ T) ∨
      ((∀ i j, r i = r j → i = j) ∧
        ∃ T ∈ subs5, (∀ i, r i ∈ T) ∧ ∀ t ∈ T, ∃ i, r i = t) := by
  classical
  set U : Finset ℕ := Finset.image r Finset.univ with hU
  have hUS : ∀ x ∈ U, x ∈ S21 := by
    intro x hx
    simp only [hU, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx; exact hr i
  have hmemU : ∀ i, r i ∈ U := by
    intro i; simp [hU, Finset.mem_image]
  have hcard : U.card ≤ 5 := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 5))) (f := r)
    simpa [hU] using this
  by_cases h5 : U.card = 5
  · right
    refine ⟨?_, U.sort (· ≤ ·), ?_, ?_, ?_⟩
    · intro i j hij
      have hinj : Set.InjOn r (Finset.univ : Finset (Fin 5)) :=
        Finset.injOn_of_card_image_eq (by simpa [hU] using h5)
      exact hinj (by simp) (by simp) hij
    · refine mem_subs5_of_sorted _ ?_ ?_ ?_
      · exact (Finset.sortedLT_sort U).pairwise
      · simpa using h5
      · intro x hx; exact hUS x ((Finset.mem_sort _).1 hx)
    · intro i; exact (Finset.mem_sort _).2 (hmemU i)
    · intro t ht
      have := (Finset.mem_sort _).1 ht
      simp only [hU, Finset.mem_image, Finset.mem_univ, true_and] at this
      exact this
  · left
    have hcard4 : U.card ≤ 4 := by omega
    have hsub : U ⊆ S21.toFinset := by
      intro x hx; exact List.mem_toFinset.2 (hUS x hx)
    have hbig : 4 ≤ S21.toFinset.card := by decide
    obtain ⟨V, hUV, hVS, hVcard⟩ := Finset.exists_subsuperset_card_eq hsub hcard4 hbig
    refine ⟨V.sort (· ≤ ·), ?_, ?_⟩
    · refine mem_subs4_of_sorted _ (Finset.sortedLT_sort V).pairwise (by simpa using hVcard) ?_
      intro x hx
      exact List.mem_toFinset.1 (hVS ((Finset.mem_sort _).1 hx))
    · intro i; exact (Finset.mem_sort _).2 (hUV (hmemU i))

/-- Reading `S21` membership back off. -/
theorem S21_spec {n : ℕ} (h : n ∈ S21) : n < 49 ∧ (n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4) := by
  simp only [S21, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  tauto

/-- `hres` in arithmetic form. -/
theorem emod7_of_mem (x : ℤ) (h : (x : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7))) :
    x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 4 := by
  have h' : (x : ZMod 7) = 1 ∨ (x : ZMod 7) = 2 ∨ (x : ZMod 7) = 4 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using h
  have hd : ∀ a : ℤ, (x : ZMod 7) = ((a : ℤ) : ZMod 7) → (7 : ℤ) ∣ (x - a) := by
    intro a ha
    have h0 : ((x - a : ℤ) : ZMod 7) = 0 := by push_cast; rw [ha]; ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x - a) 7).1 h0
  rcases h' with h1 | h1 | h1
  · left; have := hd 1 (by rw [h1]; norm_num); omega
  · right; left; have := hd 2 (by rw [h1]; norm_num); omega
  · right; right; have := hd 4 (by rw [h1]; norm_num); omega

/-- Unfolding `okFor`. -/
theorem okFor_spec {lam : ℕ} {T : List ℕ} (h : okFor lam T = true) :
    ∀ t ∈ T, 7 ≤ lam * t % 49 ∧ lam * t % 49 ≤ 42 := by
  intro t ht
  have := (List.all_eq_true.1 h) t ht
  simpa [Bool.and_eq_true, decide_eq_true_eq] using this

/-! ## The `N = 49` witness -/

/-- If a multiplier from `S21` puts the five residues in `[7,42]` mod `49`, then
`P = 7` works for all six speeds: the five level-`0` ones by transfer, `d₆` for
free because `band_top` puts a level-`m` element in band for any unit multiplier. -/
theorem witness_at_49 (d : Fin 5 → ℤ) (d6 : ℤ) (r : Fin 5 → ℕ) (lam : ℕ)
    (hlamS : lam ∈ S21) (hr49 : ∀ i, d i % 49 = (r i : ℤ)) (hrlt : ∀ i, r i < 49)
    (T : List ℕ) (hT : ∀ i, r i ∈ T) (hok : okFor lam T = true)
    (h6 : (7 : ℤ) ∣ d6) (h6' : ¬ ((7 : ℤ) ^ 2 ∣ d6)) :
    ∃ (P : ℕ) (mu : ℤ), 0 < P ∧
      (∀ i, (P : ℤ) ≤ (mu * d i) % (7 * (P : ℤ)) ∧ (mu * d i) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) ∧
      ((P : ℤ) ≤ (mu * d6) % (7 * (P : ℤ)) ∧ (mu * d6) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  have hlam7 : ¬ (7 : ℤ) ∣ (lam : ℤ) := by
    intro hh
    have h1 : (7 : ℕ) ∣ lam := by exact_mod_cast hh
    have := (S21_spec hlamS).2
    omega
  refine ⟨7, (lam : ℤ), by norm_num, ?_, ?_⟩
  · intro i
    have hb := okFor_spec hok (r i) (hT i)
    have hkey := band_transfer 49 lam (r i) (d i) (hrlt i) (hr49 i) 7 42 hb.1 hb.2
    norm_num at hkey ⊢
    exact hkey
  · have hd1 : (7 : ℤ) ^ 1 ∣ d6 := by simpa using h6
    have hd2 : ¬ (7 : ℤ) ^ (1 + 1) ∣ d6 := by simpa using h6'
    have hb := band_top 1 (lam : ℤ) d6 hlam7 hd1 hd2
    norm_num at hb ⊢
    exact hb

/-! ## The `N' = 98` search: consuming stage 2 -/

/-- Choosing, for each element of `T`, one of its two lifts mod `98` produces a
member of `liftsOf T`. -/
theorem liftsOf_map_mem (T : List ℕ) (f : ℕ → ℕ) (h : ∀ t ∈ T, f t = t ∨ f t = t + 49) :
    T.map f ∈ liftsOf T := by
  induction T with
  | nil => simp [liftsOf]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun t ht => h t (by simp [ht]))
    simp only [liftsOf, List.foldr_cons, List.mem_flatMap, List.map_cons] at hxs ⊢
    exact ⟨xs.map f, hxs, by rcases hx with hx | hx <;> simp [hx]⟩

/-- `d6vals` is exactly the set of residues mod `98` that are nonzero multiples of
`7` but not of `49`. -/
theorem mem_d6vals (v : ℕ) (h1 : v < 98) (h2 : 7 ∣ v) (h3 : ¬ (49 ∣ v)) (h4 : v ≠ 0) :
    v ∈ d6vals := by
  have hlist : d6vals = [7, 14, 21, 28, 35, 42, 56, 63, 70, 77, 84, 91] := by rfl
  rw [hlist]
  have hv : v = 7 ∨ v = 14 ∨ v = 21 ∨ v = 28 ∨ v = 35 ∨ v = 42 ∨ v = 56 ∨ v = 63 ∨
      v = 70 ∨ v = 77 ∨ v = 84 ∨ v = 91 := by omega
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

/-- Unfolding `solvable98`. -/
theorem solvable98_spec {D : List ℕ} (h : solvable98 D = true) :
    ∃ lam : ℕ, 0 < lam ∧ ∀ x ∈ D, 14 ≤ lam * x % 98 ∧ lam * x % 98 ≤ 84 := by
  simp only [solvable98, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨lam, _, hpos, hall⟩ := h
  exact ⟨lam, by simpa using hpos, fun x hx => by simpa [Bool.and_eq_true] using hall x hx⟩

/-- The lift selector: sends the residue `r i` mod `49` to the residue `s i` mod
`98` of the same speed. Well defined on the image of `r` precisely because, in
the branch where stage 2 is needed, the five residues mod `49` are distinct. -/
def sel5 (r s : Fin 5 → ℕ) (t : ℕ) : ℕ :=
  if t = r 0 then s 0 else if t = r 1 then s 1 else if t = r 2 then s 2 else
    if t = r 3 then s 3 else s 4

theorem sel5_apply (r s : Fin 5 → ℕ) (hinj : ∀ i j, r i = r j → i = j) (i : Fin 5) :
    sel5 r s (r i) = s i := by
  have hne : ∀ i j : Fin 5, i ≠ j → r i ≠ r j := fun i j hij h => hij (hinj i j h)
  have e10 := hne 1 0 (by decide)
  have e20 := hne 2 0 (by decide)
  have e21 := hne 2 1 (by decide)
  have e30 := hne 3 0 (by decide)
  have e31 := hne 3 1 (by decide)
  have e32 := hne 3 2 (by decide)
  have e40 := hne 4 0 (by decide)
  have e41 := hne 4 1 (by decide)
  have e42 := hne 4 2 (by decide)
  have e43 := hne 4 3 (by decide)
  fin_cases i <;> simp only [sel5] <;>
    simp [e10, e20, e21, e30, e31, e32, e40, e41, e42, e43]

/-- **The stage-2 fact in the form the bridge needs.** A configuration of the
`N' = 98` enumeration with at least one odd entry admits a good multiplier.
`stage2_all_clean` covers the `gcdAll = 1` configurations, `stage2_odd_nonunit_clean`
the odd ones with `gcdAll ≠ 1`. -/
theorem solvable98_of_odd {D : List ℕ}
    (hD : D ∈ exc63.flatMap fun E => (liftsOf E).flatMap fun L => d6vals.map fun d6 => d6 :: L)
    (hodd : D.any (fun x => x % 2 == 1) = true) : solvable98 D = true := by
  by_contra hns
  have hfalse : solvable98 D = false := by
    cases h : solvable98 D
    · rfl
    · exact absurd h hns
  by_cases hg : gcdAll D = 1
  · have hm : D ∈ bad2Of exc63 := by
      simp only [bad2Of, List.mem_filter]
      exact ⟨hD, by simp [hg, hfalse]⟩
    rw [stage2_all_clean] at hm
    simp at hm
  · have hm : D ∈ bad2OddOf exc63 := by
      simp only [bad2OddOf, List.mem_filter]
      exact ⟨hD, by simp [hodd, hg, hfalse]⟩
    rw [stage2_odd_nonunit_clean] at hm
    simp at hm

/-! ## The `N' = 98` witness -/

/-- `P = 14`: a multiplier placing all six residues mod `98` in `[14,84]`. -/
theorem witness_at_98 (d : Fin 5 → ℤ) (d6 : ℤ) (s : Fin 5 → ℕ) (d6v : ℕ) (lam : ℕ)
    (hs98 : ∀ i, d i % 98 = (s i : ℤ)) (hslt : ∀ i, s i < 98)
    (h6v : d6 % 98 = (d6v : ℤ)) (h6vlt : d6v < 98)
    (D : List ℕ) (hDs : ∀ i, s i ∈ D) (hD6 : d6v ∈ D)
    (hsol : ∀ x ∈ D, 14 ≤ lam * x % 98 ∧ lam * x % 98 ≤ 84) :
    ∃ (P : ℕ) (mu : ℤ), 0 < P ∧
      (∀ i, (P : ℤ) ≤ (mu * d i) % (7 * (P : ℤ)) ∧ (mu * d i) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) ∧
      ((P : ℤ) ≤ (mu * d6) % (7 * (P : ℤ)) ∧ (mu * d6) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  refine ⟨14, (lam : ℤ), by norm_num, ?_, ?_⟩
  · intro i
    have hb := hsol (s i) (hDs i)
    have hkey := band_transfer 98 lam (s i) (d i) (hslt i) (hs98 i) 14 84 hb.1 hb.2
    norm_num at hkey ⊢
    exact hkey
  · have hb := hsol d6v hD6
    have hkey := band_transfer 98 lam d6v d6 h6vlt h6v 14 84 hb.1 hb.2
    norm_num at hkey ⊢
    exact hkey

/-! ## The bridge -/

/-- **Barajas–Serra §7, the case `|A| = 5`, `m = 1`.** Five level-`0` speeds with
residue class in `{1,2,4}` mod `7`, together with one level-`1` speed `d₆`, admit
a modulus `P` and a multiplier `lam` placing all six of them in the band
`[P, 6P]` mod `7P` — hence, by `circDist_ge_of_band`, at circle distance at least
`1/7`.

`P = 7` (`N = 49`) suffices unless the five residues mod `49` are distinct and
form one of the 63 exceptional sets, in which case `P = 14` (`N' = 98`) is used —
which needs one of the six to be odd (`hodd`); nothing else about common factors is used —
exactly as in BS §7. -/
theorem m1_six_witness
    (d : Fin 5 → ℤ) (d6 : ℤ)
    (hndvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hres : ∀ i, (d i : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)))
    (h6 : (7 : ℤ) ∣ d6)
    (h6' : ¬ ((7 : ℤ) ^ 2 ∣ d6))
    (hodd : ¬ ((∀ i, (2 : ℤ) ∣ d i) ∧ (2 : ℤ) ∣ d6)) :
    ∃ (P : ℕ) (lam : ℤ), 0 < P ∧
      (∀ i, (P : ℤ) ≤ (lam * d i) % (7 * (P : ℤ)) ∧
            (lam * d i) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) ∧
      ((P : ℤ) ≤ (lam * d6) % (7 * (P : ℤ)) ∧
       (lam * d6) % (7 * (P : ℤ)) ≤ 6 * (P : ℤ)) := by
  classical
  -- residues mod 49, mod 98
  obtain ⟨r, hr49⟩ : ∃ r : Fin 5 → ℕ, ∀ i, d i % 49 = (r i : ℤ) :=
    ⟨fun i => (d i % 49).toNat,
      fun i => (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm⟩
  obtain ⟨s, hs98⟩ : ∃ s : Fin 5 → ℕ, ∀ i, d i % 98 = (s i : ℤ) :=
    ⟨fun i => (d i % 98).toNat,
      fun i => (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm⟩
  obtain ⟨d6v, h6v⟩ : ∃ v : ℕ, d6 % 98 = (v : ℤ) :=
    ⟨(d6 % 98).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm⟩
  have hrlt : ∀ i, r i < 49 := by
    intro i
    have h1 := Int.emod_lt_of_pos (d i) (show (0 : ℤ) < 49 by norm_num)
    have h2 := hr49 i
    omega
  have hslt : ∀ i, s i < 98 := by
    intro i
    have h1 := Int.emod_lt_of_pos (d i) (show (0 : ℤ) < 98 by norm_num)
    have h2 := hs98 i
    omega
  have h6vlt : d6v < 98 := by
    have h1 := Int.emod_lt_of_pos d6 (show (0 : ℤ) < 98 by norm_num)
    omega
  have hsr : ∀ i, s i % 49 = r i := by
    intro i; have h1 := hr49 i; have h2 := hs98 i; omega
  have hr7 : ∀ i, r i % 7 = 1 ∨ r i % 7 = 2 ∨ r i % 7 = 4 := by
    intro i
    have h1 := hr49 i
    have h2 := emod7_of_mem (d i) (hres i)
    omega
  have hrS : ∀ i, r i ∈ S21 := fun i => mem_S21 _ (hrlt i) (hr7 i)
  rcases residue_cover r hrS with ⟨T, hT4, hTr⟩ | ⟨hinj, T, hT5, hTr, hTsurj⟩
  · -- fewer than five distinct residues mod 49: every 4-subset is solvable
    have hsolT : solvable T = true := (List.all_eq_true.1 subs4_all_solvable) T hT4
    simp only [solvable, List.any_eq_true] at hsolT
    obtain ⟨lam, hlamS, hok⟩ := hsolT
    exact witness_at_49 d d6 r lam hlamS hr49 hrlt T hTr hok h6 h6'
  · by_cases hsolT : solvable T = true
    · simp only [solvable, List.any_eq_true] at hsolT
      obtain ⟨lam, hlamS, hok⟩ := hsolT
      exact witness_at_49 d d6 r lam hlamS hr49 hrlt T hTr hok h6 h6'
    · -- the exceptional case: pass to N' = 98
      have hTbad : T ∈ bad := by
        simp only [bad, List.mem_filter]
        exact ⟨hT5, by simp [hsolT]⟩
      have hTexc : T ∈ exc63 := by
        have h := (List.all_eq_true.1 bad_subset_exc63) T hTbad
        simpa using h
      have hfr : ∀ i, sel5 r s (r i) = s i := sel5_apply r s hinj
      have hlift : ∀ t ∈ T, sel5 r s t = t ∨ sel5 r s t = t + 49 := by
        intro t ht
        obtain ⟨i, rfl⟩ := hTsurj t ht
        rw [hfr i]
        have h1 := hsr i
        have h2 := hslt i
        omega
      have hLmem : T.map (sel5 r s) ∈ liftsOf T := liftsOf_map_mem T _ hlift
      have h6'' : ¬ ((49 : ℤ) ∣ d6) := by
        intro hh; exact h6' (by norm_num; exact hh)
      have h6v7 : 7 ∣ d6v := by omega
      have h6v49 : ¬ (49 ∣ d6v) := by omega
      have h6vne : d6v ≠ 0 := by omega
      have hDenum : (d6v :: T.map (sel5 r s)) ∈
          exc63.flatMap fun E => (liftsOf E).flatMap fun L => d6vals.map fun x => x :: L := by
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨T, hTexc, T.map (sel5 r s), hLmem, d6v,
          mem_d6vals d6v h6vlt h6v7 h6v49 h6vne, rfl⟩
      have hDs : ∀ i, s i ∈ (d6v :: T.map (sel5 r s)) := by
        intro i
        refine List.mem_cons_of_mem _ ?_
        rw [← hfr i]
        exact List.mem_map_of_mem (hTr i)
      have hD6 : d6v ∈ (d6v :: T.map (sel5 r s)) := by simp
      have hodd : (d6v :: T.map (sel5 r s)).any (fun x => x % 2 == 1) = true := by
        by_contra hc
        simp only [Bool.not_eq_true, List.any_eq_false, beq_iff_eq] at hc
        have hev : ∀ i, (2 : ℤ) ∣ d i := by
          intro i
          have h1 := hc (s i) (hDs i)
          have h2 := hs98 i
          omega
        have hev6 : (2 : ℤ) ∣ d6 := by
          have h1 := hc d6v hD6
          omega
        exact hodd ⟨hev, hev6⟩
      obtain ⟨lam, _, hlam⟩ := solvable98_spec (solvable98_of_odd hDenum hodd)
      exact witness_at_98 d d6 s d6v lam hs98 hslt h6v h6vlt _ hDs hD6 hlam

end LRC.OrderSevenN
