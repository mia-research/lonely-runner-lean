import LonelyRunner.LRC.Spec.SymbolicWindowTransportN

/-!
# Finite lap families do not lose their windows at a parameter limit

This is the accumulation part of the AP-deformation programme, not the
replacement theorem. A finite set of lap assignments has a closed feasible
parameter set. Covering every parameter before an endpoint therefore covers
the endpoint itself. No assertion supplies coverage before or after it.
-/

namespace LRC.FiniteWindowContinuation

variable {ι κ : Type*}

/-- An upper disparity bound and an upper witness-time bound bound each lap.
Both bounds are needed; a time bound alone does not bound arbitrary speeds. -/
theorem lap_bound {d t D T : ℝ} (q : ℕ) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hdD : d ≤ D) (htT : t ≤ T)
    (hband : (q : ℝ) + 1 / 8 ≤ d * t) : (q : ℝ) < D * T := by
  have hm := mul_le_mul hdD htT ht (hd.trans hdD)
  linarith

/-- All intermediate disparities inherit the common endpoint bound. -/
theorem deformation_bound {a d D s : ℝ} (ha : a ≤ D) (hd : d ≤ D)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) * a + s * d ≤ D := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ha),
    mul_nonneg hs (sub_nonneg.mpr hd)]

/-- A fixed collection of affine inequalities is closed in the parameter.
The constraint index may be arbitrary; no strict-margin assumption is used. -/
theorem affine_region_closed (A B : ι → ℝ) :
    IsClosed {s : ℝ | ∀ i, 0 ≤ A i + s * B i} := by
  have he : {s : ℝ | ∀ i, 0 ≤ A i + s * B i} =
      ⋂ i, {s : ℝ | 0 ≤ A i + s * B i} := by ext; simp
  rw [he]
  exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)

/-- Finitely many candidate mechanisms, each with closed affine constraints,
give a closed union. This does not claim the union covers the whole path. -/
theorem finite_regions_closed (Q : Finset κ) (A B : κ → ι → ℝ) :
    IsClosed {s : ℝ | ∃ q ∈ Q, ∀ i, 0 ≤ A q i + s * B q i} := by
  classical
  have he : {s : ℝ | ∃ q ∈ Q, ∀ i, 0 ≤ A q i + s * B q i} =
      ⋃ q ∈ Q, {s : ℝ | ∀ i, 0 ≤ A q i + s * B q i} := by ext; simp
  rw [he]
  exact isClosed_biUnion_finset fun q _ => affine_region_closed (A q) (B q)

/-- Even infinitely many changes of selected candidate cannot lose coverage
at the endpoint when only finitely many fixed candidates are needed. -/
theorem endpoint_of_finite_coverage (Q : Finset κ) (A B : κ → ι → ℝ)
    {l r : ℝ} (hlr : l < r)
    (hcover : ∀ s ∈ Set.Ico l r, ∃ q ∈ Q, ∀ i, 0 ≤ A q i + s * B q i) :
    ∃ q ∈ Q, ∀ i, 0 ≤ A q i + r * B q i := by
  have hsub : Set.Ico l r ⊆ {s : ℝ | ∃ q ∈ Q, ∀ i, 0 ≤ A q i + s * B q i} :=
    hcover
  have h := closure_minimal hsub (finite_regions_closed Q A B)
  apply h
  rw [closure_Ico hlr.ne]
  exact ⟨hlr.le, le_rfl⟩

/-- Apply the finite-family limit theorem to actual lap windows along a
straight deformation. The endpoint window may be a singleton: it still counts.
Coverage before the endpoint and finite candidate labels remain explicit. -/
theorem endpoint_lap_window [Finite ι] [Nonempty ι]
    (Q : Finset (ι → ℕ)) (a d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hcover : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ∃ q ∈ Q, ∃ t : ℝ, ∀ i,
        (q i : ℝ) + 1 / 8 ≤ ((1 - s) * a i + s * d i) * t ∧
        ((1 - s) * a i + s * d i) * t ≤ q i + 7 / 8)
    (hpositive : ∀ s ∈ Set.Ico (0 : ℝ) 1, ∀ i, 0 < (1 - s) * a i + s * d i) :
    ∃ q ∈ Q, ∃ t : ℝ, 0 < t ∧ ∀ i,
      (q i : ℝ) + 1 / 8 ≤ d i * t ∧ d i * t ≤ q i + 7 / 8 := by
  classical
  letI := Fintype.ofFinite ι
  let A : (ι → ℕ) → (ι × ι) → ℝ := fun q p =>
    (8 * (q p.2 : ℝ) + 7) * a p.1 - (8 * (q p.1 : ℝ) + 1) * a p.2
  let B : (ι → ℕ) → (ι × ι) → ℝ := fun q p =>
    (8 * (q p.2 : ℝ) + 7) * (d p.1 - a p.1)-
      (8 * (q p.1 : ℝ) + 1) * (d p.2 - a p.2)
  have hlin : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ∃ q ∈ Q, ∀ p, 0 ≤ A q p + s * B q p := by
    intro s hs
    obtain ⟨q, hq, t, ht⟩ := hcover s hs
    have hw := (WindowPinch.lap_windows_iff Finset.univ Finset.univ_nonempty
      (fun i => (1 - s) * a i + s * d i) (fun i => (q i : ℤ))
      (fun i _ => hpositive s hs i)).mp
      ⟨t, fun i _ => by simpa using ht i⟩
    refine ⟨q, hq, fun p => ?_⟩
    have hh := hw p.1 (Finset.mem_univ _) p.2 (Finset.mem_univ _)
    simp only [Int.cast_natCast] at hh
    dsimp [A, B]
    nlinarith
  obtain ⟨q, hq, hh⟩ := endpoint_of_finite_coverage Q A B (by norm_num) hlin
  have hw : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      (8 * ((q i : ℤ) : ℝ) + 1) * d j ≤ (8 * ((q j : ℤ) : ℝ) + 7) * d i := by
    intro i _ j _
    have hp := hh (i,j)
    dsimp [A, B] at hp
    simp only [Int.cast_natCast]
    nlinarith
  obtain ⟨t, ht⟩ := (WindowPinch.lap_windows_iff Finset.univ Finset.univ_nonempty
    d (fun i => (q i : ℤ)) (fun i _ => hd i)).mpr hw
  refine ⟨q, hq, t, ?_, fun i => by simpa using ht i (Finset.mem_univ _)⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hb := (ht i (Finset.mem_univ _)).1
  have hqpos : (0 : ℝ) ≤ ((q i : ℤ) : ℝ) := by positivity
  have hp : 0 < d i * t := by linarith
  exact pos_of_mul_pos_right hp (hd i).le

/-- Bounded witness times on a fixed bounded-speed deformation automatically
supply the finite label family needed above. The time bound is a hypothesis,
not a new universal bound for order eight. -/
theorem endpoint_of_bounded_witnesses [Finite ι] [Nonempty ι]
    (a d : ι → ℝ) (D T : ℝ) (N : ℕ)
    (ha : ∀ i, 0 < a i) (hd : ∀ i, 0 < d i)
    (haD : ∀ i, a i ≤ D) (hdD : ∀ i, d i ≤ D)
    (hN : D * T ≤ (N : ℝ))
    (hcover : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ∃ q : ι → ℕ, ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ ∀ i,
        (q i : ℝ) + 1 / 8 ≤ ((1 - s) * a i + s * d i) * t ∧
        ((1 - s) * a i + s * d i) * t ≤ q i + 7 / 8) :
    ∃ q : ι → ℕ, ∃ t : ℝ, 0 < t ∧ ∀ i,
      (q i : ℝ) + 1 / 8 ≤ d i * t ∧ d i * t ≤ q i + 7 / 8 := by
  classical
  letI := Fintype.ofFinite ι
  let Q : Finset (ι → ℕ) := Finset.univ.image
    (fun f : ι → Fin (N + 1) => fun i => (f i).val)
  have hpositive : ∀ s ∈ Set.Ico (0 : ℝ) 1, ∀ i,
      0 < (1 - s) * a i + s * d i := by
    intro s hs i
    have h1 := mul_pos (sub_pos.mpr hs.2) (ha i)
    have h2 := mul_nonneg hs.1 (hd i).le
    linarith
  have hfinite : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ∃ q ∈ Q, ∃ t : ℝ, ∀ i,
        (q i : ℝ) + 1 / 8 ≤ ((1 - s) * a i + s * d i) * t ∧
        ((1 - s) * a i + s * d i) * t ≤ q i + 7 / 8 := by
    intro s hs
    obtain ⟨q, t, ht, htT, hband⟩ := hcover s hs
    have hq : ∀ i, q i < N + 1 := by
      intro i
      have hh := (lap_bound (q i) (hpositive s hs i).le ht.le
        (deformation_bound (haD i) (hdD i) hs.1 hs.2.le) htT (hband i).1).trans_le hN
      have hn : q i < N := by exact_mod_cast hh
      omega
    refine ⟨q, ?_, t, hband⟩
    exact Finset.mem_image.mpr ⟨fun i => ⟨q i, hq i⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨q, _, t, ht, hband⟩ := endpoint_lap_window Q a d hd hfinite hpositive
  exact ⟨q, t, ht, hband⟩

end LRC.FiniteWindowContinuation
