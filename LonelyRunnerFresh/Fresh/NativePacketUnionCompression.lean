import Fresh.NativePacketRestartExchange

/-! A supplied changing-packet fragment can be replaced by its fixed union
at a clear-union exit. Internal recapture words and labels need not match.
No fragment endpoint or fixed-union isolation is asserted to exist. -/
open Classical
namespace Fresh.NativePacketUnionCompression
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeReturnHandoff
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery

-- Every move uses a subset of the same union; no common maximum is assumed.
noncomputable def Fragment (ds : Finset ℝ) (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ) : Prop :=
  ∀ j : ℕ,j<N → G j ⊆ ds ∧ IsMove (G j) (q j) (q (j+1))

theorem fragment_below_isolation {ds : Finset ℝ} (hp : ∀ d∈ds,0<d)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ) (hf : Fragment ds q G N)
    (t : ℝ) (ht : LonelyAt ds t) (h0 : q 0≤t) : ∀ j,j≤N → q j≤t := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hg := hf j (by omega)
    exact isMove_le_of_lonely (fun d hd=>hp d (hg.1 hd))
      (fun d hd=>ht d (hg.1 hd)) (ih (by omega)) hg.2

theorem fragment_first_union_isolation {ds : Finset ℝ} (hp : ∀ d∈ds,0<d)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ) (hf : Fragment ds q G N)
    (hclear : LonelyAt ds (q N)) :
    LonelyAt ds (q N) ∧ ∀ t,q 0≤t → LonelyAt ds t → q N≤t := by
  exact ⟨hclear,fun t h0 ht=>fragment_below_isolation hp q G N hf t ht h0 N le_rfl⟩

theorem fragment_start_le {ds : Finset ℝ} (hp : ∀ d∈ds,0<d)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ) (hf : Fragment ds q G N) :
    ∀ j,j≤N → q 0≤q j := by
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih =>
    intro hj
    have hg := hf j (by omega)
    exact (ih (by omega)).trans (le_of_isMove (fun d hd=>hp d (hg.1 hd)) hg.2)

theorem fragment_fixed_union_endpoint {ds : Finset ℝ} (hp : ∀ d∈ds,0<d)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N M : ℕ) (hf : Fragment ds q G N)
    (hclear : LonelyAt ds (q N)) (hfixed : LonelyAt ds (cascadeSeq ds (q 0) M)) :
    q N=cascadeSeq ds (q 0) M := by
  apply le_antisymm
  · exact fragment_below_isolation hp q G N hf _ hfixed
      (by simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove ds (q 0)) M) N le_rfl
  · exact seq_le_of_lonely hp hclear
      (by simpa only [cascadeSeq_zero] using fragment_start_le hp q G N hf N le_rfl)
      (cascadeSeq_isMove ds (q 0)) M

-- A reader captured at a clear-union exit must be outside that union.
theorem fragment_exit_outside {ds : Finset ℝ} {T s : ℝ}
    (hclear : LonelyAt ds T) (hw : InWay s T) : s∉ds := by
  intro hs
  exact not_lt_of_ge (hclear s hs) hw

theorem physical_fragment_first_isolation {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ)
    (hf : Fragment (part v k I) q G N) (hc : LonelyAt (part v k I) (q N)) :
    ∀ t,q 0≤t → LonelyAt (part v k I) t → q N≤t :=
  (fragment_first_union_isolation (part_pos hv k I hI) q G N hf hc).2

-- Supplied fragment recovery gives the same canonical last move even when
-- no common fixed-union history is supplied or visited.
theorem fragment_recovery_into_canonical {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k)
    (q : ℕ → ℝ) (G : ℕ → Finset ℝ) (N : ℕ) (hN : 0<N)
    (hf : Fragment (part v k I) q G N) (hC : 0<q 0)
    (hstrict : q (N-1)<q N) (hclear : LonelyAt (part v k I) (q N))
    (hout : ∀ d∈outside v k I,¬InWay d (q N)) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  have hn : N-1+1=N := by omega
  have hg := hf (N-1) (by omega)
  have hm := hg.2
  rw [hn] at hm
  have hsub : G (N-1) ⊆ disparitySet v k := by
    rw [←part_union_outside v k I hI]
    exact hg.1.trans Finset.subset_union_left
  have hc := endpoint_union_lonely hclear hout
  rw [part_union_outside v k I hI] at hc
  have hrest : ∀ d∈disparitySet v k \ G (N-1),¬InWay d (q N) := by
    intro d hd
    exact not_lt.mpr (hc d (Finset.mem_sdiff.mp hd).1)
  have hmove := endpoint_clear_preserves_move
    (fun d hd=>disparitySet_pos hv k d (hsub hd))
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm hrest
  rw [Finset.union_sdiff_of_subset hsub] at hmove
  have hU : 0<q (N-1) := hC.trans_le (fragment_start_le (part_pos hv k I hI) q G N hf (N-1) (by omega))
  exact canonical_of_isolating_move hv k _ _ hU hstrict hmove ((isolatedAt_iff_lonelyAt v k _).2 hc)

#print axioms fragment_below_isolation
#print axioms fragment_first_union_isolation
#print axioms fragment_start_le
#print axioms fragment_fixed_union_endpoint
#print axioms fragment_exit_outside
#print axioms physical_fragment_first_isolation
#print axioms fragment_recovery_into_canonical
end Fresh.NativePacketUnionCompression
