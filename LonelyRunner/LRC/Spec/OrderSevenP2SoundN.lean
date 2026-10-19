import LonelyRunner.LRC.Spec.OrderSevenP2CheckN
import LonelyRunner.LRC.Spec.OrderSevenAbsN

/-!
# Soundness of the AbsU5 certificate checker

`Claim U r`: any `r` table states share a good instant inside `U`.  If a checker node returns `true` and its
children satisfy their claims, the node's claim holds (`claim_of_nodeOK`).  This holds for any certificate data:
the data only chooses which checks are run.

Two table facts are hypotheses here, checked by kernel computation in their own modules:
* `BlkSpec`: `BLK x` is exactly the set of states whose mask misses `x`;
* `CapSpec`: every state misses at most two instants of each class.

No `sorry`, no `native_decide`.
-/

namespace LRC.O7P2

/-- `BLK x` lists exactly the states whose mask misses instant `x`. -/
def BlkSpec : Prop := ∀ x, x < 245 → ∀ k, k < NS → (BLK x).testBit k = !(MT k).testBit x

/-- Each state misses at most two instants of every class. -/
def CapSpec : Prop := ∀ c, c < 35 → ∀ k, k < NS → ((cmemL c).filter (fun x => !(MT k).testBit x)).length ≤ 2

/-- Class lists are duplicate-free and lie below 245. -/
def ClassSpec : Prop := ∀ c, c < 35 → (cmemL c).Nodup ∧ ∀ x ∈ cmemL c, x < 245

/-- Class blocker pairs agree with the class lists and `BLK`. -/
def CBSpec : Prop := ∀ c, c < 35 → cmemB c = (cmemL c).map (fun x => (x, BLK x))

/-- `ks` share a good instant inside `U`. -/
def Good (U : Nat) (ks : List Nat) : Prop := ∃ x, x < 245 ∧ U.testBit x = true ∧ ∀ k ∈ ks, (MT k).testBit x = true

/-- Any `r` table states share a good instant inside `U`. -/
def Claim (U r : Nat) : Prop := ∀ ks : List Nat, ks.length = r → (∀ k ∈ ks, k < NS) → Good U ks

theorem alls_eq : ALLS = 2 ^ NS - 1 := by decide +kernel

theorem alls_bit {k : Nat} (hk : k < NS) : ALLS.testBit k = true := by
  have := alls_eq
  rw [this, Nat.testBit_two_pow_sub_one]; simpa using hk

theorem range245_eq : range245 = List.range 245 := by decide +kernel

theorem mem_bitsList {U x : Nat} : x ∈ bitsList U ↔ x < 245 ∧ U.testBit x = true := by
  simp [bitsList, range245_eq]

theorem testBit_andMap (g : Nat → Nat) :
    ∀ (xs : List Nat) (acc k : Nat), (andMap g xs acc).testBit k = true ↔
      acc.testBit k = true ∧ ∀ x ∈ xs, (g x).testBit k = true
  | [], acc, k => by simp [andMap]
  | x :: xs, acc, k => by
    simp only [andMap]
    split_ifs with h
    · have h0 : acc &&& g x = 0 := by simpa using h
      have hb : (acc &&& g x).testBit k = false := by rw [h0]; simp
      rw [Nat.testBit_and] at hb
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and, List.mem_cons, forall_eq_or_imp]
      intro ha hg; simp [ha, hg] at hb
    · rw [testBit_andMap g xs, Nat.testBit_and]
      simp only [Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
      tauto

theorem testBit_orMap (g : Nat → Nat) :
    ∀ (xs : List Nat) (acc k : Nat), (orMap g xs acc).testBit k = true ↔
      acc.testBit k = true ∨ ∃ x ∈ xs, (g x).testBit k = true
  | [], acc, k => by simp [orMap]
  | x :: xs, acc, k => by
    simp only [orMap]
    have key : (orMap g xs (acc ||| g x)).testBit k = true ↔
        acc.testBit k = true ∨ ∃ y ∈ x :: xs, (g y).testBit k = true := by
      rw [testBit_orMap g xs, Nat.testBit_or]
      simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
      tauto
    split_ifs with h
    · have h0 : acc ||| g x = 0 := by simpa using h
      rw [← h0]; exact key
    · exact key

theorem testBit_atLeast {k : Nat} (hk : k < NS) :
    ∀ (xs : List Nat) (m : Nat), (atLeast xs m).testBit k = true ↔
      m ≤ (xs.filter (fun x => (BLK x).testBit k)).length
  | xs, 0 => by
    cases xs <;> simp [atLeast, alls_bit hk]
  | [], m + 1 => by simp [atLeast]
  | x :: xs, m + 1 => by
    simp only [atLeast, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true,
      testBit_atLeast hk xs, List.filter_cons]
    by_cases hx : (BLK x).testBit k = true
    · simp only [hx, true_and, if_true, List.length_cons]; omega
    · simp only [hx, false_and, false_or, Bool.false_eq_true, if_false]

theorem good_cons {U k : Nat} {ks : List Nat} : Good U (k :: ks) ↔ Good (U &&& MT k) ks := by
  unfold Good
  simp only [List.mem_cons, forall_eq_or_imp, Nat.testBit_and, Bool.and_eq_true]
  constructor
  · rintro ⟨x, hx, hU, hk, hks⟩; exact ⟨x, hx, ⟨hU, hk⟩, hks⟩
  · rintro ⟨x, hx, ⟨hU, hk⟩, hks⟩; exact ⟨x, hx, hU, hk, hks⟩

/-- Good is preserved when a member is moved to the front. -/
theorem good_perm {U : Nat} {ks ks' : List Nat} (h : ks.Perm ks') : Good U ks ↔ Good U ks' := by
  unfold Good
  constructor <;> rintro ⟨x, hx, hU, hk⟩ <;> refine ⟨x, hx, hU, fun k hk' => hk k ?_⟩
  · exact h.symm.mem_iff.mp hk'
  · exact h.mem_iff.mp hk'

/-- Leaves: if no state blocks all of `U`, any single state has a good instant in `U`. -/
theorem claim_one_of_leafOK (hB : BlkSpec) {U : Nat} (hU : ∀ x, U.testBit x = true → x < 245)
    (h : leafOK U = true) : Claim U 1 := by
  intro ks hlen hlt
  match ks, hlen with
  | [k], _ =>
    have hk : k < NS := hlt k (by simp)
    by_contra hno
    have hz : andMap BLK (bitsList U) ALLS = 0 := by simpa [leafOK] using h
    have hbit : (andMap BLK (bitsList U) ALLS).testBit k = true := by
      rw [testBit_andMap]
      refine ⟨alls_bit hk, fun x hx => ?_⟩
      obtain ⟨hx245, hUx⟩ := mem_bitsList.mp hx
      rw [hB x hx245 k hk]
      by_contra hm
      exact hno ⟨x, hx245, hUx, fun k' hk' => by simp at hk'; subst hk'; simpa using hm⟩
    rw [hz] at hbit; simp at hbit

/-- Surviving members: if more than `2n` instants of one class survive in `U`, any `n` states leave one. -/
theorem class_survivor (hC : CapSpec) {c : Nat} (hc : c < 35) :
    ∀ (ks : List Nat) (L : List Nat), (∀ k ∈ ks, k < NS) → L.Nodup → (∀ y ∈ L, y ∈ cmemL c) →
      2 * ks.length < L.length → ∃ y ∈ L, ∀ k ∈ ks, (MT k).testBit y = true
  | [], L, _, _, _, hlen => by
    obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos (by simpa using hlen)
    exact ⟨y, hy, by simp⟩
  | k :: ks, L, hlt, hnd, hsub, hlen => by
    have hkill : (L.filter (fun y => !(MT k).testBit y)).length ≤ 2 := by
      have hcap := hC c hc k (hlt k (by simp))
      exact le_trans ((List.Nodup.subperm hnd hsub).filter _).length_le hcap
    have hsplit := List.length_eq_length_filter_add (fun y => (MT k).testBit y) (l := L)
    obtain ⟨y, hy, hyks⟩ := class_survivor hC hc ks (L.filter (fun y => (MT k).testBit y))
      (fun k' hk' => hlt k' (by simp [hk'])) (hnd.filter _)
      (fun y hy => hsub y (List.mem_of_mem_filter hy)) (by simp at hlen; omega)
    have hyk : (MT k).testBit y = true := by simpa using (List.mem_filter.mp hy).2
    exact ⟨y, List.mem_of_mem_filter hy, by
      intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | h
      · exact hyk
      · exact hyks k' h⟩

theorem stepV_getD (b k : Nat) : ∀ (v : List Nat) (prev j : Nat), j < v.length →
    ((stepV b v prev).getD j 0).testBit k =
      ((v.getD j 0).testBit k || ((if j = 0 then prev else v.getD (j - 1) 0).testBit k && b.testBit k))
  | [], _, _, h => by simp at h
  | s :: rest, prev, 0, _ => by simp [stepV, Nat.testBit_or, Nat.testBit_and]
  | s :: rest, prev, j + 1, h => by
    simp only [stepV, List.getD_cons_succ]
    rw [stepV_getD b k rest s j (by simpa using h)]
    cases j with
    | zero => simp
    | succ j => simp

theorem stepV_length (b : Nat) : ∀ (v : List Nat) (prev : Nat), (stepV b v prev).length = v.length
  | [], _ => rfl
  | _ :: rest, prev => by simp [stepV, stepV_length b rest]

/-- DP invariant: entry `j` holds the states blocking at least `j` of the processed pairs. -/
theorem dpB_spec {k : Nat} (hk : k < NS) :
    ∀ (ps : List (Nat × Nat)) (v : List Nat) (n : Nat),
      (∀ j < v.length, (v.getD j 0).testBit k = true ↔ j ≤ n) →
      ∀ j < v.length, ((dpB ps v).getD j 0).testBit k = true ↔ j ≤ n + (ps.filter (fun p => p.2.testBit k)).length
  | [], v, n, hv => by simpa using hv
  | p :: ps, v, n, hv => by
    simp only [dpB]
    intro j hj
    have hlen := stepV_length p.2 v 0
    by_cases hb : p.2.testBit k = true
    · have h' := dpB_spec hk ps (stepV p.2 v 0) (n + 1) (by
        intro i hi
        rw [hlen] at hi
        rw [stepV_getD p.2 k v 0 i hi, hb, Bool.and_true]
        cases i with
        | zero => have := (hv 0 hi).mpr (Nat.zero_le n); simpa using this
        | succ i =>
          simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Bool.or_eq_true]
          rw [hv (i + 1) hi, hv i (by omega)]; omega) j (by rw [hlen]; exact hj)
      rw [h', List.filter_cons, if_pos hb, List.length_cons]; omega
    · have hb' : p.2.testBit k = false := by simpa using hb
      have h' := dpB_spec hk ps (stepV p.2 v 0) n (by
        intro i hi
        rw [hlen] at hi
        rw [stepV_getD p.2 k v 0 i hi, hb', Bool.and_false, Bool.or_false]
        exact hv i hi) j (by rw [hlen]; exact hj)
      rw [h', List.filter_cons, if_neg hb]

theorem admC_bit (hCB : CBSpec) {U r c k : Nat} (hc : c < 35) (hk : k < NS) :
    (admC U r c).testBit k = true ↔
      ((cmemL c).filter (fun x => U.testBit x)).length - 2 * (r - 1) ≤
        (((cmemL c).filter (fun x => U.testBit x)).filter (fun x => (BLK x).testBit k)).length := by
  unfold admC
  rw [hCB c hc]
  set xs := (cmemL c).filter (fun x => U.testBit x) with hxs
  have hps : ((cmemL c).map (fun x => (x, BLK x))).filter (fun p => U.testBit p.1) = xs.map (fun x => (x, BLK x)) := by
    rw [hxs, List.filter_map]; rfl
  simp only [hps, List.length_map]
  set m := xs.length - 2 * (r - 1)
  have hinit : ∀ j < (ALLS :: List.replicate m 0).length,
      ((ALLS :: List.replicate m 0).getD j 0).testBit k = true ↔ j ≤ 0 := by
    intro j hj
    cases j with
    | zero => simp [alls_bit hk]
    | succ j =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate]
      by_cases hjm : j < m <;> simp [hjm]
  rw [dpB_spec hk _ _ 0 hinit m (by simp)]
  have : (xs.map (fun x => (x, BLK x))).filter (fun p => p.2.testBit k) = (xs.filter (fun x => (BLK x).testBit k)).map (fun x => (x, BLK x)) := by
    rw [List.filter_map]; rfl
  rw [this, List.length_map]; omega

/-- Admissibility: a state that blocks too few members of a class leaves more than `2(r-1)` survivors there. -/
theorem claim_of_not_adm (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) {U r c k : Nat}
    (hc : c < 35) (hk : k < NS) (hadm : (admC U r c).testBit k = false) : Claim (U &&& MT k) (r - 1) := by
  intro ks hlen hlt
  set xs := (cmemL c).filter (fun x => U.testBit x) with hxs
  have hxs245 : ∀ x ∈ xs, x < 245 := fun x hx => (hCl c hc).2 x (List.mem_of_mem_filter hx)
  have hcnt : ¬ (xs.length - 2 * (r - 1) ≤ (xs.filter (fun x => (BLK x).testBit k)).length) := by
    intro hle
    have := (admC_bit hCB hc hk).mpr hle
    rw [hadm] at this; simp at this
  have hflt : xs.filter (fun x => (BLK x).testBit k) = xs.filter (fun x => !(MT k).testBit x) :=
    List.filter_congr (fun x hx => by rw [hB x (hxs245 x hx) k hk])
  have hsplit := List.length_eq_length_filter_add (fun y => (MT k).testBit y) (l := xs)
  rw [hflt] at hcnt
  obtain ⟨y, hy, hyks⟩ := class_survivor hC hc ks (xs.filter (fun y => (MT k).testBit y)) hlt
    (((hCl c hc).1.filter _).filter _) (fun y hy => List.mem_of_mem_filter (List.mem_of_mem_filter hy))
    (by rw [hlen]; omega)
  have hyxs := List.mem_of_mem_filter hy
  refine ⟨y, hxs245 y hyxs, ?_, hyks⟩
  rw [Nat.testBit_and]
  simp only [Bool.and_eq_true]
  exact ⟨by simpa using (List.mem_filter.mp hyxs).2, by simpa using (List.mem_filter.mp hy).2⟩

/-- Dominance: a state good on all of `U ∩ M_k` inherits `k`'s claim. -/
theorem claim_of_dom (hB : BlkSpec) {U k a n : Nat} (ha : a < NS) (hd : (domk U k).testBit a = true)
    (h : Claim (U &&& MT k) n) : Claim (U &&& MT a) n := by
  have hgood : ∀ x, (U &&& MT k).testBit x = true → x < 245 → (MT a).testBit x = true := by
    intro x hx hx245
    have := ((testBit_andMap _ _ _ _).mp hd).2 x (mem_bitsList.mpr ⟨hx245, hx⟩)
    rw [Nat.testBit_xor, alls_bit ha, hB x hx245 a ha] at this
    simpa using this
  intro ks hlen hlt
  obtain ⟨x, hx245, hx, hks⟩ := h ks hlen hlt
  refine ⟨x, hx245, ?_, hks⟩
  have hU : U.testBit x = true := by rw [Nat.testBit_and] at hx; simp at hx; exact hx.1
  rw [Nat.testBit_and, hU, hgood x hx hx245]; rfl

theorem testBit_one_shift {j k : Nat} : (1 <<< j).testBit k = true ↔ k = j := by
  rw [Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have : k - j = 0 := by
      by_contra hne
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h2; exact hne h2
    omega
  · rintro rfl; simp

/-- **The node lemma.** -/
theorem claim_of_nodeOK (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) {U r l : Nat} {cs K Kd : List Nat}
    (hU : ∀ x, U.testBit x = true → x < 245) (hcs : ∀ c ∈ cs, c < 35) (h : nodeOK U r l cs K Kd = true)
    (hK : ∀ k ∈ K, k < NS → Claim (U &&& MT k) (r - 1)) (hKd : ∀ k ∈ Kd, Claim (U &&& MT k) (r - 1)) :
    Claim U r := by
  intro ks hlen hlt
  by_contra hno
  simp only [nodeOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, hz⟩ := h
  have hl245 := hU l hl
  obtain ⟨k, hkks, hkl⟩ : ∃ k ∈ ks, (MT k).testBit l = false := by
    by_contra hall
    push Not at hall
    exact hno ⟨l, hl245, hl, fun k hk => by simpa using hall k hk⟩
  have hk : k < NS := hlt k hkks
  have hperm := List.perm_cons_erase hkks
  have hlen' : (ks.erase k).length = r - 1 := by rw [List.length_erase_of_mem hkks, hlen]
  have hlt' : ∀ j ∈ ks.erase k, j < NS := fun j hj => hlt j (List.mem_of_mem_erase hj)
  have finish : Claim (U &&& MT k) (r - 1) → False := fun hcl =>
    hno ((good_perm hperm).mpr (good_cons.mpr (hcl _ hlen' hlt')))
  have hbl : (BLK l).testBit k = true := by rw [hB l hl245 k hk, hkl]; rfl
  by_cases hadm : (admL U r cs).testBit k = true
  · have hb : (BLK l &&& admL U r cs &&& ((orMap (fun k => 1 <<< k) K 0 ||| orMap (fun k => domk U k) Kd 0) ^^^
        ALLS)).testBit k = false := by rw [hz]; simp
    rw [Nat.testBit_and, Nat.testBit_and, hbl, hadm, Nat.testBit_xor, alls_bit hk] at hb
    simp only [Bool.true_and, Bool.bne_true, Bool.not_eq_false'] at hb
    rw [Nat.testBit_or] at hb
    rcases Bool.or_eq_true_iff.mp hb with h1 | h2
    · obtain ⟨j, hj, hjk⟩ := ((testBit_orMap _ _ _ _).mp h1).resolve_left (by simp)
      have := testBit_one_shift.mp hjk; subst this
      exact finish (hK _ hj hk)
    · obtain ⟨j, hj, hjk⟩ := ((testBit_orMap _ _ _ _).mp h2).resolve_left (by simp)
      exact finish (claim_of_dom hB hk hjk (hKd j hj))
  · have : ¬ (ALLS.testBit k = true ∧ ∀ c ∈ cs, (admC U r c).testBit k = true) := fun h' =>
      hadm ((testBit_andMap _ _ _ _).mpr h')
    have hc : ∃ c ∈ cs, (admC U r c).testBit k = false := by
      by_contra hn; push Not at hn
      exact this ⟨alls_bit hk, fun c hc => by simpa using hn c hc⟩
    obtain ⟨c, hc, hcf⟩ := hc
    exact finish (claim_of_not_adm hB hC hCl hCB (hcs c hc) hk hcf)

theorem bits_and_left {U V x : Nat} (hU : ∀ x, U.testBit x = true → x < 245) (h : (U &&& V).testBit x = true) :
    x < 245 := by
  rw [Nat.testBit_and] at h; simp at h; exact hU x h.1

/-- Depth 2: children are leaves. -/
theorem claim_two (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) {U l : Nat} {cs K : List Nat}
    (hU : ∀ x, U.testBit x = true → x < 245) (hcs : ∀ c ∈ cs, c < 35) (h : node2 U l cs K = true) :
    Claim U 2 := by
  simp only [node2, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hK⟩ := h
  have hleaf : ∀ k ∈ K, Claim (U &&& MT k) (2 - 1) := fun k hk =>
    claim_one_of_leafOK hB (fun x hx => bits_and_left hU hx) (hK k hk).2
  exact claim_of_nodeOK hB hC hCl hCB hU hcs hn (fun k hk _ => hleaf k hk) (by simp)

theorem bits_full_and {V x : Nat} (h : (FULL &&& V).testBit x = true) : x < 245 := by
  have hF : FULL = 2 ^ 245 - 1 := by decide +kernel
  rw [Nat.testBit_and, hF, Nat.testBit_two_pow_sub_one] at h
  simp at h; exact h.1

/-- Depth 1, assembled from its coverage check and its chunks. -/
theorem claim_three_of_chunks (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) {U l : Nat} {cs : List Nat}
    (chs : List (List (Nat × Nat × List Nat × List Nat))) (hU : ∀ x, U.testBit x = true → x < 245)
    (hcov : covOK U l cs (chs.flatMap (fun ch => ch.map (·.1))) = true)
    (hch : ∀ ch ∈ chs, chunkOK U ch = true) : Claim U 3 := by
  simp only [covOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcov
  obtain ⟨hcs, hn⟩ := hcov
  refine claim_of_nodeOK hB hC hCl hCB hU hcs hn (fun k hk _ => ?_) (by simp)
  obtain ⟨ch, hchm, hkm⟩ := List.mem_flatMap.mp hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hkm
  have := hch ch hchm
  simp only [chunkOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨_, hcs2⟩, h2⟩ := this e he
  exact claim_two hB hC hCl hCB (fun x hx => bits_and_left hU hx) hcs2 h2

/-- The root: every state blocking `l0` has its depth-1 claim. -/
theorem claim_four (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) {l0 : Nat} {R : List Nat}
    (hroot : nodeOK FULL 4 l0 [] R [] = true) (hR : ∀ k ∈ R, Claim (FULL &&& MT k) 3) : Claim FULL 4 :=
  claim_of_nodeOK hB hC hCl hCB (fun x hx => by
      have hF : FULL = 2 ^ 245 - 1 := by decide +kernel
      rw [hF, Nat.testBit_two_pow_sub_one] at hx; simpa using hx) (by simp) hroot
    (fun k hk _ => hR k hk) (by simp)

end LRC.O7P2
