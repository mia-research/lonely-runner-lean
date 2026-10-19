import LonelyRunner.LRC.Spec.OrderSevenP2SoundN

/-!
# AbsU5 certificate: table facts and the reduction of abstract states to table states

Bool checks (instantiated by kernel `decide` in the `OrderSevenP2Tab` part modules) and their meaning:
* `blkB` gives `BlkSpec`; `capB` gives `CapSpec`; `clsB` gives `ClassSpec` and `CBSpec`;
* `domB T ws` (one per top-digit value `T`): every unit abstract state `(T, g, rho)` has a witness table state
  (listed in `ws`) whose good instants are good for the state;
* `instTab`: runner 1's 245 instants `(c, s)` in table order; `r1B`: runner 1 is in band at each, `1 <= c <= 6`.

No `sorry`, no `native_decide`.
-/

namespace LRC.O7P2
open LRC.O7Abs

instance okDec (T : Nat) (g : List Nat) (ρ c s : Nat) : Decidable (ok T g ρ c s) := by
  unfold ok; infer_instance

def allB : Nat → Nat → (Nat → Bool) → Bool
  | 0, _, _ => true
  | n + 1, i, f => f i && allB n (i + 1) f

theorem allB_spec : ∀ (n i : Nat) (f : Nat → Bool), allB n i f = true → ∀ j, i ≤ j → j < i + n → f j = true
  | 0, i, f, _, j, h1, h2 => by omega
  | n + 1, i, f, h, j, h1, h2 => by
    simp only [allB, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact allB_spec n (i + 1) f h.2 j h1' (by omega)

theorem allB_spec2 {n m : Nat} {f : Nat → Nat → Bool} (h : allB n 0 (fun j => allB m 0 (fun t => f j t)) = true)
    {j t : Nat} (hj : j < n) (ht : t < m) : f j t = true :=
  allB_spec m 0 _ (allB_spec n 0 _ h j (Nat.zero_le _) (by omega)) t (Nat.zero_le _) (by omega)

def blkB (lo hi : Nat) : Bool := allB (hi - lo) lo (fun x => allB 81 0 (fun j => allB 128 0 (fun t =>
  !decide (128 * j + t < NS) || ((BLK x).testBit (128 * j + t) == !(MT (128 * j + t)).testBit x))))

theorem blk_of {lo hi : Nat} (h : blkB lo hi = true) {x k : Nat} (h1 : lo ≤ x) (h2 : x < hi) (hk : k < NS) :
    (BLK x).testBit k = !(MT k).testBit x := by
  have hx := allB_spec _ _ _ h x h1 (by omega)
  have hNS : NS = 10290 := rfl
  have := allB_spec2 hx (j := k / 128) (t := k % 128) (by omega) (Nat.mod_lt _ (by norm_num))
  rw [show 128 * (k / 128) + k % 128 = k by omega] at this
  simpa [hk] using this

def capB (lo hi : Nat) : Bool := allB (hi - lo) lo (fun j => allB 128 0 (fun t =>
  !decide (128 * j + t < NS) || allB 35 0 (fun c =>
    decide (((cmemL c).filter (fun x => !(MT (128 * j + t)).testBit x)).length ≤ 2))))

theorem cap_of {lo hi : Nat} (h : capB lo hi = true) {k : Nat} (h1 : lo ≤ k / 128) (h2 : k / 128 < hi)
    (hk : k < NS) {c : Nat} (hc : c < 35) : ((cmemL c).filter (fun x => !(MT k).testBit x)).length ≤ 2 := by
  have hj := allB_spec _ _ _ h (k / 128) h1 (by omega)
  have ht := allB_spec _ _ _ hj (k % 128) (Nat.zero_le _)
    (by have := Nat.mod_lt k (show 128 > 0 by norm_num); omega)
  rw [show 128 * (k / 128) + k % 128 = k by omega] at ht
  simp only [hk, decide_true, Bool.not_true, Bool.false_or] at ht
  simpa using allB_spec _ _ _ ht c (Nat.zero_le _) (by omega)

def clsB : Bool := allB 35 0 (fun c => decide (cmemL c).Nodup && (cmemL c).all (fun x => decide (x < 245)) &&
  decide (cmemB c = (cmemL c).map (fun x => (x, BLK x))))

theorem cls_of (h : clsB = true) : ClassSpec ∧ CBSpec := by
  constructor
  · intro c hc
    have := allB_spec _ _ _ h c (Nat.zero_le _) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact ⟨this.1.1, this.1.2⟩
  · intro c hc
    have := allB_spec _ _ _ h c (Nat.zero_le _) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

def instTab : List (Nat × Nat) := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 19), (1, 20), (1, 21), (1, 22), (1, 23), (1, 24), (1, 25), (1, 26), (1, 27), (1, 28), (1, 29), (1, 30), (1, 31), (1, 32), (1, 33), (1, 34), (1, 35), (1, 36), (1, 37), (1, 38), (1, 39), (1, 40), (1, 41), (1, 42), (1, 43), (1, 44), (1, 45), (1, 46), (1, 47), (1, 48), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (2, 17), (2, 18), (2, 19), (2, 20), (2, 21), (2, 22), (2, 23), (2, 24), (2, 25), (2, 26), (2, 27), (2, 28), (2, 29), (2, 30), (2, 31), (2, 32), (2, 33), (2, 34), (2, 35), (2, 36), (2, 37), (2, 38), (2, 39), (2, 40), (2, 41), (2, 42), (2, 43), (2, 44), (2, 45), (2, 46), (2, 47), (2, 48), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (3, 18), (3, 19), (3, 20), (3, 21), (3, 22), (3, 23), (3, 24), (3, 25), (3, 26), (3, 27), (3, 28), (3, 29), (3, 30), (3, 31), (3, 32), (3, 33), (3, 34), (3, 35), (3, 36), (3, 37), (3, 38), (3, 39), (3, 40), (3, 41), (3, 42), (3, 43), (3, 44), (3, 45), (3, 46), (3, 47), (3, 48), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (4, 16), (4, 17), (4, 18), (4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (4, 24), (4, 25), (4, 26), (4, 27), (4, 28), (4, 29), (4, 30), (4, 31), (4, 32), (4, 33), (4, 34), (4, 35), (4, 36), (4, 37), (4, 38), (4, 39), (4, 40), (4, 41), (4, 42), (4, 43), (4, 44), (4, 45), (4, 46), (4, 47), (4, 48), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27), (5, 28), (5, 29), (5, 30), (5, 31), (5, 32), (5, 33), (5, 34), (5, 35), (5, 36), (5, 37), (5, 38), (5, 39), (5, 40), (5, 41), (5, 42), (5, 43), (5, 44), (5, 45), (5, 46), (5, 47), (5, 48)]

def units49L : List Nat := [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48]

def inst (x : Nat) : Nat × Nat := instTab.getD x (0, 0)

def walk (m T : Nat) (g : List Nat) (ρ : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | x, p :: ps => (!m.testBit x || decide (ok T g ρ p.1 p.2)) && walk m T g ρ (x + 1) ps

theorem walk_spec {m T ρ : Nat} {g : List Nat} : ∀ (x0 : Nat) (ps : List (Nat × Nat)),
    walk m T g ρ x0 ps = true → ∀ i (hi : i < ps.length), m.testBit (x0 + i) = true → ok T g ρ (ps[i]).1 (ps[i]).2
  | _, [], _, i, hi, _ => by simp at hi
  | x0, p :: ps, h, i, hi, hm => by
    simp only [walk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    cases i with
    | zero =>
      simp only [Nat.add_zero] at hm
      rcases h.1 with h1 | h1
      · rw [h1] at hm; simp at hm
      · simpa using h1
    | succ i =>
      have := walk_spec (x0 + 1) ps h.2 i (by simpa using hi)
        (by rw [show x0 + 1 + i = x0 + (i + 1) by omega]; exact hm)
      simpa using this

def domB (T : Nat) (ws : List Nat) : Bool := allB 12 0 (fun gi => allB 42 0 (fun ri =>
  decide (ws.getD (42 * gi + ri) 0 < NS) &&
    walk (MT (ws.getD (42 * gi + ri) 0)) T (fvecs.getD gi []) (units49L.getD ri 0) 0 instTab))

theorem instTab_len : instTab.length = 245 := by decide +kernel

theorem inst_eq {x : Nat} (hx : x < 245) : inst x = instTab[x]'(by rw [instTab_len]; exact hx) := by
  simp [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x < instTab.length by rw [instTab_len]; exact hx)]

theorem dom_of {T : Nat} {ws : List Nat} (h : domB T ws = true) {gi ri : Nat} (hg : gi < 12) (hr : ri < 42) :
    ∃ k, k < NS ∧ ∀ x, x < 245 → (MT k).testBit x = true →
      ok T (fvecs.getD gi []) (units49L.getD ri 0) (inst x).1 (inst x).2 := by
  have := allB_spec2 h hg hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨_, this.1, fun x hx hm => ?_⟩
  have hw := walk_spec 0 instTab this.2 x (by rw [instTab_len]; exact hx) (by simpa using hm)
  rw [inst_eq hx]; exact hw

def cB : Bool := instTab.all (fun p => decide (1 ≤ p.1 ∧ p.1 ≤ 5))

theorem c_of (h : cB = true) {x : Nat} (hx : x < 245) : 1 ≤ (inst x).1 ∧ (inst x).1 ≤ 5 := by
  simp only [cB, List.all_eq_true, decide_eq_true_eq] at h
  rw [inst_eq hx]
  exact h _ (List.getElem_mem _)

def bdomB (bs : List Nat) : Bool := allB 12 0 (fun gi => allB 42 0 (fun ri =>
  decide (bs.getD (42 * gi + ri) 0 < 420) &&
    walk (AB (bs.getD (42 * gi + ri) 0)) 0 (fvecs.getD gi []) (units49L.getD ri 0) 0 instTab))

theorem bdom_of {bs : List Nat} (h : bdomB bs = true) {gi ri : Nat} (hg : gi < 12) (hr : ri < 42) :
    ∃ b, b < 420 ∧ ∀ x, x < 245 → (AB b).testBit x = true →
      ok 0 (fvecs.getD gi []) (units49L.getD ri 0) (inst x).1 (inst x).2 := by
  have := allB_spec2 h hg hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨_, this.1, fun x hx hm => ?_⟩
  have hw := walk_spec 0 instTab this.2 x (by rw [instTab_len]; exact hx) (by simpa using hm)
  rw [inst_eq hx]; exact hw

theorem unit_index {ρ : Nat} (h1 : ρ < 49) (h2 : ρ % 7 ≠ 0) : ∃ ri, ri < 42 ∧ units49L.getD ri 0 = ρ := by
  have : ∀ ρ, ρ < 49 → ρ % 7 ≠ 0 → ∃ ri, ri < 42 ∧ units49L.getD ri 0 = ρ := by decide
  exact this ρ h1 h2

theorem fvec_index {g : List Nat} (h : g ∈ fvecs) : ∃ gi, gi < 12 ∧ fvecs.getD gi [] = g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, by simpa [fvecs] using hi, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]⟩

end LRC.O7P2
