import Mathlib
import HarmonicCompute

namespace Fresh.Harmonic

def Bound.Holds (a : Bound) (x : ℝ) : Prop :=
  if a.strict then x < a.value else x ≤ a.value

theorem Bound.holds_add {a b : Bound} {x y : ℝ} (ha : a.Holds x) (hb : b.Holds y) :
    (a.add b).Holds (x+y) := by
  rcases a with ⟨a,s⟩
  rcases b with ⟨b,t⟩
  cases s <;> cases t <;> simp [Holds, add] at * <;> linarith

theorem Bound.holds_of_not_tighter {a b : Bound} {x : ℝ}
    (h : a.tighter b = false) (hx : b.Holds x) : a.Holds x := by
  rcases a with ⟨a,s⟩
  rcases b with ⟨b,t⟩
  cases s <;> cases t <;> simp [Holds, tighter] at *
  · exact hx.trans (by exact_mod_cast (show b ≤ a by omega))
  · exact hx.le.trans (by exact_mod_cast (show b ≤ a by omega))
  · exact hx.trans_lt (by exact_mod_cast (show b < a by omega))
  · exact hx.trans_le (by exact_mod_cast (show b ≤ a by omega))

theorem Bound.holds_min {a b : Bound} {x : ℝ} (ha : a.Holds x) (hb : b.Holds x) :
    (a.min b).Holds x := by unfold min; split <;> assumption

theorem Bound.not_negative {a : Bound} (h : a.Holds 0) :
    a.tighter ⟨0,false⟩ = false := by
  rcases a with ⟨a,s⟩
  cases s
  · simp [Holds] at h
    simp [tighter,not_lt.mpr (show 0 ≤ a by exact_mod_cast h)]
  · simp [Holds] at h
    have hz : 0 < a := by exact_mod_cast h
    simp [tighter,not_lt.mpr hz.le,ne_of_gt hz]

def Fits (b : Matrix n) (z : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, Bound.Holds b[i][j] (z i-z j)

def Valid (c : Choice n) (z : Fin n → ℝ) : Prop :=
  c.2.2.1.Holds (z c.1-z c.2.1) ∧ c.2.2.2.Holds (z c.2.1-z c.1)

def Satisfies (cs : List (Clause n)) (z : Fin n → ℝ) : Prop :=
  ∀ c ∈ cs, ∃ w ∈ c, Valid w z

private theorem cycle {a b : Bound} {x : ℝ}
    (ha : a.Holds x) (hb : b.Holds (-x)) : (a.add b).tighter ⟨0,false⟩ = false := by
  apply Bound.not_negative
  simpa using Bound.holds_add ha hb

private theorem constrain_sound {b : Matrix n} {i j : Fin n} {a : Bound} {z : Fin n → ℝ}
    (h : Fits b z) (ha : a.Holds (z i-z j)) : ∃ b', constrain b i j a = some b' ∧ Fits b' z := by
  have hn := cycle ha (show b[j][i].Holds (-(z i-z j)) by convert h j i using 1 <;> ring)
  unfold constrain
  split
  · exact ⟨b,rfl,h⟩
  · simp only [hn,Bool.false_eq_true,if_false]
    refine ⟨_,rfl,?_⟩
    intro p q
    change Bound.Holds ((matrix _)[p.val][q.val]) _
    simp only [matrix, Vector.getElem_ofFn]
    apply Bound.holds_min (h p q)
    convert Bound.holds_add (Bound.holds_add (h p i) ha) (h j q) using 1 <;> ring

private theorem impose_sound {b : Matrix n} {c : Choice n} {z : Fin n → ℝ}
    (h : Fits b z) (hc : Valid c z) : ∃ b', impose b c = some b' ∧ Fits b' z := by
  rcases c with ⟨i,j,u,v⟩
  obtain ⟨d,hd,hf⟩ := constrain_sound h hc.1
  obtain ⟨e,he,hf'⟩ := constrain_sound hf hc.2
  exact ⟨e, by simp [impose,hd,he],hf'⟩

theorem possible_true {b : Matrix n} {c : Choice n} {z : Fin n → ℝ}
    (h : Fits b z) (hc : Valid c z) : possible b c = true := by
  rcases c with ⟨i,j,u,v⟩
  have neg {a : Bound} {i j : Fin n} (ha : a.Holds (z i-z j)) (hd : Bound.Holds (x := z j-z i) b[j][i]) :
      (a.add b[j][i]).tighter ⟨0,false⟩ = false :=
    cycle ha (by convert hd using 1 <;> ring)
  have hv : (u.add v).tighter ⟨0,false⟩ = false :=
    cycle hc.1 (by convert hc.2 using 1 <;> ring)
  unfold possible
  change (!(u.add b[j][i]).tighter ⟨0,false⟩ &&
    !(v.add b[i][j]).tighter ⟨0,false⟩ && !(u.add v).tighter ⟨0,false⟩) = true
  rw [neg hc.1 (h j i), neg hc.2 (h i j), hv]
  rfl

private theorem pending_sound {b : Matrix n} {cs : List (Clause n)} {z : Fin n → ℝ}
    (h : Fits b z) (hc : Satisfies cs z) : Satisfies (pending b cs) z := by
  intro c hm
  unfold pending at hm
  rw [List.mem_mergeSort] at hm
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  obtain ⟨w,hw,hv⟩ := hc a (List.mem_filter.mp ha).1
  exact ⟨w,List.mem_filter.mpr ⟨hw,possible_true h hv⟩,hv⟩

theorem solve_sound {b : Matrix n} {cs : List (Clause n)} {z : Fin n → ℝ}
    (h : Fits b z) (hc : Satisfies cs z) (fuel : ℕ) :
    ∃ b' ∈ solve fuel b cs, Fits b' z := by
  induction fuel generalizing b cs with
  | zero => exact ⟨b,by simp [solve],h⟩
  | succ k ih =>
    have hp := pending_sound h hc
    cases he : pending b cs with
    | nil => exact ⟨b,by simp [solve,he],h⟩
    | cons first rest =>
      rw [he] at hp
      obtain ⟨w,hw,hv⟩ := hp first (by simp)
      obtain ⟨d,hd,hf⟩ := impose_sound h hv
      obtain ⟨e,he',hf'⟩ := ih (cs := rest) hf (fun a ha => hp a (List.mem_cons_of_mem _ ha))
      refine ⟨e, ?_,hf'⟩
      simp only [solve,he,List.mem_flatMap]
      exact ⟨w,hw,by simpa [hd] using he'⟩

theorem replay_sound {p : Vector ℕ n} {ms : List ℕ} {z : Fin n → ℝ}
    (h : Fits (root p) z) (hc : ∀ m ∈ ms, Satisfies (clauses p m) z) :
    ∃ b ∈ replay p ms, Fits b z := by
  unfold replay
  have go (ms : List ℕ) (states : List (Matrix n))
      (hs : ∃ b ∈ states, Fits b z) (hc : ∀ m ∈ ms, Satisfies (clauses p m) z) :
      ∃ b ∈ ms.foldl (fun states m =>
        let jobs := clauses p m
        dedup (states.flatMap fun b => solve (jobs.length+1) b jobs)) states, Fits b z := by
    induction ms generalizing states with
    | nil => exact hs
    | cons m rest ih =>
      simp only [List.foldl_cons]
      apply ih _ _ (fun j hj => hc j (List.mem_cons_of_mem _ hj))
      obtain ⟨b,hb,hf⟩ := hs
      obtain ⟨d,hd,hd'⟩ := solve_sound hf (hc m (by simp)) ((clauses p m).length+1)
      refine ⟨d,?_,hd'⟩
      unfold dedup
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList]
      simpa only [List.contains_iff_mem] using (List.mem_flatMap.mpr ⟨b,hb,hd⟩ :
        d ∈ states.flatMap (fun b => solve ((clauses p m).length+1) b (clauses p m)))
  exact go ms _ ⟨_,by simp,h⟩ hc

#print axioms replay_sound
end Fresh.Harmonic
