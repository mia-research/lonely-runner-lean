import Mathlib

/-!
# The covering count, proved

`EXISTENCE_MAP_v4` §2 carried this as *verified, not proved* on 9,323,468 movers:

> mover `d` covers exactly `c · gcd(d,e)` of the flank's `e` openings,
> `c` being its blocked classes mod `q = e/gcd(d,e)`.

It is a counting statement and needs no arithmetic of `inWay` at all. The openings of a flank
are `k ∈ [0, e)` (`Openings.lcm_div_eq`), the blocking pattern has period `q`, and `q ∣ e`, so
each blocked class mod `q` contributes exactly `e/q = gcd(d,e)` openings.

The consequence is the native necessary condition for a flank to be shadowed:
`Σ_j c_j · gcd(d_j, e) ≥ e`. That condition is **necessary and not sufficient** — at the
extremal set's surviving flank it reads `24 ≥ 16` and the flank is clear regardless.
-/

namespace CoverCount

/-- **The counting lemma.**  Over `q*m` consecutive openings, a pattern that depends only on
the residue mod `q` covers exactly `|C| * m` of them. -/
theorem card_filter_mod (q : ℕ) (hq : 0 < q) (C : Finset ℕ) (hC : ∀ c ∈ C, c < q) :
    ∀ m : ℕ, ((Finset.range (q * m)).filter (fun k => k % q ∈ C)).card = C.card * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit : q * (m + 1) = q * m + q := by ring
      rw [hsplit, Finset.range_add, Finset.filter_union, Finset.card_union_of_disjoint]
      · rw [ih]
        have : ((Finset.range q).map (addLeftEmbedding (q * m))).filter (fun k => k % q ∈ C)
            = (C.filter (fun c => c < q)).map (addLeftEmbedding (q * m)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range,
            addLeftEmbedding_apply]
          constructor
          · rintro ⟨⟨i, hi, rfl⟩, hmem⟩
            have hmod : (q * m + i) % q = i := by
              rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
            rw [hmod] at hmem
            exact ⟨i, ⟨hmem, hi⟩, rfl⟩
          · rintro ⟨c, ⟨hcC, hcq⟩, rfl⟩
            refine ⟨⟨c, hcq, rfl⟩, ?_⟩
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hcq]
            exact hcC
        rw [this, Finset.card_map, Finset.filter_true_of_mem hC]
        ring
      · apply Finset.disjoint_filter_filter
        simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_map,
          addLeftEmbedding_apply]
        rintro a ha ⟨i, hi, rfl⟩
        omega

/-- **The covering count.**  With `q ∣ e`, a mover whose blocked openings are the `C`-classes
mod `q` covers exactly `|C| * (e/q)` of the `e` openings — and `e/q = gcd(d,e)` when
`q = e/gcd(d,e)`. -/
theorem cover_count {e q : ℕ} (hq : 0 < q) (hdvd : q ∣ e) (C : Finset ℕ)
    (hC : ∀ c ∈ C, c < q) :
    ((Finset.range e).filter (fun k => k % q ∈ C)).card = C.card * (e / q) := by
  obtain ⟨m, rfl⟩ := hdvd
  rw [card_filter_mod q hq C hC m, Nat.mul_div_cancel_left _ hq]

/-- `e/q = gcd(d,e)` for the reduced denominator, so the count is `c * gcd(d,e)`. -/
theorem cover_count_gcd {d e : ℕ} (he : 0 < e) (hd : 0 < Nat.gcd d e) (C : Finset ℕ)
    (hC : ∀ c ∈ C, c < e / Nat.gcd d e) :
    ((Finset.range e).filter (fun k => k % (e / Nat.gcd d e) ∈ C)).card
      = C.card * Nat.gcd d e := by
  have hg : Nat.gcd d e ∣ e := Nat.gcd_dvd_right d e
  have hq : 0 < e / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd he hg) hd
  have hqe : (e / Nat.gcd d e) ∣ e := Nat.div_dvd_of_dvd hg
  rw [cover_count hq hqe C hC, Nat.div_div_self hg he.ne']

/-- **Shadowing needs the count.**  If the blocked sets of the movers cover every opening, the
gcd-weighted count is at least `e`.  Necessary; the extremal flank shows it is not sufficient. -/
theorem shadow_needs_count {e : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range e)
    (B : ℕ → Finset ℕ) (hcov : Finset.range e ⊆ S.biUnion B) :
    e ≤ ∑ j ∈ S, (B j).card := by
  calc e = (Finset.range e).card := (Finset.card_range e).symm
    _ ≤ (S.biUnion B).card := Finset.card_le_card hcov
    _ ≤ ∑ j ∈ S, (B j).card := Finset.card_biUnion_le

end CoverCount

#print axioms CoverCount.card_filter_mod
#print axioms CoverCount.cover_count
#print axioms CoverCount.cover_count_gcd
#print axioms CoverCount.shadow_needs_count
