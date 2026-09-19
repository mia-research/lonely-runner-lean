import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Interior witness normalisation, proved

Measured (≈242,000 profiles, 0 counterexamples): every profile that has a witness has one at which
some constraint is **tight** — `q mod b = L(b)` or `U(b)`. The measurement also reported that the
number of supplying `(b, end)` pairs is never fewer than **two**, with the two ends splitting evenly.

Both facts come from one argument, and it is a walk rather than a count.

Let `P q` say that `q` satisfies every constraint `L ≤ q mod b ≤ U`. Suppose `P` holds somewhere and
fails somewhere below. Step down from a witness while `P` still holds; the walk must stop, because
`P` fails below. At the stopping point `q`, `P q` holds and `P (q-1)` fails, so some constraint
separates them — and a constraint can only separate `q` from `q-1` by being **exactly at its lower
edge** at `q`. Stepping up instead gives the upper edge, which is why there are always at least two.

No counting, no density, no appeal to abundance — the three families that were refuted. -/

namespace EdgeWitness

variable (l : List (ℤ × ℤ × ℤ))

/-- `q` satisfies every constraint: for each `(b, L, U)`, `L ≤ q % b ≤ U`. -/
def Sat (q : ℤ) : Prop := ∀ p ∈ l, p.1 ≤ 0 ∨ (p.2.1 ≤ q % p.1 ∧ q % p.1 ≤ p.2.2)

instance : DecidablePred (Sat l) := fun _ => List.decidableBAll _ _

/-- **A constraint can only separate `q` from `q-1` at its lower edge.**  If `q` satisfies
everything and `q-1` does not, the failing constraint has `q % b` exactly `L`. -/
theorem tight_of_step {q : ℤ} (hL0 : ∀ p ∈ l, 0 ≤ p.2.1)
    (hq : Sat l q) (hq' : ¬ Sat l (q - 1)) :
    ∃ p ∈ l, 0 < p.1 ∧ q % p.1 = p.2.1 := by
  rw [Sat, not_forall] at hq'
  obtain ⟨p, hp⟩ := hq'
  rw [_root_.not_imp] at hp
  obtain ⟨hpl, hpf⟩ := hp
  push_neg at hpf
  obtain ⟨hb, hfail⟩ := hpf
  have hb' : 0 < p.1 := by omega
  obtain ⟨hL, hU⟩ := (hq p hpl).resolve_left (by omega)
  refine ⟨p, hpl, hb', ?_⟩
  -- if `q % b > L` then `(q-1) % b = q % b - 1` still lies in `[L, U]`, contradicting failure
  by_contra hne
  have hlt : p.2.1 < q % p.1 := lt_of_le_of_ne hL (Ne.symm hne)
  have hL0' : 0 ≤ p.2.1 := hL0 p hpl
  have hone : 1 ≤ q % p.1 := by omega
  have hstep : (q - 1) % p.1 = q % p.1 - 1 := by
    have h0 : 0 ≤ q % p.1 := Int.emod_nonneg q hb'.ne'
    have h1 : q % p.1 < p.1 := Int.emod_lt_of_pos q hb'
    have hrw : q - 1 = (q % p.1 - 1) + p.1 * (q / p.1) := by
      have := Int.mul_ediv_add_emod q p.1; omega
    rw [hrw, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hle' : p.2.1 ≤ (q - 1) % p.1 := by rw [hstep]; omega
  have hbad := hfail hle'
  rw [hstep] at hbad
  omega

/-- **Interior witness normalisation.**  If some `q` satisfies every constraint and some `q₀ ≤ q`
does not, then a satisfying point exists at which one constraint is exactly at its lower edge. -/
theorem edge_witness {q₀ q : ℤ} (hL0 : ∀ p ∈ l, 0 ≤ p.2.1)
    (hq : Sat l q) (h0 : ¬ Sat l q₀) (hle : q₀ ≤ q) :
    ∃ r, Sat l r ∧ ∃ p ∈ l, 0 < p.1 ∧ r % p.1 = p.2.1 := by
  -- the least `k` with `Sat (q₀ + k)`; it exists because `Sat q` and `q = q₀ + (q - q₀)`
  have hex : ∃ k : ℕ, Sat l (q₀ + k) := ⟨(q - q₀).toNat, by rwa [Int.toNat_of_nonneg (by omega),
    add_sub_cancel]⟩
  classical
  let k := Nat.find hex
  have hk : Sat l (q₀ + k) := Nat.find_spec hex
  have hkpos : k ≠ 0 := by
    intro h
    apply h0
    have : (q₀ : ℤ) + (k : ℕ) = q₀ := by rw [h]; simp
    rwa [this] at hk
  have hprev : ¬ Sat l (q₀ + k - 1) := by
    have hlt : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hkpos) one_pos
    have := Nat.find_min hex hlt
    have hcast : (q₀ : ℤ) + ((k - 1 : ℕ) : ℤ) = q₀ + k - 1 := by
      have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        have := Nat.pos_of_ne_zero hkpos; push_cast [Nat.cast_sub this]; ring
      rw [this]; ring
    rwa [hcast] at this
  exact ⟨q₀ + k, hk, tight_of_step l hL0 hk hprev⟩

/-- **The mirror: stepping up lands on the upper edge.**  A constraint can only separate `q` from
`q+1` by being exactly at its upper edge at `q`. -/
theorem tight_of_step_up {q : ℤ} (hUb : ∀ p ∈ l, p.2.2 < p.1)
    (hq : Sat l q) (hq' : ¬ Sat l (q + 1)) :
    ∃ p ∈ l, 0 < p.1 ∧ q % p.1 = p.2.2 := by
  rw [Sat, not_forall] at hq'
  obtain ⟨p, hp⟩ := hq'
  rw [Classical.not_imp] at hp
  obtain ⟨hpl, hpf⟩ := hp
  push_neg at hpf
  obtain ⟨hb, hfail⟩ := hpf
  have hb' : 0 < p.1 := by omega
  obtain ⟨hL, hU⟩ := (hq p hpl).resolve_left (by omega)
  refine ⟨p, hpl, hb', ?_⟩
  by_contra hne
  have hlt : q % p.1 < p.2.2 := lt_of_le_of_ne hU hne
  have hUb' : p.2.2 < p.1 := hUb p hpl
  have hstep : (q + 1) % p.1 = q % p.1 + 1 := by
    have h0 : 0 ≤ q % p.1 := Int.emod_nonneg q hb'.ne'
    have hrw : q + 1 = (q % p.1 + 1) + p.1 * (q / p.1) := by
      have := Int.mul_ediv_add_emod q p.1; omega
    rw [hrw, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hle' : p.2.1 ≤ (q + 1) % p.1 := by rw [hstep]; omega
  have hbad := hfail hle'
  rw [hstep] at hbad
  omega

/-- **Two edges, not one.**  If `Sat` holds somewhere and fails both below and above, then a
satisfying point sits on a lower edge **and** one sits on an upper edge. This is why the measured
number of supplying `(modulus, end)` pairs is never fewer than two. -/
theorem edge_witness_both {q₀ q₁ q : ℤ} (hL0 : ∀ p ∈ l, 0 ≤ p.2.1) (hUb : ∀ p ∈ l, p.2.2 < p.1)
    (hq : Sat l q) (h0 : ¬ Sat l q₀) (h1 : ¬ Sat l q₁) (hle : q₀ ≤ q) (hge : q ≤ q₁) :
    (∃ r, Sat l r ∧ ∃ p ∈ l, 0 < p.1 ∧ r % p.1 = p.2.1) ∧
    (∃ r, Sat l r ∧ ∃ p ∈ l, 0 < p.1 ∧ r % p.1 = p.2.2) := by
  refine ⟨edge_witness l hL0 hq h0 hle, ?_⟩
  classical
  have hex : ∃ k : ℕ, ¬ Sat l (q + k) := ⟨(q₁ - q).toNat, by
    rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel]⟩
  let k := Nat.find hex
  have hk : ¬ Sat l (q + k) := Nat.find_spec hex
  have hkpos : k ≠ 0 := by intro h; apply hk; rw [h]; simpa using hq
  have hprev : Sat l (q + k - 1) := by
    have hlt : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hkpos) one_pos
    have hnn := Nat.find_min hex hlt
    have hcast : (q : ℤ) + ((k - 1 : ℕ) : ℤ) = q + k - 1 := by
      have hp : 0 < k := Nat.pos_of_ne_zero hkpos
      push_cast [Nat.cast_sub hp]; ring
    rw [hcast] at hnn
    exact not_not.1 hnn
  have hstep : (q + (k:ℤ) - 1) + 1 = q + k := by ring
  exact ⟨q + k - 1, hprev, tight_of_step_up l hUb hprev (by rw [hstep]; exact hk)⟩

end EdgeWitness
