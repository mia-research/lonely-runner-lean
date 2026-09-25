import LonelyRunner.LRC.Spec.SyncBlockN
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# The synchronised block at its period points: a train cannot carry the isolation past them

2026-09-25.  A fast block `{N + e : e ∈ E}` with whole-number offsets moves at its common phase `N·t`,
while its offsets `e·t` fix its shape.  When `E`'s offsets share the factor `g`, at every period point
`t₀ = k/g` each offset reads a whole number: the whole train sits at one point of the circle.  Then
`y = 1/2` is at distance `1/2` from every offset, and `sync_block` clears the whole block at a named
instant within one turn `[t₀, t₀ + 1/N]`, as soon as `8·Emax ≤ 3·N`
(`block_clear_at_period`).  With a core clear on that turn, everything is clear
(`lonely_at_period`).

So the delay a resonant train imposes (the relay of `experiments/nN/redo/perturb_delay_v3.out`) ends by
the train's next period point at which the core has room: a train cannot carry the isolation event
beyond it.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SyncPeriod

/-- `circDist (1/2 − m) = 1/2` for a whole number `m`. -/
theorem circDist_half_sub_int (m : ℤ) : circDist ((1 : ℝ) / 2 - m) = 1 / 2 := by
  rw [show (1 : ℝ) / 2 - m = 1 / 2 + ((-m : ℤ) : ℝ) by push_cast; ring, ConstructionN.circDist_add_int]
  unfold circDist
  rw [show Int.fract ((1 : ℝ) / 2) = 1 / 2 from Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- **The train at a period point.**  Offsets all multiples of `g > 0`, `t₀ = k/g`: the block
`{N + e}` is clear at `1/8` at a named instant in `[t₀, t₀ + 1/N)`, once `8·Emax ≤ 3·N`. -/
theorem block_clear_at_period {E : Finset ℕ} {g k N Emax : ℕ} (hg : 0 < g) (hN : 0 < N)
    (hdiv : ∀ e ∈ E, g ∣ e) (hEm : ∀ e ∈ E, e ≤ Emax) (hbig : 8 * Emax ≤ 3 * N) :
    let t₀ : ℝ := (k : ℝ) / g
    let t := t₀ + Int.fract (-(1 / 2 : ℝ) - N * t₀) / N
    t₀ ≤ t ∧ t < t₀ + 1 / N ∧ ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist (((N : ℝ) + e) * t) := by
  intro t₀ t
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have key := LRC.SyncBlock.sync_block (E := E.image (fun e : ℕ => (e : ℝ))) (N := (N : ℝ)) (t₀ := t₀)
    (y := 1 / 2) (Emax := (Emax : ℝ)) hNR
    (by intro x hx; obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx; positivity)
    (by intro x hx; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx; exact_mod_cast hEm e he)
    (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, rfl⟩ := hdiv e he
      have hint : ((g * q : ℕ) : ℝ) * t₀ = ((q * k : ℕ) : ℤ) := by
        show ((g * q : ℕ) : ℝ) * ((k : ℝ) / g) = _
        push_cast; field_simp
      rw [hint, circDist_half_sub_int]
      have : (Emax : ℝ) / N ≤ 3 / 8 := by
        rw [div_le_iff₀ hNR]; have : (8 * Emax : ℝ) ≤ 3 * N := by exact_mod_cast hbig
        linarith
      linarith)
  obtain ⟨h1, h2, h3⟩ := key
  exact ⟨h1, h2, fun e he => h3 _ (Finset.mem_image_of_mem _ he)⟩

/-- **A core and a train at a period point.**  If the core is clear at `1/8` throughout the turn after
`t₀ = k/g`, the core and the whole block are clear together at a named instant of that turn. -/
theorem lonely_at_period {C E : Finset ℕ} {g k N Emax : ℕ} (hg : 0 < g) (hN : 0 < N)
    (hdiv : ∀ e ∈ E, g ∣ e) (hEm : ∀ e ∈ E, e ≤ Emax) (hbig : 8 * Emax ≤ 3 * N)
    (hC : ∀ c ∈ C, ∀ s : ℝ, (k : ℝ) / g ≤ s → s ≤ (k : ℝ) / g + 1 / N →
      (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * s)) :
    ∃ t : ℝ, (k : ℝ) / g ≤ t ∧ t ≤ (k : ℝ) / g + 1 / N ∧
      (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * t)) ∧
      ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist (((N : ℝ) + e) * t) := by
  obtain ⟨h1, h2, h3⟩ := block_clear_at_period (k := k) hg hN hdiv hEm hbig
  exact ⟨_, h1, h2.le, fun c hc => hC c hc _ h1 h2.le, h3⟩

end LRC.SyncPeriod
