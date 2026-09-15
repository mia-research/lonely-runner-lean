import LonelyRunner.LRC.Cascade.SmallOrders

/-!
# The finite certificate: why the word list is finite, and what a setting is worth

Part of the cascade artefact (`LRC/Cascade/`).  The order-5 certificate (`docs/n8/ORDER5_CERTIFICATE_v2.md`) proves
`R < 4` for bounded spread by enumerating finitely many words `(setter, lap)` and bounding each by a linear program.
This module carries the part that makes that enumeration legitimate: the three finiteness bounds, and the identity
that gives a setting its value.

With `m` the nearest difference and `R = n · m · t` the reading of the cascade at time `t`:

* `cascadeR_zoneHi`      — a setting of `x` at lap `Q` lands exactly at `R = (n·Q + 1)·m/x`, so `R = (n·Q+1)/u`
                           where `u = x/m` is the setter's reading;
* `nearest_setting_ge`   — the nearest runner's own settings land at `R = n·Q + 1 ≥ n + 1`, above any cap `≤ n+1`;
  `nearest_never_sets`     hence below such a cap the nearest never sets;
* `lap_lt_of_cascadeR_lt` — under a cap `C`, a setting of `x` has `n·Q + 1 < C·u`, bounding the lap by the reading;
* `lap_lt_of_spread`      — with spread `u ≤ S`, the same bound is uniform in the arrangement: `Q < (C·S − 1)/n`;
* `laps_strictly_increase`— a runner's successive settings carry strictly increasing laps.

Together: each of the other runners sets at most `⌊(C·S−1)/n⌋` times, at strictly increasing laps, and the nearest
never sets — so the words are finitely many, which is what the enumeration needs.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CascadeCertificate

open ConstructionN MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- The cascade's reading at time `t`, measured at the nearest difference `m`: `R = n · m · t`. -/
noncomputable def cascadeR (n : ℕ) (m t : ℝ) : ℝ := (n : ℝ) * m * t

/-- **The value of a setting.** A setting of `x` at lap `Q` is the instant `zoneHi n x Q`, and there the cascade
reads exactly `(n·Q + 1)·m/x`. -/
theorem cascadeR_zoneHi (m x : ℝ) (hx : 0 < x) (Q : ℤ) :
    cascadeR n m (zoneHi n x Q) = ((n : ℝ) * Q + 1) * m / x := by
  have hn0 : (0 : ℝ) < n := n_pos
  unfold cascadeR zoneHi
  field_simp

/-- The same identity in terms of the setter's **reading** `u = x/m`: `R = (n·Q + 1)/u`. -/
theorem cascadeR_zoneHi_reading (m x : ℝ) (hm : 0 < m) (hx : 0 < x) (Q : ℤ) :
    cascadeR n m (zoneHi n x Q) = ((n : ℝ) * Q + 1) / (x / m) := by
  rw [cascadeR_zoneHi m x hx Q]
  field_simp

/-- **The nearest runner's settings are expensive.** Its reading is 1, so its own setting at lap `Q ≥ 1` lands at
`R = n·Q + 1 ≥ n + 1`. -/
theorem nearest_setting_ge (m : ℝ) (hm : 0 < m) {Q : ℤ} (hQ : 1 ≤ Q) :
    (n : ℝ) + 1 ≤ cascadeR n m (zoneHi n m Q) := by
  have hn0 : (0 : ℝ) < n := n_pos
  rw [cascadeR_zoneHi m m hm Q]
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  rw [mul_div_assoc, div_self hm.ne', mul_one]
  nlinarith

/-- **The nearest never sets below the cap.** Under any cap `C ≤ n + 1`, no setting by the nearest runner at a lap
`Q ≥ 1` keeps the cascade below `C`. -/
theorem nearest_never_sets (m : ℝ) (hm : 0 < m) {Q : ℤ} (hQ : 1 ≤ Q) {C : ℝ} (hC : C ≤ (n : ℝ) + 1) :
    ¬ cascadeR n m (zoneHi n m Q) < C := by
  have := nearest_setting_ge m hm hQ (n := n)
  linarith

/-- **The lap bound.** A setting of `x` that keeps the cascade below `C` has `n·Q + 1 < C·u`, where `u = x/m` is the
setter's reading: the lap is bounded by the reading. -/
theorem lap_lt_of_cascadeR_lt (m x : ℝ) (hm : 0 < m) (hx : 0 < x) (Q : ℤ) {C : ℝ}
    (h : cascadeR n m (zoneHi n x Q) < C) :
    (n : ℝ) * Q + 1 < C * (x / m) := by
  rw [cascadeR_zoneHi_reading m x hm hx Q] at h
  have hu : 0 < x / m := div_pos hx hm
  rwa [div_lt_iff₀ hu] at h

/-- **The lap bound is uniform in the spread.** With every reading at most `S`, a setting below the cap `C` has
`n·Q + 1 < C·S`, a bound depending on the arrangement only through `S`. -/
theorem lap_lt_of_spread (m x : ℝ) (hm : 0 < m) (hx : 0 < x) (Q : ℤ) {C S : ℝ} (hC : 0 ≤ C)
    (hS : x / m ≤ S) (h : cascadeR n m (zoneHi n x Q) < C) :
    (n : ℝ) * Q + 1 < C * S := by
  have h1 := lap_lt_of_cascadeR_lt m x hm hx Q h
  nlinarith

/-- **Laps strictly increase per runner.** A runner's settings happen at `zoneHi n x Q`, which is strictly monotone
in `Q`, so a later setting by the same runner carries a strictly larger lap. -/
theorem laps_strictly_increase (x : ℝ) (hx : 0 < x) {Q Q' : ℤ}
    (h : zoneHi n x Q < zoneHi n x Q') : Q < Q' := by
  unfold zoneHi at h
  rw [div_lt_div_iff_of_pos_right hx] at h
  have : (Q : ℝ) < Q' := by linarith
  exact_mod_cast this

/-- The converse direction, recorded for use in the other order: a larger lap is a later instant. -/
theorem zoneHi_lt_of_lap_lt (x : ℝ) (hx : 0 < x) {Q Q' : ℤ} (h : Q < Q') :
    zoneHi n x Q < zoneHi n x Q' := by
  unfold zoneHi
  rw [div_lt_div_iff_of_pos_right hx]
  have : (Q : ℝ) < Q' := by exact_mod_cast h
  linarith

/-- **The word list is finite.** Under a cap `C` and spread bound `S`, every lap at which a runner can set lies in a
fixed finite interval, uniformly over arrangements. -/
theorem lap_mem_Icc (m x : ℝ) (hm : 0 < m) (hx : 0 < x) (Q : ℤ) {C S : ℝ} (hC : 0 ≤ C)
    (hQ : 0 ≤ Q) (hS : x / m ≤ S) (h : cascadeR n m (zoneHi n x Q) < C) :
    Q ∈ Finset.Icc (0 : ℤ) ⌈C * S⌉ := by
  have h1 := lap_lt_of_spread m x hm hx Q hC hS h
  have hn0 : (0 : ℝ) < n := n_pos
  have hn1 : (1 : ℝ) ≤ n := by have := two_le_n (n := n); linarith
  have hQ0 : (0 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQr : (Q : ℝ) ≤ C * S := by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hQ0]
  have : (Q : ℝ) ≤ (⌈C * S⌉ : ℝ) := le_trans hQr (Int.le_ceil _)
  exact Finset.mem_Icc.mpr ⟨hQ, by exact_mod_cast this⟩

end CascadeCertificate
