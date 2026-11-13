import Fresh.NativeJ2DmaxBoxChecked
import Fresh.NativeJ2RatioEnvelopeLanding

/-!
Composition of the 13-guard dmax box with the six native landings:
`NativeJ2DmaxBoxChecked.guardsK` turns `dmaxBox ++ selectorsK` validity into
routeK guard validity, which re-feeds the public row calculus
(`Row.move`, `terminal`) on the landing module's public route data.
The landing hypothesis `envelope ++ selectorsK` of `landingK` is bypassed:
the box does not imply the 42-guard trace envelope. Its tightest walk for
`r 1 / r 0` (0 -> 6 -> 1) gives 10000/649 * 919/5000 = 1838/649, which is
strictly weaker than the envelope guard 3185844913713931/1125899906842624,
and the same holds for all 42 envelope guards; the route guards, however,
are implied, which is all the landing chain consumes.
-/

namespace Fresh.NativeJ2DmaxBoxLanding

open Fresh Cascade Localisation NativeGuardedRouteRows NativeRationalGuardPaths
open NativeJ2RatioEnvelopeChecked NativeJ2RatioEnvelopeLanding

section Route1
set_option maxRecDepth 12000 in
private theorem box_route1_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end1 (clear1 i) i).all (fun g => guards1.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_0_box_checked : move1_0.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_0.src.time r) (move1_0.dst.time r) := by
  apply move1_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_1_box_checked : move1_1.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_1.src.time r) (move1_1.dst.time r) := by
  apply move1_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_2_box_checked : move1_2.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_2.src.time r) (move1_2.dst.time r) := by
  apply move1_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_3_box_checked : move1_3.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_3.src.time r) (move1_3.dst.time r) := by
  apply move1_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_4_box_checked : move1_4.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_4.src.time r) (move1_4.dst.time r) := by
  apply move1_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_5_box_checked : move1_5.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_5.src.time r) (move1_5.dst.time r) := by
  apply move1_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_6_box_checked : move1_6.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_6.src.time r) (move1_6.dst.time r) := by
  apply move1_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_7_box_checked : move1_7.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_7.src.time r) (move1_7.dst.time r) := by
  apply move1_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_8_box_checked : move1_8.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_8.src.time r) (move1_8.dst.time r) := by
  apply move1_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_9_box_checked : move1_9.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_9.src.time r) (move1_9.dst.time r) := by
  apply move1_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_10_box_checked : move1_10.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_10.src.time r) (move1_10.dst.time r) := by
  apply move1_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_11_box_checked : move1_11.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_11.src.time r) (move1_11.dst.time r) := by
  apply move1_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_12_box_checked : move1_12.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_12.src.time r) (move1_12.dst.time r) := by
  apply move1_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_13_box_checked : move1_13.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_13.src.time r) (move1_13.dst.time r) := by
  apply move1_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_14_box_checked : move1_14.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_14.src.time r) (move1_14.dst.time r) := by
  apply move1_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_15_box_checked : move1_15.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_15.src.time r) (move1_15.dst.time r) := by
  apply move1_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_16_box_checked : move1_16.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_16.src.time r) (move1_16.dst.time r) := by
  apply move1_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_17_box_checked : move1_17.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_17.src.time r) (move1_17.dst.time r) := by
  apply move1_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_18_box_checked : move1_18.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_18.src.time r) (move1_18.dst.time r) := by
  apply move1_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_19_box_checked : move1_19.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_19.src.time r) (move1_19.dst.time r) := by
  apply move1_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_20_box_checked : move1_20.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_20.src.time r) (move1_20.dst.time r) := by
  apply move1_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_21_box_checked : move1_21.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_21.src.time r) (move1_21.dst.time r) := by
  apply move1_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_22_box_checked : move1_22.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_22.src.time r) (move1_22.dst.time r) := by
  apply move1_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_23_box_checked : move1_23.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_23.src.time r) (move1_23.dst.time r) := by
  apply move1_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_23_box_checked g h))

/-- dmaxBox plus the route1 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 24). -/
theorem boxLanding1 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors1, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 24 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards1, g.valid r := NativeJ2DmaxBoxChecked.guards1 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move1_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move1_0]
  have at1 : seq 1 = move1_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move1_0_box_sound r hp hg)
  have at2 : seq 2 = move1_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move1_1_box_sound r hp hg)
  have at3 : seq 3 = move1_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move1_2_box_sound r hp hg)
  have at4 : seq 4 = move1_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move1_3_box_sound r hp hg)
  have at5 : seq 5 = move1_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move1_4_box_sound r hp hg)
  have at6 : seq 6 = move1_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move1_5_box_sound r hp hg)
  have at7 : seq 7 = move1_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move1_6_box_sound r hp hg)
  have at8 : seq 8 = move1_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move1_7_box_sound r hp hg)
  have at9 : seq 9 = move1_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move1_8_box_sound r hp hg)
  have at10 : seq 10 = move1_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move1_9_box_sound r hp hg)
  have at11 : seq 11 = move1_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move1_10_box_sound r hp hg)
  have at12 : seq 12 = move1_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move1_11_box_sound r hp hg)
  have at13 : seq 13 = move1_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move1_12_box_sound r hp hg)
  have at14 : seq 14 = move1_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move1_13_box_sound r hp hg)
  have at15 : seq 15 = move1_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move1_14_box_sound r hp hg)
  have at16 : seq 16 = move1_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move1_15_box_sound r hp hg)
  have at17 : seq 17 = move1_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move1_16_box_sound r hp hg)
  have at18 : seq 18 = move1_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move1_17_box_sound r hp hg)
  have at19 : seq 19 = move1_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move1_18_box_sound r hp hg)
  have at20 : seq 20 = move1_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move1_19_box_sound r hp hg)
  have at21 : seq 21 = move1_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move1_20_box_sound r hp hg)
  have at22 : seq 22 = move1_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move1_21_box_sound r hp hg)
  have at23 : seq 23 = move1_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move1_22_box_sound r hp hg)
  have at24 : seq 24 = move1_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move1_23_box_sound r hp hg)
  have hfin : move1_23.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move1_23, end1]
  have hl : LonelyAt (Finset.univ.image r) (move1_23.dst.time r) := by
    apply terminal r hp end1 clear1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route1_checked i (by simp)) g hm)
  exact ⟨at24.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding1

end Route1

section Route2
set_option maxRecDepth 12000 in
private theorem box_route2_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end2 (clear2 i) i).all (fun g => guards2.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_0_box_checked : move2_0.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_0.src.time r) (move2_0.dst.time r) := by
  apply move2_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_1_box_checked : move2_1.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_1.src.time r) (move2_1.dst.time r) := by
  apply move2_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_2_box_checked : move2_2.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_2.src.time r) (move2_2.dst.time r) := by
  apply move2_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_3_box_checked : move2_3.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_3.src.time r) (move2_3.dst.time r) := by
  apply move2_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_4_box_checked : move2_4.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_4.src.time r) (move2_4.dst.time r) := by
  apply move2_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_5_box_checked : move2_5.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_5.src.time r) (move2_5.dst.time r) := by
  apply move2_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_6_box_checked : move2_6.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_6.src.time r) (move2_6.dst.time r) := by
  apply move2_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_7_box_checked : move2_7.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_7.src.time r) (move2_7.dst.time r) := by
  apply move2_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_8_box_checked : move2_8.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_8.src.time r) (move2_8.dst.time r) := by
  apply move2_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_9_box_checked : move2_9.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_9.src.time r) (move2_9.dst.time r) := by
  apply move2_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_10_box_checked : move2_10.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_10.src.time r) (move2_10.dst.time r) := by
  apply move2_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_11_box_checked : move2_11.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_11.src.time r) (move2_11.dst.time r) := by
  apply move2_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_12_box_checked : move2_12.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_12.src.time r) (move2_12.dst.time r) := by
  apply move2_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_13_box_checked : move2_13.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_13.src.time r) (move2_13.dst.time r) := by
  apply move2_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_14_box_checked : move2_14.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_14.src.time r) (move2_14.dst.time r) := by
  apply move2_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_15_box_checked : move2_15.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_15.src.time r) (move2_15.dst.time r) := by
  apply move2_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_16_box_checked : move2_16.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_16.src.time r) (move2_16.dst.time r) := by
  apply move2_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_17_box_checked : move2_17.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_17.src.time r) (move2_17.dst.time r) := by
  apply move2_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_18_box_checked : move2_18.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_18.src.time r) (move2_18.dst.time r) := by
  apply move2_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_19_box_checked : move2_19.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_19.src.time r) (move2_19.dst.time r) := by
  apply move2_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_20_box_checked : move2_20.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_20.src.time r) (move2_20.dst.time r) := by
  apply move2_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_21_box_checked : move2_21.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_21.src.time r) (move2_21.dst.time r) := by
  apply move2_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_22_box_checked : move2_22.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_22.src.time r) (move2_22.dst.time r) := by
  apply move2_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_23_box_checked : move2_23.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_23.src.time r) (move2_23.dst.time r) := by
  apply move2_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_23_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_24_box_checked : move2_24.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_24_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_24.src.time r) (move2_24.dst.time r) := by
  apply move2_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_24_box_checked g h))

/-- dmaxBox plus the route2 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 25). -/
theorem boxLanding2 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors2, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards2, g.valid r := NativeJ2DmaxBoxChecked.guards2 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move2_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move2_0]
  have at1 : seq 1 = move2_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move2_0_box_sound r hp hg)
  have at2 : seq 2 = move2_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move2_1_box_sound r hp hg)
  have at3 : seq 3 = move2_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move2_2_box_sound r hp hg)
  have at4 : seq 4 = move2_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move2_3_box_sound r hp hg)
  have at5 : seq 5 = move2_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move2_4_box_sound r hp hg)
  have at6 : seq 6 = move2_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move2_5_box_sound r hp hg)
  have at7 : seq 7 = move2_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move2_6_box_sound r hp hg)
  have at8 : seq 8 = move2_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move2_7_box_sound r hp hg)
  have at9 : seq 9 = move2_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move2_8_box_sound r hp hg)
  have at10 : seq 10 = move2_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move2_9_box_sound r hp hg)
  have at11 : seq 11 = move2_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move2_10_box_sound r hp hg)
  have at12 : seq 12 = move2_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move2_11_box_sound r hp hg)
  have at13 : seq 13 = move2_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move2_12_box_sound r hp hg)
  have at14 : seq 14 = move2_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move2_13_box_sound r hp hg)
  have at15 : seq 15 = move2_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move2_14_box_sound r hp hg)
  have at16 : seq 16 = move2_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move2_15_box_sound r hp hg)
  have at17 : seq 17 = move2_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move2_16_box_sound r hp hg)
  have at18 : seq 18 = move2_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move2_17_box_sound r hp hg)
  have at19 : seq 19 = move2_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move2_18_box_sound r hp hg)
  have at20 : seq 20 = move2_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move2_19_box_sound r hp hg)
  have at21 : seq 21 = move2_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move2_20_box_sound r hp hg)
  have at22 : seq 22 = move2_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move2_21_box_sound r hp hg)
  have at23 : seq 23 = move2_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move2_22_box_sound r hp hg)
  have at24 : seq 24 = move2_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move2_23_box_sound r hp hg)
  have at25 : seq 25 = move2_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move2_24_box_sound r hp hg)
  have hfin : move2_24.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move2_24, end2]
  have hl : LonelyAt (Finset.univ.image r) (move2_24.dst.time r) := by
    apply terminal r hp end2 clear2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route2_checked i (by simp)) g hm)
  exact ⟨at25.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding2

end Route2

section Route3
set_option maxRecDepth 12000 in
private theorem box_route3_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end3 (clear3 i) i).all (fun g => guards3.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_0_box_checked : move3_0.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_0.src.time r) (move3_0.dst.time r) := by
  apply move3_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_1_box_checked : move3_1.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_1.src.time r) (move3_1.dst.time r) := by
  apply move3_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_2_box_checked : move3_2.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_2.src.time r) (move3_2.dst.time r) := by
  apply move3_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_3_box_checked : move3_3.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_3.src.time r) (move3_3.dst.time r) := by
  apply move3_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_4_box_checked : move3_4.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_4.src.time r) (move3_4.dst.time r) := by
  apply move3_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_5_box_checked : move3_5.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_5.src.time r) (move3_5.dst.time r) := by
  apply move3_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_6_box_checked : move3_6.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_6.src.time r) (move3_6.dst.time r) := by
  apply move3_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_7_box_checked : move3_7.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_7.src.time r) (move3_7.dst.time r) := by
  apply move3_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_8_box_checked : move3_8.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_8.src.time r) (move3_8.dst.time r) := by
  apply move3_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_9_box_checked : move3_9.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_9.src.time r) (move3_9.dst.time r) := by
  apply move3_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_10_box_checked : move3_10.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_10.src.time r) (move3_10.dst.time r) := by
  apply move3_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_11_box_checked : move3_11.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_11.src.time r) (move3_11.dst.time r) := by
  apply move3_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_12_box_checked : move3_12.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_12.src.time r) (move3_12.dst.time r) := by
  apply move3_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_13_box_checked : move3_13.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_13.src.time r) (move3_13.dst.time r) := by
  apply move3_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_14_box_checked : move3_14.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_14.src.time r) (move3_14.dst.time r) := by
  apply move3_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_15_box_checked : move3_15.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_15.src.time r) (move3_15.dst.time r) := by
  apply move3_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_16_box_checked : move3_16.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_16.src.time r) (move3_16.dst.time r) := by
  apply move3_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_17_box_checked : move3_17.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_17.src.time r) (move3_17.dst.time r) := by
  apply move3_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_18_box_checked : move3_18.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_18.src.time r) (move3_18.dst.time r) := by
  apply move3_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_19_box_checked : move3_19.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_19.src.time r) (move3_19.dst.time r) := by
  apply move3_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_20_box_checked : move3_20.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_20.src.time r) (move3_20.dst.time r) := by
  apply move3_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_21_box_checked : move3_21.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_21.src.time r) (move3_21.dst.time r) := by
  apply move3_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_22_box_checked : move3_22.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_22.src.time r) (move3_22.dst.time r) := by
  apply move3_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_23_box_checked : move3_23.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_23.src.time r) (move3_23.dst.time r) := by
  apply move3_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_23_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_24_box_checked : move3_24.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_24_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_24.src.time r) (move3_24.dst.time r) := by
  apply move3_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_24_box_checked g h))

/-- dmaxBox plus the route3 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 25). -/
theorem boxLanding3 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors3, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards3, g.valid r := NativeJ2DmaxBoxChecked.guards3 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move3_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move3_0]
  have at1 : seq 1 = move3_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move3_0_box_sound r hp hg)
  have at2 : seq 2 = move3_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move3_1_box_sound r hp hg)
  have at3 : seq 3 = move3_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move3_2_box_sound r hp hg)
  have at4 : seq 4 = move3_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move3_3_box_sound r hp hg)
  have at5 : seq 5 = move3_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move3_4_box_sound r hp hg)
  have at6 : seq 6 = move3_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move3_5_box_sound r hp hg)
  have at7 : seq 7 = move3_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move3_6_box_sound r hp hg)
  have at8 : seq 8 = move3_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move3_7_box_sound r hp hg)
  have at9 : seq 9 = move3_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move3_8_box_sound r hp hg)
  have at10 : seq 10 = move3_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move3_9_box_sound r hp hg)
  have at11 : seq 11 = move3_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move3_10_box_sound r hp hg)
  have at12 : seq 12 = move3_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move3_11_box_sound r hp hg)
  have at13 : seq 13 = move3_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move3_12_box_sound r hp hg)
  have at14 : seq 14 = move3_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move3_13_box_sound r hp hg)
  have at15 : seq 15 = move3_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move3_14_box_sound r hp hg)
  have at16 : seq 16 = move3_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move3_15_box_sound r hp hg)
  have at17 : seq 17 = move3_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move3_16_box_sound r hp hg)
  have at18 : seq 18 = move3_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move3_17_box_sound r hp hg)
  have at19 : seq 19 = move3_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move3_18_box_sound r hp hg)
  have at20 : seq 20 = move3_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move3_19_box_sound r hp hg)
  have at21 : seq 21 = move3_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move3_20_box_sound r hp hg)
  have at22 : seq 22 = move3_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move3_21_box_sound r hp hg)
  have at23 : seq 23 = move3_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move3_22_box_sound r hp hg)
  have at24 : seq 24 = move3_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move3_23_box_sound r hp hg)
  have at25 : seq 25 = move3_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move3_24_box_sound r hp hg)
  have hfin : move3_24.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move3_24, end3]
  have hl : LonelyAt (Finset.univ.image r) (move3_24.dst.time r) := by
    apply terminal r hp end3 clear3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route3_checked i (by simp)) g hm)
  exact ⟨at25.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding3

end Route3

section Route4
set_option maxRecDepth 12000 in
private theorem box_route4_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end4 (clear4 i) i).all (fun g => guards4.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_0_box_checked : move4_0.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_0.src.time r) (move4_0.dst.time r) := by
  apply move4_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_1_box_checked : move4_1.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_1.src.time r) (move4_1.dst.time r) := by
  apply move4_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_2_box_checked : move4_2.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_2.src.time r) (move4_2.dst.time r) := by
  apply move4_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_3_box_checked : move4_3.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_3.src.time r) (move4_3.dst.time r) := by
  apply move4_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_4_box_checked : move4_4.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_4.src.time r) (move4_4.dst.time r) := by
  apply move4_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_5_box_checked : move4_5.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_5.src.time r) (move4_5.dst.time r) := by
  apply move4_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_6_box_checked : move4_6.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_6.src.time r) (move4_6.dst.time r) := by
  apply move4_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_7_box_checked : move4_7.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_7.src.time r) (move4_7.dst.time r) := by
  apply move4_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_8_box_checked : move4_8.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_8.src.time r) (move4_8.dst.time r) := by
  apply move4_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_9_box_checked : move4_9.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_9.src.time r) (move4_9.dst.time r) := by
  apply move4_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_10_box_checked : move4_10.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_10.src.time r) (move4_10.dst.time r) := by
  apply move4_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_11_box_checked : move4_11.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_11.src.time r) (move4_11.dst.time r) := by
  apply move4_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_12_box_checked : move4_12.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_12.src.time r) (move4_12.dst.time r) := by
  apply move4_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_13_box_checked : move4_13.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_13.src.time r) (move4_13.dst.time r) := by
  apply move4_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_14_box_checked : move4_14.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_14.src.time r) (move4_14.dst.time r) := by
  apply move4_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_15_box_checked : move4_15.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_15.src.time r) (move4_15.dst.time r) := by
  apply move4_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_16_box_checked : move4_16.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_16.src.time r) (move4_16.dst.time r) := by
  apply move4_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_17_box_checked : move4_17.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_17.src.time r) (move4_17.dst.time r) := by
  apply move4_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_18_box_checked : move4_18.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_18.src.time r) (move4_18.dst.time r) := by
  apply move4_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_19_box_checked : move4_19.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_19.src.time r) (move4_19.dst.time r) := by
  apply move4_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_20_box_checked : move4_20.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_20.src.time r) (move4_20.dst.time r) := by
  apply move4_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_21_box_checked : move4_21.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_21.src.time r) (move4_21.dst.time r) := by
  apply move4_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_22_box_checked : move4_22.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_22.src.time r) (move4_22.dst.time r) := by
  apply move4_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_23_box_checked : move4_23.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_23.src.time r) (move4_23.dst.time r) := by
  apply move4_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_23_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_24_box_checked : move4_24.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_24_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_24.src.time r) (move4_24.dst.time r) := by
  apply move4_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_24_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_25_box_checked : move4_25.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_25_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_25.src.time r) (move4_25.dst.time r) := by
  apply move4_25.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_25_box_checked g h))

/-- dmaxBox plus the route4 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 26). -/
theorem boxLanding4 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors4, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 26 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards4, g.valid r := NativeJ2DmaxBoxChecked.guards4 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move4_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move4_0]
  have at1 : seq 1 = move4_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move4_0_box_sound r hp hg)
  have at2 : seq 2 = move4_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move4_1_box_sound r hp hg)
  have at3 : seq 3 = move4_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move4_2_box_sound r hp hg)
  have at4 : seq 4 = move4_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move4_3_box_sound r hp hg)
  have at5 : seq 5 = move4_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move4_4_box_sound r hp hg)
  have at6 : seq 6 = move4_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move4_5_box_sound r hp hg)
  have at7 : seq 7 = move4_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move4_6_box_sound r hp hg)
  have at8 : seq 8 = move4_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move4_7_box_sound r hp hg)
  have at9 : seq 9 = move4_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move4_8_box_sound r hp hg)
  have at10 : seq 10 = move4_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move4_9_box_sound r hp hg)
  have at11 : seq 11 = move4_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move4_10_box_sound r hp hg)
  have at12 : seq 12 = move4_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move4_11_box_sound r hp hg)
  have at13 : seq 13 = move4_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move4_12_box_sound r hp hg)
  have at14 : seq 14 = move4_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move4_13_box_sound r hp hg)
  have at15 : seq 15 = move4_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move4_14_box_sound r hp hg)
  have at16 : seq 16 = move4_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move4_15_box_sound r hp hg)
  have at17 : seq 17 = move4_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move4_16_box_sound r hp hg)
  have at18 : seq 18 = move4_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move4_17_box_sound r hp hg)
  have at19 : seq 19 = move4_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move4_18_box_sound r hp hg)
  have at20 : seq 20 = move4_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move4_19_box_sound r hp hg)
  have at21 : seq 21 = move4_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move4_20_box_sound r hp hg)
  have at22 : seq 22 = move4_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move4_21_box_sound r hp hg)
  have at23 : seq 23 = move4_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move4_22_box_sound r hp hg)
  have at24 : seq 24 = move4_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move4_23_box_sound r hp hg)
  have at25 : seq 25 = move4_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move4_24_box_sound r hp hg)
  have at26 : seq 26 = move4_25.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 25) (seq 26) :=
      cascadeSeq_isMove _ _ 25
    rw [at25] at hm
    exact isMove_unique hm (move4_25_box_sound r hp hg)
  have hfin : move4_25.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move4_25, end4]
  have hl : LonelyAt (Finset.univ.image r) (move4_25.dst.time r) := by
    apply terminal r hp end4 clear4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route4_checked i (by simp)) g hm)
  exact ⟨at26.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding4

end Route4

section Route5
set_option maxRecDepth 12000 in
private theorem box_route5_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end5 (clear5 i) i).all (fun g => guards5.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_0_box_checked : move5_0.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_0.src.time r) (move5_0.dst.time r) := by
  apply move5_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_1_box_checked : move5_1.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_1.src.time r) (move5_1.dst.time r) := by
  apply move5_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_2_box_checked : move5_2.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_2.src.time r) (move5_2.dst.time r) := by
  apply move5_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_3_box_checked : move5_3.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_3.src.time r) (move5_3.dst.time r) := by
  apply move5_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_4_box_checked : move5_4.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_4.src.time r) (move5_4.dst.time r) := by
  apply move5_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_5_box_checked : move5_5.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_5.src.time r) (move5_5.dst.time r) := by
  apply move5_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_6_box_checked : move5_6.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_6.src.time r) (move5_6.dst.time r) := by
  apply move5_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_7_box_checked : move5_7.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_7.src.time r) (move5_7.dst.time r) := by
  apply move5_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_8_box_checked : move5_8.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_8.src.time r) (move5_8.dst.time r) := by
  apply move5_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_9_box_checked : move5_9.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_9.src.time r) (move5_9.dst.time r) := by
  apply move5_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_10_box_checked : move5_10.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_10.src.time r) (move5_10.dst.time r) := by
  apply move5_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_11_box_checked : move5_11.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_11.src.time r) (move5_11.dst.time r) := by
  apply move5_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_12_box_checked : move5_12.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_12.src.time r) (move5_12.dst.time r) := by
  apply move5_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_13_box_checked : move5_13.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_13.src.time r) (move5_13.dst.time r) := by
  apply move5_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_14_box_checked : move5_14.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_14.src.time r) (move5_14.dst.time r) := by
  apply move5_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_15_box_checked : move5_15.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_15.src.time r) (move5_15.dst.time r) := by
  apply move5_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_16_box_checked : move5_16.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_16.src.time r) (move5_16.dst.time r) := by
  apply move5_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_17_box_checked : move5_17.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_17.src.time r) (move5_17.dst.time r) := by
  apply move5_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_18_box_checked : move5_18.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_18.src.time r) (move5_18.dst.time r) := by
  apply move5_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_19_box_checked : move5_19.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_19.src.time r) (move5_19.dst.time r) := by
  apply move5_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_20_box_checked : move5_20.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_20.src.time r) (move5_20.dst.time r) := by
  apply move5_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_21_box_checked : move5_21.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_21.src.time r) (move5_21.dst.time r) := by
  apply move5_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_22_box_checked : move5_22.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_22.src.time r) (move5_22.dst.time r) := by
  apply move5_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_23_box_checked : move5_23.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_23.src.time r) (move5_23.dst.time r) := by
  apply move5_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_23_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_24_box_checked : move5_24.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_24_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_24.src.time r) (move5_24.dst.time r) := by
  apply move5_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_24_box_checked g h))

/-- dmaxBox plus the route5 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 25). -/
theorem boxLanding5 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors5, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards5, g.valid r := NativeJ2DmaxBoxChecked.guards5 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move5_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move5_0]
  have at1 : seq 1 = move5_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move5_0_box_sound r hp hg)
  have at2 : seq 2 = move5_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move5_1_box_sound r hp hg)
  have at3 : seq 3 = move5_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move5_2_box_sound r hp hg)
  have at4 : seq 4 = move5_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move5_3_box_sound r hp hg)
  have at5 : seq 5 = move5_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move5_4_box_sound r hp hg)
  have at6 : seq 6 = move5_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move5_5_box_sound r hp hg)
  have at7 : seq 7 = move5_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move5_6_box_sound r hp hg)
  have at8 : seq 8 = move5_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move5_7_box_sound r hp hg)
  have at9 : seq 9 = move5_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move5_8_box_sound r hp hg)
  have at10 : seq 10 = move5_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move5_9_box_sound r hp hg)
  have at11 : seq 11 = move5_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move5_10_box_sound r hp hg)
  have at12 : seq 12 = move5_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move5_11_box_sound r hp hg)
  have at13 : seq 13 = move5_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move5_12_box_sound r hp hg)
  have at14 : seq 14 = move5_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move5_13_box_sound r hp hg)
  have at15 : seq 15 = move5_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move5_14_box_sound r hp hg)
  have at16 : seq 16 = move5_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move5_15_box_sound r hp hg)
  have at17 : seq 17 = move5_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move5_16_box_sound r hp hg)
  have at18 : seq 18 = move5_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move5_17_box_sound r hp hg)
  have at19 : seq 19 = move5_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move5_18_box_sound r hp hg)
  have at20 : seq 20 = move5_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move5_19_box_sound r hp hg)
  have at21 : seq 21 = move5_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move5_20_box_sound r hp hg)
  have at22 : seq 22 = move5_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move5_21_box_sound r hp hg)
  have at23 : seq 23 = move5_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move5_22_box_sound r hp hg)
  have at24 : seq 24 = move5_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move5_23_box_sound r hp hg)
  have at25 : seq 25 = move5_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move5_24_box_sound r hp hg)
  have hfin : move5_24.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move5_24, end5]
  have hl : LonelyAt (Finset.univ.image r) (move5_24.dst.time r) := by
    apply terminal r hp end5 clear5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route5_checked i (by simp)) g hm)
  exact ⟨at25.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding5

end Route5

section Route6
set_option maxRecDepth 12000 in
private theorem box_route6_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end6 (clear6 i) i).all (fun g => guards6.contains g)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_0_box_checked : move6_0.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_0_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_0.src.time r) (move6_0.dst.time r) := by
  apply move6_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_0_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_1_box_checked : move6_1.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_1_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_1.src.time r) (move6_1.dst.time r) := by
  apply move6_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_1_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_2_box_checked : move6_2.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_2_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_2.src.time r) (move6_2.dst.time r) := by
  apply move6_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_2_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_3_box_checked : move6_3.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_3_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_3.src.time r) (move6_3.dst.time r) := by
  apply move6_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_3_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_4_box_checked : move6_4.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_4_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_4.src.time r) (move6_4.dst.time r) := by
  apply move6_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_4_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_5_box_checked : move6_5.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_5_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_5.src.time r) (move6_5.dst.time r) := by
  apply move6_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_5_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_6_box_checked : move6_6.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_6_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_6.src.time r) (move6_6.dst.time r) := by
  apply move6_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_6_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_7_box_checked : move6_7.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_7_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_7.src.time r) (move6_7.dst.time r) := by
  apply move6_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_7_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_8_box_checked : move6_8.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_8_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_8.src.time r) (move6_8.dst.time r) := by
  apply move6_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_8_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_9_box_checked : move6_9.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_9_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_9.src.time r) (move6_9.dst.time r) := by
  apply move6_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_9_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_10_box_checked : move6_10.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_10_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_10.src.time r) (move6_10.dst.time r) := by
  apply move6_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_10_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_11_box_checked : move6_11.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_11_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_11.src.time r) (move6_11.dst.time r) := by
  apply move6_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_11_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_12_box_checked : move6_12.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_12_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_12.src.time r) (move6_12.dst.time r) := by
  apply move6_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_12_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_13_box_checked : move6_13.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_13_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_13.src.time r) (move6_13.dst.time r) := by
  apply move6_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_13_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_14_box_checked : move6_14.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_14_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_14.src.time r) (move6_14.dst.time r) := by
  apply move6_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_14_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_15_box_checked : move6_15.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_15_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_15.src.time r) (move6_15.dst.time r) := by
  apply move6_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_15_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_16_box_checked : move6_16.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_16_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_16.src.time r) (move6_16.dst.time r) := by
  apply move6_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_16_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_17_box_checked : move6_17.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_17_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_17.src.time r) (move6_17.dst.time r) := by
  apply move6_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_17_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_18_box_checked : move6_18.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_18_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_18.src.time r) (move6_18.dst.time r) := by
  apply move6_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_18_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_19_box_checked : move6_19.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_19_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_19.src.time r) (move6_19.dst.time r) := by
  apply move6_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_19_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_20_box_checked : move6_20.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_20_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_20.src.time r) (move6_20.dst.time r) := by
  apply move6_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_20_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_21_box_checked : move6_21.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_21_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_21.src.time r) (move6_21.dst.time r) := by
  apply move6_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_21_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_22_box_checked : move6_22.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_22_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_22.src.time r) (move6_22.dst.time r) := by
  apply move6_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_22_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_23_box_checked : move6_23.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_23_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_23.src.time r) (move6_23.dst.time r) := by
  apply move6_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_23_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_24_box_checked : move6_24.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_24_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_24.src.time r) (move6_24.dst.time r) := by
  apply move6_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_24_box_checked g h))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_25_box_checked : move6_25.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_25_box_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_25.src.time r) (move6_25.dst.time r) := by
  apply move6_25.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_25_box_checked g h))

/-- dmaxBox plus the route6 selectors alone land the standard opening
lonely at `(145/8)/r 6` (cascade step 26). -/
theorem boxLanding6 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ NativeJ2DmaxBoxChecked.dmaxBox ++ selectors6, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 26 = (145 / 8) / r 6 ∧
      LonelyAt (Finset.univ.image r) ((145 / 8) / r 6) := by
  have hg : ∀ g ∈ guards6, g.valid r := NativeJ2DmaxBoxChecked.guards6 r hp he
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move6_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move6_0]
  have at1 : seq 1 = move6_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move6_0_box_sound r hp hg)
  have at2 : seq 2 = move6_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move6_1_box_sound r hp hg)
  have at3 : seq 3 = move6_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move6_2_box_sound r hp hg)
  have at4 : seq 4 = move6_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move6_3_box_sound r hp hg)
  have at5 : seq 5 = move6_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move6_4_box_sound r hp hg)
  have at6 : seq 6 = move6_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move6_5_box_sound r hp hg)
  have at7 : seq 7 = move6_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move6_6_box_sound r hp hg)
  have at8 : seq 8 = move6_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move6_7_box_sound r hp hg)
  have at9 : seq 9 = move6_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move6_8_box_sound r hp hg)
  have at10 : seq 10 = move6_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move6_9_box_sound r hp hg)
  have at11 : seq 11 = move6_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move6_10_box_sound r hp hg)
  have at12 : seq 12 = move6_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move6_11_box_sound r hp hg)
  have at13 : seq 13 = move6_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move6_12_box_sound r hp hg)
  have at14 : seq 14 = move6_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move6_13_box_sound r hp hg)
  have at15 : seq 15 = move6_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move6_14_box_sound r hp hg)
  have at16 : seq 16 = move6_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move6_15_box_sound r hp hg)
  have at17 : seq 17 = move6_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move6_16_box_sound r hp hg)
  have at18 : seq 18 = move6_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move6_17_box_sound r hp hg)
  have at19 : seq 19 = move6_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move6_18_box_sound r hp hg)
  have at20 : seq 20 = move6_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move6_19_box_sound r hp hg)
  have at21 : seq 21 = move6_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move6_20_box_sound r hp hg)
  have at22 : seq 22 = move6_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move6_21_box_sound r hp hg)
  have at23 : seq 23 = move6_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move6_22_box_sound r hp hg)
  have at24 : seq 24 = move6_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move6_23_box_sound r hp hg)
  have at25 : seq 25 = move6_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move6_24_box_sound r hp hg)
  have at26 : seq 26 = move6_25.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 25) (seq 26) :=
      cascadeSeq_isMove _ _ 25
    rw [at25] at hm
    exact isMove_unique hm (move6_25_box_sound r hp hg)
  have hfin : move6_25.dst.time r = (145 / 8) / r 6 := by
    norm_num [Anchor.time, move6_25, end6]
  have hl : LonelyAt (Finset.univ.image r) (move6_25.dst.time r) := by
    apply terminal r hp end6 clear6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro i g hm
    apply hg
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp box_route6_checked i (by simp)) g hm)
  exact ⟨at26.trans hfin, hfin ▸ hl⟩

#print axioms boxLanding6

end Route6

end Fresh.NativeJ2DmaxBoxLanding
