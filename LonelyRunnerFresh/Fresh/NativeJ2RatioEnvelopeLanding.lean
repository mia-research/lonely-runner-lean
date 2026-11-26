import Fresh.NativeGuardedRouteRows
import Fresh.NativeJ2RatioEnvelopeChecked

namespace Fresh.NativeJ2RatioEnvelopeLanding

open Fresh Cascade NativeGuardedRouteRows NativeRationalGuardPaths
open NativeJ2RatioEnvelopeChecked

def guards1 := route1.map Prod.fst

def move1_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_0_checked : move1_0.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_0.src.time r) (move1_0.dst.time r) := by
  apply move1_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_0_checked g h))

def move1_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_1_checked : move1_1.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_1.src.time r) (move1_1.dst.time r) := by
  apply move1_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_1_checked g h))

def move1_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_2_checked : move1_2.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_2.src.time r) (move1_2.dst.time r) := by
  apply move1_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_2_checked g h))

def move1_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_3_checked : move1_3.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_3.src.time r) (move1_3.dst.time r) := by
  apply move1_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_3_checked g h))

def move1_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_4_checked : move1_4.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_4.src.time r) (move1_4.dst.time r) := by
  apply move1_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_4_checked g h))

def move1_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_5_checked : move1_5.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_5.src.time r) (move1_5.dst.time r) := by
  apply move1_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_5_checked g h))

def move1_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_6_checked : move1_6.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_6.src.time r) (move1_6.dst.time r) := by
  apply move1_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_6_checked g h))

def move1_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_7_checked : move1_7.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_7.src.time r) (move1_7.dst.time r) := by
  apply move1_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_7_checked g h))

def move1_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_8_checked : move1_8.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_8.src.time r) (move1_8.dst.time r) := by
  apply move1_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_8_checked g h))

def move1_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_9_checked : move1_9.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_9.src.time r) (move1_9.dst.time r) := by
  apply move1_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_9_checked g h))

def move1_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_10_checked : move1_10.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_10.src.time r) (move1_10.dst.time r) := by
  apply move1_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_10_checked g h))

def move1_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_11_checked : move1_11.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_11.src.time r) (move1_11.dst.time r) := by
  apply move1_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_11_checked g h))

def move1_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_12_checked : move1_12.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_12.src.time r) (move1_12.dst.time r) := by
  apply move1_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_12_checked g h))

def move1_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_13_checked : move1_13.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_13.src.time r) (move1_13.dst.time r) := by
  apply move1_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_13_checked g h))

def move1_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_14_checked : move1_14.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_14.src.time r) (move1_14.dst.time r) := by
  apply move1_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_14_checked g h))

def move1_15 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_15_checked : move1_15.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_15.src.time r) (move1_15.dst.time r) := by
  apply move1_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_15_checked g h))

def move1_16 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_16_checked : move1_16.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_16.src.time r) (move1_16.dst.time r) := by
  apply move1_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_16_checked g h))

def move1_17 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_17_checked : move1_17.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_17.src.time r) (move1_17.dst.time r) := by
  apply move1_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_17_checked g h))

def move1_18 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_18_checked : move1_18.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_18.src.time r) (move1_18.dst.time r) := by
  apply move1_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_18_checked g h))

def move1_19 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_19_checked : move1_19.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_19.src.time r) (move1_19.dst.time r) := by
  apply move1_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_19_checked g h))

def move1_20 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_20_checked : move1_20.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_20.src.time r) (move1_20.dst.time r) := by
  apply move1_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_20_checked g h))

def move1_21 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_21_checked : move1_21.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_21.src.time r) (move1_21.dst.time r) := by
  apply move1_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_21_checked g h))

def move1_22 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_22_checked : move1_22.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_22.src.time r) (move1_22.dst.time r) := by
  apply move1_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_22_checked g h))

def move1_23 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move1_23_checked : move1_23.guards.all
    (fun g => guards1.contains g) = true := by decide +kernel

private theorem move1_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards1, g.valid r) :
    IsMove (Finset.univ.image r) (move1_23.src.time r) (move1_23.dst.time r) := by
  apply move1_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move1_23_checked g h))

def end1 : Anchor := ⟨6, 145 / 8⟩
def clear1 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear1_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end1 (clear1 i) i).all (fun g => guards1.contains g)) = true := by
  decide +kernel

theorem landing1 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors1, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 24 = end1.time r ∧
    LonelyAt (Finset.univ.image r) (end1.time r) := by
  have hg : ∀ g ∈ guards1, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route1_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move1_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move1_0]
  have at1 : seq 1 = move1_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move1_0_sound r hp hg)
  have at2 : seq 2 = move1_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move1_1_sound r hp hg)
  have at3 : seq 3 = move1_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move1_2_sound r hp hg)
  have at4 : seq 4 = move1_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move1_3_sound r hp hg)
  have at5 : seq 5 = move1_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move1_4_sound r hp hg)
  have at6 : seq 6 = move1_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move1_5_sound r hp hg)
  have at7 : seq 7 = move1_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move1_6_sound r hp hg)
  have at8 : seq 8 = move1_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move1_7_sound r hp hg)
  have at9 : seq 9 = move1_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move1_8_sound r hp hg)
  have at10 : seq 10 = move1_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move1_9_sound r hp hg)
  have at11 : seq 11 = move1_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move1_10_sound r hp hg)
  have at12 : seq 12 = move1_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move1_11_sound r hp hg)
  have at13 : seq 13 = move1_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move1_12_sound r hp hg)
  have at14 : seq 14 = move1_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move1_13_sound r hp hg)
  have at15 : seq 15 = move1_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move1_14_sound r hp hg)
  have at16 : seq 16 = move1_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move1_15_sound r hp hg)
  have at17 : seq 17 = move1_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move1_16_sound r hp hg)
  have at18 : seq 18 = move1_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move1_17_sound r hp hg)
  have at19 : seq 19 = move1_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move1_18_sound r hp hg)
  have at20 : seq 20 = move1_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move1_19_sound r hp hg)
  have at21 : seq 21 = move1_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move1_20_sound r hp hg)
  have at22 : seq 22 = move1_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move1_21_sound r hp hg)
  have at23 : seq 23 = move1_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move1_22_sound r hp hg)
  have at24 : seq 24 = move1_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move1_23_sound r hp hg)
  refine ⟨at24, ?_⟩
  apply terminal r hp end1 clear1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear1_checked i (by simp)) g hm)

#print axioms landing1

def guards2 := route2.map Prod.fst

def move2_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_0_checked : move2_0.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_0.src.time r) (move2_0.dst.time r) := by
  apply move2_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_0_checked g h))

def move2_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_1_checked : move2_1.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_1.src.time r) (move2_1.dst.time r) := by
  apply move2_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_1_checked g h))

def move2_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_2_checked : move2_2.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_2.src.time r) (move2_2.dst.time r) := by
  apply move2_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_2_checked g h))

def move2_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_3_checked : move2_3.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_3.src.time r) (move2_3.dst.time r) := by
  apply move2_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_3_checked g h))

def move2_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_4_checked : move2_4.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_4.src.time r) (move2_4.dst.time r) := by
  apply move2_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_4_checked g h))

def move2_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_5_checked : move2_5.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_5.src.time r) (move2_5.dst.time r) := by
  apply move2_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_5_checked g h))

def move2_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_6_checked : move2_6.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_6.src.time r) (move2_6.dst.time r) := by
  apply move2_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_6_checked g h))

def move2_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_7_checked : move2_7.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_7.src.time r) (move2_7.dst.time r) := by
  apply move2_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_7_checked g h))

def move2_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_8_checked : move2_8.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_8.src.time r) (move2_8.dst.time r) := by
  apply move2_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_8_checked g h))

def move2_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_9_checked : move2_9.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_9.src.time r) (move2_9.dst.time r) := by
  apply move2_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_9_checked g h))

def move2_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_10_checked : move2_10.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_10.src.time r) (move2_10.dst.time r) := by
  apply move2_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_10_checked g h))

def move2_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_11_checked : move2_11.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_11.src.time r) (move2_11.dst.time r) := by
  apply move2_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_11_checked g h))

def move2_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_12_checked : move2_12.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_12.src.time r) (move2_12.dst.time r) := by
  apply move2_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_12_checked g h))

def move2_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_13_checked : move2_13.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_13.src.time r) (move2_13.dst.time r) := by
  apply move2_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_13_checked g h))

def move2_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_14_checked : move2_14.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_14.src.time r) (move2_14.dst.time r) := by
  apply move2_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_14_checked g h))

def move2_15 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_15_checked : move2_15.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_15.src.time r) (move2_15.dst.time r) := by
  apply move2_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_15_checked g h))

def move2_16 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_16_checked : move2_16.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_16.src.time r) (move2_16.dst.time r) := by
  apply move2_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_16_checked g h))

def move2_17 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_17_checked : move2_17.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_17.src.time r) (move2_17.dst.time r) := by
  apply move2_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_17_checked g h))

def move2_18 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_18_checked : move2_18.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_18.src.time r) (move2_18.dst.time r) := by
  apply move2_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_18_checked g h))

def move2_19 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_19_checked : move2_19.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_19.src.time r) (move2_19.dst.time r) := by
  apply move2_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_19_checked g h))

def move2_20 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_20_checked : move2_20.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_20.src.time r) (move2_20.dst.time r) := by
  apply move2_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_20_checked g h))

def move2_21 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨6, 137 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨7, .clear⟩, ⟨17, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_21_checked : move2_21.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_21.src.time r) (move2_21.dst.time r) := by
  apply move2_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_21_checked g h))

def move2_22 : Row :=
  ⟨⟨6, 137 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_22_checked : move2_22.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_22.src.time r) (move2_22.dst.time r) := by
  apply move2_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_22_checked g h))

def move2_23 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_23_checked : move2_23.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_23.src.time r) (move2_23.dst.time r) := by
  apply move2_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_23_checked g h))

def move2_24 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move2_24_checked : move2_24.guards.all
    (fun g => guards2.contains g) = true := by decide +kernel

private theorem move2_24_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards2, g.valid r) :
    IsMove (Finset.univ.image r) (move2_24.src.time r) (move2_24.dst.time r) := by
  apply move2_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move2_24_checked g h))

def end2 : Anchor := ⟨6, 145 / 8⟩
def clear2 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear2_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end2 (clear2 i) i).all (fun g => guards2.contains g)) = true := by
  decide +kernel

theorem landing2 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors2, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = end2.time r ∧
    LonelyAt (Finset.univ.image r) (end2.time r) := by
  have hg : ∀ g ∈ guards2, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route2_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move2_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move2_0]
  have at1 : seq 1 = move2_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move2_0_sound r hp hg)
  have at2 : seq 2 = move2_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move2_1_sound r hp hg)
  have at3 : seq 3 = move2_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move2_2_sound r hp hg)
  have at4 : seq 4 = move2_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move2_3_sound r hp hg)
  have at5 : seq 5 = move2_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move2_4_sound r hp hg)
  have at6 : seq 6 = move2_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move2_5_sound r hp hg)
  have at7 : seq 7 = move2_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move2_6_sound r hp hg)
  have at8 : seq 8 = move2_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move2_7_sound r hp hg)
  have at9 : seq 9 = move2_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move2_8_sound r hp hg)
  have at10 : seq 10 = move2_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move2_9_sound r hp hg)
  have at11 : seq 11 = move2_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move2_10_sound r hp hg)
  have at12 : seq 12 = move2_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move2_11_sound r hp hg)
  have at13 : seq 13 = move2_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move2_12_sound r hp hg)
  have at14 : seq 14 = move2_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move2_13_sound r hp hg)
  have at15 : seq 15 = move2_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move2_14_sound r hp hg)
  have at16 : seq 16 = move2_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move2_15_sound r hp hg)
  have at17 : seq 17 = move2_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move2_16_sound r hp hg)
  have at18 : seq 18 = move2_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move2_17_sound r hp hg)
  have at19 : seq 19 = move2_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move2_18_sound r hp hg)
  have at20 : seq 20 = move2_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move2_19_sound r hp hg)
  have at21 : seq 21 = move2_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move2_20_sound r hp hg)
  have at22 : seq 22 = move2_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move2_21_sound r hp hg)
  have at23 : seq 23 = move2_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move2_22_sound r hp hg)
  have at24 : seq 24 = move2_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move2_23_sound r hp hg)
  have at25 : seq 25 = move2_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move2_24_sound r hp hg)
  refine ⟨at25, ?_⟩
  apply terminal r hp end2 clear2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear2_checked i (by simp)) g hm)

#print axioms landing2

def guards3 := route3.map Prod.fst

def move3_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_0_checked : move3_0.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_0.src.time r) (move3_0.dst.time r) := by
  apply move3_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_0_checked g h))

def move3_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_1_checked : move3_1.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_1.src.time r) (move3_1.dst.time r) := by
  apply move3_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_1_checked g h))

def move3_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_2_checked : move3_2.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_2.src.time r) (move3_2.dst.time r) := by
  apply move3_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_2_checked g h))

def move3_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_3_checked : move3_3.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_3.src.time r) (move3_3.dst.time r) := by
  apply move3_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_3_checked g h))

def move3_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_4_checked : move3_4.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_4.src.time r) (move3_4.dst.time r) := by
  apply move3_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_4_checked g h))

def move3_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_5_checked : move3_5.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_5.src.time r) (move3_5.dst.time r) := by
  apply move3_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_5_checked g h))

def move3_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_6_checked : move3_6.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_6.src.time r) (move3_6.dst.time r) := by
  apply move3_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_6_checked g h))

def move3_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_7_checked : move3_7.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_7.src.time r) (move3_7.dst.time r) := by
  apply move3_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_7_checked g h))

def move3_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_8_checked : move3_8.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_8.src.time r) (move3_8.dst.time r) := by
  apply move3_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_8_checked g h))

def move3_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_9_checked : move3_9.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_9.src.time r) (move3_9.dst.time r) := by
  apply move3_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_9_checked g h))

def move3_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_10_checked : move3_10.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_10.src.time r) (move3_10.dst.time r) := by
  apply move3_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_10_checked g h))

def move3_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_11_checked : move3_11.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_11.src.time r) (move3_11.dst.time r) := by
  apply move3_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_11_checked g h))

def move3_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_12_checked : move3_12.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_12.src.time r) (move3_12.dst.time r) := by
  apply move3_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_12_checked g h))

def move3_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_13_checked : move3_13.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_13.src.time r) (move3_13.dst.time r) := by
  apply move3_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_13_checked g h))

def move3_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_14_checked : move3_14.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_14.src.time r) (move3_14.dst.time r) := by
  apply move3_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_14_checked g h))

def move3_15 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_15_checked : move3_15.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_15.src.time r) (move3_15.dst.time r) := by
  apply move3_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_15_checked g h))

def move3_16 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_16_checked : move3_16.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_16.src.time r) (move3_16.dst.time r) := by
  apply move3_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_16_checked g h))

def move3_17 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_17_checked : move3_17.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_17.src.time r) (move3_17.dst.time r) := by
  apply move3_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_17_checked g h))

def move3_18 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_18_checked : move3_18.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_18.src.time r) (move3_18.dst.time r) := by
  apply move3_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_18_checked g h))

def move3_19 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨6, 105 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨5, .clear⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_19_checked : move3_19.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_19.src.time r) (move3_19.dst.time r) := by
  apply move3_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_19_checked g h))

def move3_20 : Row :=
  ⟨⟨6, 105 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_20_checked : move3_20.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_20.src.time r) (move3_20.dst.time r) := by
  apply move3_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_20_checked g h))

def move3_21 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_21_checked : move3_21.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_21.src.time r) (move3_21.dst.time r) := by
  apply move3_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_21_checked g h))

def move3_22 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_22_checked : move3_22.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_22.src.time r) (move3_22.dst.time r) := by
  apply move3_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_22_checked g h))

def move3_23 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_23_checked : move3_23.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_23.src.time r) (move3_23.dst.time r) := by
  apply move3_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_23_checked g h))

def move3_24 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move3_24_checked : move3_24.guards.all
    (fun g => guards3.contains g) = true := by decide +kernel

private theorem move3_24_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards3, g.valid r) :
    IsMove (Finset.univ.image r) (move3_24.src.time r) (move3_24.dst.time r) := by
  apply move3_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move3_24_checked g h))

def end3 : Anchor := ⟨6, 145 / 8⟩
def clear3 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear3_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end3 (clear3 i) i).all (fun g => guards3.contains g)) = true := by
  decide +kernel

theorem landing3 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors3, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = end3.time r ∧
    LonelyAt (Finset.univ.image r) (end3.time r) := by
  have hg : ∀ g ∈ guards3, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route3_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move3_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move3_0]
  have at1 : seq 1 = move3_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move3_0_sound r hp hg)
  have at2 : seq 2 = move3_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move3_1_sound r hp hg)
  have at3 : seq 3 = move3_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move3_2_sound r hp hg)
  have at4 : seq 4 = move3_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move3_3_sound r hp hg)
  have at5 : seq 5 = move3_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move3_4_sound r hp hg)
  have at6 : seq 6 = move3_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move3_5_sound r hp hg)
  have at7 : seq 7 = move3_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move3_6_sound r hp hg)
  have at8 : seq 8 = move3_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move3_7_sound r hp hg)
  have at9 : seq 9 = move3_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move3_8_sound r hp hg)
  have at10 : seq 10 = move3_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move3_9_sound r hp hg)
  have at11 : seq 11 = move3_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move3_10_sound r hp hg)
  have at12 : seq 12 = move3_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move3_11_sound r hp hg)
  have at13 : seq 13 = move3_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move3_12_sound r hp hg)
  have at14 : seq 14 = move3_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move3_13_sound r hp hg)
  have at15 : seq 15 = move3_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move3_14_sound r hp hg)
  have at16 : seq 16 = move3_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move3_15_sound r hp hg)
  have at17 : seq 17 = move3_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move3_16_sound r hp hg)
  have at18 : seq 18 = move3_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move3_17_sound r hp hg)
  have at19 : seq 19 = move3_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move3_18_sound r hp hg)
  have at20 : seq 20 = move3_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move3_19_sound r hp hg)
  have at21 : seq 21 = move3_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move3_20_sound r hp hg)
  have at22 : seq 22 = move3_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move3_21_sound r hp hg)
  have at23 : seq 23 = move3_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move3_22_sound r hp hg)
  have at24 : seq 24 = move3_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move3_23_sound r hp hg)
  have at25 : seq 25 = move3_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move3_24_sound r hp hg)
  refine ⟨at25, ?_⟩
  apply terminal r hp end3 clear3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear3_checked i (by simp)) g hm)

#print axioms landing3

def guards4 := route4.map Prod.fst

def move4_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_0_checked : move4_0.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_0.src.time r) (move4_0.dst.time r) := by
  apply move4_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_0_checked g h))

def move4_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_1_checked : move4_1.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_1.src.time r) (move4_1.dst.time r) := by
  apply move4_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_1_checked g h))

def move4_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_2_checked : move4_2.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_2.src.time r) (move4_2.dst.time r) := by
  apply move4_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_2_checked g h))

def move4_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_3_checked : move4_3.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_3.src.time r) (move4_3.dst.time r) := by
  apply move4_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_3_checked g h))

def move4_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_4_checked : move4_4.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_4.src.time r) (move4_4.dst.time r) := by
  apply move4_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_4_checked g h))

def move4_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_5_checked : move4_5.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_5.src.time r) (move4_5.dst.time r) := by
  apply move4_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_5_checked g h))

def move4_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_6_checked : move4_6.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_6.src.time r) (move4_6.dst.time r) := by
  apply move4_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_6_checked g h))

def move4_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_7_checked : move4_7.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_7.src.time r) (move4_7.dst.time r) := by
  apply move4_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_7_checked g h))

def move4_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_8_checked : move4_8.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_8.src.time r) (move4_8.dst.time r) := by
  apply move4_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_8_checked g h))

def move4_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_9_checked : move4_9.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_9.src.time r) (move4_9.dst.time r) := by
  apply move4_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_9_checked g h))

def move4_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_10_checked : move4_10.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_10.src.time r) (move4_10.dst.time r) := by
  apply move4_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_10_checked g h))

def move4_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_11_checked : move4_11.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_11.src.time r) (move4_11.dst.time r) := by
  apply move4_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_11_checked g h))

def move4_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_12_checked : move4_12.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_12.src.time r) (move4_12.dst.time r) := by
  apply move4_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_12_checked g h))

def move4_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_13_checked : move4_13.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_13.src.time r) (move4_13.dst.time r) := by
  apply move4_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_13_checked g h))

def move4_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_14_checked : move4_14.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_14.src.time r) (move4_14.dst.time r) := by
  apply move4_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_14_checked g h))

def move4_15 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_15_checked : move4_15.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_15.src.time r) (move4_15.dst.time r) := by
  apply move4_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_15_checked g h))

def move4_16 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_16_checked : move4_16.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_16.src.time r) (move4_16.dst.time r) := by
  apply move4_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_16_checked g h))

def move4_17 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_17_checked : move4_17.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_17.src.time r) (move4_17.dst.time r) := by
  apply move4_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_17_checked g h))

def move4_18 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_18_checked : move4_18.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_18.src.time r) (move4_18.dst.time r) := by
  apply move4_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_18_checked g h))

def move4_19 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨6, 105 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨5, .clear⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_19_checked : move4_19.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_19.src.time r) (move4_19.dst.time r) := by
  apply move4_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_19_checked g h))

def move4_20 : Row :=
  ⟨⟨6, 105 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_20_checked : move4_20.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_20.src.time r) (move4_20.dst.time r) := by
  apply move4_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_20_checked g h))

def move4_21 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_21_checked : move4_21.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_21.src.time r) (move4_21.dst.time r) := by
  apply move4_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_21_checked g h))

def move4_22 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨6, 137 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨7, .clear⟩, ⟨17, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_22_checked : move4_22.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_22.src.time r) (move4_22.dst.time r) := by
  apply move4_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_22_checked g h))

def move4_23 : Row :=
  ⟨⟨6, 137 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_23_checked : move4_23.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_23.src.time r) (move4_23.dst.time r) := by
  apply move4_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_23_checked g h))

def move4_24 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_24_checked : move4_24.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_24_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_24.src.time r) (move4_24.dst.time r) := by
  apply move4_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_24_checked g h))

def move4_25 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move4_25_checked : move4_25.guards.all
    (fun g => guards4.contains g) = true := by decide +kernel

private theorem move4_25_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards4, g.valid r) :
    IsMove (Finset.univ.image r) (move4_25.src.time r) (move4_25.dst.time r) := by
  apply move4_25.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move4_25_checked g h))

def end4 : Anchor := ⟨6, 145 / 8⟩
def clear4 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear4_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end4 (clear4 i) i).all (fun g => guards4.contains g)) = true := by
  decide +kernel

theorem landing4 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors4, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 26 = end4.time r ∧
    LonelyAt (Finset.univ.image r) (end4.time r) := by
  have hg : ∀ g ∈ guards4, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route4_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move4_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move4_0]
  have at1 : seq 1 = move4_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move4_0_sound r hp hg)
  have at2 : seq 2 = move4_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move4_1_sound r hp hg)
  have at3 : seq 3 = move4_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move4_2_sound r hp hg)
  have at4 : seq 4 = move4_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move4_3_sound r hp hg)
  have at5 : seq 5 = move4_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move4_4_sound r hp hg)
  have at6 : seq 6 = move4_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move4_5_sound r hp hg)
  have at7 : seq 7 = move4_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move4_6_sound r hp hg)
  have at8 : seq 8 = move4_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move4_7_sound r hp hg)
  have at9 : seq 9 = move4_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move4_8_sound r hp hg)
  have at10 : seq 10 = move4_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move4_9_sound r hp hg)
  have at11 : seq 11 = move4_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move4_10_sound r hp hg)
  have at12 : seq 12 = move4_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move4_11_sound r hp hg)
  have at13 : seq 13 = move4_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move4_12_sound r hp hg)
  have at14 : seq 14 = move4_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move4_13_sound r hp hg)
  have at15 : seq 15 = move4_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move4_14_sound r hp hg)
  have at16 : seq 16 = move4_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move4_15_sound r hp hg)
  have at17 : seq 17 = move4_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move4_16_sound r hp hg)
  have at18 : seq 18 = move4_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move4_17_sound r hp hg)
  have at19 : seq 19 = move4_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move4_18_sound r hp hg)
  have at20 : seq 20 = move4_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move4_19_sound r hp hg)
  have at21 : seq 21 = move4_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move4_20_sound r hp hg)
  have at22 : seq 22 = move4_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move4_21_sound r hp hg)
  have at23 : seq 23 = move4_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move4_22_sound r hp hg)
  have at24 : seq 24 = move4_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move4_23_sound r hp hg)
  have at25 : seq 25 = move4_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move4_24_sound r hp hg)
  have at26 : seq 26 = move4_25.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 25) (seq 26) :=
      cascadeSeq_isMove _ _ 25
    rw [at25] at hm
    exact isMove_unique hm (move4_25_sound r hp hg)
  refine ⟨at26, ?_⟩
  apply terminal r hp end4 clear4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear4_checked i (by simp)) g hm)

#print axioms landing4

def guards5 := route5.map Prod.fst

def move5_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_0_checked : move5_0.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_0.src.time r) (move5_0.dst.time r) := by
  apply move5_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_0_checked g h))

def move5_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_1_checked : move5_1.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_1.src.time r) (move5_1.dst.time r) := by
  apply move5_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_1_checked g h))

def move5_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_2_checked : move5_2.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_2.src.time r) (move5_2.dst.time r) := by
  apply move5_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_2_checked g h))

def move5_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_3_checked : move5_3.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_3.src.time r) (move5_3.dst.time r) := by
  apply move5_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_3_checked g h))

def move5_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_4_checked : move5_4.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_4.src.time r) (move5_4.dst.time r) := by
  apply move5_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_4_checked g h))

def move5_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_5_checked : move5_5.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_5.src.time r) (move5_5.dst.time r) := by
  apply move5_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_5_checked g h))

def move5_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_6_checked : move5_6.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_6.src.time r) (move5_6.dst.time r) := by
  apply move5_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_6_checked g h))

def move5_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_7_checked : move5_7.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_7.src.time r) (move5_7.dst.time r) := by
  apply move5_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_7_checked g h))

def move5_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_8_checked : move5_8.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_8.src.time r) (move5_8.dst.time r) := by
  apply move5_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_8_checked g h))

def move5_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_9_checked : move5_9.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_9.src.time r) (move5_9.dst.time r) := by
  apply move5_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_9_checked g h))

def move5_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_10_checked : move5_10.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_10.src.time r) (move5_10.dst.time r) := by
  apply move5_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_10_checked g h))

def move5_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_11_checked : move5_11.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_11.src.time r) (move5_11.dst.time r) := by
  apply move5_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_11_checked g h))

def move5_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_12_checked : move5_12.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_12.src.time r) (move5_12.dst.time r) := by
  apply move5_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_12_checked g h))

def move5_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_13_checked : move5_13.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_13.src.time r) (move5_13.dst.time r) := by
  apply move5_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_13_checked g h))

def move5_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨6, 73 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_14_checked : move5_14.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_14.src.time r) (move5_14.dst.time r) := by
  apply move5_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_14_checked g h))

def move5_15 : Row :=
  ⟨⟨6, 73 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_15_checked : move5_15.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_15.src.time r) (move5_15.dst.time r) := by
  apply move5_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_15_checked g h))

def move5_16 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_16_checked : move5_16.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_16.src.time r) (move5_16.dst.time r) := by
  apply move5_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_16_checked g h))

def move5_17 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_17_checked : move5_17.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_17.src.time r) (move5_17.dst.time r) := by
  apply move5_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_17_checked g h))

def move5_18 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_18_checked : move5_18.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_18.src.time r) (move5_18.dst.time r) := by
  apply move5_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_18_checked g h))

def move5_19 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_19_checked : move5_19.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_19.src.time r) (move5_19.dst.time r) := by
  apply move5_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_19_checked g h))

def move5_20 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_20_checked : move5_20.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_20.src.time r) (move5_20.dst.time r) := by
  apply move5_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_20_checked g h))

def move5_21 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_21_checked : move5_21.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_21.src.time r) (move5_21.dst.time r) := by
  apply move5_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_21_checked g h))

def move5_22 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_22_checked : move5_22.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_22.src.time r) (move5_22.dst.time r) := by
  apply move5_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_22_checked g h))

def move5_23 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_23_checked : move5_23.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_23.src.time r) (move5_23.dst.time r) := by
  apply move5_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_23_checked g h))

def move5_24 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move5_24_checked : move5_24.guards.all
    (fun g => guards5.contains g) = true := by decide +kernel

private theorem move5_24_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards5, g.valid r) :
    IsMove (Finset.univ.image r) (move5_24.src.time r) (move5_24.dst.time r) := by
  apply move5_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move5_24_checked g h))

def end5 : Anchor := ⟨6, 145 / 8⟩
def clear5 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear5_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end5 (clear5 i) i).all (fun g => guards5.contains g)) = true := by
  decide +kernel

theorem landing5 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors5, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 25 = end5.time r ∧
    LonelyAt (Finset.univ.image r) (end5.time r) := by
  have hg : ∀ g ∈ guards5, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route5_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move5_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move5_0]
  have at1 : seq 1 = move5_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move5_0_sound r hp hg)
  have at2 : seq 2 = move5_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move5_1_sound r hp hg)
  have at3 : seq 3 = move5_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move5_2_sound r hp hg)
  have at4 : seq 4 = move5_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move5_3_sound r hp hg)
  have at5 : seq 5 = move5_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move5_4_sound r hp hg)
  have at6 : seq 6 = move5_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move5_5_sound r hp hg)
  have at7 : seq 7 = move5_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move5_6_sound r hp hg)
  have at8 : seq 8 = move5_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move5_7_sound r hp hg)
  have at9 : seq 9 = move5_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move5_8_sound r hp hg)
  have at10 : seq 10 = move5_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move5_9_sound r hp hg)
  have at11 : seq 11 = move5_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move5_10_sound r hp hg)
  have at12 : seq 12 = move5_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move5_11_sound r hp hg)
  have at13 : seq 13 = move5_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move5_12_sound r hp hg)
  have at14 : seq 14 = move5_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move5_13_sound r hp hg)
  have at15 : seq 15 = move5_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move5_14_sound r hp hg)
  have at16 : seq 16 = move5_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move5_15_sound r hp hg)
  have at17 : seq 17 = move5_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move5_16_sound r hp hg)
  have at18 : seq 18 = move5_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move5_17_sound r hp hg)
  have at19 : seq 19 = move5_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move5_18_sound r hp hg)
  have at20 : seq 20 = move5_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move5_19_sound r hp hg)
  have at21 : seq 21 = move5_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move5_20_sound r hp hg)
  have at22 : seq 22 = move5_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move5_21_sound r hp hg)
  have at23 : seq 23 = move5_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move5_22_sound r hp hg)
  have at24 : seq 24 = move5_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move5_23_sound r hp hg)
  have at25 : seq 25 = move5_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move5_24_sound r hp hg)
  refine ⟨at25, ?_⟩
  apply terminal r hp end5 clear5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear5_checked i (by simp)) g hm)

#print axioms landing5

def guards6 := route6.map Prod.fst

def move6_0 : Row :=
  ⟨⟨0, 1 / 8⟩, ⟨6, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨2, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_0_checked : move6_0.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_0_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_0.src.time r) (move6_0.dst.time r) := by
  apply move6_0.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_0_checked g h))

def move6_1 : Row :=
  ⟨⟨6, 17 / 8⟩, ⟨5, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_1_checked : move6_1.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_1_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_1.src.time r) (move6_1.dst.time r) := by
  apply move6_1.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_1_checked g h))

def move6_2 : Row :=
  ⟨⟨5, 9 / 8⟩, ⟨4, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_2_checked : move6_2.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_2_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_2.src.time r) (move6_2.dst.time r) := by
  apply move6_2.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_2_checked g h))

def move6_3 : Row :=
  ⟨⟨4, 9 / 8⟩, ⟨3, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_3_checked : move6_3.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_3_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_3.src.time r) (move6_3.dst.time r) := by
  apply move6_3.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_3_checked g h))

def move6_4 : Row :=
  ⟨⟨3, 9 / 8⟩, ⟨2, 9 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨3, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_4_checked : move6_4.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_4_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_4.src.time r) (move6_4.dst.time r) := by
  apply move6_4.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_4_checked g h))

def move6_5 : Row :=
  ⟨⟨2, 9 / 8⟩, ⟨5, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_5_checked : move6_5.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_5_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_5.src.time r) (move6_5.dst.time r) := by
  apply move6_5.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_5_checked g h))

def move6_6 : Row :=
  ⟨⟨5, 17 / 8⟩, ⟨4, 17 / 8⟩, ![⟨0, .clear⟩, ⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨4, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_6_checked : move6_6.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_6_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_6.src.time r) (move6_6.dst.time r) := by
  apply move6_6.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_6_checked g h))

def move6_7 : Row :=
  ⟨⟨4, 17 / 8⟩, ⟨1, 9 / 8⟩, ![⟨0, .clear⟩, ⟨1, .capture⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨5, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_7_checked : move6_7.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_7_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_7.src.time r) (move6_7.dst.time r) := by
  apply move6_7.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_7_checked g h))

def move6_8 : Row :=
  ⟨⟨1, 9 / 8⟩, ⟨3, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨6, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_8_checked : move6_8.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_8_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_8.src.time r) (move6_8.dst.time r) := by
  apply move6_8.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_8_checked g h))

def move6_9 : Row :=
  ⟨⟨3, 17 / 8⟩, ⟨5, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨6, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_9_checked : move6_9.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_9_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_9.src.time r) (move6_9.dst.time r) := by
  apply move6_9.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_9_checked g h))

def move6_10 : Row :=
  ⟨⟨5, 25 / 8⟩, ⟨6, 57 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨7, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_10_checked : move6_10.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_10_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_10.src.time r) (move6_10.dst.time r) := by
  apply move6_10.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_10_checked g h))

def move6_11 : Row :=
  ⟨⟨6, 57 / 8⟩, ⟨4, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_11_checked : move6_11.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_11_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_11.src.time r) (move6_11.dst.time r) := by
  apply move6_11.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_11_checked g h))

def move6_12 : Row :=
  ⟨⟨4, 25 / 8⟩, ⟨2, 17 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨3, .clear⟩, ⟨7, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_12_checked : move6_12.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_12_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_12.src.time r) (move6_12.dst.time r) := by
  apply move6_12.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_12_checked g h))

def move6_13 : Row :=
  ⟨⟨2, 17 / 8⟩, ⟨5, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨8, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_13_checked : move6_13.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_13_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_13.src.time r) (move6_13.dst.time r) := by
  apply move6_13.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_13_checked g h))

def move6_14 : Row :=
  ⟨⟨5, 33 / 8⟩, ⟨6, 73 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_14_checked : move6_14.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_14_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_14.src.time r) (move6_14.dst.time r) := by
  apply move6_14.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_14_checked g h))

def move6_15 : Row :=
  ⟨⟨6, 73 / 8⟩, ⟨3, 25 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨9, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_15_checked : move6_15.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_15_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_15.src.time r) (move6_15.dst.time r) := by
  apply move6_15.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_15_checked g h))

def move6_16 : Row :=
  ⟨⟨3, 25 / 8⟩, ⟨4, 33 / 8⟩, ![⟨0, .clear⟩, ⟨1, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨4, .clear⟩, ⟨10, .optional⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_16_checked : move6_16.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_16_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_16.src.time r) (move6_16.dst.time r) := by
  apply move6_16.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_16_checked g h))

def move6_17 : Row :=
  ⟨⟨4, 33 / 8⟩, ⟨1, 17 / 8⟩, ![⟨0, .clear⟩, ⟨2, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨4, .clear⟩, ⟨10, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_17_checked : move6_17.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_17_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_17.src.time r) (move6_17.dst.time r) := by
  apply move6_17.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_17_checked g h))

def move6_18 : Row :=
  ⟨⟨1, 17 / 8⟩, ⟨2, 25 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .capture⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨11, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_18_checked : move6_18.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_18_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_18.src.time r) (move6_18.dst.time r) := by
  apply move6_18.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_18_checked g h))

def move6_19 : Row :=
  ⟨⟨2, 25 / 8⟩, ⟨3, 33 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .capture⟩, ⟨5, .capture⟩, ⟨5, .clear⟩, ⟨12, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_19_checked : move6_19.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_19_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_19.src.time r) (move6_19.dst.time r) := by
  apply move6_19.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_19_checked g h))

def move6_20 : Row :=
  ⟨⟨3, 33 / 8⟩, ⟨5, 49 / 8⟩, ![⟨0, .clear⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .capture⟩, ⟨13, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_20_checked : move6_20.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_20_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_20.src.time r) (move6_20.dst.time r) := by
  apply move6_20.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_20_checked g h))

def move6_21 : Row :=
  ⟨⟨5, 49 / 8⟩, ⟨0, 9 / 8⟩, ![⟨1, .capture⟩, ⟨2, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨13, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_21_checked : move6_21.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_21_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_21.src.time r) (move6_21.dst.time r) := by
  apply move6_21.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_21_checked g h))

def move6_22 : Row :=
  ⟨⟨0, 9 / 8⟩, ⟨6, 137 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨6, .clear⟩, ⟨7, .clear⟩, ⟨17, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_22_checked : move6_22.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_22_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_22.src.time r) (move6_22.dst.time r) := by
  apply move6_22.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_22_checked g h))

def move6_23 : Row :=
  ⟨⟨6, 137 / 8⟩, ⟨4, 57 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .capture⟩, ⟨7, .clear⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_23_checked : move6_23.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_23_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_23.src.time r) (move6_23.dst.time r) := by
  apply move6_23.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_23_checked g h))

def move6_24 : Row :=
  ⟨⟨4, 57 / 8⟩, ⟨5, 65 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .capture⟩, ⟨17, .clear⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_24_checked : move6_24.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_24_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_24.src.time r) (move6_24.dst.time r) := by
  apply move6_24.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_24_checked g h))

def move6_25 : Row :=
  ⟨⟨5, 65 / 8⟩, ⟨6, 145 / 8⟩, ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .capture⟩]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem move6_25_checked : move6_25.guards.all
    (fun g => guards6.contains g) = true := by decide +kernel

private theorem move6_25_sound (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (hg : ∀ g ∈ guards6, g.valid r) :
    IsMove (Finset.univ.image r) (move6_25.src.time r) (move6_25.dst.time r) := by
  apply move6_25.move r hp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact fun g h => hg g (List.contains_iff_mem.mp (List.all_eq_true.mp move6_25_checked g h))

def end6 : Anchor := ⟨6, 145 / 8⟩
def clear6 : Fin 7 → Band := ![⟨1, .clear⟩, ⟨3, .clear⟩, ⟨4, .clear⟩, ⟨5, .clear⟩, ⟨7, .clear⟩, ⟨8, .clear⟩, ⟨18, .clear⟩]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem clear6_checked : (List.finRange 7).all (fun i =>
    (phaseGuards end6 (clear6 i) i).all (fun g => guards6.contains g)) = true := by
  decide +kernel

theorem landing6 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ envelope ++ selectors6, g.valid r) :
    cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0) 26 = end6.time r ∧
    LonelyAt (Finset.univ.image r) (end6.time r) := by
  have hg : ∀ g ∈ guards6, g.valid r := by
    intro g hm
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    exact route6_guards r hp he row hr
  let seq := cascadeSeq (Finset.univ.image r) ((1 / 8) / r 0)
  have at0 : seq 0 = move6_0.src.time r := by
    norm_num [seq, cascadeSeq_zero, Anchor.time, move6_0]
  have at1 : seq 1 = move6_0.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 0) (seq 1) :=
      cascadeSeq_isMove _ _ 0
    rw [at0] at hm
    exact isMove_unique hm (move6_0_sound r hp hg)
  have at2 : seq 2 = move6_1.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 1) (seq 2) :=
      cascadeSeq_isMove _ _ 1
    rw [at1] at hm
    exact isMove_unique hm (move6_1_sound r hp hg)
  have at3 : seq 3 = move6_2.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 2) (seq 3) :=
      cascadeSeq_isMove _ _ 2
    rw [at2] at hm
    exact isMove_unique hm (move6_2_sound r hp hg)
  have at4 : seq 4 = move6_3.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 3) (seq 4) :=
      cascadeSeq_isMove _ _ 3
    rw [at3] at hm
    exact isMove_unique hm (move6_3_sound r hp hg)
  have at5 : seq 5 = move6_4.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 4) (seq 5) :=
      cascadeSeq_isMove _ _ 4
    rw [at4] at hm
    exact isMove_unique hm (move6_4_sound r hp hg)
  have at6 : seq 6 = move6_5.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 5) (seq 6) :=
      cascadeSeq_isMove _ _ 5
    rw [at5] at hm
    exact isMove_unique hm (move6_5_sound r hp hg)
  have at7 : seq 7 = move6_6.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 6) (seq 7) :=
      cascadeSeq_isMove _ _ 6
    rw [at6] at hm
    exact isMove_unique hm (move6_6_sound r hp hg)
  have at8 : seq 8 = move6_7.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 7) (seq 8) :=
      cascadeSeq_isMove _ _ 7
    rw [at7] at hm
    exact isMove_unique hm (move6_7_sound r hp hg)
  have at9 : seq 9 = move6_8.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 8) (seq 9) :=
      cascadeSeq_isMove _ _ 8
    rw [at8] at hm
    exact isMove_unique hm (move6_8_sound r hp hg)
  have at10 : seq 10 = move6_9.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 9) (seq 10) :=
      cascadeSeq_isMove _ _ 9
    rw [at9] at hm
    exact isMove_unique hm (move6_9_sound r hp hg)
  have at11 : seq 11 = move6_10.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 10) (seq 11) :=
      cascadeSeq_isMove _ _ 10
    rw [at10] at hm
    exact isMove_unique hm (move6_10_sound r hp hg)
  have at12 : seq 12 = move6_11.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 11) (seq 12) :=
      cascadeSeq_isMove _ _ 11
    rw [at11] at hm
    exact isMove_unique hm (move6_11_sound r hp hg)
  have at13 : seq 13 = move6_12.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 12) (seq 13) :=
      cascadeSeq_isMove _ _ 12
    rw [at12] at hm
    exact isMove_unique hm (move6_12_sound r hp hg)
  have at14 : seq 14 = move6_13.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 13) (seq 14) :=
      cascadeSeq_isMove _ _ 13
    rw [at13] at hm
    exact isMove_unique hm (move6_13_sound r hp hg)
  have at15 : seq 15 = move6_14.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 14) (seq 15) :=
      cascadeSeq_isMove _ _ 14
    rw [at14] at hm
    exact isMove_unique hm (move6_14_sound r hp hg)
  have at16 : seq 16 = move6_15.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 15) (seq 16) :=
      cascadeSeq_isMove _ _ 15
    rw [at15] at hm
    exact isMove_unique hm (move6_15_sound r hp hg)
  have at17 : seq 17 = move6_16.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 16) (seq 17) :=
      cascadeSeq_isMove _ _ 16
    rw [at16] at hm
    exact isMove_unique hm (move6_16_sound r hp hg)
  have at18 : seq 18 = move6_17.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 17) (seq 18) :=
      cascadeSeq_isMove _ _ 17
    rw [at17] at hm
    exact isMove_unique hm (move6_17_sound r hp hg)
  have at19 : seq 19 = move6_18.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 18) (seq 19) :=
      cascadeSeq_isMove _ _ 18
    rw [at18] at hm
    exact isMove_unique hm (move6_18_sound r hp hg)
  have at20 : seq 20 = move6_19.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 19) (seq 20) :=
      cascadeSeq_isMove _ _ 19
    rw [at19] at hm
    exact isMove_unique hm (move6_19_sound r hp hg)
  have at21 : seq 21 = move6_20.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 20) (seq 21) :=
      cascadeSeq_isMove _ _ 20
    rw [at20] at hm
    exact isMove_unique hm (move6_20_sound r hp hg)
  have at22 : seq 22 = move6_21.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 21) (seq 22) :=
      cascadeSeq_isMove _ _ 21
    rw [at21] at hm
    exact isMove_unique hm (move6_21_sound r hp hg)
  have at23 : seq 23 = move6_22.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 22) (seq 23) :=
      cascadeSeq_isMove _ _ 22
    rw [at22] at hm
    exact isMove_unique hm (move6_22_sound r hp hg)
  have at24 : seq 24 = move6_23.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 23) (seq 24) :=
      cascadeSeq_isMove _ _ 23
    rw [at23] at hm
    exact isMove_unique hm (move6_23_sound r hp hg)
  have at25 : seq 25 = move6_24.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 24) (seq 25) :=
      cascadeSeq_isMove _ _ 24
    rw [at24] at hm
    exact isMove_unique hm (move6_24_sound r hp hg)
  have at26 : seq 26 = move6_25.dst.time r := by
    have hm : IsMove (Finset.univ.image r) (seq 25) (seq 26) :=
      cascadeSeq_isMove _ _ 25
    rw [at25] at hm
    exact isMove_unique hm (move6_25_sound r hp hg)
  refine ⟨at26, ?_⟩
  apply terminal r hp end6 clear6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i g hm
  apply hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp clear6_checked i (by simp)) g hm)

#print axioms landing6

end Fresh.NativeJ2RatioEnvelopeLanding
