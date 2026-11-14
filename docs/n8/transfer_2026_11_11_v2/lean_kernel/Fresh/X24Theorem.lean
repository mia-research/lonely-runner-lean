import Fresh.X24Total
import Fresh.X24Checked

namespace Fresh.X24Replay

/-- For a fixed slow profile the chosen cells are independent of the last reading. -/
theorem x24WideCells (g : Fin 7 → ℝ) (pin : g 0 = 1)
    (ordered : Monotone g) (hmax : g 5 ≤ 51/2) : CellPairFor g :=
  cells_of_check wideCheck g pin ordered hmax

/-- Every normalized tuple with fastest reading in the closed band
[22.5,25.5] has a common clear point in the two cascade windows. -/
theorem x24WideBand (g : Fin 7 → ℝ) (bounds : ∀ i, 1 ≤ g i ∧ g i ≤ 51/2)
    (pin : ∃ i, g i = 1) (fast : ∃ i, 45/2 ≤ g i) :
    Fresh.BandNoCarve.BandClearPoint g :=
  bandClearPoint_of_check_unsorted wideCheck g bounds pin fast

#print axioms x24WideCells
#print axioms x24WideBand

end Fresh.X24Replay
