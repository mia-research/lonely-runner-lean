import Mathlib
import Fresh.BandNoCarve
import Fresh.ChainZoneFinal
import Fresh.M4ZoneFinal

/-!
# `filterAssembly_of_bandData` with its first two premises paid (2026-11-22)

New file; nothing existing is edited.

`Fresh.BandNoCarve.filterAssembly_of_bandData` takes four premises: `M4BoxNoCarvePinned`,
`ChainBoxSoundPinned`, `BandCertData`, `TailBelow17`.  The first is
`Fresh.M4ZoneChunks.m4BoxNoCarvePinned_proved`, the second
`Fresh.ChainZone.chainBoxSoundPinned_proved` (gap-pattern zone certificates, log E925).
What remains is `BandCertData` and `TailBelow17`.
-/

namespace Fresh.BandAssemblyReduced

open Fresh Fresh.BandNoCarve Fresh.FilterAssembly

/-- **`LonelyRunnerEight` from the two remaining premises.** -/
theorem lonelyRunnerEight_of_band_tail (hBand : BandCertData) (hTail : TailBelow17) :
    LonelyRunnerEight :=
  filterAssembly_of_bandData Fresh.M4ZoneChunks.m4BoxNoCarvePinned_proved
    Fresh.ChainZone.chainBoxSoundPinned_proved hBand hTail

#print axioms lonelyRunnerEight_of_band_tail

end Fresh.BandAssemblyReduced
