import Fresh.BandNoCarve
import Fresh.BandCertDataExt
import Fresh.M4ZoneFinal
import Fresh.ChainZoneFinal

/-!
# The terminal assembly at the extended band strength

The covering premise of the terminal assembly is upgraded from `BandCertData` (five
schemas) to `BandCertData6` (five schemas ∨ the sixth, side-window-vertex class).  The
upgrade is load-bearing, not cosmetic: E846 measured 0/1,018 off-plane regions reducible
to the five original schemas (`FrontierTypeCensus`, bbox-extend 0/1,018), so the
off-plane tranche landed in `Fresh.BandRepOffGrand` can only be consumed through
`BandSideWindowV`.  Everything downstream of the band premise is unchanged: the sixth
schema's soundness routes through `sideWindowCertV_noCarve` → `clearPoint_of_noCarve`,
the same clear-point bridge the first five schemas use.

Both premises consumed here that are already theorems:
`Fresh.M4ZoneChunks.m4BoxNoCarvePinned_proved` and
`Fresh.ChainZone.chainBoxSoundPinned_proved` (E925).  The remaining OWED premises of
this file are `BandCertData6` (the tranche composition; the per-tranche theorems are
landed in `Fresh.BandReplayPinchFull`, `Fresh.BandRepOffGrand`, `Fresh.BandReplayBulk*`,
`Fresh.BandCertDataExt`) and `TailBelow17` (the above-51 dispatch; the [49,51] strip is
kernel-clean in `Fresh.TailStrip49Kernel`).
-/

namespace Fresh.BandNoCarve

/-- **The terminal assembly at the extended band strength** — `filterAssembly_of_bandData`
with the band premise at `BandCertData6`. -/
theorem filterAssembly_of_bandData6
    (hM4 : FilterAssemblyPerBoxV2.M4BoxNoCarvePinned)
    (hChain : FilterAssemblyPerBoxV2.ChainBoxSoundPinned)
    (hBand : BandCertData6) (hTail : FilterAssembly.TailBelow17) : LonelyRunnerEight :=
  FilterAssemblyPerBoxV2.filterAssemblyPerBoxPinned hM4 hChain (bandNoCarve6 hBand) hTail

/-- The band-premise reduction, for the record: the original assembly consumes the
extended data through the proved `bandCertData6_of_bandData` only in the five-schema
direction; at six schemas no reduction to `BandCertData` is possible (the off-plane
census), so this is the form the campaign targets. -/
theorem lonelyRunnerEight_of_band_tail6
    (hBand : BandCertData6) (hTail : FilterAssembly.TailBelow17) : LonelyRunnerEight :=
  filterAssembly_of_bandData6
    Fresh.M4ZoneChunks.m4BoxNoCarvePinned_proved
    Fresh.ChainZone.chainBoxSoundPinned_proved hBand hTail

#print axioms Fresh.BandNoCarve.filterAssembly_of_bandData6
#print axioms Fresh.BandNoCarve.lonelyRunnerEight_of_band_tail6

end Fresh.BandNoCarve
