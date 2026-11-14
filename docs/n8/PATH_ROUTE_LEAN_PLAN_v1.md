# The path route in Lean: plan (v1, 2026-09-27)

Owner: *"Ok so we need to do this in lean"* (the path route of E114), then (B). Running record: `RUNNING_LOG_order8_v1.md`
E113–E114. Lean paths relative to `LonelyRunner/LonelyRunner/LRC/Spec/`.

**Target of this plan.** For the slowest runner `k` of whole-number arrangements, with the window (B) as an explicit
hypothesis:

```
WindowOn c C c' T  →  every arrangement with readings in [c, C] is lonely
```

where `WindowOn c C c' T` says: every arrangement whose readings (the slowest runner's) lie in `[c, C]`, if lonely, is
lonely at some `t ∈ [c', T]`. With `EndRunnerN`, a proof of the window for all `c, C` gives `LonelyRunnerAt8`. The
window stays an explicit hypothesis until (B) is proved; nothing here asserts it.

**Pieces, in build order** (each a small module or section, gated, axiom-clean, committed per change):

| # | statement | status |
|---|---|---|
| P0 | `PinchOpenN`: a simple pinch stays lonely under small changes, one side by the leaving runner's opening, the other by the mirror | done (`695253c`); refactor the mirror to any common period `P > t0` (rational readings, no rescaling) |
| P1 | at a lonely instant of positive readings: an instant with margin exists, or the instant is a pinch (a runner on `+1/8` and one on `−1/8`); a pinch is simple (others strictly clear, hence a margin for them) or multi (a third runner on an edge) | |
| P2 | along a line of readings through a simple pinch: the direction is inside the wall (both sides open at the leaving runner's opening, no mirror), or the crossing parameter is rational (rational ends), so the readings have a common period and `pinch_eventually_lonely` applies | |
| P3 | at the AP (readings `g·(1…7)`) no two runners are ever on the same edge (`8 ∤ (j − i)`) | |
| P4 | multi pinches with laps `≤ L`: finitely many codimension-2 conditions; a rational point `M` in the open region of increasing positive readings off finitely many hyperplanes exists; the segments AP → M → target meet none of them at a parameter in `[0, 1)` | |
| P5 | `lonely_along_path` with `hopen` required only on `[0, 1)` (the proof already uses only that) | |
| P6 | assembly: two segments, `hopen` from margin (`eventually_lonely_of_margin`) or P1+P2 (simple) or P4 (multi excluded); `hbound` from the window | |
| P7 | `LonelyRunnerAt8` from the window for every `[c, C]`, through `EndRunnerN` | |

**Checks.** Each piece: `lake env lean` clean, then the Spec gate (`scripts/nN/spec_gate.sh`) PASS, `#print axioms` on the
new top statements shows `[propext, Classical.choice, Quot.sound]`. The window is registered as a Prop hypothesis, not a
`def … : Prop` asserted true (the gate's OWED register sees it if it is).

**Then (B)**, reasoned from the cascade: what bounds how far a relocation carries the isolation; the doubled slot as the
worked case of a predictable delay.
