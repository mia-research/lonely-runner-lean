# The movement statement: what Lean already has (v1)

2026-10-02. A crosswalk, from reading the Lean sources (nothing rebuilt; E290). Statements are the modules' own docstrings.

**The owner's argument** (`DeformationN`, 2026-09-26): *the arithmetic progression is globally isolated (the φ(n) law), every
arrangement is a deformation of it, and a deformation moves each runner's isolation point without destroying it.*
E289 added: loneliness binds only the two neighbours (one each side); every other runner need only lie in the remaining 6/8.

## Ingredients, by role
| role | Lean | what it says | status |
|---|---|---|---|
| base: the grid is globally isolated | `GridNeighbourhoodN.grid_nbhd_lonely`, `grid_nbhd_exists`; `APNeighbourhoodN` (`apT`, `ap_nbhd_lonely`); `GridPairLawN`; `GridClassN`; a complete residue system is lonely at `1/8` (R6 at `q = 8`, `OrderEightCasesN`) | at the class-1 instant every runner of the complete grid is lonely, laps invisible; with deviation `2ρ(14W+21) ≤ 1` each runner is lonely at a **named** instant (the class-1 neighbours' own openings, or the mirror) | proved |
| only the neighbours bind | `TwoPinnerN` ("the subject's two circle neighbours at `t*`"); `GridNeighbourhoodN.readings_clear` (neighbours `A`, `B` given, the rest in slots 2…6, every other runner clear) | the two neighbours' conditions fix the instant; the others are clear by their slots | proved |
| a lonely instant is a margin or a pinch | `PathRouteN.margin_or_pinch`, `simple_or_multi` | at a lonely instant either some instant has every runner strictly clear, or it is a pinch (one runner on `+1/8`, one on `−1/8`); a pinch is simple or multi | proved |
| movement, with margin | `DeformationN.lonelyAt_of_close` (openness) | lonely with margin `ε` ⇒ lonely at the same `t` under speed changes `η` with `2η|t| ≤ ε` | proved |
| movement, at a simple pinch | `PinchOpenN.opens_at_leaving`, `pinch_eventually_lonely`, `inside_wall_eventually_lonely` | at a simple pinch the subject is lonely under every small change of speeds, on both sides (the leaving neighbour's own opening, or the mirror with roles swapped) | proved |
| one runner at a time | `PathRouteN.segment_lonely`, `move_one_strict`, `move_one_period`; `OneFreeN.lonely_of_one_free_eight`; `OffLatticeN.lonely_eight_of_off_lattice` | the others stay put; the moving runner off the others' lattice is lonely by order seven plus one free reading, the step count written down | proved |
| hand-off to a new neighbour | `SeparationN` (`lonely_of_separation`, `transport`), `PinchTransportN`, `CascadeTransportN` (`HandoffDriftN`, `HandoffResonanceN`: untracked) | a reading in the subject's slot separates at its own exit; local transport statements; "they do not assert global termination" | proved (local) |
| the assembly | `DeformationN.lonely_along_path` (real induction on `[0, 1]`); `PathWindowN.lonelyRunnerAt8_of_window : WindowBound → LonelyRunnerAt8` | the owner's deformation argument, one runner at a time, from the AP to any whole-number arrangement, `EndRunnerN` giving the rest | proved **given `WindowBound`** |
| the one hypothesis | `PathWindowN.WindowBound`; used only in `DeformationN.lonelyAt_of_limit` | on every bounded set of arrangements, a lonely subject is lonely at some instant `≤ T`. "This is where *the isolation cannot escape to infinity* is used, and it is the only place" | **OWED** (registered) |

## Not in Lean
- The multi-pinch case of local stability (E114's route: avoid by a generic path through a rational point, given the window; E280: at every
  multi-pinch read there was a margin window, so no rule at the wall was needed away from tight arrangements; tight arrangements read with simple pinches only, readings ≤ 24).
- The window.

## What is known about the window (so it is not re-derived; E116, E280)
- For a whole-number arrangement the lonely set has period 1, so a window `[0, 1)` is automatic **at** the lattice point.
- The hypothesis is about arrangements **near** a lattice point: nearby instants are lonely at bounded times iff the point itself is lonely (a non-lonely
  lattice point has nearby instants escaping like `1/ε`, with a positive control). So `WindowBound` restricted to the moves is the whole-number statement.
- Between whole-number points the continuum is lonely natively (`OneFreeN`, `OffLatticeN`).
- The step in `lonely_along_path` that needs it is the limit: if `vₙ → v₀` and the subject is lonely at some instant of `vₙ` (unbounded), `v₀` is lonely.
  The owner's current view (E289): the isolation is individual, binding only the neighbours; whether this gives the limit step without a window
  bound is the question; no argument is on disk.

## What "constructing without additions" is
Everything above except the last row is on disk and proved. The construction is `lonelyRunnerAt8_of_window` with `WindowBound` replaced by a
proof of the limit step from the neighbour structure (or a route that never takes the limit). Nothing else is to be added.
