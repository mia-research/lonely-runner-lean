# A door over `ℝ`, and two impositions removed

Lean: `experiments/n8/RealDoor_v1.lean` (5 theorems, axiom-clean, built on `Spec/Doors.lean`).
Script: `real_door_reach_v1.py`.

---

## 1. Two requirements that were mine, not the framework's

**`intLRC 8` is not a requirement.** I reached for it because I had already committed to the
integer route. The obligation never mentions integers.

**Nor is the real→integer bridge.** `LEAN_OBLIGATION_AUDIT_v1` §3(b) recorded "there is no bridge
from integer results to the real target" as a gap. It is only a gap *if one goes via integers*.
The doors do not.

Every object in the obligation is real-valued:

```lean
flankOpening (n : ℕ) (e : ℝ) (k : ℕ) : ℝ := ((k:ℝ) + (n:ℝ)⁻¹) / e
sep (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : ℝ := v i * t - v k * t
circDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)
LonelyAt v k t := ∀ i ≠ k, (8:ℝ)⁻¹ ≤ circDist (sep v k i t)
```

So a door can be closed directly for real arrangements, and the commensurable case split, the
candidate lattice, `intLRC 8` and the bridge are all **strategy**, not obligation.

## 2. The first-lap argument transfers to `ℝ` outright — **[PROVED]**

At the opening `t = (j + 1/8)/e` the separation of runner `i` is `(v i − v k)·t`, and
`circDist x ≥ 1/8` is just `1/8 ≤ |x| ≤ 7/8` — no modular reduction, no lattice.

* `RealDoor.circDist_ge_of_mem` — `1/8 ≤ |x| ≤ 7/8 ⟹ circDist x ≥ 1/8`, both signs.
* `RealDoor.lonelyAt_of_window` — separations in that band give `LonelyAt`.
* `RealDoor.doorFlank_of_window` — hence **`DoorFlank` itself**.
* `RealDoor.lonelyForSubject_of_window` — hence the obligation for that subject.
* `RealDoor.lonelyRunnerAt8_of_window` — **hence `LonelyRunnerAt8`**, conditional only on the
  window being findable for every arrangement and subject.

This is the first door-level result in the tree stated and proved over `ℝ`. It needs no
commensurability, no candidate normal form, and no bridge.

## 3. What it reaches, measured — **[EMPIRICAL]**

Over real arrangements (4,000 each), fraction of **subjects** for which a window exists:

| speed distribution | subjects covered | arrangements with **all 8** |
|---|---|---|
| uniform `[0,1)` | 24.52% | **0.00%** |
| uniform `[0,10)` | 24.83% | **0.00%** |
| log-uniform `1..1000` | 20.77% | **0.00%** |

The window forces a ratio-7 spread (`max|d| ≤ 7·min|d|`), which holds for 29.02% / 23.88% of
subjects — so the door is nearly as wide as that condition allows, and no wider.

**It does not close the target.** `LonelyRunnerAt8` needs every subject of every arrangement, and
no sampled arrangement had all eight covered. This is a fragment, stated as one.

## 4. The state, without the layers

The Lean hurdle is: **prove one door for all real arrangements.** `Spec/` and `Cascade/` have zero
`sorry`; the infrastructure is finished and no door is proved.

* `RealDoor` covers subjects whose differences span a ratio-7 window — about a quarter.
* `CardSix` covers subjects whose differences collapse to `≤ 6` distinct values, via `intLRC_seven`
  — but that one *is* stated for integer speeds, so it needs the bridge that `RealDoor` avoids.
* Everything else in the arc — `LastClass`, `MinusSeven`, `Openings`, `FirstLap`, `CoverCount`,
  `DivisorOrder6`, `SmallModuli`, `CanonicalCandidate`, `WindowGeometry`, `Derestricted`,
  `ReducedOpen`, `FourResidues`, `OddSublattice`, `IsolatingPair`, `GapThreshold` — lives inside
  the candidate normal form over `ℤ`, which §1 shows is a layer I added.

The productive reading: `RealDoor` shows the framework's own objects reach the target directly.
The question worth asking of each remaining `ℤ`-result is whether it has a real counterpart, as
the first-lap argument did.

Existence at order 8 remains open.
