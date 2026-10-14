# Order five: four corrections, and where the certificate can be closed

2026-09-21, version 1. Written after reading `docs/n8/MANUSCRIPT_v19.md` §1.1–1.3, §8.1–8.2.
Corrects `SMALL_ORDER_DOORS_v3.md`, `N5_LEAN_STATUS_v1.md`, `OVERLAP_BOUND_v1.md` and
`N5_CLOSED_COMMENSURABLE_v1.md`, all written without it.

---

## 1. Four corrections

### 1.1 I was incorrectly requiring coverage  `[CORRECTED]`

`OVERLAP_BOUND_v1.md` set out to prove *the union of the blocked sets stays below `e`*. §8.2 of
the manuscript already settles what that route is worth:

> *"`n > 2k` is `2k/n < 1`, that is `k·(2/n) < 1`, which says the `k` in-the-way arcs, each of
> width `2/n`, cannot cover the circle. At `n = 8` with `k = 7` their total width is `7/4`, so
> they cover it 1.75 times over, which is why this row reaches no order on the diagonal. **The
> proof arrives at the covering threshold by a route that uses no covering.**"*

My blocking-capacity measurements (1.50 at `n = 5`, 1.75 at `n = 8`) are that coincidence,
re-derived. The covering route reaches `n > 2k` and no further, and the live proof
(`ManyDifferences.stops_when_twice_card_lt`) uses a **potential** `Ψ`, not covering. The
"overlap bound" was the wrong target.

### 1.2 Requiring the *largest* flank was a self-imposed strengthening  `[CORRECTED]`

`lonely_iff_exists_flank` — any flank — is already proved equivalent to loneliness. Demanding
the **largest** flank (`DoorLargestFlank`) is strictly more than the framework needs, and it is
`[REFUTED]` at 6, 7, 8. Chasing it at `n = 5` was chasing a strengthening, not the obligation.

### 1.3 The import broke real speeds  `[CORRECTED]`

`N5_CLOSED_COMMENSURABLE_v1.md` reported `theorem121_LRC_real` as the gap for order five over
the reals. **That gap is an artefact of the import, not a property of the framework.** §1.1:

> *"**Real speeds throughout.** Every object the results use — the band identity, drift
> intervals, the step between scales, flank openings — is stated and proved over the reals."*

`LRC.SpecN.doors_agree` carries no rationality hypothesis at any order. `intLRC` is
integer-only, so importing it introduced the restriction and then the hole. The gcd-clearing,
sorting and padding in `FiveInt.lean` are likewise shape-fixes for `intLRC`'s signature; the
framework takes an arbitrary positive **real** difference set and needs none of them.

**Consequence for `LRC/Spec/FiveInt.lean`:** it re-expresses `intLRC_five`, which already proves
order five in this tree by other means, and it is strictly weaker than the framework's own
result (§2). It is not framework work. **Recommend withdrawing it**; left in place pending the
owner's decision, since deleting outside `archive/` needs confirmation.

### 1.4 My proved flank region is subsumed  `[CORRECTED]`

`clear_at_last_opening` settles ratio `d_max ≤ 4·d_min`. The certificate below settles ratio
`≤ 26`. The first sits **strictly inside** the second, so the Lean flank work adds nothing to
order-five closure. What does survive from it is listed in §4.

---

## 2. What is actually proved at order five

From §8.2, which I had not read:

> **`sup R = 31/9` for every arrangement of ratio `d_max/d_min ≤ 26`.** `[PROVED — exhaustive
> certificate over words `(setter, lap)`, each bounded by an exact rational linear program]`

Reproduced from the deposited output (`experiments/n8/order5_certificate_S26_v3.out`): 280,785
words tested, 5,721 realisable, sup `R = 31/9 = 3.444… < 4` at the word
`(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)`, margin `τ = 132/4165`. Since `R < 4` is sufficient for
Existence, **order five holds for every arrangement of ratio at most 26** — real speeds included,
with no commensurability hypothesis.

Order five with four differences remains `[OPEN]` in general; unbounded ratio is the open part.

---

## 3. The new finding: the enumeration looks truncatable at lap 6

`R = (5Q+1)/u`, where `Q` is the **last setter's lap** and `u` its reading in units of `d_min`.
Instrumenting the certificate's own LP by the word's **maximum lap**
(`experiments/nN/order5_lapstruct_v1.{py,out}`, `S = 18`, lap bound `L = 14`):

| max lap | 1 | 2 | 3 | 4 | 5 | **6** | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| best sup `R` | 3.3750 | 3.3611 | 3.2593 | 3.0395 | 3.3611 | **3.4444** | 3.1429 | 2.7500 | 2.8750 | 2.8622 |

The maximum sits at lap 6 and falls away above it, although the lap bound `L` grows with `S`
(to 20 at `S = 26`). The extremal word has used only laps `≤ 6` at **every** ratio bound from
`S = 10` to `S = 26`, with the margin fixed at `132/4165` from `S = 14`.

**The mechanism** (`order5_growth_v1.out`). `R ≥ 4` requires `u ≤ (5Q+1)/4`. The attained `u`
grows about `1.7·Q` while that threshold grows `1.25·Q`, so the slack widens:

| `Q` | 1 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|
| attained `u` | 1.778 | 6.909 | 9.000 | 14.909 | 17.818 |
| needed `u ≥` | 1.500 | 5.250 | 7.750 | 10.250 | 12.750 |
| slack | +0.278 | +1.659 | +1.250 | +4.659 | +5.068 |

The tightest points are small `Q`, which the certificate already enumerates exhaustively.

**The target this suggests.** Prove `u ≥ (5Q+1)/4` for every realisable word with last-setter lap
`Q ≥ 7`. That truncates the enumeration at lap 6, making it independent of `S`, and the existing
exhaustive check at any `S ≥ 10` then closes **unbounded ratio** — i.e. order five, in the
framework, over the reals, with no import.

`[EMPIRICAL — the lap table and the growth rates; NOT a proof.]` The bound has not been proved,
and the table is read at `S = 18` (a run at `S = 26` is in progress).

---

## 4. What survives from the earlier work

| item | status |
|---|---|
| `LRC/Spec/DoorsN.lean` — the whole `n = 8` Spec layer at every `n`, 105/105 axiom-clean | **stands**; new, and independent of all of the above |
| the clearance law `f(3)=5, f(4)=8, f(5)=11, f(6)=13` and the blocker-count explanation of 5 vs 6 | **stands** as measurement |
| `exists_lonely_flankOpening_of_gap` — a window longer than `1/e` contains a flank opening | **stands**; general, and orthogonal to `R` |
| `four_clears_small` (`decide`, axiom-free) and the bridge `lonely_of_flankWorks` | **stands** as machinery |
| `clear_at_last_opening` | stands, but **subsumed** for order five (§1.4) |
| the overlap-bound programme | **withdrawn** (§1.1) |
| `FiveInt.lean` | **recommend withdrawal** (§1.3) |

---

## 5. Grades

| claim | grade |
|---|---|
| order five holds for ratio `≤ 26` | `[PROVED — manuscript §8.2 certificate; output reproduced]` |
| order five with four differences, general ratio | `[OPEN — manuscript §8.2]` |
| best sup `R` peaks at max lap 6 and falls away | `[EMPIRICAL — S = 18 LP instrumentation]` |
| `u ≥ (5Q+1)/4` for `Q ≥ 7` | **not proved** — the truncation target |
| the covering route reaches `n > 2k` and no further | `[PROVED — manuscript §8.2; my capacity figures agree]` |
| the real-speeds gap was an import artefact | `[VERIFIED — `doors_agree` carries no rationality hypothesis]` |
