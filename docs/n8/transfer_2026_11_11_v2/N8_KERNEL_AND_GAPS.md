# Lean kernel and open obligations

The [effective classical reduction](N8_EFFECTIVE_CLASSICAL_REDUCTION.md) gives an explicit Fourier cube
and height bound. It incorporates the existing integer dispatch so the
remaining classical obligation is restricted to bounded primitive sets
that survive the arithmetic rules.

The [classical finite reduction](N8_CLASSICAL_FINITE_REDUCTION.md) closes the qualitative reduction
to finitely many positive integer line representatives. Its remaining
obligation is a closed modular certificate for that finite family.
The results below also study the stronger two-window problem.

This extract starts at the physical eight-runner target and ends at the corrected conditional assembly. It includes the grid and path entry points and the separated-scale tail lemmas. Read the [research brief](N8_RESEARCH_BRIEF.md) for the mathematics and calibrators and the [obligation tests](N8_OBLIGATION_TESTS.md) for the independent exact replay.

## Run it independently

With Elan installed, in `lean_kernel/` run:

```sh
lake update
lake exe cache get
./check_kernel.sh
```

`lake build` is also supported. The project pins Lean 4.29.1 and Mathlib commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The first setup requires access to those dependencies. The checker can instead take one argument, an existing matching Mathlib `LEAN_PATH`. It compiles the included modules in order. The package includes the verification transcript and source hashes. There are no bundled oleans, generated certificate forests, or workspace-relative imports.

### Entry points

| Module in `lean_kernel/Fresh/` | What to reuse |
|---|---|
| `Framework`, `Localisation` | `IsArrangement`, `LonelyRunnerEight`, `IsDmin`, positive disparities, equivalence of a subject witness and a disparity witness, localisation at an opening. |
| `Grid`, `Dmax`, `GridNearFails`, `PathForm` | `gridGlobalIsolation`, AP instants, exact residue shifts, a counterexample to the proposed small-grid neighbourhood cover, ordered interpolation from a grid, and `displacementPath_iff`. The last theorem is an equivalence with the target. |
| `Cascade`, `Dilation`, `CascadeLanding` | Deterministic moves, next opening, no skipping a clear point, finite openings below a witness, first landing, scale and local link laws. |
| `KTaxonomy`, `FilterSkeleton` | Tie-aware opener selection, conditional outcome taxonomy, `allLabelled_iff_allLandBelow17`, `lonelyRunnerEight_of_allLandBelow17`. |
| `CarveExclusionCerts`, `PinchCert`, `BandPinchData` | Fixed clear points, variable windows, closed box refinement, split soundness, exact on-plane pinch and worked data. |
| `FilterAssembly`, `SpineSound`, `SpineTotalData` | Normalized tuple construction, `notCarve_witness`, clear-witness-to-landing bridge, M1 arithmetic, realized ratio conflicts and interval no-go lemmas. This includes the historical assembly so its useful lemmas and the defect checks remain available. |
| `FilterAssemblyPerBox`, `FilterAssemblyPerBoxV2` | The 73 fixed chain tuples, the pin `∃ i, g i = 1`, pinned obligations, and the corrected inside assembly. |
| `BandNoCarve`, `TransferChecks` | First- or second-window outside certificates, normalized band cover, final conditional assembly, and an exact X24 regression. |
| `TailFast`, `TailFastLadder` | Fast-top insertion and the slow-block two-window margin needed to use it. |
| `ExactCellRestoration` | Generic whole-cell failure, width and reflection lemmas from the older transport worktree. |
| `X24Compute`, `X24Sound`, `X24Total`, `X24Checked`, `X24Theorem` | End-to-end X24 cover. Geometric soundness and root coverage are proved in Lean. The finite arithmetic uses one native-decision axiom. |
| `GapPairs` | Two slow cells with disjoint blocking ranges give a clear point in the band windows. |
| `GapSplice` | Two stationary gap cells with overlapping allowed ranges for the remaining reading. |
| `SymbolicWindow` | A fixed-lap window formula, one-reading restoration, and a uniform certificate for the 509 recorded pinch leaves. |
| `FilterShortcuts` | Strict finite interval chains, their specialization to bounded joint carves, and a smaller assembly for positive isolation. |

`FilterSkeleton.lean` is the reduced transfer copy. Its optional shape-catalogue implications depend on the large native catalogue and are omitted. The other existing Lean files are copied from the main working tree, with `ExactCellRestoration` from the 99b0 worktree. The transfer adds `TransferChecks.lean`, `FilterShortcuts.lean`, `SymbolicWindow.lean`, `GapSplice.lean`, and `GapPairs.lean`. The corrected assembly and pinned interfaces are the ones published in commit `0577f64c796ffe2d80c75f8d4f6f7d4c2d373f7a` in the project’s n=8 repository. The kernel is an extract of that development and nearby reusable lemmas.

## The smaller existence route

Use `Fresh.FilterShortcuts.lonelyRunnerEight_of_jointExclusion` if the immediate goal is isolation for every subject. It takes three premises:

1. No joint carve of `[1,15]` on each pinned inside box.
2. No joint carve of `[1,15]` on normalized band inputs.
3. Any positive isolation for every subject in the tail.

With reading 1 pinned, the open gap `(7,9)` is blocked. Lean proves that excluding a cover of `[1,15]` is equivalent to a clear point in the first two windows. The existing exact search directly tests joint exclusion. Its replay can use fixed points, M4 trees or joint constraints wherever convenient. The existence route needs neither a separate M1/M4/chain partition theorem nor the 68/5 distinction. The tail may use any positive time. The original window-specific assembly below still serves the stronger two-window classification goal.

`exitChain_iff_cover` formalizes the strict-chain criterion for a finite family of open intervals. `jointCarve_iff_zoneChain` supplies the finite lap list for the bounded joint test. The next formal work is exact ratio-feasibility exclusion, completeness of the search pruning or an unpruned replay, and the box population. The checked chain criterion supplies the passage between real covers and chains.

## The original window-specific assembly

```lean
theorem Fresh.BandNoCarve.filterAssembly_of_bandData
    (hM4 : Fresh.FilterAssemblyPerBoxV2.M4BoxNoCarvePinned)
    (hChain : Fresh.FilterAssemblyPerBoxV2.ChainBoxSoundPinned)
    (hBand : Fresh.BandNoCarve.BandCertData)
    (hTail : Fresh.FilterAssembly.TailBelow17) :
    Fresh.LonelyRunnerEight
```

The outer split is $\rho_{\max} \le  17$, $17<\rho_{\max} \le  49$, and $\rho_{\max}>49$. The first branch is pinned by `pin_of_cover`. The second is pinned by `bandTuple`. The target quantifies over every moving subject in a positive, injective eight-speed arrangement.

| Obligation | Mathematical content |
|---|---|
| `M4BoxNoCarvePinned` | For a box with a least index 1, outside M1 and outside the 73 chain boxes, every real reading tuple in the faces with some coordinate exactly 1 leaves a clear point in $W_0$. |
| `ChainBoxSoundPinned` | In each of the 73 boxes, any real tuple in the faces with a reading exactly 1 either leaves a clear point in $W_0$, or has a clear point in $W_1$. |
| `BandCertData` | Every normalized tuple with all readings in $[1,49]$, a reading above 17, and a reading equal to 1 admits a fixed-point, window, split, pinch, or second-window gap certificate. |
| `TailBelow17` | For any physical arrangement and subject with a disparity $d>49d_{min}$, the actual cascade from the bound stabilizes in $W_0 \cup  W_1$. |

A theorem providing a clear witness in either of the first two windows yields the required landing via `cascadeLandsBelow17_of_clearPoint`. A proof of arbitrary positive isolation for the tail would suffice for the classical target with a modified top-level assembly.

## What the corrections changed

1. **The historical inside interface has a vacuity.** `JoinFam n ∅` holds for every `n`. The old `CoverData` therefore holds for every box through its empty family. With that family, old `PairwiseSound` demands the entire two-window statement over every box. `coverData_trivial` and `pairwiseSound_iff_universal` demonstrate this in Lean. The current route splits by `M1Cond` and actual table membership, with the remainder subject to the pinned M4 obligation.
2. **M4 needs a pointwise real verdict over a pinned box.** The old M4 condition asked for a single $W_0$ point working throughout a nearest-integer box. The exact fixed-point census reported zero such points for the M4 boxes with that condition. Also, freeing the least reading to range throughout its face can create actual $W_0$ carves. The current interface asks for `NoCarve g` for each admissible tuple `g` and pins at least one reading to 1.
3. **The original outside interface only supplied $W_0$ clearance.** The E827 X24 carve rules out that form of totality. `BandW1` now takes a point in $[9,15]$ and an integer gap for each reading. `clearPoint_of_w1` checks the gaps and composes with the actual cascade. The [X24 two-gap proof](N8_X24_GAP_PAIRS.md) now certifies every input in the slice by an independent integer replay.

## Gap register and acceptance criteria

### 1. Real chains and the M4 replay

Use the checked strict interval-chain criterion for a closed subinterval of the $R$-axis and a finite zone list. Soundness uses all three checks: the first zone contains the left endpoint, each new zone strictly spans the previous exit, and the last zone exits strictly past the right endpoint. Completeness uses the fact that the number of exits still ahead strictly decreases at each move. Bounded laps depend on the box and horizon. Equalities need explicit handling because the zones are open and the clear inequalities are closed.

Replay M4 using the resulting chain enumeration, or a certified subdivision or reachability tree. An exact Farkas contradiction for every feasible branch can justify a box verdict. Separate coverage of children from soundness of a leaf. A leaf can certify an inequality on a clipped child even when the larger box fails it. An independent exact chain search excluded carves in all 12,540. The 2,329 residual trees are the remainder of one compression, while all 12,540 still need a Lean derivation or checked replay. M1 soundness already exists. The [symbolic coalescence audit](N8_SYMBOLIC_COALESCENCE.md) reduces the M1 witnesses to 29 times and gives shorter certificates for 2,172 of the boxes already handled by the exact $C_3$ test. If using the M4 census partition, reproduce coverage or the exact exclusion tests for M1 and the chain table.

### 2. Joint chain boxes

For each real tuple covering $W_0$, realize a $W_0$ chain and its reading inequalities. If $W_1$ also has no clear point, realize a $W_1$ chain for that **same tuple**. Connect those two realized objects to an exhaustive enumeration or a symbolic conflict lemma.

The arithmetic engine is complete for an edge with a realized demand and cap. The top-firing edges in `SpineTotalData` still need a proof that every pair of chains fires one of them. The interval-only route has checked no-go lemmas. In particular, trying to force the demand from the very caps it contradicts makes the hypotheses impossible. Use real chain geometry in the coverage proof. Begin with a one-sided control and one two-sided box before scaling to all 73.

### 3. Outside data and the X24 band

The [X24 two-gap proof](N8_X24_GAP_PAIRS.md) supplies a witness in either window on the closed range $[22.5,25.5]$, including 23 and 25. Its independent verifier checks the coverage and every leaf with integer arithmetic. Lean checks the certificate implication. The portable Lean theorem now regenerates the full cover using its own exact checker and one native-decision axiom. A kernel-reduction-only replay and coverage of the rest of the band remain open.

The [symbolic coalescence audit](N8_SYMBOLIC_COALESCENCE.md) gives one witness, $R=\max(25/\rho_5,89/\rho_7)$, for the 509 recorded pinch leaves, across both signs of $h_3$ and on the plane. Lean checks soundness on three enlarged rectangles. An exact check confirms these contain all 509 recorded leaves. To use them in the full proof, connect the recorded leaves or the three rectangles to the surrounding band cover. The [extension audit](N8_SYMBOLIC_EXTENSION.md) removes the third-reading box restriction on a larger region and gives exact counterexamples to using only fastest-reading endpoints in X24. E847 groups window-certified subdivision boxes into 17 window types. The subdivision coverage and fixed-point bulk remain proof duties.

### 4. Global tail or witness transport

The [four-fast tail reduction](N8_FAST_TAIL_ENTRY.md) gives a cutoff for the sector with three bounded slow readings and four sufficiently fast ones. It applies within the two cascade windows and is proved analytically. A later endpoint proof supplies a numerical formula. Lean now checks a separate non-numerical proof of this sector in [PairedSlow.lean](lean_kernel/Fresh/PairedSlow.lean). See [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md). The [common-rate fast-block proof](N8_COMMON_RATE_FAST_BLOCK.md) handles five or six fast readings with a small relative spread by explicit input inequalities, using a small exact circle-gap calculation. The [mixed fast rates proof](N8_MIXED_FAST_RATES.md) extends the explicit families and reduces escaping obstructions to at least four independent bounded relations. Its mixed speed theorems are now checked in [the Lean kernel](lean_kernel/Fresh/HarmonicRates.lean), with one native computation axiom each. The four-relation argument, including the projected tests, now checks in Lean on buffered intervals $J$ and $2J$. The [harmonic cutoff follow-up](N8_HARMONIC_CUTOFF.md) gives a computable cutoff in the buffered five- and six-fast windows and reduces the surviving types to rational lines and planes. The newer paper proof gives numerical constants, closes the exact five-profile range through 18 and above 424,200, and reduces the six-plane phase problem to five-reading slices. The residual types and other tail regimes still need coverage. See [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md).

Aim first for a lemma with input hypotheses and a witness-bearing conclusion. The 14 outcome labels and the canonical family start with landing or isolation information. A transport or quotient should preserve a witnessed clear point or give a precise replacement in a different window. Verify independent phase lifts, equality faces, repeated disparity values, and changes of setter and return history. Grid quotienting preserves phase at specified reference instants. Preserving the real cascade between those instants requires an additional transport proof.

For the cycle route, derive a uniform bound on the middle readings of a carve or use the clear components to force a uniform obstruction. The recorded near-carve tests and lap-ladder inequality give necessary conditions. They leave the exhaustive continuations and the comparable-top regime open. For the separated-scale route, `NStarK 5` is available outside the extract. `NStarAtMostOne` is the full six-reading two-window margin at threshold $1/7$; ordinary order seven alone provides no such window restriction.

**A limitation of the proposed arbitrary-interval block-gap route [Proof].** There is no uniform $g_5$ such that every interval longer than $g_5/b_{\min}$ contains a simultaneous $1/8$-clear point for every set of five positive speeds. For any $L>0$, take $T>32L$ and five distinct speeds
$$b_i = 1 + \frac{i}{5T},\qquad 0\le i\le4.$$
For $t=T+u$, $0\le u\le L$, the phase $b_it$ equals $t+i/5+iu/(5T)$. For each $t$ one of the five evenly spaced phases $t+i/5$ lies within $1/10$ of an integer. Its perturbation is at most $4L/(5T)<1/40$, so that speed has distance strictly below $1/8$. Thus the whole interval $[T,T+L]$ is covered by forbidden zones, with $b_{min}=1$. Appending a sixth distinct speed retains the cover. This rules out the proposed unrestricted estimate in E844 for five and six speeds. A bound on a constrained slow-block window with controlled phases, or on the actual clear components inside $W_0$, remains a different question.

## Reuse boundaries

- The no-collision hypothesis preserves ordering along the grid interpolation. Use `displacementPath_iff` as a dictionary. To close a path proof, supply bounded relocation or another certified next witness at zero-margin transitions.
- Positive-time certificate localisation and finite openings apply after a witness or horizon has been supplied. Distinguish the number of possible laps for a fixed bounded tuple from a bound valid for all tuples.
- The shape-catalogue route needs an implication from arbitrary input to explicit shapes or a treatment of the remainder. The older `FilterShapeBridge` is a proposed equivalence. Both full directions with the specified landing window remain open.
- The older residue and integer transfer routes are valid alternatives where their hypotheses are proved. The residual arithmetic set is still infinite. The next model can use their results as targeted sublemmas if those routes intersect the actual cascade obstruction.

The [Lean finite relation reduction](lean_kernel/FINITE_RELATIONS.md) is unconditional for arbitrary real arrangements. A possible failure of unrestricted isolation must lie on one of finitely many proper relation hyperplanes. For the two-window property the residual cases lie in explicitly bounded neighborhoods of proper kernels. Four bounded independent rows give the line and plane types, and Lean now forces them in the buffered fast block when neither interval clears. The linked reduction notes state the remaining scope and coverage obligations.

The buffered reduction now applies directly to the five- and six-fast
cascade sectors via `Fresh.FiniteRelations.normalized_fast_dispatch`.
The remaining outcomes are a bounded neighborhood of a finite family
of line and plane kernels, or a sector with three bounded slow
readings. `Fresh.FiniteRelations.harmonic_five_finite` proves a separate
existential bound on primitive five-reading profiles that fail the
shifted-circle test; it does not evaluate the cutoff 424,200.

The newer `normalized_four_fast_dispatch` in
[PairedSlow.lean](lean_kernel/Fresh/PairedSlow.lean) closes the
four-fast branch using three slow readings and the buffered rank
argument. The residual sector has **four** bounded smallest
readings; the finite five/six-fast types and sectors with fewer
fast readings still require coverage.

The newest dispatch is `normalized_three_fast_dispatch` in
[ThreeFast.lean](lean_kernel/Fresh/ThreeFast.lean). It closes the
three-fast branch and leaves five bounded smallest readings if
neither a window witness nor a finite five/six-fast type applies.
The two-fast and one-fast sectors need strict slow-clear windows
for five and six slow readings, respectively. The general append theorem
proves that pointwise strict clearance there already suffices;
a separate uniform margin theorem is unnecessary.


For classical positive-time isolation, rescaling through the buffered
rank theorem now reduces all inputs to a strict witness or a finite
family of exact three-dimensional kernels. For the two-window route,
the fixed-prefix strict append equivalence identifies a genuine
obstruction at touch-only prefixes, and the five-slow question is now
bounded qualitatively. See [the proof route audit](N8_PROOF_ROUTE_AUDIT.md).
