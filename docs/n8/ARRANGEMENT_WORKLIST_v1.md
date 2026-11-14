# Arrangement working list — corpus recovery, v1

Rules: v4, 1–16, 18, 20. 2026-10-20. Owner requested a practical list of types to investigate, starting from the known AP/residue reductions and the arrangement-outcome surveys. The auditor waiver persists.

This list supersedes using E482's six numerical band departures as the main research worklist. Those departures remain correct local scope facts. Here the starting objects are the AP/grid, exact deviations, ordered clusters, actual cascade outcomes and forced handoffs. Rows may overlap; each is a family to investigate and refine, not an assertion of a separate unresolved theorem. The list is meant to be used now and updated as mechanisms join or exclusions remove types.

## 1. Start with the known reductions

| Reduction | What is retained | Use in the worklist |
|---|---|---|
| Physical arrangement and subject | Eight positive distinct speeds; isolate each moving subject separately | Every example retains a physical realization and a named subject |
| Order, common drift, positive scale and physical mirror | Relabelled subject; exact speed differences; normalize by the subject's positive smallest disparity | Remove numerical/label copies before introducing types |
| AP and complete residue grid | Global isolation at the grid instants | Reference arrangements; no new displacement obligation for a pure complete-grid shift |
| Owner's D_max shift | Add independent whole-eight multiples of the grid step; reference readings are unchanged modulo laps | Identify these reference copies; at displaced instants retain each quotient advance |
| Owner's D_min deformation | Exact changes between AP/grid speeds, possibly different grid steps | Follow actual individual displacement and the other carried readings |
| Subject's d_min bound | At R=8*d_min*t=1, clear iff every normalized reading is at least one from a multiple of8 | Remove direct-isolation cases, including closed equality edges |
| Residue plus deviation | Write rho=r+8q+epsilon in a nearest-grid convention | At R=1 only residue0, residue1 with negative deviation, residue7 with positive deviation can be in the way; keep q and epsilon afterwards |
| Settled arithmetic/special cases | Keep each theorem's positivity, integrality, primitivity, divisibility and capture hypotheses | Apply exclusions within each proposed type; divisible-by32 is only the exactly-one-multiple-of8 branch |
| Smaller reading count and group transfer | Repeated magnitudes and at most six distinct readings have existing native support; group deletion requires actual clearance | Reuse lower-order results and exact retained phases without discarding a carried reading |

Sources: [ArrangementShapeN.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ArrangementShapeN.lean>), [DMax.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/DMax.lean>), [GridToGrid.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/GridToGrid.lean>), [NormalForm.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/NormalForm.lean>), [QuotientReduction.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/QuotientReduction.lean>), [ClusterTransferN.lean](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ClusterTransferN.lean>).

Notation matters: the owner's D_max grid direction and the subject's largest disparity d_max are distinct uses in the corpus. Likewise D_min deformation and the subject's smallest disparity d_min are related coordinates, not interchangeable theorem statements. The known grid endpoint identities do not erase deviations along the displacement.

The seven nonempty starting capture-presence profiles are `0`, `1-`, `7+`, `0+1-`, `0+7+`, `1-+7+`, `0+1-+7+`; the eighth profile is already clear. Within a profile retain which readings participate, their multiplicities, ordering, independent quotients, deviations and equality edges.

## 2. Working types, existing support and next investigation

### AP/grid reference types

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| A01 | Exact AP, arbitrary positive scale and common drift | Global grid isolation proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/Grid.lean>) | Use as the reference; remove scale/drift/labels before splitting types |
| A02 | Complete residue grid with independent whole-eight index shifts | D_max invariance proved at grid instants; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/DMax.lean>) | Identify these as the same reference type; retain quotient advance after displacement |
| A03 | Incomplete grid, all subject readings initially clear | Exact d_min attainment criterion proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/NormalForm.lean>) | Classify as direct isolation; keep equality faces, no extra mechanism owed |

### Deformations

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| A04 | One reading moved between consecutive AP/grid speeds, either direction | Exact displacement identities and several native forced continuations proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/GridToGrid.lean>) | Follow the whole old-clear group when the moved reading enters; distinguish each resulting carried packet |
| A05 | Several coupled deviations, including opposing edge crossings | Input and displacement formulas proved; full coupled continuation conditional; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/NormalForm.lean>) | Index by the seven initial capture-presence profiles, then actual forced handoffs |

### Residue interactions

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| A06 | One own-slot sharer with remaining nonzero residue readings | Exactly-one-multiple-of8 not-divisible-by32 branch proved; other cases retain hypotheses; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/OrderEightOneMultipleNativeN.lean>) | Track the remaining divisible-by32 branch and perturbations without imposing it on other types |
| A07 | Several own-slot sharers; mixtures with incoming residue1/7 edge readings | Canonical capture classification proved; many special exclusions available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/OrderEightCasesN.lean>) | Retain multiplicity, quotient and deviation; apply actual residual exclusions before choosing a new subcase |

### Exact boundary cases

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| A08 | Simultaneous entry/exit, setter ties, or singleton isolation | Several exact boundary lemmas and surveyed singleton outcomes; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/taxo_outcome_classes_v1.md>) | Retain closed clearance and actual tie setters; do not require a positive-length isolation interval |

### Cluster placement and spread

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| G01 | Distributed/AP-like readings; no prominent gap | Surveyed; exact AP and initial-clear subcases proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/arrangement_types_v1.py>) | Split initial residue/deviation captures and same-lap versus mixed-lap handoffs |
| G02 | Irregular spread or geometric ladder; no selected compact cluster | Surveyed; scale and largest-gap coordinates available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/dmin_dmax_v2.py>) | Use largest-gap split, then check whether the slow group actually displaces the fast-group landing |
| G03 | Low cluster and one high outlier: reading composition6 / 1 | Fast-single and conditional shift mechanisms available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/FastRunnerN.lean>) | Separate grid-resonant outliers from forced nudge/carry interactions across deviations |
| G04 | High cluster and one low reading:1 / 6 | Surveyed; recent local six-fast-reading packet mechanisms lie here or in refinements; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ResumptionBandsN.lean>) | Extend the shared forced packet resumption; current WindowType upper-clear branch is one concrete frontier |
| G05 | Low cluster with two high readings:5 / 2 | Fast-pair and special common-factor cases available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/FastPairEightN.lean>) | Follow the interaction between the two outlier clocks and the slow cluster, retaining entry history |
| G06 | Two low readings and a high five-reading group:2 / 5 | Surveyed; lower-order group and scale transfer available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ClusterTransferN.lean>) | Test both slow readings at the actual fast-group separation, including successive delays |
| G07 | Three low and four high readings:3 / 4 | Surveyed; factor9 block-size4 obligation conditional; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/Order8SkeletonN.lean>) | AP/grid description within both groups; identify which slow reading forces a changed continuation |
| G08 | Four low and three high readings:4 / 3 | Surveyed; factor9 block-size3 obligation conditional; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/Order8SkeletonN.lean>) | Same group-transfer investigation with three high readings; compare against the inverse physical arrangement |
| G09 | Middle cluster with outliers on both sides:1 / 5 / 1,1 / 4 / 2,2 / 4 / 1,2 / 3 / 2 | Represented in recovered full survey; not a newly proved common mechanism; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/dmin_dmax_v2.out>) | Track both outside groups at the middle group separation; distinguish harmless shifts from successive displacement |
| G10 | Several close pairs or pair-plus-triple structures:2 / 2 / 2 / 1 and rotations of group position | Physical close-pair survey and all ordered composition records available; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/arrangement_types_v1.py>) | Keep the subject role; resolve alternating pair separations and cross-pair carries |
| G11 | Three or more clusters, including nested scales:all15 three-part and all remaining compositions of7 | All64 ordered reading compositions recovered; symbolic scale-transfer formulas proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ClusterTransferN.lean>) | Apply the already retained phase at each group clock; test when a formerly clear group re-enters |
| G12 | Compact translated train versus internally spread fast group | Existing compact-train theorem has explicit width/separation hypotheses; spread trains surveyed; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/TrainCollapseN.lean>) | Use train collapse only with its width and endpoint provenance; treat the spread complement through cascade group transfer |

### Cascade displacement mechanisms

| ID | Type | Existing support / standing | What to work through next |
|---|---|---|---|
| H01 | Same-lap descending sweep | SweepBridge inequalities proved for arbitrary lap; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/SweepBridgeN.lean>) | Derive which ordered packet segment is captured; its slowest captured member sets the separation |
| H02 | Bridge to a faster reading on a higher lap | Lap ordering proved; conditional coupled two-handoff law proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/CoupledReturnN.lean>) | Find which retained earlier captures force return or exclude it |
| H03 | Bridge to a slower reading on a lower lap | Lap ordering proved; specific resumption mechanisms proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/SweepBridgeN.lean>) | Preserve the earlier whole-lap inequalities rather than classifying only the last setter |
| H04 | Immediate carry versus delayed resumption through a third reading | Whole-lap relay proved for every common integer shift; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/DeferredPacketN.lean>) | Establish its input inequalities from the actual new group type; follow its exact exceptions |
| H05 | Changed maximum setter skips a named comparison state | Computed-path transfer and earlier-isolation assembly proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/ClearE5TailN.lean>) | Compose the same verified continuation through opening comparisons, without assuming visits |
| H06 | A previously clear low group displaces the fast group isolation | 3171 exact examples in the recovered taxonomy population; 703 in the older E147 population; [source](</Users/trentpalelei/Desktop/Math Ex/experiments/n8/arrangement_worklist_2026_10_20/recovered.json>) | Start with one slow participant, then two or more; compare carried versus returned readings and derive a type-wide law |
| H07 | The nearest reading becomes in the way: gate crossing and subsequent resumption | 4939 exact late member records recovered; some conditional nearest-move theorems proved; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Spec/FirstGateN.lean>) | Include close-to-unit companions; do not assume the generic move must land exactly at9 without its hypothesis |
| H08 | Mixed independent lap changes and nested packet returns | Recorded; common-lap relay alone does not settle independent shifts; [source](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunnerFresh/Fresh/QuotientReduction.lean>) | Keep each actual quotient advance and derive the coupled capture inequalities |

The recent packet proofs are supporting mechanisms inside this list. They do not define its outer scope: E482's lower/middle/upper branches occupy only a few input compositions and outcome labels. Physical low/high cluster inversion transports the subject; reversing a bare positive-reading list is not that symmetry.

## 3. Enumerate every ordered cluster-size pattern

For seven distinct positive readings, at any SPECIFIED lap K>=1 use the native sweep ratio theta_K=(8K+1)/(8K-1): consecutive ratios below theta_K are in one run; equality or a larger ratio is a cut. Keep K symbolic. These are speed-reading groups, not circular track gaps. For input analysis K is specified independently; for outcome analysis it may also be evaluated at the actual computed landing lap. No input theorem assumes a landing exists.

There are64 ordered compositions of7. All64 occur in the recovered52,000 population. Here is the complete group-size worklist; AP structure, residues/deviations and the relevant handoff distinguish subtypes within a row.

- 1 group (1 patterns): `7`.
- 2 groups (6 patterns): `1|6`, `2|5`, `3|4`, `4|3`, `5|2`, `6|1`.
- 3 groups (15 patterns): `1|1|5`, `1|2|4`, `1|3|3`, `1|4|2`, `1|5|1`, `2|1|4`, `2|2|3`, `2|3|2`, `2|4|1`, `3|1|3`, `3|2|2`, `3|3|1`, `4|1|2`, `4|2|1`, `5|1|1`.
- 4 groups (20 patterns): `1|1|1|4`, `1|1|2|3`, `1|1|3|2`, `1|1|4|1`, `1|2|1|3`, `1|2|2|2`, `1|2|3|1`, `1|3|1|2`, `1|3|2|1`, `1|4|1|1`, `2|1|1|3`, `2|1|2|2`, `2|1|3|1`, `2|2|1|2`, `2|2|2|1`, `2|3|1|1`, `3|1|1|2`, `3|1|2|1`, `3|2|1|1`, `4|1|1|1`.
- 5 groups (15 patterns): `1|1|1|1|3`, `1|1|1|2|2`, `1|1|1|3|1`, `1|1|2|1|2`, `1|1|2|2|1`, `1|1|3|1|1`, `1|2|1|1|2`, `1|2|1|2|1`, `1|2|2|1|1`, `1|3|1|1|1`, `2|1|1|1|2`, `2|1|1|2|1`, `2|1|2|1|1`, `2|2|1|1|1`, `3|1|1|1|1`.
- 6 groups (6 patterns): `1|1|1|1|1|2`, `1|1|1|1|2|1`, `1|1|1|2|1|1`, `1|1|2|1|1|1`, `1|2|1|1|1|1`, `2|1|1|1|1|1`.
- 7 groups (1 patterns): `1|1|1|1|1|1|1`.

Thus low clusters, high clusters, middle clusters and several small clusters are listed explicitly, not left as an unspecified complement. Compact versus internally spread groups, an AP-like internal structure versus irregular spacing, and nested scale changes remain separate annotations to test.

A separate physical control file lists all128 ordered compositions of EIGHT moving speeds, tests every subject (1,024 subject controls), and checks physical mirror and positive affine rescaling exactly. These have72 group-size orbits under physical mirror. The group signatures organize the research; one separated-gap control does not prove an entire signature. [Physical group list](</Users/trentpalelei/Desktop/Math Ex/experiments/n8/arrangement_worklist_2026_10_20/physical_groups.json>).

## 4. Restore the existing outcome survey

The recovered survey has52,000 exact stored arrangements (50,709 distinct), eight original generators. Every stored input was replayed with exact Fractions; its original cascade label, landing, move count, opener, closer and width agree. The generator histories used floats to choose some rational inputs; the recovery uses the stored exact rational inputs and no floating-point computation.

An opener is the actual final setter at the isolation. A closer is the next reading to enter. A strip reading was in the way at the original R=1. Zero width is a valid closed isolation, not a failed output.

| Label | Outcome | Stored arrangements | Current standing |
|---|---|---:|---|
| K0 | No move; positive clearance interval | 14,418 | Realized; cross-index with input types |
| K0z | No move; singleton/zero-width interval | 4,029 | Realized; cross-index with input types |
| K1a | One move; lap-one opener, different closer | 11,258 | Realized; cross-index with input types |
| K1b | One move; higher-lap opener, different closer | 9,067 | Realized; cross-index with input types |
| K1s1 | One move; lap-one opener also closer | 93 | Realized; cross-index with input types |
| K1s2 | One move; higher-lap opener also closer | 341 | Realized; cross-index with input types |
| K1z | One move; singleton isolation | 5 | Realized; cross-index with input types |
| K2a | Several moves; initial-strip opener on lap one | 0 | Excluded by the recorded paper ordering argument; not merely unreached |
| K2b | Several moves; initial-strip opener on a later lap | 2,482 | Realized; cross-index with input types |
| K2c | Several moves; newly involved opener on lap one | 4,198 | Realized; cross-index with input types |
| K2d | Several moves; newly involved opener on a later lap | 5,394 | Realized; cross-index with input types |
| K2s1 | Several moves; lap-one opener also closer | 0 | Excluded by the recorded paper ordering argument; not merely unreached |
| K2s2 | Several moves; higher-lap opener also closer | 621 | Realized; cross-index with input types |
| K2z | Several moves; singleton isolation | 94 | Realized; cross-index with input types |

Sources: [Original14-class survey](</Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/taxo_outcome_classes_v1.md>), [Later L4 correction](</Users/trentpalelei/Desktop/Math Ex/docs/n8/GATE_LEMMAS_v1.md>). The old taxonomy called K2s1 unproved; the later paper argument excludes it, so that obsolete open status is not repeated. No new Lean theorem is asserted for that exclusion.

The independent110,081 stored rational tree members were also fully replayed, including all1,320,740 actual moves. Their four recorded groups are preserved:4,939 nearest-reading move cases,57,861 with a slower closer,47,083 with a faster closer,198 with the opener also the closer. The original float-LP tree is not re-certified by checking one stored exact point per region.

The separate tree-region output has another14 labels: no move in A; opener ranks2..7 in A; opener ranks1..7 in B, where A means landing R<=7 and B means R>=9. These are NOT the same14 labels as the K taxonomy. Keep the tree's float-feasibility caveat. No lonely output lies in(7,9), but generic passage through exactly9 requires its actual hypotheses; the current Lean conditional theorem retains the gap from the unit.

## 5. The actual mechanism map recovered from the survey

Split each input at its largest consecutive disparity ratio and run the fast subset from the SAME original start, on the SAME clock. Compare its computed isolated output with the original full cascade; do not insert a comparison state into the original path.

| Outcome at this split | Survey inputs | Next use |
|---|---:|---|
| Full arrangement isolates at d_min's bound |18,447|Direct-clear baseline; inspect closed edges|
| Full arrangement shares the fast group's computed output |30,382|Prove why the slow group remains clear for the relevant type|
| Slow group displaces that computed fast output further |3,171|Follow the newly carried slow readings and force resumption|

Of the3,171 displaced outputs,1,116 have the fast group already clear at the original bound. In2,055 the fast comparison itself requires moves:1,459 have one slow reading in the way there,596 have several. Only106 of these comparison points are actually visited by the original cascade;1,949 are bypassed. This is exactly where the recent forced-opening/computed-continuation transfer is relevant beyond its narrow numerical bands.

All15 three-cluster compositions occur. At the middle group's computed first isolation in this survey, either the whole arrangement is already isolated or only the higher group is in the way. A lower-group or both-side carry is a candidate to exclude or construct under the retained type, not an obligation assumed to occur. The detailed counts and exact examples, including the first-departure packet and actual original path, are in [placement analysis](</Users/trentpalelei/Desktop/Math Ex/experiments/n8/arrangement_worklist_2026_10_20/placement.json>). This observation is restricted to the studied input grouping at the first-lap sweep cut; it is not asserted for later laps or arbitrary geometrical descriptions.

## 6. Work order

1. Use G04/G06/G09 and H06 to organize the displacement of a computed group isolation by one or several outside readings; derive retained capture inequalities and test whether the same forced resumption law applies.
2. Keep the current upper-clear c branch as one concrete G04/H01/H04 subcase: identify the ordered c/d/e captured segment, its first setter, delayed carriage and any earlier original isolation.
3. Investigate the missing low-side/both-side carry in the three-cluster record through the actual order/capture relations; either explain its exclusion for the retained type or construct its genuine permitted continuation.
4. Carry H07 and A08 separately through thin gate-crossing cases, close-to-unit companions, setter ties and singleton isolations; the broad samplers do not exercise all these populations.
5. Generalize through symbolic whole-lap and grid-shift parameters where the reading identity permits it. Keep independent quotient advance and initial phase when moving to a new group clock.

For every proposed type record its input inequalities/AP data, the actual original packet, why the next displacement is forced, when it rejoins a known mechanism, and its exact exceptions. Mark proved outcomes, tested patterns and candidate exclusions separately. The aim is to join mechanisms across type changes, not accumulate a new family for each numerical setter word.

Recovery artifacts: [28-entry machine-readable worklist](</Users/trentpalelei/Desktop/Math Ex/experiments/n8/arrangement_worklist_2026_10_20/worklist.json>), [complete recovered counts and representatives](</Users/trentpalelei/Desktop/Math Ex/experiments/n8/arrangement_worklist_2026_10_20/recovered.json>).
