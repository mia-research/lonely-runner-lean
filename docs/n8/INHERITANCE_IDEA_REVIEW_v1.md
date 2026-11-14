# E485 — exact review of the supplied inheritance and scale-transfer ideas

Rules v4: 1–16,18. Owner requests testing the ideas and retaining useful content. This is an addendum to the unchanged [arrangement worklist](ARRANGEMENT_WORKLIST_v1.md), not a replacement proof programme. Auditor waiver retained. [L] means Lean theorem; [T] means exact finite test; [OWED] means no proof supplied.

## Useful relationships retained

- **[L] Corrected first-band scale transfer.** At an actual selected block opening `t=(8k+1)/(8e)`, `e>0`, a core with `m≤c≤M` is clear whenever `e≤(8k+1)m` and `(8k+1)M≤7e`. These two relations put every core reading in its first closed clear band. `OpeningCompatibility.core_clear_at_opening` proves this implication; `first_band_at_opening_iff` proves the exact individual equivalence. Later core laps require their own whole-lap inequalities. Scale separation alone does not derive the two relations or force the cascade to select this opening.
- **[L] The first-fast-lap sign is reversed in the proposal.** If `0<c` and `9c<e`, then at `9/(8e)` the c-reading lies strictly between 0 and1/8 and is captured. `first_fast_opening_in_way` proves this. At equality `e=9c`, c is exactly clear on the boundary; smaller core readings can still be captured. Concrete kernel control: e18,c1 is captured, c2 is exactly clear.
- **[P algebra] Exact residue test retained.** For integer e>0 and x=8c, at the e-opening `(8j+1)/(8e)`, put `r=c(8j+1) mod e`. The added reading is clear exactly when `e≤8r≤7e`. Discrete phases, additional powers of2, sample success, and mean circular distance do not imply these inequalities. The phase increment as j advances is `8c/e`, not generally `4/e` for x32k.
- **[L] Keep survival inside a core-clear cell separate from winning on its boundary.** An added reading can force isolation inside that cell at its own opening, even if every core-flank opening is captured. That is precisely the distinction needed when applying `Fresh.SecondStage.OneMultipleCellExists`.

## Tested inheritance claims and actual displacement

- **[L, all K≥1]** Let `D={1,2,3,4,5,6}`, `x=480K`, and `S=D∪{x}`. All D-readings are clear at1/8; only x is captured. Its forced opening is `t*=(x+1)/(8x)`, strictly inside `(1/8,7/48)`. The original cascade moves once to t* and is fixed there, with every reading clear. The physical speeds `[1,2,3,4,5,6,7,1+x]` are positive and distinct, subject speed1.
- **[L, all laps]** For each e in D and every natural j, `x(8j+1)/(8e)=60K(8j+1)/e` is an integer because each e divides60. Thus x captures EVERY core-flank opening, despite `32|x`. This disproves the proposed universal core-flank/power-of-two inheritance mechanism. It does not disprove isolation or surviving-cell inheritance.
- **[T / catalogue reuse]** All six recorded K-controls and the smaller counterexample below classify as **K1s2**: one move, a higher-lap opener which is also the next closer. This reuses the known fast-nudge outcome; no new unresolved type or progress on the residual is claimed.
- **[L actual path; T complete flank check]** For `S={2,3,4,5,6,7,32}`, the original cascade moves from1/16 to17/256 and fixes there. Every core flank fails throughout the full integer period; all successful disparity-flank openings in that period belong to32. The integer-period phase identity extends the check to every natural lap.
- **[T scope]** That small example fails several recorded residual exclusions. The infinite480K family also lies in already settled fast-single cases. Neither is advertised as an `EightResidual` counterexample.

## Complete bounded tests and retained residual candidate

All sets below have seven distinct positive integer disparities from1..32. Every e in the set and every j<e is evaluated by exact integer modular comparisons, a complete integer period. The one-multiple population fixes its multiple to32. Each full set has a clear opening; the stronger claim that some non-multiple core flank wins fails in every profile.

| Multiples / non-multiples | Complete tested inputs | Core-flank inheritance counterexample |
|---|---:|---|
|1 /6, multiple32|376,740|2,3,4,5,6,7,32|
|2 /5|589,680|4,6,8,10,12,14,32|
|3 /4|81,900|1,2,3,8,9,16,24|
|4 /3|3,276|1,2,3,8,16,24,32|

- **[T 1,051,596 /1,051,596]** Complete bounded population, not sampled percentages or a universal theorem. The second displayed example has gcd2; it is not primitive. All four displayed examples fail some recorded residual exclusions, as saved explicitly in `scope.json`.
- **[T genuine recorded residual controls]** Two prior primitive residual diagnostic controls, retaining every recorded field, have non-multiple cores clear at1/8 while all added multiples are captured there. Their complete original cascades are retained. This refutes automatic preservation of that computed core instant within the retained diagnostic scope; it does not exclude another successful core opening. Recorded Python fields are not a new Lean `EightResidual` membership proof.
- **[OWED candidate retained]** A narrower statement that every remaining `EightResidual` input admits a successful non-multiple core flank has not been disproved by these examples and has not been proved here. Keep its complete residual hypotheses. No shape is removed from the worklist by the supplied inheritance argument. Lower-order subsystem isolation still needs a simultaneous compatibility/displacement relationship for outside readings.

## Status corrections and useful hygiene

| Supplied item | Checked standing / action retained |
|---|---|
|`lonelyRunnerAt8_iff_residual`|Threshold1/8 at some positive time, not necessarily time1/8. Every multiple8 is captured at time1/8.|
|`OneMultipleCellExists`|Still OWED in `Fresh.SecondStage`; its existing equivalence is proved. A cell survives if the added reading's displacement from the cell start stays within its end. The supplied “CRT overconstraint” is a candidate explanation, not a proved mechanism.|
|One-multiple residue branch|`¬32∣x` is already proved in `OrderEightOneMultipleNativeN`; `32∣x` is the remaining branch there. The supplied final table reverses this standing.|
|Five skeleton premises and `WideStep8`|Alternative sufficient proof routes; do not combine their hypotheses into a new compulsory task list. Numerical win rates do not discharge them.|
|`BandCover.band_lonely`|Existing band result uses an exact wall-cut certificate route. Keep its provenance distinct from a newly derived native displacement law.|
|`mapped_late_bound`|Conditional upper bound `89/b≤26433/2209<12` from `b>0,47≤9c,47c≤33b`; not an unconditional exact global supremum. Derive its capture hypotheses before reuse.|
|`ZoneLink.InZone`|Prop definition found, registration absent from the inspected foreign gate. Recorded as hygiene owed; no gate changed and no fresh gate failure claimed.|
|`FiveDisparitiesLowQuotient`|OWED tag remains at its definition; `Fresh.FiveLow.fiveDisparitiesLowQuotient` already proves it. Ledger discrepancy, not a new mathematical hole; old source preserved.|
|Exact rational `(e,k,t)` triples|Useful individual-input certificates. Replacing a float witness by a rational point does not certify its entire LP region or a partition. The earlier110,081 replay likewise certifies stored points.|
|Quoted sandbox files/rates|`/workspace/scratch` is absent here. The quoted2.81m totals and supplied percentages remain unverified; independent exact evidence is saved instead.|

## Where this helps the arrangement programme

E485 adds the two-sided core-band compatibility lemma to G06/G09 scale handoffs, and links the misleading power-of-two/core-boundary intuition back to the existing K1s2 displacement mechanism. For the unresolved allowed type, retain original packet, whole-lap readings and earlier-isolation alternatives; derive compatibility at the actual carried opening, or follow the carried-in readings using the existing continuation laws. The residue signature alone supplies no clearance implication.

Sources and checks: [new Lean statements](../../LonelyRunner/LonelyRunner/LRC/Spec/OpeningCompatibilityN.lean), [kernel/axiom audit](../../LonelyRunner/experiments/nN/opening_compatibility_2026_10_20/audit.lean), [audit manifest](../../LonelyRunner/experiments/nN/opening_compatibility_2026_10_20/manifest.json), [complete exact tests](../../experiments/n8/inheritance_review_2026_10_20/tests.json), [residual scope](../../experiments/n8/inheritance_review_2026_10_20/scope.json), [outcome reuse](../../experiments/n8/inheritance_review_2026_10_20/outcome_reuse.json). Twelve public theorems and45 theorem/helper axiom/dependency audits pass; only standard Lean axioms occur. All19 preceding proof manifests and the frozen corpus-worklist fingerprints are preserved. No n8 closure, commit or push claimed.
