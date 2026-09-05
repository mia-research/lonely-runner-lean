# LRC `n=all` Overarching Structure Review Memo (v1)
**Date:** 2026-03-07  
**Scope:** full `n=all` program: proofs, analytics, algebraic reductions, heuristics, and certification artifacts.  
**Objective:** determine whether the remaining open gaps are genuinely separate, or all consequences of one missing discrete-geometric theorem.

## 1) Current state to review against

### Theorem-grade / near-theorem-grade core already in pack
- Irrational branch via equidistribution.
- Rational normalization to finite lattice / dangerous-set problem.
- Case 1 (`no e \equiv 0 mod n`) closure.
- Canonical small-`L` branches (`L=n`, `L=2n`).
- TM/TCP machinery, lower/top-band safety, and several scoped prime/composite sub-closures.
- Exact overlap/moment formulas through low order and strong certified finite-window scans.

### Load-bearing open frontier
Per the current canonical gap notes, the live blockers are:
1. `G4B-COMP-CAP` full closure.
2. Multi-divisible asymptotic theorem-grade closure.
3. Composite-`n` general non-unit regime.
4. Universal `S3` / rational-all-`n` structural closure.

### Review thesis
The open items do not currently look like four unrelated failures. They look like four coordinate projections of one missing object:
- residue coverage on the discrete torus,
- alpha-state transitions,
- dangerous-set occupancy / overlap moments,
- coset-essentiality under non-unit transitions,
- period-summed safe mass outside canonical bands.

The review must test whether these are equivalent formulations of the same theorem.

## 2) Canonical review rule
Every artifact used in this review must be placed in exactly one status bucket:
- `PROVED`
- `PROVED-UNDER-H`
- `CERTIFIED-FINITE-WINDOW`
- `HEURISTIC`
- `DISPROVED/RETIRED`

Hard rule:
- finite-window certification may guide conjecture choice,
- but no certified slice may be treated as proof unless its theorem statement is explicitly scope-locked to that slice.

## 3) Primary review question

> Is there a single structural theorem on the rational/discrete side whose local faces are:
> 1. complementarity run cap,
> 2. non-unit coset essentiality,
> 3. outside-band safe-mass positivity,
> 4. alternating-sum positivity for dangerous sets?

If yes, the project should pivot to that theorem and demote branch-local lemma chasing.
If no, the project should keep the branch decomposition but make the irreducible split explicit.

## 4) Shared objects that every branch must be translated into
The review should force all branch arguments into one common language.

### Core objects
- `alpha = b/L` on `I_div`.
- alpha-state `tau(alpha) = (floor(e alpha))_{e in E_fix}`.
- `U_fix(tau)` and `R_fix(tau)`.
- dangerous sets `D_e subset Z_N` and multiplicity counts `x_r`.
- overlap moments `S_k`.
- obstruction components / runs in `B_div`.
- residue cosets attached to `gcd(e,n) > 1` runners.
- period index `t_div` for divisible runners.

### Translation table to build during review
| Frontier item | Rewrite target | Statistic that must be controlled |
|---|---|---|
| `G4B-COMP-CAP` | obstruction components in alpha-state graph | max obstruction run / guaranteed safe event density |
| multidiv closure | fiber-safe count or direct `x0` | `x0 >= phi(n)` or equivalent deficit bound |
| composite non-unit regime | coset-transition geometry | essential departing residue / forced miss |
| `S3` / rational all-`n` | dangerous-set occupancy | `x0 = N + sum (-1)^k S_k > 0` |
| Xi residual / outside-band mass | period-summed safe fibers | positive lower bound over full `t_div` range |

A branch that cannot be translated into this table is either non-canonical or still underspecified.

## 5) Candidate master structures to test
The review should test exactly these master candidates before inventing new ones.

### Candidate A: universal alternating-sum positivity
Target form:
`x0 = N + sum_{k=1}^{n-1} (-1)^k S_k > 0`.

Question:
- Are complementarity, coset-essentiality, and outside-band safe mass merely local witnesses forcing this positivity?

### Candidate B: complementarity / run-cap master theorem
Target form:
- every obstruction component loses density fast enough that at least `n-1` fibers or residues survive.

Question:
- Can dangerous-set positivity be derived from component-wise run caps plus fiber summation?

### Candidate C: subgroup-opacity / coset-essentiality theorem
Target form:
- non-unit runners cover only subgroup cosets, and any transition that vacates a coset forces a miss unless compensated by a forbidden coincidence.

Question:
- Is this the true local engine behind both `G4B` and multidiv closure?

### Candidate D: period-summed safe-mass theorem
Target form:
- safe mass is positive after summing over the full divisible-runner period range, not just canonical lower/top bands.

Question:
- Is outside-band safe mass the global averaged form of the same complementarity phenomenon?

## 6) Review workstreams

### Workstream A: canon lock
Build a one-page map of what is genuinely closed and what is still only supported.

Deliverable:
- one table with each frontier claim, exact status, scope, and canonical source.

Fail signal:
- same claim appears in two incompatible statuses across pack documents.

### Workstream B: notation compression
Rewrite each open branch in the shared object language from Section 4.

Deliverable:
- one branch-to-object dictionary.

Pass signal:
- at least three open branches reduce to the same controlled quantity.

### Workstream C: invariant mining from certified data
Pull only invariants that recur across branches and already have exact arithmetic support.

Priority invariants to test:
1. z=0 termination or near-termination density.
2. Farey-denominator control for witness times.
3. coset vacating implies sole-cover exposure.
4. outside-band safe mass spread over all interior `t_div` periods.
5. low-order moment positivity forcing higher-order safety in small `n`.

Deliverable:
- short list of invariants promoted to conjecture-level candidate lemmas.

Fail signal:
- an empirical pattern is branch-specific and does not transfer across scopes.

### Workstream D: minimal-counterexample profile
Define the smallest hypothetical bad tuple by:
- `n`,
- `L`,
- `|E_div|`,
- gcd pattern,
- obstruction component structure,
- multiplicity histogram,
- coset-transition anatomy.

Review question:
- what exact profile would a true counterexample need to exhibit simultaneously?

Deliverable:
- one “minimal bad tuple” specification.

Pass signal:
- the specification is incompatible with at least one proved structural fact.

### Workstream E: master-theorem adjudication
Score each candidate A-D against the same criteria:
1. closes at least two current frontier branches,
2. matches all known exact small-`n` identities,
3. explains the certified patterns without new ad hoc machinery,
4. survives the minimal-counterexample profile,
5. yields a publication-grade theorem statement.

Deliverable:
- choose one primary theorem route and one fallback route only.

## 7) Review checklist
1. Confirm that the current “true remaining gaps” list is consistent across the latest gap docs.
2. Mark every promoted theorem or memo as `PROVED`, `PROVED-UNDER-H`, `CERTIFIED-FINITE-WINDOW`, or `HEURISTIC`.
3. Remove any frontier item that is only a bookkeeping duplicate of another one.
4. Rewrite each remaining frontier item in the common language of alpha-states, dangerous sets, cosets, and period sums.
5. Identify the exact controlled quantity for each branch.
6. Test whether that quantity is local, averaged, or inclusion-exclusion form of the same object.
7. Write the minimal bad tuple profile.
8. Test Candidates A-D against that profile.
9. Choose one route to prioritize and explicitly demote the others to support status.
10. Write a final go/no-go note stating whether the missing answer is unified or irreducibly split.

## 8) Questions the review must answer explicitly
1. Is `M1` merely technical housekeeping, or is coincident-boundary handling the true obstruction to a master theorem?
2. Is non-unit coset essentiality the local geometric reason that dangerous-set unions cannot saturate?
3. Is outside-band safe mass just the period-averaged form of complementarity?
4. Can `G4B`, multidiv closure, and universal `S3` all be rephrased as positivity of one occupancy-deficit functional?
5. Are the remaining open branches actually proving positivity of the same quantity at different resolutions: local event, component run, period sum, or full inclusion-exclusion?

## 9) What not to spend review time on
- Re-running broad finite scans without a theorem-shaped question.
- Creating new branch-specific notation when a shared object already exists.
- Treating strong certification as closure.
- Chasing special-case lemmas that do not map to at least one master candidate.

## 10) Expected outputs of this review
The review should end with exactly one of the following conclusions:

### Outcome A: unified theorem exists
At least three frontier gaps are shown to be consequences of one shared discrete-geometric theorem. The program should pivot to proving that theorem directly.

### Outcome B: two irreducible master problems remain
The branches do not collapse fully, but the frontier compresses to two genuinely independent master problems.

### Outcome C: branch split is real
The apparent unification is illusory; the current decomposition is materially correct and should remain the working proof architecture.

## 11) Recommended default expectation
Based on the current proof pack, the most plausible outcome is **Outcome A** or **Outcome B**, not Outcome C.

Reason:
- the remaining blockers are all rational/discrete,
- all of them involve residue coverage instability rather than missing raw computation,
- and the same geometric vocabulary keeps reappearing: dangerous-set occupancy, alpha-state transitions, coset cover, obstruction runs, and full-period safe mass.

Working hypothesis:

> the missing answer for `n=all` is likely one theorem stating that full obstruction is not structurally stable on the discrete residue torus.

Local forms of that instability may appear as:
- a forced miss interval,
- a forced safe event at a z=0 or coset-vacating transition,
- a positive period-summed safe mass,
- or a positive global inclusion-exclusion deficit.
