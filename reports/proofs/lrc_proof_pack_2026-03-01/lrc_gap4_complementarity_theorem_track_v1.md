# Gap 4 Theorem-Track Block: G4.A-G4.C (Composite `n>=6`, `L>2n`)
**Date:** 2026-03-04  
**Scope:** Universal S3 closure track for the remaining composite regime (`n>=6`, Case-2, `L>2n`).  
**Intent:** Promote the current empirical complementarity signal to a theorem-track chain with explicit proof obligations.

---

## 0. Scope and Notation

Let `E` be a Case-2 tuple with `|E|=n-1`, `E_div != emptyset`, `gcd(E)=1`, composite `n>=6`, and `L>2n`.

For each fiber `b in B_div`, define:

- `B_e(b)`: bad-a set contributed by runner `e` (inverse-free congruence definition).
- `U(b) := union_{e in E_non} B_e(b)`.
- `D(b) := n - |U(b)|` (deficit).
- `b` is obstructed iff `D(b)=0`.
- `O := { b in B_div : D(b)=0 }` (obstruction set).

Then `B_safe(B_div) = |B_div| - |O|`.

Write `g_e := gcd(e,n)` for each non-divisible runner `e`.

---

## 1. Lemma G4.A (Event-transition Lipschitz bound on `|U|`)  [PROVED]

### Statement

Let `b,b+1 in B_div` be adjacent fibers in the same event path component.  
Let `J(b)` be runners whose local state changes from `b` to `b+1` (i.e. some of `t_e,z_e` changes).

Then

`||U(b+1)| - |U(b)|| <= 4 * sum_{e in J(b)} g_e`.    `(G4.A.1)`

Equivalently,

`|D(b+1) - D(b)| <= 4 * sum_{e in J(b)} g_e`.        `(G4.A.2)`

### Proof

For each changed runner `e in J(b)`, by the composite bad-set structure (`G3.A`), each `B_e(.)` is a union of at most two cosets of size `g_e`; hence

`|B_e(b+1) Delta B_e(b)| <= 4 g_e`.

Unchanged runners contribute zero symmetric difference. Therefore

`|U(b+1) Delta U(b)| <= sum_{e in J(b)} |B_e(b+1) Delta B_e(b)| <= 4 sum_{e in J(b)} g_e`.

Since `||A|-|B|| <= |A Delta B|` for finite sets, `(G4.A.1)` follows; `(G4.A.2)` is immediate from `D=n-|U|`. QED.

### Use

`G4.A` supplies the quantitative "no explosive one-step jump" control needed in any obstruction-run argument.

---

## 2. Lemma G4.B (Complementarity obstruction-run cap)  [TARGET]

### Target statement

In the scope above, prove:

1. `O` is a union of at most one contiguous run on each `B_div` component.  
2. For each component `C`,

`max_obstr_run(C) <= |C| - n`.    `(G4.B.1)`

Consequently,

`|O cap C| <= |C| - n`.           `(G4.B.2)`

### Why this is the right target

If `(G4.B.2)` holds on every component, summing components gives

`|O| <= |B_div| - n`,

which is exactly the empirical complementarity law observed in the diagnostic.

### Proof obligations (explicit)

- **B.Obs-1 (contiguity/one-block):** show obstruction cannot fracture into many disjoint long runs once event transitions are accounted for.
- **B.Obs-2 (length cap):** combine event-transition control (`G4.A`) with endpoint/transition constraints to force at least `n` non-obstructed fibers per component.
- **B.Obs-3 (component summation):** transfer per-component cap to global `|O|`.

### Current evidence status

- Empirical support: zero violations in the 88,626-tuple diagnostic pack (`max_obstr_run < (n-1)|B_div|/n`, and equivalently no violation of the practical complementarity envelope used in Gap-4 notes).
- Analytic status: open target (not yet proved).

---

## 3. Theorem G4.C (S3 from complementarity cap)  [CONDITIONAL DERIVATION]

### Statement

Assume `G4.B` (i.e. `|O| <= |B_div| - n`). Then

`B_safe(B_div) = |B_div| - |O| >= n >= n-1`.    `(G4.C.1)`

Hence S3 holds in the full `n>=6`, `L>2n` composite branch.

### Proof

Direct from `B_safe=|B_div|-|O|` and the assumed cap. QED.

---

## 4. Integration into canonical Gap-4 program

This block gives the clean theorem-track split:

- `G4.A`: proved quantitative transition lemma (load-bearing and reusable).
- `G4.B`: single remaining structural theorem target (complementarity run cap).
- `G4.C`: immediate closure corollary once `G4.B` is established.

So Gap-4 closure in the remaining regime is reduced to one explicit combinatorial theorem (`G4.B`).

---

## 5. Canonical status label (recommended)

Use:

- `G4.A`: `PROVED`
- `G4.B`: `OPEN-TARGET`
- `G4.C`: `CONDITIONAL`

This keeps tracker language honest while preserving forward momentum.


---

## 6. Empirical Addendum: G4B Run-Cap Stress (`G4B-Emp-v1`, 2026-03-05)

This section records the current **empirical** cap evidence in theorem-track format without promoting it to proof.

### 6.1 Empirical Lemma Statement (not yet analytic)

In tested near-complete multi-divisible scope with

- `E_div = {n,2n}`,
- `E_fix subset {1,...,n-1}`, `|E_fix|=n-3`,
- free runner `M` with `gcd(M,n)=1`,

the obstruction-run length measured in `t_M`-blocks (where `t_M=floor(b/L0)`) satisfies:

- `max_run_t <= 2` in all tested cases.

### 6.2 Test Coverage

Sweeps completed:

- `n=12`: 550 `(E_fix,M)` cases, `max_run_t=2`
- `n=15`: 1001 `(E_fix,M)` cases, `max_run_t=2`
- `n=20`: 1881 `(E_fix,M)` cases, `max_run_t=2`

Additional observations:

- Minimum safe ratio across tested miss-lattice points remained positive (`~0.10` lower tail in these sweeps).
- Large `b`-runs can occur due to block size (`L0`) even when `t`-run remains small; therefore the cap should be stated on `t`-runs, not raw `b` length.

### 6.3 Scope and Exclusions

Included:

1. Exact miss-interval construction from `E_fix union E_div` on rational partition.
2. Exact block overlay for free runner obstruction (`bad_set(M,t_M,n)`).
3. Full template sweeps for listed `n` values and declared `M` sets.

Excluded:

1. General `E_div` choices beyond `{n,2n}`.
2. Full `n=all` theorem claim.
3. Analytic derivation of `max_run_t <= 2`.

### 6.4 Script-Ready Theorem Checklist for `G4B`

Use these checklist IDs for all future packs.

- `G4BE.C1` Miss-interval constructor correctness:
  - build `Miss_r` by exact Farey partition and exact `bad_set` algebra.
  - fail on any float-only approximation.
- `G4BE.C2` Block overlay correctness:
  - define `t_M=floor(b/L0)` and test obstruction by `r in bad_set(M,t_M,n)`.
  - fail if using `b/L` state directly for free runner.
- `G4BE.C3` Run metric separation:
  - report both `max_run_b` and `max_run_t`.
  - fail if only `b`-run is reported.
- `G4BE.C4` Cap check:
  - verify `max_run_t <= 2` on all tested tuples.
  - fail with first witness tuple dump.
- `G4BE.C5` Safe-mass sanity:
  - compute `safe_ratio = safe_pts / total_miss_pts`.
  - pass iff `safe_ratio > 0` on all tested tuples.
- `G4BE.C6` Sweep completeness:
  - for each `n`, enumerate all `E_fix` in declared scope and all declared coprime `M`.
  - fail if counts do not match expected totals.
- `G4BE.C7` Artifact output:
  - emit rows CSV with tuple key and metrics, plus summary markdown.
  - include date, script hash, and scope line.

### 6.5 Recommended Tracker Language

- Keep `G4B-COMP-CAP` as `OPEN-TARGET`.
- Add evidence note: "Empirical run-cap pack (`max_run_t<=2`) verified in scope `E_div={n,2n}`, `n in {12,15,20}` sweeps."



---

## 7. Session 9 Sub-Case Status Split (2026-03-05)

This section records the current theorem-grade split implied by Session 9 diagnostics and partial analytic closure.

### 7.1 New Analytic Sub-Lemma (at_B_div_end)

**Lemma (at_B_div_end CB bound):**
In Case-2 with a unit runner `e_u` (`gcd(e_u,n)=1`) and `n|L`, `e_u|L`,

- `lcm(n,e_u)=n e_u | L`, hence `min_period = L/e_u >= n`.
- By T3(b), all `min_period` lower-band fibers are safe.
- Any obstruction run that ends at `b_hi` must start after the lower band.

Therefore:

- `run_len <= B_div - n`.

This closes the `at_B_div_end` truncation mechanism analytically in the declared scope.

### 7.2 Empirical Session 9 Observations

- Test 2 (`n=6`, 93,150 tuples): 0 complementarity-bound violations.
- `at_B_div_end -> next z=0 within min_period`: 100%.
- Prime `n=7`: zero `at_B_div_end` runs in tested pack.
- `gcd_struct_bound` hypothesis refuted (not usable as theorem route).

- Test 3 (`n=4..12`, 1,705 `at_B_div_end` runs):
  - 100% are the final run in `B_div`.
  - 100% have a next `z=0` event within `min_period` beyond `b_hi`.
  - no Type-B bad-set-shift mechanism detected in this bucket.

### 7.3 Updated G4B Split (post NZ0-Leave revision)

- Prime `n` (`z=0` from unit events): `PROVED-UNDER-H`.
- Composite `n`, `at_B_div_end`: `PROVED-UNDER-H`.
- Composite `n`, unit-runner `z=0` terminations: `PROVED-UNDER-H`.
- Composite `n`, non-unit terminations:
  - `nu_only_pos` exits (pure non-unit leave): `PROVED-UNDER-H` via `NZ0-Pure-Existential`.
  - `mixed` / `unit_only` exits: routed to unit branch (not NZ0 failures).

**Resulting status:** the former NZ0 blocker is reduced from event-local existence to branch-integration.

### 7.4 Remaining G4B Promotion Task

The load-bearing task is now aggregation/integration:

- insert the pure-exit existential theorem and mixed-routing lemma into the run-cap chain,
- show the branch partition is exhaustive for interior exits in declared scope,
- conclude component-wise run cap transfer to `G4.B` target (`max_obstr_run(C) <= |C|-n`).

So the open work is no longer “does a non-unit witness exist?” but
“does the proved branch split fully close the global cap theorem in declared scope?”.


### 7.5 Lemma `G4B-Branch-Closure` (formal integration target)

**Status:** OPEN-TARGET (integration lemma; branch pieces now isolated).

#### Statement

Fix a `B_div` component `C`. Assume:

1. **Boundary branch:** any obstruction run in `C` ending at `b_hi(C)` satisfies  
   `run_len <= |C| - n` (proved `at_B_div_end` sub-lemma).
2. **Interior branch partition:** every interior exit `b_last -> b_exit` is classified into exactly one of  
   `nu_only_pos`, `mixed`, `unit_only`.
3. **Interior deficit-opening:**
   - on `nu_only_pos`, `NZ0-Pure-Existential` gives a non-unit leave witness and thus `D(b_exit) >= 1`;
   - on `mixed`/`unit_only`, unit-branch lemmas give `D(b_exit) >= 1`.
4. **Safe-fiber budget:** certified safe fibers in `C` are at least `n`
   (from existing band and/or exit-certified safe-fiber machinery in scope).

Then:

`|O cap C| <= |C| - n`, hence `max_obstr_run(C) <= |C| - n`.

#### Proof

By (2) and (3), every interior exit is a genuine safe opening (`D>0`) on the exit fiber.  
By (1), boundary-ending runs are already capped by `|C|-n`.  
By (4), total safe fibers in `C` are at least `n`; therefore the obstruction count satisfies
`|O cap C| = |C| - B_safe(C) <= |C| - n`.  
Any single obstruction run is a subset of `O cap C`, so
`max_obstr_run(C) <= |O cap C| <= |C| - n`. QED.

#### Promotion checklist (`G4BI.C*`)

- `G4BI.C1` Exhaustive interior partition proof (`nu_only_pos`/`mixed`/`unit_only` disjoint + complete).
- `G4BI.C2` Pure non-unit existential theorem cited in final form (`NZ0-Pure-Existential`).
- `G4BI.C3` Mixed/unit routing theorem references resolved to proved unit branch.
- `G4BI.C4` Safe-fiber budget theorem in declared scope gives `B_safe(C) >= n`.
- `G4BI.C5` Final implication recorded: `G4B-Branch-Closure => G4.B`.

#### 2026-03-07 integration update

`G4BI.C1` is now reduced to a proved local lemma package in
`lrc_master_problem1_branch_integration_v1.md`:

- any genuine interior exit has at least one causative leave set;
- therefore every genuine interior exit falls into exactly one of
  `nu_only_pos`, `mixed`, `unit_only`.

So the remaining integration debt is no longer exit taxonomy.
The live open items are:

- `G4BI.C4` theorem-grade safe-fiber budget,
- `G4BI.C5` final aggregation implication.

`G4BI.C3` is now resolved in final theorem form by
`NZ0-Unit-Routing` in `lrc_g4b_nonunit_z0_lemma_v1.md`,
and is imported into the Master Problem 1 integration note.

The run-end coverage package is now also isolated in
`lrc_master_problem1_branch_integration_v1.md`:
- every maximal run ends either at the boundary branch or at an interior exit,
- every genuine interior exit is classified into exactly one of
  `nu_only_pos`, `mixed`, `unit_only`,
- each interior class is attached to a theorem-controlled safe opening.

So the remaining unresolved content of `G4B-Branch-Closure` is purely:
- `G4BI.C4` safe-fiber budget,
- `G4BI.C5` final aggregation.

Current first theorem route for `G4BI.C4`:
- `lrc_master_problem1_safe_fiber_budget_sf3_v1.md`
- route type: distributed event-spacing / safe-cell occupancy transfer
- motivation: lower-band-only and pure safe-cell-count routes are both too weak on current diagnostics.

2026-03-07 draft-review update:
- the later O1/O2 closure draft is **not** imported as a closure of `G4BI.C4`;
- clean salvage only: exact per-runner interior unit `z=0` event count `= e-1`,
  packaged in `lrc_g4b_unit_z0_event_count_lemma_v1.md`;
- blocker memo: `lrc_o1_o2_closure_review_memo_v1.md`.

Program consequence:
- raw runner-event counting is support only,
- `G4BI.C4` still requires distributed occupancy / overlap control,
- so SF3 remains the live theorem route.
