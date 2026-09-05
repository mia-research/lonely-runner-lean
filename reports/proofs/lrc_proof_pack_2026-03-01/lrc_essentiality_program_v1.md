# Essentiality Program (E1-E4) v1
Date: 2026-03-05
Status: Program note (scope-locked decomposition)

## 0) Goal
Promote the observed "every runner is essential somewhere" mechanism into theorem-grade closure components that connect directly to remaining open claims.

Core split:
- `E1` is fully proved in current locked scope.
- `E2-E4` are the remaining analytic bridge from existence to global quantitative closure.

---

## 1) Scope Taxonomy

### Siiib-U (closed sub-scope)
- One-div near-complete Case-iiib branch.
- Dropped runners `a,b` are units: `gcd(a,n)=gcd(b,n)=1`.
- `n>=10`, one-parameter family as in canonical scope lock.

### Siiib-G (generalized Case-iiib)
- Same structural branch, but dropped runner may be non-unit.
- Includes delayed-sole-cover behavior for non-unit dropped runners.

### Sglobal (full unresolved frontier)
- Multi-divisible and/or broader Case-2 outside `Siiib-U`.
- Includes global S3/complementarity and composite non-unit extensions.

---

## 2) The Program Claims

### E1 (Sole Cover, unit dropped)
In `Siiib-U`, for each dropped unit `d in {a,b}`:
- `r_d := -d^{-1} mod n`,
- `I_d := (1/n, 1/(n-1))`,
- `I_d subseteq Miss_{E_fix}(r_d)`.
Hence `meas(Miss(r_d)) >= 1/(n(n-1))`.

Status: `PROVED-UNDER-H`.
Primary source: `lrc_dropped_runner_witness_v1.md` §11.

### E2 (Delayed essentiality, non-unit dropped)
In `Siiib-G`, for any dropped `d` (possibly non-unit), there exists a transition index/interval pair `(t_d, I_d)` and residue `r_d` such that
`I_d subseteq Miss(r_d)`.

Interpretation: non-unit dropped runners remain essential, but witness interval may be delayed from the first window.

Status: `OPEN`.

### E3 (Quantitative width bound)
Establish explicit lower bound
`|I_d| >= c(n, g_d)` where `g_d := gcd(d,n)`
for witnesses from `E2`.

Target output: explicit formula or theorem-grade lower envelope usable in M3.

Status: `OPEN`.

### E4 (Global counting transfer)
Use M3 counting bridge with `E2/E3` bounds to obtain required safe-mass thresholds in unresolved branches:
- complementarity/run-cap implications,
- S3 quantitative targets,
- `x0 >= phi(n)` style closure statements in target regimes.

Status: `OPEN`.

---

## 3) Dependency Graph

`E1` -> validates scoped closure already recorded (`Siiib-U`).

`E2` + `E3` + `M3` -> positive quantitative slope/width in generalized non-unit branch.

`E4` consumes these quantitative outputs and maps them into remaining canonical open claims:
- `G4B-COMP-CAP` (or equivalent replacement statement),
- broader `S3-GENERAL` obligations outside `Siiib-U`,
- composite non-unit branch pieces in `COMPOSITE-N`.

---

## 4) Pass/Fail Criteria

### E1 pass
A proof that does not use empirical steps and gives explicit witness interval in `Siiib-U`.

### E2 pass
Existence theorem for non-unit dropped runner witnesses with explicit admissibility conditions; no finite enumeration as proof.

### E3 pass
Closed-form lower bound `c(n,g_d)` with a full derivation and scope assumptions.

### E4 pass
A fully explicit counting theorem (via M3) that yields the target inequality in each declared branch.

---

## 5) Immediate Work Items

1. Normalize non-unit witness definition (`r_d`, `t_d`, admissible interval family) to avoid unit-inverse dependence.
2. Prove a delay bound in terms of `g_d` (transition index distance from first window).
3. Derive interval-width lower envelope robust under overlapping blocker families.
4. Bind derived width to discrete count constants used in canonical S3/complementarity trackers.

---

## 6) Canonical References

- Scoped witness closure: `lrc_dropped_runner_witness_v1.md`.
- Master geometry and bridge: `lrc_master_geometry_m1_m3_v1.md`.
- Main theorem sequence anchor: `lrc_ap_grid_extremizer_theorem_sequence_v11.md` §17.33.
- Open-gap and status governance:
  - `lrc_open_gaps_v1.md`
  - `lrc_claim_status_table_v1.csv`
  - `lrc_proof_checklist_v1.md`

---

## 7) E3-v2 Verified Scope Statement (2026-03-05)

This addendum locks the current **verified** quantitative claim in strict scope, and separates it from the still-open analytic universal E3 theorem.

### 7.1 Verified Scope (`E3-v2-VERIFIED-SCOPE`)

- `n` composite or prime in tested set:
  - exhaustive: `n in {6,8,9,10,12,14,15,16,18}`
- near-complete fixed subsystem:
  - `E_fix subset {1,...,n-1}` with `|E_fix| = n-3`
- two divisible placeholders in the residue-frame model:
  - `E_div = {n, 2n}`
- absent runner set in residue frame:
  - `D_abs = {1,...,n-1} \\ E_fix`
- witness-width metric for each absent `d in D_abs`:
  - `w_d := meas({alpha in I_div : bad_set(d, floor(d alpha), n) \\ U_fix(alpha) != emptyset})`
  - where `I_div = [1/n, (n-1)/n]` and `U_fix(alpha) = union_{e in E_fix union E_div} bad_set(e, floor(e alpha), n)`

### 7.2 Verified Bound

For every tested tuple in scope above:

- `w_d >= 1/(n(n-1))` for all absent `d`.

Observed minima over exhaustive tested `n`:

- `n=6:  min_d w_d = 1/6   >= 1/30`
- `n=8:  min_d w_d = 17/168 >= 1/56`
- `n=9:  min_d w_d = 4/45   >= 1/72`
- `n=10: min_d w_d = 2/15   >= 1/90`
- `n=12: min_d w_d = 7/60   >= 1/132`
- `n=14: min_d w_d = 3/28   >= 1/182`
- `n=15: min_d w_d = 8/105  >= 1/210`
- `n=16: min_d w_d = 7/72   >= 1/240`
- `n=18: min_d w_d = 11/126 >= 1/306`

### 7.3 Exact Hypotheses and Exclusions

Hypotheses locked in this verification:

1. Two divisible placeholders are exactly `n` and `2n`.
2. Near-complete shape is exactly `|E_fix|=n-3` over residue-frame speeds `1..n-1`.
3. Width is existential per absent runner (`bad_set(d) \\ U_fix != emptyset`), not uniform over all residues.

Exclusions (not covered by this lock):

1. General `E_div` families beyond `{n,2n}`.
2. Cases with `|E_div| != 2`.
3. Full universal `E3` formula `c(n,g_d)` proved analytically for all composite branches.
4. Any theorem claim that uses finite enumeration as sole proof.

### 7.4 Status Interpretation

- This is a **script-verified quantitative scope lock**, not final analytic closure of E3.
- Recommended status label in trackers:
  - `E3-WIDTH-BOUND-NONUNIT`: `OPEN-PROGRESS` with explicit verified-scope note.

### 7.5 Script-Ready Checklist (E3-v2)

- `E3V2.C1` Domain constructor:
  - build all `E_fix` with `|E_fix|=n-3`, set `E_div={n,2n}`.
  - pass iff full enumeration count matches `C(n-1,n-3)`.
- `E3V2.C2` Absent-runner set:
  - compute `D_abs={1,...,n-1}\\E_fix`.
  - pass iff `|D_abs|=2`.
- `E3V2.C3` Witness-width metric:
  - compute `w_d` exactly on Farey partition of `I_div`.
  - pass iff rational-exact arithmetic used (no float-only grid approximation).
- `E3V2.C4` Lower-bound test:
  - check `w_d >= 1/(n(n-1))` for each absent `d`.
  - fail on first violation with tuple witness dump.
- `E3V2.C5` Min-envelope report:
  - output `min_{E_fix,d} w_d` by `n`.
  - pass iff minima and comparison to target are printed.
- `E3V2.C6` Scope guard:
  - assert and log that run is only for `E_div={n,2n}`.
  - fail if other `E_div` appears.
- `E3V2.C7` Artifact policy:
  - emit rows CSV + summary markdown with seed/date/hash.

