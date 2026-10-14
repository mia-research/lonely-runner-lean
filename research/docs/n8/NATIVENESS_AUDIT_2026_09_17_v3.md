# Nativeness audit of the 2026-09-17 cap work, second correction

2026-09-17. Supersedes `NATIVENESS_AUDIT_2026_09_17_v2.md`; v1 and v2 kept as the record. **One claim
carried from v1 through v2 is wrong** and is corrected in §1. Everything else in v2 stands, including
its own corrections to v1.

---

## 1. The correction: the import is not "empirically vacuous"

v1 §1 and v2 §3 both rested on a sweep of 28,000 shuffled arrangements returning **0 beyond the first
window**, and concluded the confinement was *"real in the statement and empirically vacuous in
extension"*.

**The measurement is sound and the conclusion drawn from it is wrong.** The sweep sampled shuffled
integer difference sets; the arrangements that cross the window are rare and are reached by directed
search, not by sampling. The manuscript already carried two of them (`u = 1.2826` and `u = 1.2891`
laps) and records `R ≈ 11.96`. §6.9's row is flagged there precisely as *"nothing clears in its first
window"* — the named refutation of the confinement, on file, unread.

So the corrected statement is stronger than v1's, not weaker:

> The first-window confinement is **not** a harmless over-statement. It is **false at order 8**, and the
> manuscript already names the arrangements that break it.

`sup R = 7 at the arrangement level` (v2 §3, third bullet) is likewise wrong: `R` reaches `10.31`.

## 2. Why this is the audit's own failure mode, not a detail

The register's §6 names the generator: *an absence in my own model is converted into a requirement on
the construction.* This instance runs the other way and is worse — an absence in my own **search** was
converted into a property of the object. A null from random sampling was reported as though it bounded
the extremes.

`MEMORY.md`'s core-bias entry describes the signature exactly: *~zero false positives where a calibrated
search throws off several*. 0 of 28,000 was that signature, and it was reported rather than tested. The
rule it violates is the one in that entry: surface the positive and test it; rigour lives in the test.

The gate that now exists for this is **G6** of `PROVENANCE_MAP_v1.md`, and the mechanical form is
`experiments/n8/framework_cases_v1.py`, which refutes the null in one second.

## 3. Unchanged from v2

§1 (the implementation is the framework's — three ways, 6000/6000 in the scale coordinate), §2 (it is
not a search; `first_isolation_of_fixed`), §3's identification of the **word enumeration** as where the
search entered, §4's two corrections to v1, §5 (the native target, and the R-programme being stronger in
two ways), §6 (the beam stopped).
