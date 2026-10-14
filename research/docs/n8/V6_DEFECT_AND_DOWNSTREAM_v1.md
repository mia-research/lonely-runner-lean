# v6 §7.4 has a counterexample — and the audit's verdicts move

2026-09-14. Two findings, one urgent.

---

## 1. URGENT: v6's §7.4 Claim is refuted, by an arrangement already on file

> **v6 §7.4, Claim.** For every arrangement and every runner there exist `d ∈ D` and
> `a ≡ 1 (mod 8)` with `d ≤ a·m ≤ 7d` such that `d ≤ (a·e mod 8d) ≤ 7d` for every `e ∈ D`.

**Speeds `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`, the runner at speed 1.**
Differences `1974, 5264, 6909, 8736, 9588, 11844, 15134`, `m = 1974`.

> **All 23 candidates examined. None clears.**

This is `CLAIM_REFUTED_v1`'s arrangement. Its arithmetic was never in doubt —
`CLAIM_REFUTED_v2` retracted the *conclusion*, not the computation, and said so.

**Why it bites v6 and not the framework.** The cascade rescues the runner at lattice
`D = 1451`, `p = 7`, `t = 7/11608`. But

- `1451` is **not** one of the runner's own differences, and v6's §7.4 quantifies `d` over `D`;
- `t = 7/11608` lies **outside** `d_min`'s window `[1/15792, 7/15792]`, and v6's window
  condition `d ≤ am ≤ 7d` confines the search to that window.

**So I reintroduced the over-narrow claim in integer clothing.** The `(d, a)` form is a
faithful translation of §7.1 — and §7.1 was already the reduction, as
`AUDIT_WINDOW_ASSUMPTION_v1` established. Translating it into integers did not widen it. I
had the refuting arrangement on file and did not run it against the new statement before
shipping v5 and v6.

**LRC(8) is untouched.** The runner is lonely at `t = 7/11608`.

### What v7 should say instead

The honest repair is not to widen the Claim quietly. It is to split it:

| | |
|---|---|
| **the window-restricted claim** (v6 §7.4 as written) | **`[REFUTED]`** — witness above, exhibited and checkable |
| **the cascade claim** — some lattice `D ≤ 7·d_min` and `p ∈ {1,3,5,7}` clear | **`[CLAIMED]`** — the actual open statement |

That converts an open claim into a **settled negative result plus a sharper open one**, and
the negative belongs in §6 with the other routes that cannot work.

---

## 2. Proposition 7.1 reverses three verdicts in `AUDIT_WINDOW_ASSUMPTION_v1`

That audit marked several documents "framing wrong" for measuring the window search rather
than the framework's procedure. **Proposition 7.1 now proves the window search and the
own-difference integer search are the same thing**, so those documents measured a real,
framework-native object after all.

| artefact | audit verdict | verdict now |
|---|---|---|
| `PHI_REACH_SCALE_v1–v3` | sound | **sound, and sharper** — it measures the four-candidate row at general `n`, exactly what v5 restored. Its `n = 8` figure `0.71–0.76` is that row |
| `EXHAUSTIVE_OTHER_ORDERS_v1` | framing wrong | **SOUND** — by Prop 7.1 its 4,025,986-instance sweep decides v6's §7.4 procedure exactly. Its zero failures at `n = 5…10` are consistent with §1: the counterexample has `v₈ = 15135`, far outside those bounds |
| `TIGHTEST_v1` | framing wrong | **SOUND** — "number of clear components" equals "number of clearing candidates". A clear zone right endpoint is always its component's left endpoint, since the points just below it lie in that zone |
| `failure_hunt_v1`, `failure_laps_v1`, `margin_count_v1` | wrong object | **SOUND, and they generate counterexamples to §7.4** — their hits at `n = 6, 7, 8` are exactly runners with no clearing candidate |
| `CASCADE_SHARPENED_v1` | sound | unchanged |

**The audit's error was one level up.** Those documents measured the right object; what was
wrong was calling that object "the framework's procedure" when the framework has the cascade
above it. The correction is to the *label*, not to the measurements — and the measurements
now have a proved identity behind them.

---

## 3. The generalisation work is unaffected

| | |
|---|---|
| `ConstructionN` parts 1–6 at general `n` | unaffected — explicit hypotheses, no search space asserted |
| part 2(b) derived (`Instants.lean`) | unaffected, and **more central**: `t = p/n`, `gcd(p,n) = 1` is the four-candidate row at general `n` |
| the six generalised forms, the thresholds | unaffected |
| `Band.lean`, now with `returns_at_spine` | unaffected, extended |
| `Negative.lean`, now with the `2σ` containment | unaffected, extended |
| `Candidates.lean` | new; it is what reverses the verdicts in §2 |
| `Soundness.lean` | flagged for restatement on `(d, a)` — deferred, at the owner's direction |

**`Construction8` is untouched throughout**, digest
`578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`.

---

## 4. What I should have done

Run the one arrangement I already knew breaks the window against the new statement, before
shipping it. The check is three lines and I had written the arrangement down myself the day
before.
