# PROCESS REVIEW — session "BTC project next steps" (2026-08-01)

**Source:** session `local_55348e2f`, 854 messages, read in full (5 pages via `list_events`).
**Scope:** process only. No mathematical claim in this file, and nothing here promotes,
retracts, or re-grades any result. Where a result is cited it is cited as *evidence about
the process*, at whatever grade its own file carries.

**Premise this review is written under (CLAUDE.md §2b):** instruction-based correction has a
measured track record on this project of ~0 — 17 `feedback_*` memories each describing a
failure mode precisely, every one of which recurred anyway. So the recommendations below are
ranked by how *mechanical* they are. "Be more careful about X" is not a proposal. A script,
a required field, or an import that aborts is.

---

## §1. What the session actually cost, itemised

Ten defects, each with the transcript evidence. Two are already fixed; eight are not.

| # | defect | evidence | fixed? |
|---|---|---|---|
| 1 | **Scope ban misfired onto in-scope work** | The `μ₃`/GLV lane was flagged as "generation-side, permanently out of scope" when it is the *conversion* `d ↦ (x,y)`. Twice in one session. | ✅ memory rewritten |
| 2 | **False-choice menus at turn end** | ~6 turns ended `Want me to (a)… or (b)…?` | ✅ memory written |
| 3 | **Manufactured defects against the record** | Item 1: three objections raised to a `[VERIFIED]` claim; **all three were my own bugs** | ❌ |
| 4 | **Hedged a decidable question** | `gauss()` Euclidean-vs-Eisenstein metric "flagged as unreconciled" | ❌ |
| 5 | **Verification claim inside a `print` string** | `"(matches curve trace)"` printed next to a number that did not match `t_p` | ❌ |
| 6 | **Self-authored forced statistic** | `mean(T)` as S3 — exactly permutation-invariant under my own null; 20/20 null draws identical to data | ❌ |
| 7 | **Dropped a guard the record already documented** | `p ≡ 1 mod 4` → `u ≡ 0`; the source script's own header states the `p ≡ 3 mod 4` requirement | ❌ |
| 8 | **Stale OPEN marks** | Addendum dated Jul 26 lists 4 statistics as unmeasured; 2 were measured Jul 30. **Third logged instance.** `OPEN_ITEMS_LEDGER_v1.md` last touched Jul 25 | ❌ |
| 9 | **Named-as-unrun, then walked past** | `|T(a,b)|²` intensity object named as uncovered, then item 2 declared done and item 3 announced | ❌ |
| 10 | **Turn ends on an announcement, not a result** | Several turns closed with "Moving to item N — I'll report when it's run", requiring another prompt to start | ❌ |

### The two that share a root cause (#3 and #4)

These are the expensive pair, and they are the same mechanism running in opposite directions.

**#3, manufacturing defects.** In item 1 I reported that the record used an "undocumented
convention", that its pinned pair was a forced constant, and that its bridge scored 35/69
against a published 0/69. All three were mine: the record's hardcoded `(aP,bP)` satisfies
`2aP − bP = t_p` exactly — it was the **trace-pinned Frobenius** all along; my "canonical
normalization" `arg(π) ∈ [0°,60°)` changes `Re(π)` and therefore changes `t`, so it erased
the Frobenius angle by construction and I then blamed the record for the constant I had
manufactured; and the 35/69 was my implementing `θ < 30°` where §2.4 states `θ mod 60°`.

The turnaround came from one act: **constructing `π` from the trace reproduced the record's
hardcoded `(aP,bP)` exactly.** That single reproduction validated the instrument, and every
"defect" evaporated. It was available at minute one and I did it at the end.

**#4, hedging.** Immediately after being corrected on #3, I found a second candidate defect —
`gauss()` reducing with the Euclidean dot product `a₀b₀+a₁b₁` on a lattice whose native norm
is `a²−ab+b²` — and wrote *"I haven't verified it changes any published number, and I've
already over-claimed once on this item. Flagged as unreconciled."* One computation settled
it: `p` is the minimal Eisenstein norm in `(π)`, the only vectors of norm `p` are the six
associates, so **any** reduction terminates on an associate and every reduced basis is a
congruent rhombus. Blast radius provably zero — a stronger result than the flag, and it also
surfaced the `θ mod 60°` bug, taking the bridge to **69/69**.

My own formulation at the time is the rule worth keeping: *the correct response to "I might
be wrong again" is a computation, not a caveat.* A caveat after a correction is an
unfinished computation wearing caution as a costume.

**Calibration note.** The standing calibration says my errors run one-way deflationary. This
session adds a distinct second mode — **manufacturing defects against the record** — and then
a third — **hedging after correction**. Both are triggered by the same thing: a fresh
implementation disagreeing with the record, with no instrument-validation step in between.

---

## §2. What worked — preserve these, they are load-bearing

Not padding. These are the mechanisms that caught real defects, and any process change must
not disturb them.

1. **The out-of-sample retest rule killed a chance pattern.** `A2`, the spectral inversion
   statistic — the exact variant predicted to be live — read `p = 0.069` in-sample and then
   `0.831 / 0.324 / 0.700` on three fresh seeds. Controls fired at 12–25% planted, so the
   instrument had the power. **Sixth chance pattern killed by this rule.**
2. **Control rows caught four separate real bugs**, each of which would have produced a
   publishable-looking false positive:
   - `C-ORBIT` read max within-orbit spread ≈ 7.5 instead of 0 → my symmetry group was wrong
     (two nontrivial cube roots mod `n` and two mod `p`; only the *matched* pair satisfies
     `x_{λd} = βx_d`). Every `p ≈ 0.01` under it was invalid and none was reported.
   - `C-FORCED` failed at `p = 349, 373` → both `p ≡ 1 mod 4`, where nothing is forced.
   - the even-`n` control's discrepancy of exactly `−1` → Sage's `0.is_square()` is `True`,
     scoring a degenerate fibre `+1` instead of `0`.
   - five statistics pinned to the floor simultaneously at `p = 2089` → diagnosed as a broken
     cell rather than reported.
3. **An independent integer-only reimplementation settled the float-guard question** instead
   of a blanket `noqa` exemption, and doubled as a second code path reproducing the headline
   number bit-for-bit.
4. **Artifact-stacking was caught before reporting.** The `|T(a,b)|²` field produced *three*
   separate artifacts — wrong symmetry group, trivial-frequency spike (`I(0,0)=n`, `b=0` row
   exactly zero, null spread inflated 37×), and Parseval (`Σ_a|T|² = n²` per row, forced,
   which the orbit-permutation null violated). Each individually read a clean `p ≈ 0.01` at
   **every** prime.
5. **The method note that came out of it:** *cross-prime consistency is not reassurance.* All
   three artifacts were perfectly consistent across all five primes. Consistency across cells
   discriminates nothing when the defect is in the instrument.
6. **Per-point critique handling.** Each incoming critique was answered point-by-point with
   concede-and-run or hold-with-reason, never blanket. That is what allowed conceding "no
   mechanism ≠ low power" (correct) while holding on Hamming-weight-via-double-and-add
   (the same representation-vs-reality error the Voronoi thesis had just died of).

---

## §3. Process observation about the incoming critiques

The user asked about *our* process, so this belongs here. The pasted critiques were **right in
thesis every time and wrong in particulars most times** — exactly the pattern
`feedback_verify_external_critiques_2026_07_17` already records for GLM-5.2.

| critique | particular | status |
|---|---|---|
| "failed to execute the scan on the valid `p ≡ 3 mod 4` domain" | the gated re-run **was** on `p ≡ 3 mod 4` — 14 primes, 823–3343, the table was in the message being critiqued | wrong; **but** the thesis (an item was left half-run) was right, and named the real miss: the `|T|²` intensity object |
| "targeted boundary sampling — point the telescope at the edges" | census: **1** `c₂` boundary in the entire `[2¹²⁷,2¹²⁸)` octave, and `[d]G` is provably blind to the Voronoi cell (any valid `(k₁,k₂)` gives the same point) | dead |
| "Hamming weight is the literal physical footprint via double-and-add" | `[d]G` is the same point under double-and-add, wNAF, Montgomery ladder or GLV — algorithm, not mechanism | wrong as a mechanism; the test is legal and was run (null) |
| "the model forced a canonical normalization and erased the Frobenius angle" | correct in full — `π` is the Frobenius endomorphism, pinned by `2Re(π)=t` | **right, and it reversed item 1** |
| "the gauss() metric threatens the geometric foundation" | blast radius provably zero | wrong in prediction; **right that flagging instead of computing was the error** |

**The transferable point:** the critiques' *thesis* — "you are dropping live threads" — was
correct in five of five instances, including the two where every particular was wrong.
Refuting a mechanism is not refuting a claim. Check the two separately, thesis first. That is
already the standing rule and it was applied correctly this session.

**One cheap improvement on the input side:** a critique asserting that something was not run
can be checked in one command before it is answered — the run leaves a named artifact. The
`p ≡ 3 mod 4` exchange cost a full round-trip that `ls`-ing the result file would have saved.

---

## §4. Proposed changes, ranked

Ranked by (defects killed) × (how mechanical the kill is). Per the no-false-choices rule this
list *is* the decision — start at #1 and work down.

### 1. `probe_guard.py` — one import that every new harness uses

A single module in `btc_puzzle_investigation/` providing four things that **abort**, not warn:

- `verify(cond, msg)` — the *only* sanctioned way to emit the words
  matches / confirmed / verified / holds / exactly. Raises on failure. → kills #5.
- `assert_unforced(stat_fn, pool, R=20)` — computes the statistic on `R` null draws before
  the real run; aborts if the spread is zero or the data value is invariant. **Runs on my own
  specs, not only on incoming proposals** — `mean(T)` (#6) was mine, and is the seventh logged
  forced statistic on this project. → kills #6.
- `require(object_name)` — a registry of documented preconditions keyed by object
  (`u`-framework → `p ≡ 3 mod 4`; `χ₂(y)` readouts → `ε = −1`; …), so reusing a record object
  carries the record's guards as executable asserts. → kills #7.
- a control registry: `report()` refuses to emit a verdict unless ≥1 registered control fired.
  → hardens the §2.2 mechanism that is already the best thing in the process.

Cost: one file, one afternoon. Kills three of the eight open defects outright and makes a
fourth (broken controls) structurally hard.

### 2. Extend `check_no_float.py` with a claim-in-string rule

The AST walker already exists and already runs. Add: any string literal containing
`matches|verified|confirmed|holds|exactly|✓` that is not an argument to `verify()` or `assert`
→ flag. ~20 lines in a walker that is already written. This is the exact shape of #5 — a
verification claim emitted inside a format string with no verification behind it.

### 3. `REPRO:` as a required field on any result that disputes the record

Any result file that disputes an existing record claim must carry a line naming **one
published number of that record which the new code reproduced exactly**. Item 1 produced
three false objections and turned around the instant this was done. Grep-checkable: result
files containing a dispute verb but no `REPRO:` line. → kills #3, the most expensive defect.

**Rationale in one line:** when a fresh implementation disagrees with the record, the null
hypothesis is that the fresh implementation is wrong.

### 4. Ledger write is the turn's exit condition

Any object a turn names as unrun or uncovered gets appended to `OPEN_ITEMS_LEDGER` **in that
turn**, dated. Plus a small `ledger_staleness_check.py`: for each ledger item, list result
files newer than its mark whose keywords match. → kills #8 (three logged instances; the
ledger is currently 7 days stale against work that answers it) and #9 (`|T|²` was named and
walked past inside a single turn).

### 5. The hedge rule, with a checkable form

A flagged-but-unresolved concern is legal **only** if the file states the computation that
would settle it *and* why that computation cannot run now. Otherwise: run it. Grep-checkable
against "flagged as unreconciled" / "candidate cause" / "not calling it a defect" with no
adjacent settling computation. → kills #4.

### 6. Turn shape

Already half-covered by the no-false-choices memory. The missing half: **a turn ends on a
completed item, not on the announcement of the next one.** When working a list, the next
item's first computation belongs in the same turn as the previous item's result. → kills #10.

---

## §5. Gates that apply to acting on this file

- Items **3** and **5** would become `feedback_*` memories → CLAUDE.md §2 makes
  **`memory-drafter` mandatory** before either is written. Not spawned; this file is a review,
  not a memory.
- Item **1**'s control registry touches how leakage tests are specified → any *new* test built
  on it still needs its `experiment-designer` prereg as usual. The guard module does not
  replace the gate.
- Nothing here is a promotion, so `compile-diff` does not apply.
