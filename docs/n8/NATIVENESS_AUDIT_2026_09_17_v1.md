# Nativeness audit of the 2026-09-17 cap work

Checked against `OBJECT_REGISTER_v1.md` — §0's positive list of the framework's own objects, and the
28 import rows of §2/§3. Subject: everything produced on 2026-09-17
(`RETURN_CORRECTION_v1/v2.md`, `ladder_cap_word_check/replay/extend/lean_crosscheck_v1.py`,
`first_window_nativeness_v1/v2.py`), and the instruments they inherit
(`order_n_certificate_v1.py`, `LADDER_BOUND_v1.md`).

**Headline: one substantive finding, two wording hits, and the rest clean.** The substantive one is an
identity, proved below, not an opinion: **the certificate's cap `R < n − 1` is register item 15 — the
first window — in lap coordinates.** It is empirically non-binding, which is why it has not shown up as
a defect, and naming it opens a route that was not on the list.

Artefacts: `experiments/n8/first_window_nativeness_v2.py` / `.out`.

---

## 1. The substantive finding: the cap *is* the first window  `[PROVED — identity; VERIFIED]`

Two framework objects, both from the positive list:

- `OBJECT_REGISTER_v1` §0, **Laps**: `u = d_min·t`, readings `s_j = d_j/d_min`.
- `ORDER5_GROWTH_v2` §2: `R = n·m·t` with `m = d_min`.

Therefore **`R = n·u` exactly** — `R` is `n` times the lap, and is native. Checked on the replay's own
numbers: `u = 49/64 → R = 49/8`; `u = 765625/875001 → R = 6.999992`; equality exact in all four.

The cascade opens at `t = 1/n`, i.e. `u = 1/n`. So

    cap  R < n − 1   ⟺   u < (n−1)/n ,      cascade opening at u = 1/n

and the cap says precisely: **`u` stays inside `[1/n, (n−1)/n]`**. That is register item 15, *the first
window `u ∈ [1/8, 7/8]`*, classified **MISPLACED**, with the owner's ruling recorded there:

> *"I never thought the first window/cycle was a requirement and think it keeps getting introduced from
> context loss and revert to training data."*

The word "window" appears nowhere in the certificate; the constraint arrived in the framework's own
coordinate. This is exactly §1's warning — *a misplacement survives every audit that checks whether a
foreign word appears, because the word is the framework's own.*

**Is it binding?** Measured, not assumed. With no cap and no window imposed, running the native cascade
(`LRC/Cascade/Iteration.lean`, transcribed) on shuffled integer difference sets:

| ratio bound | arrangements | instant inside the window | beyond it | max steps |
|---|---|---|---|---|
| 8 | 4000 | 4000 | **0** | 12 |
| 10 | 4000 | 4000 | **0** | 12 |
| 14 | 4000 | 4000 | **0** | 11 |
| 20 | 4000 | 4000 | **0** | 10 |
| 30 | 4000 | 4000 | **0** | 9 |
| 60 | 4000 | 4000 | **0** | 15 |
| 120 | 4000 | 4000 | **0** | 11 |

**0 of 28 000 beyond the window**, and every arrangement produced an instant. So the import is real in
the *statement* and empirically vacuous in *extension*. This is consistent with the cap finding rather
than in tension with it: `sup R = n − 1` **not attained** says exactly that arrangements crowd the
window's edge without crossing it.

**What naming it opens.** `RETURN_CORRECTION_v2` §4 lists three ways forward. There is a fourth, and it
is the framework's own: **stop requiring the first window.** Existence asks for an instant, not an
instant in lap 1. Against the cap the obligation is `R < n − 1`, which is tight — `sup R` equals the cap,
so there is no margin and Lemma C is asking for something false. Without it the obligation is "an
instant is produced", which has no tightness problem at all. The measured table says nothing is lost:
the cascade does not use the second lap. **This is a question for the owner, not a decision taken here**
— the certificate may be wanted as a stronger statement on purpose.

## 2. Wording hits  `[MISPLACED — substitution, per §1]`

Counted by grep over the 2026-09-17 artefacts.

| word | count | register | the framework's object |
|---|---|---|---|
| **witness** | 13 | item 6, MISPLACED. Owner, twice: *"My work does not need a witness."* | the **readings**. A point is computed, not witnessed. My use is of a reading vector the LP produced — so the object is right and only the name is foreign |
| **terminate** | 6 | item 25, NOT APPLICABLE. Owner: *"Termination is not required in my framework"* | the instant is **produced**. Note the tension: `LRC/Cascade/Iteration.lean` does carry `lonely_iff_run_ends` and `first_isolation_of_fixed`, so run-end is native **to the Lean cascade**; item 25 rejects termination as a *requirement on the construction*. My use is descriptive, not a blocker, but the outcome should be stated as production |

Neither changes a number. Not corrected in place, because that would version four artefacts for wording;
flagged here for a decision.

## 3. Clean, with the evidence that makes it a check rather than an assurance

| register item | status in this work | how checked |
|---|---|---|
| 4 covering, 27 union bounds | absent | grep, 0 hits |
| 5, 14, 20 measure / density / interior | absent. The 9 hits on "measure" are all *measured/measurement* in the ordinary sense | grep + read each hit |
| 9 Weyl equidistribution | absent | grep, 0 hits |
| 10 LRC(7) / induction on `n` | absent | grep, 0 hits |
| 11, 16 primes, `p ∈ {1,3,5,7}` | absent | grep, 0 hits |
| 12 a stationary first runner | absent. The work is in differences throughout, which are frame-free; no runner is pinned | grep + read |
| 13 slots | absent | grep, 0 hits |
| 2 blocking, 7 carrier, 8 set emptiness | absent; the predicate used is `inWay`, the Lean artefact's own | grep, 0 hits |
| 18 `D ∈ ℤ` | not used; readings are rationals `d_j/d_min`, scales not integers | read |
| 28 global clock / simultaneity | **not present, and worth stating.** `Lonely n ds s` quantifies over one subject's own differences. Nothing here asks for an instant at which several runners are lonely together | read the definition |

**Two positive signals, both checkable:**

- **Six readings, not five.** The LP carries `NV = n − 2 = 6` unknown readings plus the nearest at
  reading 1 — seven differences, six read. That is §0's *"six, not five"* and §4a's standing rule, met
  by the instrument without anyone aiming at it.
- **The ceiling reproduces.** §0's ceiling object predicts that at `u = 1/n` the subject is lonely iff
  every `d_j ≤ (n−1)·d_min`. Derived independently here from the phase `d_j/(n·d_min)` and **verified on
  500 shuffled sets, 500/500**. The framework's own object falls out of the native cascade.

## 4. One open question I am not resolving  `[for the owner]`

**Register item 1** rejects *"Lemma 6 — for any six reals `s ≥ 1` there is a `u`…"* as **NOT APPLICABLE**:
*"It is LRC(8) restated. The construction's objects are gaps and laps, not a list of six reals."*

The certificate quantifies over a **box of six free readings** `1 ≤ u_i ≤ S` and asks what the cascade
does across all of them. That is the shape item 1 names, though not its content: the six readings are a
framework object (§0), the quantity bounded is a lap, and the LP is a tool, which the 2026-09-15 ruling
permits — *"tools are fine, targets and statements are what must stay native"*, test: *does the statement
exist in your vocabulary alone?*

Stated in the framework's vocabulary the target reads: **for every arrangement, the cascade's instant has
`u < (n−1)/n`.** That passes the test on its face. Whether quantifying over a box of reading vectors —
rather than computing the instant for a given arrangement — re-imports item 1's shape is a call I should
not make alone. It is the difference between *proving the construction works* and *proving a statement
about all arrangements*, and only the owner can say which was intended.

## 5. A defect in my own instrument, recorded

`first_window_nativeness_v1.py` iterated without advancing `t`. Every arrangement whose cascade moved
was counted as non-terminating and dropped, so its headline — *"100% inside the window"* — was computed
from the 0-step cases alone and was worthless. Caught by a diagnostic that disagreed with it (1–3 steps
where v1 reported thousands), not by review. v1 and its `.out` are kept as the record; v2 carries the
fix and the table in §1.

The 0-step cases were not noise, as it happens: they are exactly the ratio `≤ n−1` arrangements, lonely
at the opening instant — which is how the ceiling check in §3 came to be written.
