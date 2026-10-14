# Provenance map and gate — what the framework owns, and seven checks before a step counts

2026-09-17, written at the owner's instruction after the day's work imported a confinement for the
fourth recorded time. **This is not a reminder.** Instruction-based correction has a measured record of
about zero on this project; seventeen `feedback_*` memories each describe a failure that recurred anyway.
So every gate below resolves to a **runnable artefact or a citation**, never to care, and the mechanical
part is a script: `experiments/n8/framework_cases_v1.py`.

Companion: `OBJECT_REGISTER_v1.md` (the 28 imports, append-only). This file is the *positive* side plus
the procedure. Neither replaces the other.

---

## 1. The positive list — the only objects a target may be stated in

| object | what it is | citation |
|---|---|---|
| **Gaps** | the eight cyclic gaps on the **track**, summing to 1. Lonely ⟺ both flanking gaps `≥ 1/8` | Thm 4.1; register §0 |
| **`d_min`** | the nearest speed difference, at a speed-neighbour | §2.1 |
| **Readings** | `s_j = d_j/d_min ≥ 1`. **Six read, not five** | §2.1; register §0, §4a |
| **Laps** | `u = d_min·t`; phase `s_j·u mod 1` | §2.1; register §0 |
| **In the way / next opening / move** | `‖d·t‖ < 1/8`; least `(k+1/8)/d` at or after `t`; move = **largest** next opening among those in the way | **§6.1** |
| **The cascade (the determinator)** | the sequence of moves from the **bound** `1/(8m)`. *"There is no set of candidates: the runners in the way at `t` fix the move."* | **§6.1** |
| **The scale recursion** | the same object in the other coordinate: `D_0 = d_min`, `D_{j+1} = D_j·min{s/(8N+1) : |s−8N| < 1}`, instant `= 1/(8·D_final)` | **§6.2** |
| **`R`** | `R = n·u = d_min/D_final` — the instant in units of the bound | §6.2, line 118 |
| **The clearing test** | at `t = a/(nD)`, `e` clear ⟺ `D ≤ (a·e mod nD) ≤ (n−1)D`. An integer comparison | Prop 2.1; register §0 |
| **Existence** | *"For every arrangement and every runner, the cascade reaches a fixed point — it arrives at a scale at which no reading lies within 1 of a multiple of 8."* Per **runner**, not per arrangement | **§6.7** `[OPEN]` |

**Three standing facts that repeatedly get re-imported as requirements:**

- **No window.** §1.3: *"The framework does not require it, and there is no window here: the cascade
  runs over every lap, and no bound on when an instant falls is a requirement of any result."*
- **Not the cascade's own instant.** §6.6: *"Existence needs some lonely instant, not the cascade's."*
- **Not a search.** §6.2: the recursion is *"fixed by the speeds"*. §1.3: *"Not picking."* Lean
  `first_isolation_of_fixed` proves the fixed point is `≤` **every** positive lonely instant — the
  minimum of a static set, computed, not found.

## 2. The gate — seven checks, each with an artefact

Run before a step counts. "I considered it" is not an answer; the right-hand column is.

| | check | what answers it |
|---|---|---|
| **G1** | **Object.** Name every object in the statement and cite its §. Anything not in §1 above is **outside** | the citation, written down |
| **G2** | **Tool or target.** If outside: is it only in the method (tool — admissible) or in the statement (must be native)? Test: *does the statement exist in the framework's vocabulary alone?* | the statement, rewritten in §1's vocabulary |
| **G3** | **Reduction.** For any bound `X < c`: reduce **both** `X` and `c` to laps / readings / scales / gaps. Then read what `c` is. If it names a lap boundary, a window edge, a "first" anything, or a cardinality the framework does not have — it is a **confinement**, not a bound | the reduction, done explicitly |
| **G4** | **Strength.** Does my target imply §6.7 Existence? Does Existence imply my target? If not both, I am proving something **strictly stronger**; name why that is worth it | both implications, stated |
| **G5** | **Premise.** What does my *instrument* assume that the framework does not? List each | the list, from the instrument's own code or derivation |
| **G6** | **Calibration.** Any null — "no arrangement", "bounded", "generic", "does not occur" — is run against `framework_cases_v1.py` **first**, then a directed search. A clean null from random sampling is not a result | the harness output, plus the search |
| **G7** | **Determination.** Am I treating a determined **output** as a free input? Speeds fix the path; a path is not a thing to search over | name the input and the output, and check the arrow |

## 3. Today, gate by gate — the worked failure

The day's instrument was the word certificate and the ladder bound (Lemma A/B/C), targeting
`sup R < n − 1`. Five of seven gates fail, and each failure is cheap to detect.

| | verdict on 2026-09-17 |
|---|---|
| G1 | **pass.** `R`, laps, readings, the cascade — all native |
| G2 | **pass.** The LP is a tool; the statement is in laps |
| G3 | **FAIL.** `R = n·u`, so `R < n−1` reduces to `u < (n−1)/n` with the cascade opening at `u = 1/n` — the **first window**. §1.3 disavows it; the revision table already records *"`R < 4` is the first window (audit R1; boundary audit B2)"*. A one-line reduction, not run |
| G4 | **FAIL.** `R < n−1` ⟹ Existence, but not conversely — stronger in **two** ways (the window, §1.3; the cascade's own instant, §6.6). Never stated |
| G5 | **FAIL.** The enumeration assumes **the nearest runner never sets** (sound only *before* the cap is reached). At `(27,70,107,137,159,188,344,393)` the nearest sets at step 24. The premise is the confinement in disguise |
| G6 | **FAIL.** "0 of 28,000 beyond the window" was reported as settling it. §6.7 already records `R ≈ 11.96`; §6.9's table already names `u = 165/128`. **One second of checking would have refuted it** |
| G7 | **FAIL.** The word enumeration searches `(setter, lap)` sequences and solves back for readings — the determined path treated as free. Hence 7.25×10²⁶ words for a thing that has **one** path per arrangement |

## 4. The mechanical part: `framework_cases_v1.py`

Every case the manuscript names, with its published values, runnable. Current rows, **all reproducing
exactly, 0 failures**:

| case | subject | `t` | moves | `u` (laps) | `R` | beyond window |
|---|---|---|---|---|---|---|
| §6.7 adversarial climb `(27,70,107,137,159,188,344,393)` | 393 | `49/1872` | 28 | `2401/1872` = 1.2826 | `2401/234` = **10.26** | **yes** |
| §6.9 table / v7 Claim refutation `(1,31,75,97,128,160,176,225)` | 1 | `11/256` | 23 | `165/128` = 1.2891 | `165/16` = **10.31** | **yes** |
| §6.6 near-wrap `(1,…,7,9)` | 1 | `9/64` | 1 | `9/64` | `9/8` | no |
| §6.2 scale chain `(1,…,6,8,9)` | 1 | `9/56` | 2 | `9/56` | `9/7` | no |

Two of four are above the cap, so **the harness refutes `R < n−1` at order 8 on its own**. The
first-window scan on row 2 returns *no lonely instant in* `[1/8, 7/8]`, reproducing line 558's *"nothing
clears in its first window"*.

**Add a row whenever the manuscript names a case. Never delete one.** The harness is only as good as its
coverage, and its value is entirely that it is cheaper than being wrong.

## 5. What this costs and what it does not buy

G3 and G4 are one line each. G6 is one command. G5 and G7 need the instrument read rather than trusted,
which is the expensive one — and the one that caught the word enumeration only after a full day.

It does not buy correctness. The register's §1 warning stands: **a misplacement wears the framework's
own word**, so no grep finds it. G3 is the only gate aimed at that, and it works only if the reduction
is actually carried out to a number, not gestured at.
