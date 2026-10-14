# The n = 8 Framework — Cheat Sheet

**T. Palelei.** v1, 2026-09-18. Written to be read first, or pasted at the top of a session.
Sources: `OBJECT_REGISTER_v3.md`, `OBJECTION_LEDGER_v1.md`, `MANUSCRIPT_v9_6.md` §6A, and the
owner's rulings of 2026-09-14, 09-15, 09-17 and 09-18.

---

## 0. If you read nothing else

> The framework fixes **one runner at a time**, reads the other seven against it, and runs a
> **cascade fixed by the speeds** from the instant `1/(8·d_min)` to a **named instant**.
> It does not search, does not measure, does not cover, and does not pin any runner to zero.
>
> **Before naming a problem, name the object it is about.** If the object is not in §2, the
> problem belongs to your model of the construction, not to the construction.

---

## 1. What is being produced

For each of the eight runners separately: **an instant at which that runner is lonely.** Not a
proof that one exists — the instant itself, computed.

That is the type difference from every other approach. An existence argument concludes that some
point survives; this names which. It is why covering and candidate-counting are refused **by type**
rather than as unsuccessful.

---

## 2. The positive list — the objects the framework owns

| object | what it is |
|---|---|
| **Gaps** | the **eight cyclic gaps between runners on the track**, summing to 1. Theorem 4.1: lonely ⟺ both flanking gaps `≥ 1/8`. This is the framework's only gap condition |
| **`d_min`** | the smallest speed disparity, from the two speed-**neighbours** (speed order, not track order) |
| **Readings** | `s_j = d_j/d_min ≥ 1`. **All seven are evaluated**, the `d_min` reading and the second neighbour's included |
| **Laps** | `u = d_min·t`; phase `s_j·u mod 1`; clear ⟺ phase in `[1/8, 7/8]` |
| **Zones** | **open** intervals where one reading is in the way, one per lap, width `1/(4s)`; clear intervals between them, closed, width `3/(4s)` |
| **The band identity** | at `1/(8D)` a reading `s` is in the way ⟺ `s` is within 1 of a multiple of 8. **Real-valued, every `D > 0`** |
| **The clearing test** | the integer form of the same thing: `D ≤ (a·e mod 8D) ≤ 7D`. Used when readings are rational |
| **The ideal** | the arithmetic progression. Every arrangement = ideal of some gap `D` + deviations in `[0, D)` |
| **Gap `D` of the ideal** | **a scale — a positive real.** Not an integer, and not a track gap |
| **Spine** | the instants `r/(8D)`, `r` odd. `r = 1` is the first spine point |
| **The bound** | `1/(8·d_min)`, the first spine point at the subject's own scale. Where the cascade starts |
| **Opening** | `(k + 1/8)/d` — one eighth past a lap line of disparity `d` |
| **The move** | to the **largest** next opening among the runners in the way; `t` unchanged if none is |
| **The cascade** | the sequence of moves from the bound. **Scales decrease**, `D_{j+1} = D_j·s/(8N+1)` with the factor below 1 |
| **Flank** | one of the subject's own disparities, hosting openings. At its `k`-th opening only the **ratios** `d_j/e` enter |
| **The output** | **an instant** |

---

## 3. The three outcomes — settled, do not re-litigate

| | statement | status |
|---|---|---|
| **Construction** | a fixed point of the cascade is lonely, is the **first** lonely instant, ends the run of lap-completion zones from the bound, and has a flank at exactly one eighth | `[PROVED]`, in Lean |
| **Localisation** | every lonely instant is at or after every cascade step, and is matched by a lonely opening no later than it | `[PROVED]`, in Lean |
| **Existence** | the cascade reaches a fixed point | **`[OPEN]`** at order 8 |

**Corollary 6.4 is the hinge**: lonely somewhere ⟺ cascade arrives ⟺ the zone run ends ⟺ some flank
has a lonely opening. All four are the same statement. Closing any one closes it.

---

## 4. The bans, each with what to say instead

A ban is not a deletion where the framework has an object. Substitute, do not just remove.

| do not bring in | say instead |
|---|---|
| **a window** / first lap / "how long" / "when does it fall" | nothing — evaluation is over every lap, and no result needs a bound on when |
| **density, measure, zero-measure, stability radius** | the zone geometry and exact arithmetic. The progression's lonely set has length zero and the framework still names `t = 1/8` there |
| **covering, union bounds, complements, "the set is empty"** | the cascade runs to a named instant. Proofs are pointwise |
| **a stationary runner**, pinning `v_1 = 0` | read `v_j − v_i`. That *is* what "`i` is lonely" means. Pinned enumerations carry a caveat |
| **a global clock / simultaneity** | each runner gets its own instant in its own `u`. (The slowest speed does define a cycle — the owner's qualification) |
| **blocking** (as a word) | **in the way** / **clear** — the `inWay` predicate |
| **a witness** | a point is **computed**. The output is the instant |
| **a carrier** ("which constraint is tight") | nothing — the construction never asks |
| **a search, candidates, a loop over `D` or `a`, termination** | the move is fixed by the runners in the way. Each step is one move. `D = p/(8t)`, so searching for the gap re-asks the output as the input |
| **"return the first one that passes"** | first-ness is a **proved property** of the output (Thm 6.2(b)), never a demand |
| **induction on `n` / LRC(7) / Weyl equidistribution** | nothing is cited from another order. The `φ(n)` law is derived in Lean from the framework's own objects |
| **`D ∈ ℤ`, `p ∈ {1,3,5,7}`, `a ≡ 1 (mod 8)`, the lap in the output** | all four are imported restrictions. Scales are real; the numerator is free; the instant is the output |
| **"the interior / no-interior split"** | that sorts by whether a density argument applies |
| **rule coverage read as reach** (81.9%, 66%, 86.8%) | those measure **explanation**. The object is **production** |
| **"Status: it is LRC(8) itself"** | state the outcome in the framework's objects. The conjecture is named **once**, afterwards, as a consequence |

---

## 5. The four tests — each decidable, each runnable unaided

**1. The object test.** Name the object before naming the problem. Not in §2 ⇒ the problem is yours.

**2. The vocabulary test** (owner, 2026-09-15 — the boundary of "no imports"):
> *Does the statement exist without the other literature, in your vocabulary alone?*

Applied to the **statement**, never to the machinery inside a proof. **Tools are fine; targets and
statements must stay native.**

**3. The false-blocker test** (ledger Part 4):
> If an objection is about **how long a search takes**, **how much of the space is covered**, or
> **when the instant falls** — it is a false blocker.

It rejects objections about a search the construction does not perform. It does **not** close
Existence.

**4. The tool-domain test.** Beside any limit, obstacle or bound, write **which tool produced it**,
then run the matching check:

| the limit came from | run this |
|---|---|
| periodicity / rationality | an exact irrational case (`ℚ(√2)`, decided by integer square roots) |
| an `ℕ`-typed Lean statement | find the real-valued declaration, or scope the claim to the type |
| a fixed or arbitrary scale | the determinator from the subject's own bound, on that example |
| a random sample | adversarial **plus** exhaustive search, script on disk, **before** the bound is stated |

Every one of these has fired. "Lattice needs rationals", "the dead lattice is about integers", "one
scale cannot decide" and "lattice gap ≤ 3" were all withdrawn the same day they were written.

---

## 6. The caution running the other way

Added because after the tools-versus-targets ruling, over-refusal became the live risk and cost real
work — the flank sum criterion and the half-integer pair Lean work sat deferred for exactly this.

- **Do not excise anything on the strength of a word.** "Pigeonhole", "residue", "count", "measure"
  appearing inside a proof is **not a finding**. Apply the vocabulary test and quote the statement
  you applied it to.
- **Pigeonhole and residue counts are admissible as tools** (owner, 2026-09-15). `exists_clear_step`
  argues by contradiction and is native; `exists_fixed_of_lonely` uses pigeonhole and is native.
- **The test that withdrew Props 6.10–6.11 was the index bound, not the tool.** They concluded a
  lonely opening exists without bounding where. `AdvanceBudget` stays excised not because it counts
  but because of what it **sums**: zone widths over the time they span.
- **Never withdraw a proved result because its proof uses a tool.** Reframing is not regrading.
- **An import found is excised and replaced, not labelled.** A labelled row still stands in the
  table and keeps being read as a result.
- **No pre-registration and no `experiment-designer` here.** CLAUDE.md §2's row is scoped to the
  BTC/secp work (owner, 2026-09-14: *"you don't need pre-registration for this work that was for
  btc"*). Grades do that job: `[PROVED]` / `[VERIFIED — scope]` / `[EMPIRICAL]` / `[OPEN]` — and
  grade the **observations about a result**, not only the result.

---

## 7. Word collisions that survive a grep

A misplacement wears the framework's own word, so searching for foreign vocabulary misses it.

| word | the framework's object | what it gets confused with |
|---|---|---|
| **gap** | the eight cyclic gaps **on the track** | the ideal's **scale** `D` — the sharpest error on the register |
| **neighbour** | **speed**-neighbour | track neighbour |
| **spread** | `W = v_8 − v_1`, a difference | `S = d_max/d_min`, a ratio |
| **slot** | which eighth a runner occupies | a synonym for "an eighth" |
| **7/4** | a union bound on blocked **time** | a statement about the eight track gaps (ruled 2026-09-18) |
| **candidate**, **window**, **predictor** | nothing — no object in the present framework | leftovers from the 2026-09-14 rule-based construction |

---

## 8. What on this page is dated

`OBJECT_REGISTER_v3.md` §0 describes the construction as of **2026-09-14** — a rule-based procedure
over lattice instants with **integer** scales and `4D` candidates per gap, and the cascade as
`SKETCH_v7` §7c's three tiers. Its entries for *candidates*, the *ceiling* `D ≤ 7·d_min`, the
*enlarged tier* and the *output pair `(D, a)`* describe that, not the present cascade. §2 above is
current.

**Use v2, not v1.** The register is append-only and its rows are never edited, so v2 carries every v1
row verbatim and adds two things: a banner before the §0 table saying it is a 2026-09-14 snapshot, and
**§0a, a supersession table** naming each dated row and what replaced it. v1 has neither, and read as
current it supplies exactly the candidate-and-loop apparatus that the register's own items 22–24
refuse.

Also current, and newer than most documents: **the target is `LRC.Spec.LonelyRunnerAt8`** on an
arrangement `v : Fin 8 → ℝ` injective (amended 2026-09-18). `ExistenceAt8`, on a difference set, is
retained and still proved sufficient, but is **not the target** — a `Finset` collapses duplicates
and discards the arrangement.
