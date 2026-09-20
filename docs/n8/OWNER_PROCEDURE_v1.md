# The procedure, in its own objects — and what each proof owes

2026-09-13. n = 8, threshold 1/8. Written in the owner's procedure (`NEIGHBOUR_INTERVAL_v1` §1),
in the owner's objects: neighbours, gaps, laps, `d_min`. Supersedes the jump-chain framing of
`MOMENT_ITERATION_v1`, which that document had already superseded and which I re-introduced in
error.

**No "blocking" language.** The owner ruled it out as not a brick, and the procedure does not
need it: there is no walk, so nothing blocks anything.

---

## 1. The procedure

For runner `i`:

1. **From its two neighbours**, `m = d_min = min(v_i − v_{i−1}, v_{i+1} − v_i)`.
2. **One window.** `I = [1/(8m), 7/(8m)]`. In the lap coordinate `u = m·t` this is `[1/8, 7/8]` —
   **exactly the stretch on which the nearest runner is clear of the threshold.** It is three
   quarters of one base lap.
3. **Inside `I`, read the other six.** Runner `j` sweeps `(3/4)·s_j` laps across the window and is
   in the way only within `1/8` of one of its **lap lines**. The moment is the first point of `I`
   where nobody is on a lap line.

Step 3 is a finite reading, not a search: the lap lines are `u = k/s_j`, listed directly.

**BSM is mandatory at step 3.** The clear set has two kinds of piece — open intervals and
**isolated points where the gap is exactly `1/8`** — and they must be evaluated separately.
Merging touching closed zones destroys the isolated points and reports the AP's end runners as
never lonely. (I made exactly that error building this and caught it on the AP.)

## 2. The procedure run on the worked examples  `[VERIFIED — exact]`

| | runner | `d_min` | window `I` | lap lines in `I` | clear points | clear intervals | measure | moment `t*` |
|---|---|---|---|---|---|---|---|---|
| **AP** | r1 | 1 | `[1/8, 7/8]` | 21 | **4** | **0** | **0** | `1/8` |
| | r4 | 1 | `[1/8, 7/8]` | 9 | 12 | 6 | `1/3` | `1/8` |
| | r8 | 1 | `[1/8, 7/8]` | 21 | **4** | **0** | **0** | `1/8` |
| **r8→9** | r1 | 1 | `[1/8, 7/8]` | 22 | 12 | 6 | `9/160` | `9/64` |
| | r2…r7 | 1 | `[1/8, 7/8]` | 10–16 | | | | `1/8` each |
| | r8 | **2** | `[1/16, 7/16]` | 12 | 2 | 1 | `3/32` | `1/16` |
| **two blocks** | r1 | 1 | `[1/8, 7/8]` | 29 | 8 | 4 | `13/224` | `9/56` |
| | **r4, r5** | 1 | `[1/8, 7/8]` | **21** | **4** | **0** | **0** | `1/8` |
| **the wide one** | r1 | 4 | `[1/32, 7/32]` | 86 | 38 | 19 | ≈0.0919 | `49/752` |
| | r3 | 11 | `[1/88, 7/88]` | 19 | 8 | 4 | ≈0.1173 | `1/88` |

**The AP signature is `21 lap lines, 4 clear points, 0 clear intervals`** — and runners r4, r5 of
`[8,9,10,11,15,16,17,18]` carry it exactly. They *are* APs, based at 11 and 15 rather than at 1.
Zero measure is the AP's fingerprint, not a difficulty.

`d_min` and nothing else converts the window to real time: the same `u = 1/8` gives
`t* = 1/8, 1/16, 1/88` across these rows.

---

## 3. What is proved, and what each proof owes

Kept strictly separate. **These do not compose into a proof of n = 8** and must not be summed as
though they did; they cover different regions and leave the main one open.

### Block A — self-contained. Owes nothing outside itself.

| | statement | owes |
|---|---|---|
| A1 | Runner `i` is lonely iff both its cyclic-adjacent gaps are `≥ 1/8`. There are no end runners. | the circle's ordering |
| A2 | `Σ_k g_k = 1` at every instant. | circumference |
| A3 | `#lonely = |A| − c(A)`, `A` = gaps `≥ 1/8`, `c` = cyclic runs. | A1 + adjacency counting |
| A4 | φ(8) law: all eight lonely ⟺ every gap exactly `1/8`. | A1 + A2 — **derived, not cited** |
| A5 | `m = d_min` is one of the two adjacent gaps, exactly. | sortedness of speeds |
| A6 | Nothing happens before `t = 1/(8m)`. | `‖x‖ = x` for `x ≤ 1/2` |
| A7 | The window `I` is exactly the nearest runner's clear stretch. | A6 |
| A8 | Band identity: at `u = 1/8`, runner `j` is in the way iff `dist(s_j, 8ℤ) < 1`. | arithmetic on `ℝ/8ℤ` |
| A9 | Spine: `u = p/8` (`gcd(p,8)=1`) serves every `j` with `dist(s_j p, 8ℤ) ≥ 1`. | A8 |
| A10 | Grid theorem: grid with `d_min = g` throughout ⟹ every moment `1/(8g)`. | A8 + distinct residues |

Block A is closed, all real speeds, no external citation. **It does not prove n = 8.** It
determines the window, the lap lines, and settles every runner for which the spine serves.

### Block B — owes Weyl's equidistribution theorem.

| | statement | owes | covers |
|---|---|---|---|
| B1 | If the seven differences are `ℚ`-linearly independent (no grand return), the runner is lonely on a set of frequency `(3/4)^7 = 0.1335`. | **Weyl** (external, classical, not LRC) | all incommensurable configurations |

Verified: measured frequencies `0.1335, 0.1299, 0.1326, 0.1330` against `(3/4)^7 = 0.13348`.

**The debt is to a classical theorem outside this subject.** It is not circular. But it is a
different kind of argument from Block A — density, not counting — and the two must not be spliced.

### Block C — owes LRC(7).

| | statement | owes | covers |
|---|---|---|---|
| C1 | Integer `s` with `gcd(s_2,…,s_7) = c ≥ 2` ⟹ the moment exists. | **LRC(7)** (a different case of the same conjecture) | 1.5% of integral-`s` runners |

Not circular — LRC(7) is independently established (Barajas–Serra 2008, axiom-clean in our Lean
tree). But it is a debt **inside the conjecture**, and the owner has flagged unease about it. The
proof works because `c ≥ 2` widens the window to `3c/4 ≥ 1`, a full lap, where periodicity applies.

## 4. What is left, stated in these objects

Commensurable speeds, `gcd(s_2,…,s_7) = 1`, and at least one runner on a lap line at `u = 1/8`.

> **Open.** The lap lines of the six other runners never cover the whole window `I`.

Nothing in Block A bounds this; Block B does not apply (there is a grand return); Block C does not
apply (`c = 1`). This is the region the AP itself sits in, and it is where the spikes of
`TRANSIT_MAP_v1` §2 are.

## 5. Ledger

`[PROVED]` A1–A10, all real speeds, self-contained.
`[PROVED — owes Weyl]` B1.
`[PROVED — owes LRC(7)]` C1.
`[OPEN]` §4.
`[VERIFIED — exact]` §2's table.

**n = 8 is not proved here.** Blocks A, B, C cover disjoint regions and leave §4 open. Summing
their coverage would be a mix-and-match error: A settles cases, B settles a class by a density
argument, C settles a class by an induction on `n`. They are three arguments, not one.
