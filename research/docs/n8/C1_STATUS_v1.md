# C1 — where it stands

2026-09-15. **C1 is not proved. Neither branch of it is.** This records what is closed, what is
not, and how much of the population each covers — including the part that deflates the session's
own result.

C1: every runner's isolation space empties at some instant. By `LEMMAS_v2` L8 it splits on
**reading integrality** — whether `d_min ∣ d_j` for all `j`, so that every `s_j = d_j/d_min` is an
integer.

---

## 1. What is settled by construction

By construction means: an instant is named, with a proof, without searching. Measured over 24,000
runner-instances, random integer 8-sets in `[0, 600)`:

| route | share |
|---|---|
| the ratio condition `d_max ≤ 7·d_min` | **29.8%** |
| spine alive (integral reading, no `s_j ≡ 0 mod 8`) | 1.0% |
| the residue-blocked construction (`C1_INTEGER_CONSTRUCTION_v1` §2 and its reduction) | 0.6% |
| window-widening, `gcd ≥ 2` | 0.03% |
| **settled** | **31.4%** |
| **open — mixed reading** | **68.0%** |
| **open — integral, residue-blocked** | 0.6% |

## 2. The deflating fact, stated plainly

**The integral branch is a small population at large span.** At `[0,600)` only about 2.2% of
runners have an integral reading at all, so everything in the C1-integer line — including this
session's construction — is settled *within* a slice that is itself small. The construction closes
51.1% of the residue-blocked integral population, and that is **0.6% of all runners** at this span.

It is not small at every span. `GRID_REFERENCE_REACH_v1` §2 measures the same hypothesis
directly: `d_min` divides all differences for 0.888 of runners at `[1,12)`, 0.329 at `[1,40)`,
0.074 at `[1,200)`, 0.024 at `[1,600)`. So:

> **C1-integer is the dominant population at small span and a marginal one at large span.
> C1-mixed is the reverse.** Which branch matters depends entirely on where you look.

And what actually carries the settled column at large span is not any of this session's work — it
is the ratio condition `d_max ≤ 7·d_min`, which was already proved.

## 3. C1-integer

**No localisation surplus.** The reading is 1-periodic and `s_1 = 1` confines every isolation
instant to `[1/n, (n−1)/n]` mod 1, so *isolated somewhere* and *isolated in the first window* are
the same statement (`Construction8.localisation_free`). C1-integer is therefore exactly LRC(`n`)
restricted to integral readings — no more.

**Closed:** spine alive; `gcd(s_2…s_7) ≥ 2` via window-widening; the ratio condition; and the
residue-blocked construction — 51.1% of the residue-blocked population, with the clean form
(one blocked runner, the largest, residues missing one of `{3,5,7}`) proved and verified
16,117/16,117.

**Open:** the other 48.9% of residue-blocked cases, where the interval `(0, E]` is too short to
hold an opening of the blocked comb; and the two-or-more-blocked case, which is the same reduction
applied again.

## 4. C1-mixed

**Nothing is closed here beyond the ratio condition and the near-collision trigger of
window-widening**, and the latter needs a commensurable sub-pack to survive, which is the special
circumstance rather than the general one (`SKETCH_v6` §7d).

**And the localisation is a genuine extra demand here.** `localisation_free` does not apply — the
reading is not periodic, so an isolation instant in a later lap cannot be folded back. So the
surplus content of C1 over plain LRC(`n`) lives **entirely** in this branch.

This is 68% of runners at span 600 and it is where the work is.

## 5. Machine-checked

`LonelyRunner/LRC/Construction8/` — 29 theorems, zero `sorry`, no `native_decide`, all at
general `n`. Relevant to C1:

| | |
|---|---|
| `localisation_free` | §3's no-surplus statement |
| `spine_all_or_nothing` | the four instants stand or fall together for an integral reading |
| `circDist_int_div`, `circDist_int_div_of_dvd` | the spine test |
| `blocked_lands_on_threshold`, `unblocked_stays_clear` | the residue-blocked construction |
| `clear_periodic`, `periodic_meets`, `window_length` | window-widening |
| `reading_complete`, `clear_on_left`, `opening_le` | L3 |
| `dead_iff`, `dead_downward`, `exists_live` | the dead-step structure |

## 6. Status

`[PROVED]` the pieces named in §5.
`[VERIFIED]` §1's rates; §3's 51.1% and 16,117/16,117.
**`[OPEN]` C1.** Both branches. The integral branch is open on 48.9% of its residue-blocked cases;
the mixed branch is open outright and is the larger population at any span past about 40.

**n = 8 is not proved. C1 is not proved. The session's construction closes a sub-case of a
sub-case, and at large span that sub-case is 2% of runners.**
