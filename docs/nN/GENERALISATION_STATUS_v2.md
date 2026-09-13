# General-`n` line: status

2026-09-13, v2. Tree `LonelyRunner/LRC/ConstructionN/`, gate `scripts/nN/gate.sh`.

**RING-FENCE.** The `n = 8` paper cites `LRC/Construction8/`, which is frozen. Its digest
is `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d` and is unchanged by
everything below. `scripts/n8/gate.sh` still passes at 85 theorems.

---

## 1. Where it stands

**120 theorems, 48 headline declarations axiom-clean, no `sorry`, part 7 unstated.**

| | status |
|---|---|
| Parts 1, 2(a), 3, 4, 5, 6(a), 6(b), 6(c) | at general `n`, machine-checked |
| The six forms that carried `n = 8` | generalised, with `n = 8` instantiation checks |
| Part 2(b), the external dependency | **derived at general `n`** — no longer cited |
| Thm 7.1, soundness | **stated once**, `Soundness.lean` |
| §6.1, §6.2, §6.3, §9 | at general `n`, with the `n = 8` numbers derived |
| Part 7, the Claim | **not stated, deliberately** — the gate fails if it is |

**The generalisation of the manuscript is complete.** A mechanical audit of the 27 Lean
declarations named in the manuscript's §8 table finds all 27 present in `ConstructionN`, and
a literal scan finds **no** theorem in the tree fixed at `n = 8` outside the deliberate
`n8_*` instantiation checks.

---

## 2. Part 2(b), derived

The manuscript's §5 records part 2(b) — the `φ(n)` count of global-isolation instants for
an arithmetic progression — as the framework's **sole external dependency**. `Instants.lean`
derives it at general `n` from the framework's own objects, in two halves.

**On the grid.**

| | |
|---|---|
| `spine_iff` | at `t = p/n`, pairwise separation is non-divisibility |
| `spine_iff_residues` | with `p` coprime to `n`, that is residue distinctness |
| `break_of_not_coprime` | `gcd(p,n) > 1` stops the residue map being a permutation, so a pair collides |
| `isolation_iff_coprime` | isolation at `p/n` **iff** `gcd(n,p) = 1` |
| `card_coprime_eq_totient` | and there are `φ(n)` such `p` |

**Off the grid — that no other instant works at all.**

| | |
|---|---|
| `int_of_forall_int_mul` | Bézout: if `e i · y ∈ ℤ` for every `i`, then `gcd(e) · y ∈ ℤ` |
| `instants_on_grid` | isolation at **any real** `t` forces `n·t ∈ ℤ` |
| `coprime_of_isolation` | and that integer is coprime to `n` |
| `isolation_forces_coprime_grid` | the two together |

Two things are worth recording about the proof. `int_of_forall_int_mul` needs no rationality
of `y` — Bézout does the work directly on the reals, which is why the step is one induction
rather than a denominator argument. And **primitivity is load-bearing in exactly one place**,
`instants_on_grid`: without `gcd(e) = 1` the conclusion is false, and the theorem says so.

`instants_hypotheses_satisfiable` exhibits a configuration meeting every hypothesis of the
capstone, so none of this is proved from hypotheses that cannot hold.

**Scope.** This says *where* global isolation can occur once it occurs. It does not say that
it occurs, and it does not approach part 7.

---

## 3. Thresholds in `n` that `n = 8` could not show

Generalising surfaced two hypotheses with no counterpart in the `n = 8` statements.

| | threshold | what happens below it |
|---|---|---|
| single-reading exclusion, `2/(ns′) < (n−2)/(nσ)` | `n > 4` | at `n = 4` the two sides coincide; the exclusion is vacuous |
| clear interval, `(n−2)/(ns)` | `n > 2` | at `n = 2` the zones tile with nothing between them |

Both are now stated as theorems rather than left as remarks. At `n = 8` each is discharged
by arithmetic, which is why neither left a trace in `Construction8`.

The other four general forms hold for every `n ≥ 1`.

---

## 4. Empirical: the `φ(n)` reach law

`docs/nN/PHI_REACH_SCALE_v1.md`. `φ(n)` sets the ordering of spine reach and `n` does not —
`n = 24` beats `n = 12` by `0.108`, about 85 clustered standard errors, in the direction a
count-of-readings account forbids. Three controls qualify it: coprimality is load-bearing;
the spine's advantage over arbitrary window instants reverses by `φ = 10`; and the `φ(n)`
shots are heavily correlated, `k_eff` saturating near 3. Every one of 5,608 spine misses has
an exact isolation instant elsewhere in the window.

All `[EMPIRICAL]`, scoped to two speed populations and `n ≤ 24`.

---

## 5. What was added after v1

**Theorem 7.1 stated once** (`Soundness.lean`), closing the `partial` in the manuscript's
§8 table. Writing it surfaced two things the assembled version could not show:

- **Minimality of `d_min` is not needed for soundness.** The proof needs only that `dmin` is
  the distance to *some* runner; any runner closer in has a reading below `1` and is covered
  by the clearance hypothesis anyway. Minimality is what makes the window the right place to
  search — a completeness property — not what makes a returned `u` correct.
- The subject's index need not be in range. The hypothesis is carried for the statement's
  sake and is unused.

**§6.1 at general `n`** (`ap_reading_finite`). The arithmetic progression's reading inside a
period is finite, so no argument bounding how little the obstructions amount to can reach
it, at any `n`. `ap_pairwise_of_subject` records *why* one runner's reading and global
isolation coincide for the AP and not in general: its difference set is the same seen from
any runner.

**§6.2, §6.3 and §9 at general `n`** (`Negative.lean`). All were prose-only.

| | general form | at `n = 8` |
|---|---|---|
| §6.2(2), lap `k` against lap `k'` | `(nk′−1)s < (nk+1)s′` | `9/7`, `17/7`, `25/7` |
| §6.2(4), `s = n` blocks both ends | `n·(1/n) = 1`, `n·((n−1)/n) = n−1` | `s = 8` |
| §6.3, the fragmentation | `n−1` zones, `n−2` gaps of width `(n−2)/n²` | seven, six, `3/32` |
| §9, overlap bound | `(n+1)/(n−1)` strictly decreasing, never `1` | `9/7` |
| §9, exclusion | `2σ/(n−2)` strictly decreasing | `σ/3` |

The `n = 8` numbers are **derived from the general forms**, not restated beside them.

Generalising a refutation generalises the refutation. **None of §6 bears on whether the
conjecture holds at any order.**

---

## 6. What is left

**Generalisation of the manuscript is finished.** What remains is not generalisation:

1. **Part 7.** Open, deliberately unstated. The gate fails if any declaration in the tree is
   named for it.
2. **The settled cases of §7.3** — the ratio condition, the all-grid case, the runners no
   reading of which lies within `1` of a multiple of `n`. These are conditional partial
   results *towards* part 7 rather than statements of it, so they are stateable; whether
   they should be is a decision about the plan's §2 reasoning, not a technical question.
3. **Empirical work.** The reach law is measured on two populations to `n = 60`. The
   finding that the grid's arithmetic beats an equal number of arbitrary instants **only at
   `n = 8`** rests on those two populations and would bear widening.

No item above bears on whether LRC holds at any order.
