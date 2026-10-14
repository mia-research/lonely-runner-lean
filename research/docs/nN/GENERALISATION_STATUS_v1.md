# General-`n` line: status

2026-09-13. Tree `LonelyRunner/LRC/ConstructionN/`, gate `scripts/nN/gate.sh`.

**RING-FENCE.** The `n = 8` paper cites `LRC/Construction8/`, which is frozen. Its digest
is `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d` and is unchanged by
everything below. `scripts/n8/gate.sh` still passes at 85 theorems.

---

## 1. Where it stands

**104 theorems, 34 headline declarations axiom-clean, no `sorry`, part 7 unstated.**

| | status |
|---|---|
| Parts 1, 2(a), 3, 4, 5, 6(a), 6(b), 6(c) | at general `n`, machine-checked |
| The six forms that carried `n = 8` | generalised, with `n = 8` instantiation checks |
| Part 2(b), the external dependency | **derived at general `n`** — no longer cited |
| Thm 7.1, soundness | still assembled from parts, not one declaration |
| Part 7, the Claim | **not stated, deliberately** — the gate fails if it is |

No statement in the tree is fixed at `n = 8`. A literal scan returns two hits, both the
`4 < n` hypothesis rather than a constant.

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

## 5. What is left

1. **Thm 7.1 as a single declaration.** Soundness is currently assembled from the formalised
   parts rather than stated once. The manuscript's §8 table marks it `partial`, correctly.
   This is a formalisation gap, not a mathematical one, and it is not part 7.
2. **§6.1 at general `n`.** The negative result — that no argument bounding how little the
   obstructions amount to can work — rests on the arithmetic progression's reading being a
   finite set. §2 now supplies that at general `n`, so §6.1 generalises; stating it in Lean
   means formalising the per-runner reading, not just global isolation.
3. **The reach law above `n = 24`.** Untested. The `φ`-classes available past there
   (`φ = 16` at `n = 32, 40, 48, 60`) would extend the matched comparison considerably.
4. **Part 7.** Open, deliberately unstated, and untouched by any of the above.

Nothing in items 1–3 bears on whether LRC holds at any order.
