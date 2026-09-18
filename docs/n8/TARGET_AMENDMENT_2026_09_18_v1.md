# Amendment: the target is the conjecture, not the difference-set form

2026-09-18. **Recorded decision by the author.** `Spec/Target.lean` requires that a different
statement be recorded as an amendment rather than slipped in as a correction. This is that record.

---

## 1. The change

| | |
|---|---|
| **was** | `ExistenceAt8` — `∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∃ s > 0, Lonely 8 ds s` |
| **is** | `LonelyRunnerAt8` — `∀ v : Fin 8 → ℝ, Injective v → ∀ k, ∃ t > 0, ∀ i ≠ k, 1/8 ≤ circDist (v i · t − v k · t)` |

`ExistenceAt8` is kept in the file: it **suffices** (`lonelyRunnerAt8_of_existence`, axiom-clean), and
everything proved against it still transfers. It is no longer what a proof must be a term of.

## 2. Why equivalence was not a reason to keep it

The two are equivalent given theorems already in the tree — the difference-set form exceeds the
conjecture only on `card ≤ 3`, which `exists_lonely_of_card_le_three` settles. **I treated that as
grounds to carry on in the difference-set form. That was the error.** Equivalent statements can demand
entirely different machinery, and this one demands more while offering less.

What `ExistenceAt8` requires that the conjecture does not:

- **Decidable equality on `ℝ`**, forced by `Finset ℝ`.
- **Duplicate collapse.** `|v i − v k|` can coincide for two runners; the `Finset` merges them, and
  the indexing — hence the arrangement — is destroyed before a proof begins.
- **`card ≤ 7` rather than eight runners**, which admits difference sets of `card ≤ 3` that *no*
  arrangement produces. Settling those cost a theorem the conjecture never asked for.
- **The arrangement itself.** Gaps, the AP structure, the coupling across the eight subjects (they
  share the 28 pairwise differences, each in exactly two sets), and "the subject and its two
  neighbours" are all arrangement-level and are **not expressible in `ds` alone**.

The last is the substantive one. Every mechanism the author has supplied this session — the two
neighbours, the AP's four isolation events, disparity, fast and slow blockers — is stated about
runners in an arrangement. The difference-set form discards the arrangement in its first step.

## 3. What this does and does not invalidate

**Stands.** Every theorem proved this session. They are statements about `ds` and remain true; via
`lonelyRunnerAt8_of_existence` they remain sufficient. The cascade, the flank criterion, the residue
form, the named instants, the disparity law, the two-neighbour characterisation — all unaffected.

**Changes.** What counts as arrival. A proof is now a term of `LonelyRunnerAt8`. Routes that need the
arrangement are now expressible; previously they had to be pushed through `ds` and lost their objects
on the way.

**Does not change.** The difficulty. The `7/4` wall, the unbounded naming scale and the covering
problem all live inside the conjecture as much as inside the difference-set form. This amendment makes
the right structure available; it does not make the problem smaller, and nothing here should be read
as progress on it.

## 4. Consequence for the doors

`ATTACK_SURFACE_v1`'s five doors are all stated in `ds`, and all reduce to `ExistenceAt8`. They
therefore remain **sufficient** for the target and are no longer **equivalent** to it: closing one
still proves the conjecture, but the conjecture may be provable without closing any of them, by a
route that uses the arrangement.

That is a widening of the attack surface, and it is the first one this session that came from fixing
the statement rather than from measuring.
