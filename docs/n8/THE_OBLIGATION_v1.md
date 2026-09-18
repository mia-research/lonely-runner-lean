# The one obligation, and every route that has failed against it

2026-09-18. Written because the same question — *what stops us proving Existence?* — has been
answered with a different-sounding thing each time. This file exists so that cannot happen again.
It has one obligation and one table.

---

## 1. The obligation has never moved

It is a Lean `Prop` in `LRC/Spec/Target.lean`, and it is byte-stable across every commit that has
ever touched that file:

| | `ExistenceAt8` | `CascadeCapped` |
|---|---|---|
| `6dad65f` (frozen) | `bcae7dc84b80ff09` | — |
| `48676d6` | `bcae7dc84b80ff09` | `064a4f4c8bbc9463` |
| `60c75f1` | `bcae7dc84b80ff09` | `064a4f4c8bbc9463` |
| HEAD | `bcae7dc84b80ff09` | `064a4f4c8bbc9463` |

```lean
def CascadeCapped : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
    ∃ U : ℝ, ∀ N : ℕ, (move 8 ds)^[N] (1 / (8 * m)) ≤ U
```

**What would close it: a term of that type.** Nothing else, and nothing less. `existence_of_capped`
and `capped_of_existence` prove it equivalent to `ExistenceAt8` in both directions, so it cannot be
weakened by restatement, and `target_forms_agree` blocks substituting a different wording.

## 2. What has actually been changing

Not the obligation. **My account of why each attempted route dies.** Each entry below is a reason a
*route* failed. **None of them is the obstruction.** Reporting them as though they were is what made
the target appear to move, and that is a fault in the reporting, not in the target.

| # | route | why it fails | status |
|---|---|---|---|
| 1 | measure / union bound | 7 zones × 1/4 = 7/4 > 1; vacuous | closed |
| 2 | continuity | dies on `lonely_iff_exists_flank` being an **iff** | closed |
| 3 | the naming form `∃ f` | choice proves it equivalent to `ExistenceAt8`; measured nothing | closed |
| 4 | Props 6.10–6.11 | pigeonhole attached to no rule, so no index bound | withdrawn |
| 5 | potential `Ψ` / move counting | dies at `2k < n`; coefficient −0.75 at `n=8, k=7` | closed |
| 6 | depth floor as a cap | `(2−8c_*)·C_lap ≥ 1` is **forced**, termwise, for any true inputs | closed |
| 7 | residue route | gives a decision procedure per `ds`; the target quantifies over infinitely many, and the per-flank finite problem is indexed by unbounded `b` | banked, not a route |
| 8 | `n=4` window invariant `τ ≤ 7/8` | **false** at `n=8` — named cases reach `τ = 1.283`. Also never a framework requirement | closed |
| 9 | nearest-clear invariant | **false** at `n=8` — named cases have the nearest in the way, and setting, once | closed |
| 10 | scale-free word condition | satisfiable by an infinite word (frequency argument; explicit round-robin witness) | closed |

## 3. What is banked, and why it does not close it

Real, in Lean, axiom-clean — and each falls short for a stated reason, not a vague one.

| theorem | what it gives | why it is not enough |
|---|---|---|
| `clear_at_int_flank_iff_emod`, `lonely_iff_emod_search` | the criterion is an integer congruence; a finite decision procedure per `ds` | decides each case; discharges no universal |
| `depth_floor` | `δ ≥ 1/(n·b)`, tight | a floor on depth cannot cap growth — see route 6 |
| `return_needs_growth`, `return_needs_moves` | the return lemma with `hret` removed; works for any `g` | necessary condition, not sufficient — see route 10 |
| `lonely_of_fixed`, `lonely_iff_run_ends` | terminal ⟹ lonely, and the converse | the easy direction; the hard one is that a terminal time exists |
| lap law `Q = ρτ ± 1/n` | exact, 0 violations in 3,454 moves | descriptive; `τ` cancels in the return condition |

## 4. What the owner's corrections actually fixed

Also worth separating, because it has been blurred. Each of these was **right**, and each corrected
**an error of mine**, not the obligation — which is why fixing them does not advance termination:

- speed-rank is a convention — `ExistenceAt8` quantifies over `ds`, so arrangement facts add nothing
- not all seven speeds need a common `d_min`
- runners more than seven scales out are fine, because it is a circle
- the census is one criterion, not 4,413 facts
- `ExistenceAt8` is not a naming form and classical choice is irrelevant
- **"the first window" is not a framework requirement** — correct, and it is not; the nearest runner
  re-enters a clear window every lap
- laps grow with the disparity between the speeds — correct, and exactly: `Q = ρ·τ ± 1/n`

## 5. The standing rule

If a future session names something as "what stops us", check it against §1 first. If it is not
`CascadeCapped`, it is a route failing, and it belongs in the §2 table with its reason — not in a
sentence that reads as a new obstruction.
