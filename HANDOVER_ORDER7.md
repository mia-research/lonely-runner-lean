# Handover: from order 6 to order 7 (n = 7) in the framework

Written 2026-09-24 at the end of the order-6 session; updated when order 6 was completed. Branch `claude/manuscript-paper-cleanup-ropemz` of
`mia-research/lrc-n8-lean`.

## 1. Standing rules (the user's, keep them)

- "N=x obligation is equivalent to loneliness in both directions, unconditionally and = proof. Never import any
  foreign shape — cap, move count, uniform theorem."
- Reason, don't autocomplete. Don't look for the shape of an answer.
- Framework proofs exhibit the instant (a named `t`), not a `by_contra` covering, wherever possible.
- Exact arithmetic. Say **totients**, never "primes". "Primitivity is not native, but totients are and for the
  framework work better." Do not add `gcd = 1` hypotheses; the order-6 ports dropped every one (none was used).
- No `sorry`, no `native_decide`. Axioms must be exactly `[propext, Classical.choice, Quot.sound]`.
- Australian English, concise replies, run the code and give a brief summary in chat. No documents unless asked.

## 2. Setup

| repo | role |
|---|---|
| `mia-research/lrc-n8-lean` | the work. Push here, branch above. |
| `mia-research/lonely-runner-lean` | **source to translate** (read only). Add with `add_repo`, clone beside the work repo. |

Lean `v4.29.1`, Mathlib `v4.29.1`.

```bash
export PATH=$HOME/.elan/bin:$PATH      # install elan if missing
lake exe cache get
lake build LonelyRunner.LRC.Spec.<Module>   # one module; builds its oleans
lake env lean LonelyRunner/LRC/Spec/<File>.lean   # quick check of one file
```

- `LonelyRunner.lean` imports every module; add each new one there.
- Record axioms per unit in `experiments/nN/<unit>_axioms.{lean,out}` (`#print axioms <main theorem>`).
- Workflow: build and check the axioms, then commit locally, then push. Agents work in `git worktree`s on
  `local/<unit>` branches and commit there only. The lead verifies (build, `grep -w sorry`, axioms), merges and
  pushes. Run at most one extra `lake` process while an agent is building: memory is tight.
- Large ported proofs need `set_option maxHeartbeats 1000000 in` (or 2000000) placed **before** the docstring.

## 3. The framework toolkit (all in `LonelyRunner/LRC/Spec/`, all proved)

| module | what it gives |
|---|---|
| `OrdersThreeFourN` | `lonelyRunnerAtN_three`, `lonelyRunnerAtN_four` |
| `RankTwoN`, `ManyDirectionsN`, `RealFiveN` | order 5 for **all real speeds**: rows over a ℤ-basis of the span (`exists_rows`), model direction with an exact merge, `existenceAtN_five`, `lonelyRunnerAtN_five`. **This is the template for real speeds at 6 and 7.** |
| `SteppingN` | `exists_step_near`: pigeonhole returns span ℚ^{d+1}, round down. Replaces Kronecker density. |
| `MergeN`, `MirrorN` | merge rule; mirror merge `(a+b)t ∈ ℤ ⇒` runners `a`, `b` read equally; `lonely_of_mirror_band` (residue-band check at `K/q`) |
| `OrderSixN` | whole-number order 6 by framework rules, `lonely_six_or_residual` |
| `OrderSixSevenN` | orders 6 and 7 side by side: `orderSeven_obligation`, `lonelyRunnerAtSeven_of_doorFlank`, `seven_card_le_four`, `lonely_seven_of_not_dvd`, `prime_at_most_one_multiple` (modulus 7 is a totient-full modulus, every residue ≠ 0 is a unit) |
| `WindowTwoN` | two-flank window (BHK Lemma 4): `two_flank_window`, `blocked_cover_short` |
| `GlobalIsolationTwoN` | global isolation in 2D (BHK Main Lemma, Cor 6, Lemma 7): `isolation_or_short_step`, `orbit_isolation_two_bhk`, `order_bound_of_minimal` |
| `OrderSixEightN` | BHK §8 (`v₃ ≤ 3v₁`): `lonely_8`; `window_or_inside`, `step4`, `clear_of_lap` |
| `OrderSixSecSevenN` | meeting-time window: `lonely_of_meeting`, `lonely_of_meeting_nat` (exact merge of runners 2, 3 at `τ = k/(v₃−v₂)`) |
| `OrderSixSecSevenCasesN` | BHK §7: `lonely_7` |
| `OrderSixFiveLayerN` | `IsBHKLift` and adapters that derive BHK's ℝ²-group lemmas from `GlobalIsolationTwoN` |
| `OrderSixPropElevenN`, `OrderSixSecFiveN` | BHK Prop 11 and §5 (`D ∣ v₁`): `S7.lonely_5` |
| `OrderSixSixN` | BHK §6 (`D ∣ v₃`, `D ∤ v₁`): `lonely_6` |
| `OrderSixWholeN` | dispatcher: `lonely6_of_lt` (the four BHK cases cover every `v₁ < ⋯ < v₅`), `lonely_six_nat` (≤ 5 whole numbers at `1/6`) |
| `MergeFiveN` | `exists_merge_model_five`: exact merge for five rows. Coordinates `pA`/`pB` against a non-parallel pair `u`, `v`; blockers `p ∥ u − v`, `q ∥ u + v`; the fifth row would have to follow two non-parallel directions |
| `RealSixN` | **`existenceAtN_six`, `lonelyRunnerAtN_six`: order 6 for all real speeds** |
| `NamedWindowSixN` | `lonely_of_123_window`: a window where runners 1–3 are clear, lonely at a named instant (G4/G7) |

`Lonely6 v1 … v5 t` is the order-6 predicate for five explicit ℕ speeds at `1/6`. Define `Lonely7` the same way.

## 4. Order 6: complete

`LRC.OrderSixN.lonelyRunnerAtN_six : LonelyRunnerAtN 6` is proved for every injective arrangement of
real speeds, axioms `[propext, Classical.choice, Quot.sound]` (`experiments/nN/order_six_real_axioms.out`).
The full `lake build` passes.

How it is assembled (template for order 7):
- **One commensurability class** (all rows parallel, i.e. whole multiples of one unit): `lonely_six_nat`, which
  dispatches on BHK's cases with `D = v₃ − v₂`: `v₃ ≤ 3v₁` → `lonely_8`; else `D ∣ v₁` → `lonely_5`;
  else `D ∣ v₃` → `lonely_6`; else `lonely_7`.
- **Several classes**: `exists_merge_model_five` gives ≤ 4 distinct readings, `existenceAtN_five` clears them at
  `1/5`, and `lonely_of_model_many (n := 6)` carries that to the real speeds at `1/6`.
- No primitivity (`gcd`) hypothesis anywhere.

Still open at order 6 (form, not truth):
- **Named instants.** Done for G4/G7: `NamedWindowSixN.lonely_of_123_window` names the instant on BHK's 123-window
  (two-flank window if the window is ≥ `2/(3v₄)`; else runner 4's clear stretches with runner 5's opening;
  else runner 5 at the window's ends, its opening after `A` and closing before `B`; else block counting forces
  `2v₄ < v₅`, `7v₅ < 16v₃` and `t = 2/(3v₃)` is lonely), with `t* = 1/(6v₁)` when `v₅ ≤ 5v₁`
  (`S7.bhk_s7_named`). BHK's covering helpers (`bhk_g4_single_block`, `bhk_g4_flanking`, `bhk_g4_five_v1`)
  are deleted. Still by covering: parts of the ported Prop 11 (`OrderSixPropElevenN`, ≈17.6k lines, largely
  BHK's body behind adapters) and §5's use of `block_length_bound`/`block_containment`.

## 5. Order 7: what to translate

Source: `lonely-runner-lean/LonelyRunner/LRC/SmallN/`.

- `IntLRC_7.lean` (`intLRC_seven`) splits on the fastest speed `V = v₆`:
  - `V ≤ 6v₁`: `Theorem61_BSR` (`LonelyRunner/LRC/Theorem61_BSR.lean`), instant `bsr_time 7 v₁`.
  - `6v₅ < V`: `Theorem71_LargeSR` (one fast runner over an order-6 set).
    It takes `H_seven`, which calls `intLRC_six`. Use `lonely_six_nat` (framework order 6) instead.
  - hard case: Barajas–Serra 2008, `IntLRC_7_BS/Main.lean` (`barajas_serra_seven`), ≈12k lines in
    `IntLRC_7_BS/`. BS proves all six-speed sets outright, so the hard-case bounds are not needed.
- BS structure, and where each part sits in the source:
  - `Reduction.bs_discrete_q`: the witness `t = λ/(7P)`, band `P ≤ λd mod 7P ≤ 6P` for every `d`.
    The dispatch runs on the 7-adic levels `7^j ∥ d`.
  - `PrimeFiltering`: `prime_filtering`, `corollary3` (easy branch: every level below the top has ≤ 3 elements).
  - Hard branch (a level with ≥ 4 elements): `Case_A4`, `Case_A5` (6k lines, `decide` tables over `ZMod 7`),
    `Section5*`, `Lemmas7_9`, `Lemmas10_12`, `Section7_*`. §7 needs `P = 14`, so the modulus is `98`, not a
    power of 7.
- Status of the source: the doc comments in `Main.lean`/`IntLRC_7.lean` still say "single remaining `sorry`".
  A grep finds **no `sorry` token** in `IntLRC_7*`, `Theorem61_BSR` or `Theorem71_LargeSR`, so those comments
  look stale. Before relying on the source, run `#print axioms intLRC_seven` in `lonely-runner-lean`
  (`sorryAx` must not appear). Also check that the source uses no `native_decide`.

### Suggested translation units (same pattern as order 6)

1. **Residue-band instant at modulus 7P**: the band `P ≤ λd mod 7P ≤ 6P` is exactly `lonely_of_mirror_band`
   with `q = 7P`, `n = 7`. Write `lonely7_of_band` so every BS case ends by naming `t = λ/(7P)`.
2. **Filtering by 7-adic level (totients)**: port `prime_filtering`/`corollary3` as a statement about units
   mod 7 (`ZMod 7`ˣ, φ(7) = 6 choices of `λ`), avoiding at most one bad residue class per element per level.
   No `gcd` hypothesis. Normalise by dividing out the common power of 7 instead.
3. **Regime `V ≤ 6v₁`** (`Theorem61_BSR`): the named instant `bsr_time`. It should already be framework-shaped.
4. **Regime `6v₅ < V`** (`Theorem71_LargeSR`): a fast runner over an order-6 set. It reuses order 6 plus
   `FastRunnerN`.
5. **BS hard branch**: `Case_A4`, `Case_A5`, §5, §7. Keep the `decide` tables over `ZMod 7` as they are. They
   are exact residue checks, i.e. framework instants.
6. **Dispatcher** → `lonely_seven_nat` (≤ 6 whole numbers at `1/7`), then real speeds as in `RealSixN.lean`:
   rows, one class → `lonely_seven_nat`, several classes → a **six-row merge** + `existenceAtN_six` + 
   `lonely_of_model_many (n := 7)`.
   - The six-row merge needs a new argument: `MergeFiveN`'s proof uses that only one row is left over, and with six
     rows two rows are left over. A brute-force search (entries up to ±3 in two dimensions) found no blocked
     six-row set, so the lemma looks true. Prove it on paper first.

Port by copying the source bodies, then change the namespace and swap BHK/BS-specific lemmas for framework ones
through adapters (see `OrderSixFiveLayerN` for the pattern). Section 6 has the gotchas.

## 6. Gotchas met at order 6

- `field_simp` may close the goal outright, so a following tactic errors with "no goals". Use `field_simp` alone
  or `field_simp; linarith`.
- `set_option … in` must come before the docstring.
- `Fin` literals inside `decide`: use `Fin.mk` with `Fin.mk_lt_mk`, not `⟨2, by omega⟩`.
- Mod lemmas: `Nat.mul_mod_mod`; `Int.add_emod_right` (not `Int.add_emod_self`).
- `rw [h x]` can hit the `x` inside another term; use `conv_lhs`.
- Scripts that cut and port source (`cut.py`, `cut5.py`) were in the old session's scratchpad and are gone.
  Re-write them as needed: slice the source by line ranges, rename the namespace, delete the replaced lemmas.
