# Foundations audit — is anything else sitting where termination was

*Version 2026-09-20. Termination was an obligation the conjecture did not carry, sitting unexamined
because it always answered. This checks the rest of the foundations for the same shape, by reading
the definitions and the actual hypotheses of the load-bearing theorems rather than their prose.
One claim was in that category. It survives, for a reason stronger than the evidence offered for it.*

---

## 1. Method

For each foundation: the definition or the theorem's hypothesis list, read in Lean; then two
questions. **Does it demand more than the conjecture does** (the termination failure), and **does it
quietly restrict what it ranges over** (unsoundness). Verdicts are per item.

## 2. The definitions

| object | definition | verdict |
|---|---|---|
| `circDist x` | `min (Int.fract x) (1 - Int.fract x)` | **clean.** The circle metric; even, so `\|·\|` on disparities is free |
| `sep v k i t` | `v i * t - v k * t` | **clean.** A separation between two moving runners; nothing is pinned at `0` |
| `InWay v k i t` | `circDist (sep v k i t) < 1/8` | **clean** |
| `LonelyAt v k t` | `∀ i ≠ k, 1/8 ≤ circDist (sep v k i t)` | **clean.** Closed threshold `≥ 1/8`, correct for eight runners |
| `LonelyRunnerAt8` | `∀ v, Injective v → ∀ k, ∃ t > 0, LonelyAt v k t` | **clean.** Injectivity is the only hypothesis, and it is "distinct speeds" |
| `diffSet v k` | `(univ.erase k).image (fun i => \|v i - v k\|)` | **clean, with a known cost** — it collapses duplicates and drops sides. Harmless for `Lonely` (see below); the reason §4's two-neighbour results stay at arrangement level |
| `flankOpening n e k` | `(k + 1/n)/e` | **clean.** Read off the arrangement |
| `candidateScale n e k` | `e/(n·k+1)` | **clean.** The same instant in scales |

## 3. The load-bearing theorems, by hypothesis

The question for each is whether a window, a bound, an integrality assumption or a first-ness demand
has crept into the hypotheses. None has.

| theorem | file | hypotheses | verdict |
|---|---|---|---|
| `lonelyAt_iff_lonely_diffSet` | `Cascade/Arrangement.lean:167` | **none at all** | **clean.** This is the transfer everything else uses. Duplicate collapse is harmless because `Lonely` is a `∀` over the set and duplicates impose identical constraints; `\|·\|` is harmless because `circDist` is even. Both facts are in the proof, not assumed |
| `reading_complete` (Prop 6.1's core) | `ConstructionN/LemmaPass.lean:193` | `0 < n`, `ds.Nonempty`, `∀ d ∈ ds, 0 < d` | **clean.** No integrality, no window, no lap bound. The witness is the max over `ds` of `opening n d t` — named, not asserted |
| `opening_le` | same, `:181` | `0 < n`, `0 < d`, clear at `t` | **clean** |
| `exists_flank_of_lonely` | `Cascade/Flanks.lean:44` | positivity, `0 < s`, nonempty | **clean.** Over `ℝ` |
| `lonely_iff_exists_flank` | `Cascade/Flanks.lean:57` | positivity, nonempty | **clean.** Over `ℝ` |
| `lonely_iff_exists_candidate_scale` (Thm 6.15) | `Cascade/ScaleCandidates.lean:82` | positivity, nonempty | **clean.** The amended obligation; over `ℝ`, no iteration |
| `doorFlank_iff` | `Spec/Doors.lean` | `Injective v` | **clean** |

**No hypothesis anywhere in this chain is stronger than the conjecture's own.** Whatever is wrong
with the framework's progress, it is not that the foundations demand extra.

## 4. The one claim that was sitting there because it answered

`DOOR3_v1` §2: *"**All of the difficulty is in the fully rationally dependent case**"*,
`[VERIFIED — numerical, 1e-6 grid]`, from 60 `ℚ`-independent sets and **40 sets of the single shape
"six integers + one irrational"**. In the rank language of `JOINT_REFRAME_v2`, that shape is rank 5.
**Ranks 1–4 were not tested.** The conclusion drawn from it — *"any genuine irrational freedom leaves
a margin of 1.6× to 3.7×"* — is the load-bearing sentence, and one configuration is thin support for it.

**It survives, and the structural reason is stronger than the measurement.** If the seven disparities
split into rationally independent blocks, the orbit closure in the 7-torus is a **product** of the
blocks' closures, so the block parameters are independent and the subject is lonely **iff every block
has a clear point**. The binding constraint is therefore the largest block, and a block of `k`
disparities is the lonely-runner problem at order `k+1` read at threshold `1/8`.

Measured exactly (`experiments/n8/block_margins_v1.{py,out}`, exact rational arithmetic over the
crossing candidates `p/(a_i ± a_j)`, `p/(2a_i)`):

| block | `max_s min_i ‖a_i s‖` | |
|---|---|---|
| `{1,…,7}` | **`1/8` exactly**, at `s = 1/8` | the extremal case, tight |
| `{1,…,6}` | `1/7` | |
| `{1,…,5}` | `1/6` | |
| `{1,…,4}` | `1/5` | |
| `{1,…,3}` | `1/4` | |

`{1,…,k}` gives exactly `1/(k+1)`. So every **proper** block, having `k ≤ 6`, clears `1/8` with
margin at least `1/7`, and the difficulty really does sit only at the undivided 7-block — the fully
commensurable case. Irrationality is not what supplies the margin; **dropping a disparity is**.

> **Stated as a limit, not a route.** That explanation leans on the lonely-runner result at orders
> `≤ 7`. The author has rejected lower-order LRC as non-native justification, so it is recorded here
> as *why `DOOR3_v1` §2's measurement comes out as it does*, and **not** offered as an argument the
> framework may use. Without it, §2 stands as `[EMPIRICAL]` on one intermediate configuration.

**Verdict: not termination-shaped.** `DOOR3_v1` §4 already checked the hypotheses and found every
door statement — `ExistenceAt8`, `_cascade`, `_flank`, `CascadeCapped`, `FiniteActiveMembership`,
`lonely_iff_exists_flank`, `lonely_iff_run_ends` — to be over `ℝ` with **no integrality hypothesis**,
and corrected an earlier draft that had called the real case "a separate, later obligation". The
correction was right. Only `lonely_iff_bounded_search` and `lonely_iff_emod_search` carry `hint`,
and `Target.lean` declines `ExistenceAt8_congruence` as the target for exactly that reason.

## 5. Checked and clean, stated so they are not re-opened

- **Threshold.** Closed `≥ 1/8`, not `> 1/8`. Correct for LRC, and the extremal AP attains it exactly.
- **No privileged disparity.** Theorem 6.15 quantifies over **all** `e ∈ ds`. `d_min`'s special role
  was a cascade artefact and leaves with the cascade; `leastDisp`/`firstReading` are used only by the
  iteration doors.
- **`card ≤ 7` and `Finset ℝ`.** Amended 2026-09-18; the target is on arrangements.
- **`ExistenceAt8_congruence`.** Carries `hint`; correctly not adopted.
- **Per-subject working.** Sound — the conjecture is `∀ k`. But `Doors.lean` builds the cross-subject
  coupling (`inWay_comm`, `blockDegree`, the handshake identity over 28 pairs) and then records
  *"Nothing here closes a door."* That is a **discarded asset**, not an imported obligation, and it is
  the one item in this audit worth a separate look.
- **4, 5 and 6 disparities at `n = 8`.** Not proved, and **not claimed** — §8.2 carries only `k ≤ 3`
  (`2k < n`) and keeps the rest `[OPEN]`. No smuggled closure.

## 6. Result

One item was in the termination category — the real case — and it was already caught and corrected in
`DOOR3_v1` §4 before this audit. Its supporting measurement is thinner than its wording implies, and
§4 above supplies the structural reason it holds anyway.

**Nothing else in the foundations demands more than the conjecture does.** The definitions are
minimal, the load-bearing hypotheses are positivity and nonemptiness, and the whole chain from
`LonelyAt` to Theorem 6.15 is stated over `ℝ` with no window, no bound and no integrality.
