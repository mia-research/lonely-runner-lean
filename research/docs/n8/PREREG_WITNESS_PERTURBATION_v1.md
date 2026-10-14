# PREREG — witness perturbation sweep (n = 8, threshold 1/8, integer disparities)

2026-09-20. Pre-registration gate (`CLAUDE.md` §2) for the submitted axis list A1–A6 on the
witness set `W(ds)` and the supporting-flank set `S(ds)`.

**This document is the corrected spec. It is not the submitted spec.** Part 0 records what the
submitted spec got wrong and what was already on disk before it was written; Parts 1–9 are the
runnable pre-registration. Do not run anything before Part 0 §0.4 is acknowledged, because two of
the six submitted axes ask questions whose answers are already in the tree, and one of them
measures a correlate rather than the object.

**Nothing below the instrument section has been run. No statistic in Parts 1–9 has been computed
on any set outside the contaminated window declared in §0.2.**

---

# PART 0 — AUDIT OF THE SUBMITTED SPEC

## 0.1 The instrument is stronger than the spec claims — three "verified" facts are PROVED

The submitted spec grades the integer form, the period-`e` periodicity, and self-clearness as
empirically cross-validated. All three are two-line proofs. Recording them as empirical leaves a
standing instrument doubt that does not exist, and an empirical grade invites a future run to
"re-check" them and burn budget.

With `A = 8k+1`, `t = A/(8e)`, `r_d = (d·A) mod 8e`:

> **P1 `[PROVED]`.** `circDist(d·t) = min(r_d, 8e−r_d)/(8e)`, so
> `circDist(d·t) ≥ 1/8 ⟺ r_d ≥ e and 8e−r_d ≥ e ⟺ e ≤ r_d ≤ 7e`.
> The two forms are identical, not merely concordant. "0 mismatches" is a tautological
> cross-check and is not evidence of anything.
>
> **P2 `[PROVED]`.** `k → k+e` sends `A → A+8e`, so `d·A → d·A + 8de ≡ d·A (mod 8e)`.
> The condition is exactly period `e` in `k`. Hence `W(ds)` is finite and
> `W(ds) = {(e,k) : e ∈ ds, 0 ≤ k < e, ∀d ∈ ds: e ≤ (dA) mod 8e ≤ 7e}` is exhaustive.
>
> **P3 `[PROVED]`.** For `d = e`: `e·(8k+1) mod 8e = e·((8k+1) mod 8) = e`, and `e ≤ e ≤ 7e`.
> The naming flank is self-clear **identically**, for every `e` and every `k`. So the content is
> the other six disparities, as stated — but this is a theorem, not an observation.
>
> **P4 `[PROVED]`.** The band `[e, 7e]` is symmetric about `4e`, and `(−d)·A ≡ 8e − r_d`.
> Therefore `d` and `−d ≡ 8e−d` give the **same** condition. The readout has a `±` symmetry
> by definition. **Any control that destroys it is a null mismatch** — see §3.0.
>
> **P5 `[PROVED]`.** With `g = gcd(d,e)`, `c = e/g`, `a = (d/g) mod 8c`, the set
> `{k mod c : e ≤ (dA) mod 8e ≤ 7e}` depends **only** on the pair `(c, ±a)`. The blocked set is
> a union of cosets of the subgroup `1 + 8ℤ` acting on `a` mod `8c`.
> `[VERIFIED — exhaustive e ≤ 39, d ≤ 199: zero collisions carrying different k-sets]`
>
> **P6 `[PROVED]`.** `S` is **antitone** under inclusion: `S(ds \ {d_j}) ⊇ S(ds) \ {d_j}`,
> because every `d` contributes an independent conjunct. Dropping a disparity can only add
> supporting flanks (among the survivors), never remove one.

P5 is the load-bearing one and it is what invalidates axis A3 as submitted (§0.5).

Instrument re-derivation script (all six, exact integer arithmetic, no float in the signal path):
`experiments/n8/prereg_witness_instrument_v1.py` — must be written and must print six PASS lines
before any axis runs. P1/P2/P3/P5 were re-derived mechanically on 172,244 (e,k,ds) triples and
exhaustive `e ≤ 39, d ≤ 199` during the drafting of this document; that run is an instrument check
on the *definition*, touches no set-level statistic, and is not part of the sweep.

## 0.2 CONTAMINATION — declared window, and prior data already on disk

Two separate contaminations. Both bind.

**(a) The four disclosed witness sets.** `{1..7}`, `{2,6,8,9,11,14,15}`, `{2,3,5,7,8,13,16}`,
`{1,3,4,5,6,7,8}` with `|S| = 4, 4, 4, 2`. The primary statistic `|S(ds)|` was named **after**
these four values were seen. That is a fitted-statistic risk and it is real: a statistic selected
because it took a suspiciously stable value on four sets is a statistic selected on its own
sampling fluctuation. It does not invalidate `|S|` — `|S| ≥ 1` is the Existence predicate and is
independently motivated by `LRC.Spec.doors_agree` — but it does mean:

> **These four sets are permanently excluded from every count, rate, histogram and test in this
> document.** They appear only in §4 as planted-control fixtures with known answers. No hypothesis
> they suggested may cite them as confirming evidence.

**(b) Prior runs in the tree that already compute `S`.** The submitted spec does not mention these.
`free_flanks` in `experiments/n8/flank_critical_sets_v1.py` is *exactly* `S(ds)`:

| artefact | scope | what it already reports |
|---|---|---|
| `experiments/n8/flank_critical_sets_v1.out` | exhaustive 7-subsets of `[1,30]`, 2,035,800 sets | `min |S| = 1`; `|S| = 0` count is **0**; the unique `|S| = 1` set is `[2,3,4,5,6,7,16]`, free flank `= d_max` |
| `experiments/n8/flank_overdetermination_v1.out` | exhaustive 7-subsets of `[1,18]`, 31,824 sets | same, plus the divisibility signature of that set's shadowed flanks |
| `experiments/n8/three_largest_v1.py` | exhaustive multisets from `[1,N]`, gcd 1 | the `rank(e)` statistic — the submitted spec's fourth statistic, already measured |
| `experiments/n8/flank_what_predicts_v1.out` | 7-subsets of `[1,18]`, 211,029 flanks | shadow rate by `|J|` and by largest ratio denominator; overall shadow rate 12.39% |
| `experiments/n8/flank_divisibility_v1.out` | per-pair | blocking density by `c = e/gcd(d,e)`: `1 → 0`, `2 → 1/2`, `4 → 1/4`, large-`c` limit `1/4` |
| `docs/n8/NEIGHBOUR_DEFORMATION_v2.md` §2 | 12,800 instances | residue movement of a grid neighbour has a `[PROVED]` closed form `±p mod 8` |

**Consequences that bind the design:**

1. The **contaminated window is `H ≤ 30` for `|S|`'s lower tail and `H ≤ 18` for shadow rates**.
   Inside it, no result of this sweep is a finding; it is a reproduction.
2. **A hypothesis of the form `|S| ≥ 2` is already refuted** and must not be pre-registered.
   Likewise "the best flank is always `d_max`" is already false (rank 2 in 84 cases, rank 3 in 3).
3. `flank_divisibility_v1.out` **already answers axis A4 in the aggregate**. A4 as submitted is
   largely a re-run. See §0.5.
4. The 12.39% shadow rate is used **once**, as the variance input to the power calculation in §5.
   That is a legitimate use of seen data (power planning needs a variance estimate) and is
   disclosed here rather than buried.

## 0.3 Is the submitted spec fitted to the four sets? — partly, and here is where

Asked directly, as instructed. Three specific places:

- **`|S|` as primary.** Fitted (§0.2a). Retained on independent grounds, with the four excluded.
- **"The naming flank is always self-clear (verified)".** Not fitted — it is P3, identically true.
  But it was read off four examples when it is a one-line identity, which is the tell that the
  four sets were being used as a substitute for algebra.
- **A3 "residue mod 8".** This is where the fit bites. All four disclosed sets have small
  disparities where `mod 8` and the true invariant `(c, ±a mod 8c)` are hard to tell apart
  (`c ≤ 16` throughout). The `mod 8` framing is an artefact of looking at small examples. P5 gives
  the object's own invariant; `mod 8` is a correlate of it. **Object-level objection, §0.5.**

## 0.4 Deviations required before any run — checklist

| # | Required change | Reason |
|---|---|---|
| D1 | Exclude the four disclosed sets everywhere except §4 fixtures | §0.2a |
| D2 | Declare `H ≤ 30` contaminated for `|S|`; report results there as REPRODUCTION, not finding | §0.2b |
| D3 | Regrade P1/P2/P3 from EMPIRICAL to PROVED; add P4, P5, P6 | §0.1 |
| D4 | A1 demoted from "instrument check" to *code-correctness assertion*; **and corrected** — `|W|` is **not** scale-invariant | §0.5 |
| D5 | A3 replaced by A3′ (invariant-level), `mod 8` retained only as a declared proxy arm | §0.5 |
| D6 | A4 narrowed to the 2-adic sub-question not covered by `flank_divisibility_v1.out` | §0.5 |
| D7 | A6's direction is forced by P6; only the **increment** is measurable | §0.5 |
| D8 | Add axes A7 (flank axis) and A8 (2-adic profile) | §0.6 |
| D9 | Every control must preserve the `±` symmetry of P4 | §3.0 |

## 0.5 Per-axis verdict on the submitted list

**A1 — SCALE. Redundant as a finding, and stated wrongly.**
`(c·d·A) mod (8·c·e) = c·((d·A) mod 8e)`, so the condition is identical. `S(c·ds) = c·S(ds)` with
the same `k` is `[PROVED]`, in one line, and `lonely_smul` (`LRC/Cascade/Flanks.lean:746`) already
carries the real-coefficient version. **It cannot produce a finding.** Keep it as assertion `C1`.
**The correction:** in `c·ds`, flank `ce` admits `k ∈ [0, ce)`, and by P2 the valid set is the
period-`e` extension, so the **per-flank count multiplies by `c`**:
`|{k < ce : (ce,k) ∈ W(c·ds)}| = c·|{k < e : (e,k) ∈ W(ds)}|`.
`[VERIFIED — 200 random sets, c ∈ {2,…,5}, exact]`
Therefore **`|W(ds)` and per-flank counts are not scale-invariant** and comparing them across sets
of different magnitude conflates scale with structure. Every `|W|`-based statistic in this
document is replaced by the **density** `ρ(e) = |{k < e : (e,k) ∈ W}| / e ∈ [0,1] ∩ ℚ`, which is
scale-invariant by the same algebra. This is a defect in the submitted spec, not a refinement:
the submitted `|W(ds)|` statistic would have reported pure scale as structure.

**A2 — SINGLE COORDINATE ±1. Sound, keep. Underspecified in one respect.**
"One `j` at a time" does not say what happens when `d_j ± 1` collides with another element or
breaks primitivity. Pinned in §6.2. Note `docs/n8/NEIGHBOUR_DEFORMATION_v2.md` and
`docs/n8/WITNESS_DRIFT_v1.md` already perturb single coordinates, but against a *different
readout* (isolation-point location, cascade depth) — not against `S`. Not contaminated for `S`;
do read §2 of that document first, since its `±p mod 8` closed form is `[PROVED]` and predicts
part of A2's answer analytically.

**A3 — RESIDUE mod 8. Measures a correlate. As submitted it cannot answer its question.**
This is the finding of this audit. By P5 the witness condition for the pair `(d,e)` depends only on
`(c, ±a)` with `c = e/gcd(d,e)`, `a = (d/g) mod 8c`. The modulus is `8c`, which **varies with the
flank**, and `c` depends on `gcd(d,e)`. Two sets with an identical multiset `{d_i mod 8}` can have
entirely different `(c, a)` vectors — `mod 8` is neither necessary nor sufficient. Holding
`{d_i mod 8}` fixed therefore holds nothing the object cares about, and "identical mod-8 profile,
different `S`" is **guaranteed to occur** for trivial reasons. As submitted, A3 asks a question
whose answer is forced. Replaced by:

> **A3′ (invariant level).** Group sets by the *flank-indexed invariant vector*
> `I(ds, e) = multiset{ (c_d, min(a_d, 8c_d − a_d)) : d ∈ ds, d ≠ e }`.
> **Forward direction is `[PROVED]` (P5): equal `I` ⟹ equal per-flank `k`-set.** So the only
> non-trivial question is the **converse/coarseness** one: how much smaller is `S` as a function
> of `I` than `I` itself — i.e. find pairs with `I(ds,e) ≠ I(ds',e')` but identical `k`-set, and
> characterise the extra collapse. That is a real question with an unforced answer.
> The `mod 8` arm is retained, **declared as a proxy**, solely to measure how badly it fails:
> report the mutual information between `{d_i mod 8}` and `|S|` alongside that between `I` and
> `|S|`. A proxy that carries most of the signal is worth knowing; a proxy that carries little is
> the disproof of A3-as-submitted. Either way the number is reportable.

**A4 — DIVISIBILITY. Half already answered; second half underspecified.**
`flank_divisibility_v1.out` already gives the blocking density as a function of
`c = e/gcd(d,e)` per pair. "Changing gcd structure among pairs" names no statistic and no contrast
and cannot be run as written. Narrowed to **A4′**: `d_j → 2·d_j` with the induced change in
`ν₂(d_j)` tracked explicitly, tested against the P5 invariant (i.e. does the `S` change decompose
into the per-pair `(c,a)` changes, or is there a joint effect the per-pair table misses). The
joint-vs-marginal question is the part `flank_divisibility_v1.out` does **not** answer.

**A5 — AP DIRECTION. Sound, keep.** One pin needed: `{a, a+g, …, a+6g}` is primitive iff
`gcd(a,g) = 1`; state that restriction up front rather than silently filtering (the silent-filter
failure mode).

**A6 — BLOCK SIZE. Direction is forced; only the increment is measurable.**
By P6 `S` is antitone, so "dropping a disparity increases `S`" is a theorem, not a result. The
measurable object is the **increment** `Δ_j = |S(ds \ {d_j})| − |S(ds) \ {d_j}| ≥ 0` and which
`j` maximises it. Also: the stated connection to "`{1..k}` has max-min margin exactly `1/(k+1)`"
is at a **different threshold**. That result concerns margin `1/(k+1)`; this sweep fixes the
threshold at `1/8` regardless of `|ds|`. For `{1,…,6}` the margin is `1/7 > 1/8`, so clearance is
forced and carries no information about the order-8 object. State the two thresholds separately or
the axis will read a triviality as a confirmation.

## 0.6 Axes the submitted list MISSES that the object's structure suggests

**A7 — THE FLANK AXIS (move `e`, not the constraints).** Every submitted axis perturbs the
constraint set. But `W` is indexed by `(e,k)` and the modulus is `8e`; the natural dual
perturbation is to change which element names the flank while holding the six constraints fixed —
concretely, `ds = C ∪ {e}` with `C` fixed (`|C| = 6`) and `e` ranging over all admissible values.
This isolates `e`'s role, which no submitted axis does, and it is the axis on which `rank(e)` and
the `d_max` phenomenon actually live. `flank_critical_sets_v1.out`'s unique tight set
`[2,3,4,5,6,7,16]` (free only at `d_max = 16`) is a point on this axis.

**A8 — 2-ADIC PROFILE.** The threshold is `1/8 = 2^{-3}` and the modulus is `8e = 2^3·e`. The
object is 2-adic before it is anything else (`experiments/n8/two_adic_witness_v1.py` already
identifies rung `k = 3` as where `n = 8` pays). The axis is the vector
`(ν₂(d_1), …, ν₂(d_7))` at fixed odd parts, which A4's `d → 2d` hits only incidentally and
confounded with magnitude. A8 varies `ν₂` **holding the odd part fixed**, which A4 does not.

**A9 — THE `±` ORBIT (control axis, not a finding axis).** By P4 the readout is invariant under
`d ↦ 8e − d` per flank. This is not a perturbation to test; it is the symmetry every null must
respect. Listed as an axis so that it cannot be forgotten when controls are written.

---

# PART 1 — OBJECT

The object is the witness set

    W(ds) = { (e,k) : e ∈ ds, 0 ≤ k < e, ∀ d ∈ ds : e ≤ (d·(8k+1)) mod 8e ≤ 7e }

for `ds ⊂ ℤ_{>0}`, `|ds| = 7`, `gcd(ds) = 1`, and its projection `S(ds) = {e : ∃k, (e,k) ∈ W}`.
This is the object itself, not a proxy: `S(ds) ≠ ∅` is the order-8 grid-door predicate, tied to
`LonelyForSubject` through `LRC.Spec.doors_agree` (`MANUSCRIPT_v17.md` §6.7).

**Tautology check (required by the gate, answered).** Feature and target share construction in
exactly one place and it is disclosed: `S` and the perturbation axes are both functions of `ds`,
so any axis statistic is a function of the same integers as the target. This is **not** the `r = v − w`
tautology, because the axes perturb `ds` and the statistic is evaluated on the *perturbed* set —
the map `ds ↦ S(ds)` is not algebraically implied by the map `ds ↦ ds'`. The one place a tautology
would enter is A1 and A6, where the answer **is** algebraically implied (P-facts above); both are
demoted accordingly. A3 as submitted was the third such place. No axis surviving into Part 6 has an
algebraically forced answer.

**Grade ceiling, stated up front as required.** Every output of this sweep is
`[EMPIRICAL — scope]` or `[VERIFIED-INSTANCE]`. **No output of this document can be read as a
proof of anything.** Where an item is `[PROVED]` it is proved in §0.1 by algebra, not by the
sweep, and the sweep is then a code-correctness check on that algebra. A promotion to `[PROVED]`
requires a separate argument or a Lean declaration, never a count.

---

# PART 2 — STATISTIC

**Exactly one primary statistic**, named now:

> **T = |S(ds)| ∈ {0,1,…,7}**, the number of supporting flanks.

Declared secondary statistics, in this fixed order, each reported with its own scope and never
promoted to primary after the fact:

| rank | statistic | scale-invariant | note |
|---|---|---|---|
| S1 | `T = |S(ds)|` | yes | PRIMARY |
| S2 | `ρ(e) = |{k<e : (e,k)∈W}| / e` and `ρ_max = max_e ρ(e)` | yes (A1 algebra) | replaces `|W|`, which is **not** invariant |
| S3 | `kmin(ds) = min{k : (e,k) ∈ W}` and `kmin(e)` per flank | yes (same `k`) | |
| S4 | `rank(e*)` of the best flank, descending | yes | **contaminated**, see §0.2b |
| S5 | `Δ_j` (A6 increment only) | yes | A6's only measurable content |

**Pooling over max-of-cells.** Where an axis induces many cells (e.g. seven choices of `j` in A2),
the pre-registered statistic is the **pooled mean shift** `E_j[T(ds'_j) − T(ds)]` and the **pooled
sign-test count**, not `max_j |ΔT|`. A max over seven noisy cells is upward-biased and low-power;
it is reported only as a descriptive appendix and **may not** carry a p-value.

**Null distribution.** For sampled strata, `T(ds') − T(ds)` under the matched null of §3 is
symmetric about 0 by construction, and the test is the **exact two-sided sign test** on non-zero
differences (binomial, `p = 1/2`), plus the **Wilcoxon signed-rank** on the magnitudes as a
declared secondary. For exhaustive strata there is no null distribution: the counts are exact and
are reported as counts with no p-value (§5).

**Aimed at the predicted symmetry.** Where an axis predicts that the effect lives in a subspace —
A3′ predicts it lives in the `(c, ±a)` invariant, A8 in the `ν₂` profile — the statistic is the
**conditional** `T` given that invariant, not the marginal. A marginal `T` that shows nothing while
the conditional shows structure is the documented "bound became a verdict" failure; see §7.

---

# PART 3 — MATCHED CONTROLS

## 3.0 The invariance every control must respect  `[binding]`

By P4 the readout is invariant under `d ↦ 8e − d` at flank `e`, and by P5 it factors through
`(c, ±a)`. **A control that randomises `d` freely destroys P4/P5 and is invalid** — it would
produce a difference that is an artefact of the null, which is precisely the "6–7σ soft shadow"
failure mode. Every control below therefore states what it preserves and what it destroys, and
each is required to pass the **null-symmetry assertion**:

> **C0.** Applying the control to a set, then applying `d ↦ 8e − d` at each flank, gives the same
> distribution of `T`. Checked on 2,000 control draws per axis before any axis result is read.
> Failure of C0 invalidates that axis's null; the axis is then reported as having **no usable
> control** and its numbers are descriptive only.

Because these are exact deterministic computations, the question a control must answer is, as the
submitter correctly states, *"is this structure special to `ds`, or would any 7-set show it"* —
**not** "is this above noise". Every control below is therefore a **reference population**, not a
noise model.

## 3.1 Per-axis controls

| axis | matched control (reference population) | preserves | destroys |
|---|---|---|---|
| **A2** `d_j → d_j ± 1` | **Ledger-matched twin.** For each real perturbed set `ds'_j`, draw a set `ds''` uniformly from all primitive 7-sets with the *same* `d_max`, *same* `|ds ∩ 8ℤ|`, *same* multiset of `ν₂`, and *same* number of elements changed (one), the change being `±1` at a uniformly random `j`. | magnitude scale, 2-adic profile, primitivity, edit distance | which coordinate moved, and its relation to the rest |
| **A3′** invariant | **Invariant-shuffle.** Hold the multiset `I(ds,e)` fixed and re-realise it by a *different* `(d, e)` solution of `c = e/gcd(d,e)`, `a = (d/g) mod 8c` — solutions exist because `(c,a)` under-determines `(d,e)`. | the entire P5 invariant, hence `k`-set exactly | the actual integers, magnitudes, `mod 8` profile |
| **A3 proxy arm** | **mod-8-matched shuffle.** Uniform over primitive 7-sets with the same `{d_i mod 8}` multiset. | `mod 8` profile only | the P5 invariant — **this is the point**: the arm is designed to show the proxy is not the object |
| **A4′** `d_j → 2d_j` | **Per-pair prediction.** Predict `S(ds')` from the per-pair `(c,a)` table of `flank_divisibility_v1.out` under an independence assumption; the control is the *predicted* `T`. Deviation = joint effect. | all marginal per-pair blocking rates | pair-to-pair dependence — exactly what is being tested |
| **A5** AP | **Gap-multiset-matched.** Uniform over primitive 7-sets with the same multiset of consecutive gaps as the AP-departure set (an AP has gap multiset `{g,g,g,g,g,g}`; a one-coordinate departure has `{g,…,g±1,g∓1,…}`). | gaps, hence `d_max − d_min`, hence coarse geometry | the ordering of gaps and the absolute offset `a` |
| **A6** drop-one | **Random-drop.** The same set with a uniformly random `j` dropped. Compare `Δ_j` at the observed-best `j` against the random-`j` distribution. | set, size, everything except which element left | the identity of the dropped element |
| **A7** flank axis | **`C`-matched flank shuffle.** Hold `C` (the six constraints) fixed, draw `e` uniformly from the admissible range. This control is *exactly* the axis, so A7 needs no separate null: the reference population is the axis's own sweep, and the statistic is the shape of `e ↦ 1[e ∈ S]`. | the six constraints exactly | nothing — A7 is a census, reported as a census |
| **A8** `ν₂` | **Odd-part-matched.** Hold the odd parts `{d_i / 2^{ν₂(d_i)}}` fixed, permute the `ν₂` vector among coordinates. | odd parts, hence all odd-modulus structure | the assignment of 2-adic valuation to coordinate |

**A1 has no control** and is not entitled to one: it is assertion `C1` (code correctness), pass/fail.

---

# PART 4 — PLANTED CONTROLS (positive controls)

**If a planted control does not fire, that axis's null is uninformative and the axis is reported as
UNINFORMATIVE — full stop, no result from it may be quoted.**

| ID | Plant | Must fire as |
|---|---|---|
| **PC1** | The four disclosed sets, as fixtures. `S` must reproduce `{1,3,5,7}`, `{6,8,14,15}`, `{5,7,8,13}`, `{4,7}` and the stated `k` lists exactly. | exact match, 4/4 |
| **PC2** | `[2,3,4,5,6,7,16]` must return `T = 1`, `S = {16}` (from `flank_critical_sets_v1.out`). | exact |
| **PC3** | Known-`S` injection: take any set with `T = t`, adjoin the forced blocker `d = 8e` for a target flank `e ∈ S` (then `r_d = 8e·A mod 8e = 0 < e`, so `e` is killed `[PROVED]`). Sweep must report `e ∉ S`. | 100% of trials |
| **PC4** | **Graded plant for A2.** Construct `ds` and `j` such that `d_j → d_j + 1` provably flips flank `e`: choose `d_j` with `(d_j·A) mod 8e = e` (band edge), so `+1` pushes it to `e − 1 + (A mod 8e)`… computed exactly per case. Inject at rates 1/50, 1/20, 1/10 of the A2 sample. Test must detect the 1/20 rate at `p < 0.01`. | detection at 1/20 |
| **PC5** | **Null-mismatch plant (C0).** Apply a *deliberately wrong* control — uniform random 7-sets with no matching at all — to A2. This **must** produce a large apparent effect. If the unmatched control does *not* differ from the matched control, the matching is doing nothing and the axis is uninformative for the opposite reason. | large apparent effect, reported |
| **PC6** | **Scale plant (A1/`C1`).** Run `c ∈ {2,3,5,7}`; `S(c·ds) = c·S(ds)` and per-flank count `× c`. | exact, 100% |

PC5 is the specific guard against the documented shuffle-control failure: it verifies the control
has the power to distinguish, before any real result is read.

---

# PART 5 — POWER AND RESOLUTION

**Exhaustive strata carry no sampling error.** The resolution is 1 set. A count of `m` sets with a
given property in an exhaustive stratum is exact, needs no p-value, and must be reported as
`m out of N, exhaustive over <scope>`. **No p-value may be attached to an exhaustive count.**
This is stated because attaching one is the standard way an exact census gets laundered into a
significance claim.

**Sampled strata.** Variance input `p ≈ 0.124` (per-flank shadow rate, `flank_what_predicts_v1.out`,
`H ≤ 18` — disclosed seen-data use, §0.2b item 4). Two-proportion two-sided `α = 0.05`, power 0.80:

    n_per_arm ≈ 1.656 / Δ²

| detectable rate difference `Δ` | `n` per arm |
|---|---|
| 0.10 | 166 |
| 0.05 | 663 |
| 0.02 | 4,140 |
| 0.01 | 16,560 |
| 0.005 | 66,240 |

**Declared sample size: `n = 20,000` per arm per axis**, giving 80% power at `Δ ≈ 0.0091`.
Paired axes (A2, A4′, A6, A8) use the exact sign test on discordant pairs, which is strictly more
powerful; at `n = 20,000` pairs with discordance rate `π_d`, the detectable departure from a 1:1
split is `≈ 1.4/√(π_d · 20000)` in proportion terms — for `π_d = 0.05` that is a 60:40 split, for
`π_d = 0.3` a 53:47 split.

**Minimum detectable effect on the primary statistic `T`.** `T` is integer-valued on `{0..7}`.
At `n = 20,000` paired comparisons the detectable mean shift is `2.8·σ_ΔT/√n = 0.0198·σ_ΔT`.
`σ_ΔT` is **estimated from the calibration slice declared in §6.5, never from the test arm.**
If `σ_ΔT` on the calibration slice implies the study cannot detect `|E[ΔT]| = 0.05`, the axis is
declared **UNDERPOWERED before it runs** and its null, if it comes back null, is reported as
"underpowered at the declared `n`" — not as a null. This clause exists because a null with no power
number has previously been reported here as a result.

**Feasibility, measured.** Single-core throughput of `free_flanks`: **16–18 µs/set** for
`H ∈ [30,120]`.

| `H` | `C(H,7)` | exhaustive single-core |
|---|---|---|
| 30 | 2,035,800 | 0.01 h (**already run**) |
| 40 | 18,643,560 | 0.09 h |
| 50 | 99,884,400 | 0.48 h |
| **60** | **386,206,920** | **1.8 h** |
| 80 | 3.18×10⁹ | 15 h |
| 120 | 5.95×10¹⁰ | 292 h |

---

# PART 6 — SCOPE AND SAMPLING DESIGN

## 6.1 Declared scope — every number inherits it

- `|ds| = 7`, `ds ⊂ ℤ_{>0}` distinct, `gcd(ds) = 1` (primitive). Multisets are **excluded** from
  the main sweep; if included they form a separate ledger (`three_largest_v1.py` uses multisets —
  do not pool the two).
- Threshold fixed at `1/8`; `k ∈ [0, e)` exhaustive by P2.
- **Exhaustive band: `H ≤ 60`**, i.e. all primitive 7-subsets of `[1,60]`, 386,206,920 sets
  (≈ 0.9924 primitive by `1/ζ(7)`).
- **Contaminated band: `H ≤ 30`** — reproduction only (§0.2b).
- **Clean exhaustive band: `30 < H ≤ 60`** — this is where a finding can live.
- **Sampled band: `60 < H ≤ 2000`**, `n = 20,000` per stratum per axis.
- Excluded permanently: the four sets of §0.2a.

Every number produced by this sweep is written as `<value> [scope: H-band, axis, arm, n]`. A number
without its scope is a defect, not a shorthand.

## 6.2 Pins the submitted spec left open

- **A2 collision.** If `d_j ± 1 ∈ ds` already, the perturbation is **skipped and counted**, in a
  named `skipped_collision` counter reported alongside every A2 number. It is not silently dropped.
  (The documented failure was a silent filter cutting 8 candidates to 3.)
- **A2 primitivity.** If `d_j ± 1` makes `gcd > 1`, the set is **retained** and its gcd recorded;
  by the A1 algebra a non-primitive set is `g ·` a primitive one, so `T` is unchanged under
  division by `g`. Retaining and recording is correct; filtering would bias.
- **A2 lower edge.** `d_j = 1 → 0` is not admissible; skipped and counted.
- **A5 primitivity.** `{a, a+g, …, a+6g}` is primitive iff `gcd(a,g) = 1`. Declared up front.
- **A4′/A8 range.** Doubling can exceed the band's `H`; the doubled set is evaluated regardless
  and its `d_max` is recorded. Band membership is a property of the *source* set.

## 6.3 Sampling — uniform unranking, not truncated lexicographic iteration

The standing rule (`CLAUDE.md` §5) is that lexicographic iteration biases results. Truncating
`itertools.combinations` is exactly that bias, and a shuffle of a truncated prefix does not fix it.
The design uses **uniform combinatorial unranking**: draw `r` uniformly from `[0, C(H,7))` and
decode the `r`-th combination directly.

```python
from math import comb
def unrank(r, H, k=7):
    """r-th 7-subset of [1,H] in colex order, uniform when r is uniform."""
    out = []
    x = H
    for i in range(k, 0, -1):
        while comb(x, i) > r:
            x -= 1
        out.append(x + 1)
        r -= comb(x, i)
    return sorted(out)
```

- PRNG: `random.Random(seed)`, **seed declared in the run header before the run**, one seed per
  axis, recorded in the output file.
- Duplicates rejected; the realised unique count is reported.
- **Per-structure caps** (the standing rule's second half): cap at 200 sets per
  `(d_max decile, ν₂-profile, gcd-pair signature)` stratum. Realised per-stratum counts are
  **printed**, so an under-filled stratum is visible rather than inferred.

## 6.4 Exactness  `[no-float rule]`

The entire signal path is `int`. `(d·(8k+1)) % (8*e)` and the comparisons `e ≤ r ≤ 7e` are integer
operations; no `Fraction` is needed and no float appears. **Declared float carve-outs:** (i) the
power calculation in §5, (ii) reported percentages, (iii) the mutual-information figure in A3′.
All three are analytic size only, downstream of the decision, with no key in the path. The
`Fraction` implementation is retained **only** as the PC1 cross-check and is not the signal path.

## 6.5 Calibration slice

A pre-declared slice — primitive 7-subsets of `[31,45]`, sampled `n = 5,000`, seed fixed — is used
**only** to estimate `σ_ΔT` for §5 and to fit nothing else. It is excluded from every reported
result. Its exclusion is checked mechanically, not by memory.

---

# PART 7 — FALSIFICATION

Written before the run, per axis. Each is an observation, not a feeling.

| axis | hypothesis under test | falsified by |
|---|---|---|
| **A1/`C1`** | code implements the object | any `ds`, `c` with `S(c·ds) ≠ c·S(ds)`, or per-flank count `≠ c ×`. **Stops the whole run.** |
| **A2** | `S` responds to a single-coordinate `±1` more than a ledger-matched twin does | pooled sign test over `n = 20,000` pairs indistinguishable from 1:1 at `p > 0.05` **and** PC4 fired at 1/20 (so the test had power). Both clauses required. |
| **A3′** | `S` is determined by the P5 invariant, and strictly more collapsed than it | forward direction fails on any instance (would refute P5 — an implementation error). The *coarseness* claim is falsified if **zero** pairs with `I ≠ I′` and equal `k`-set are found in the exhaustive `H ≤ 60` band. |
| **A3 proxy** | `mod 8` profile carries the signal | **the exact form required by the submitter:** exhibit `ds ≠ ds′`, both primitive 7-subsets of `[1,60]`, with multiset `{d_i mod 8} = {d′_i mod 8}` and `S(ds) ≠ S(ds′)` **as sets after rescaling to a common flank labelling** — concretely, `|S(ds)| ≠ |S(ds′)|`. **One such pair falsifies A3-as-submitted.** Prediction from P5: such pairs exist in abundance; the reportable number is their *frequency*, and the mutual information `I({d mod 8}; T)` versus `I(invariant; T)`. |
| **A4′** | `T` after doubling is predicted by the per-pair table under independence | observed vs predicted `T` distribution agrees within the §5 resolution ⟹ no joint effect at this `n`, stated conditionally. Disagreement ⟹ joint effect, size reported. |
| **A5** | AP structure is special for `S` beyond its gap multiset | AP sets and gap-multiset-matched controls have indistinguishable `T` distributions at `n = 20,000` ⟹ AP-specialness not detected at `Δ ≥ 0.009`, **conditional on method, sample and floor**. |
| **A6** | which element is dropped matters | `Δ_j` at the observed-best `j` lies inside the random-`j` distribution (two-sided, `p > 0.05`) |
| **A7** | `e`'s role is not exhausted by `e = d_max` | the map `e ↦ 1[e ∈ S]` at fixed `C` is monotone in `e` in every case examined ⟹ `e`'s role reduces to magnitude. Known non-monotone instances exist (`rank` 2 and 3 cases, §0.2b), so this is already expected to survive; the reportable object is the *shape* of the failure. |
| **A8** | the 2-adic profile carries `S` at fixed odd part | permuting `ν₂` among coordinates leaves `T` unchanged in every sampled instance ⟹ assignment does not matter, only the multiset. |

**The subspace clause (mandatory).** For every axis returning "no effect detected", the report must
additionally answer: *what would this look like if the effect lives in a subspace we are not
projecting onto?* The concrete instrument is fixed now: re-run the same statistic **conditioned on
the P5 invariant class** and on the `ν₂` profile. An axis may not be written up as null until both
conditional versions have been computed. A magnitude is a size; it is not "no structure".

---

# PART 8 — REPORTING RULE (suppression-bias guard)

`MEMORY.md` records a one-way suppression bias in this operator: positives are converted to nulls
before being tested. The design counters it mechanically, not by intention.

1. **Every positive is surfaced and logged before it is judged.** The run writes a
   `positives.jsonl` containing *every* comparison reaching `p < 0.05` uncorrected, *every* axis
   whose pooled shift exceeds the §5 resolution, and *every* exhaustive-band anomaly, **at the
   moment it is computed**, before any multiple-comparison correction and before any interpretation.
   The file is written by the sweep, not by the analyst.
2. **Nothing may be removed from `positives.jsonl`.** Corrections and dismissals are recorded as
   *additional* lines with a reason and a named artefact, never by deletion. A dismissal with no
   named artefact is not a dismissal.
3. **The write-up must state `len(positives.jsonl)` and account for every line individually.** An
   aggregate statement ("a few marginal hits, all explained") does not discharge it; the documented
   failure is that a proxy count read healthy while five items were liquidated.
4. **No pre-deflation vocabulary.** "Merely", "just an artefact", "as expected", "only" may not
   appear in a dismissal that has not yet been tested. The test comes first; the word comes after.
5. **Credibility hedges are a trigger, not a style issue.** "Genuinely", "honestly", "truly"
   appearing anywhere in the write-up triggers a stub test of the adjacent claim before the word is
   removed (`feedback_no_credibility_hedges`).
6. **Negatives are conditional, always.** Every null is phrased "not detected by <method> at
   `n = <n>` over <scope> with resolution `Δ = <Δ>`". The forms "is not", "does not", "impossible",
   "no structure" are banned in this document's outputs.

---

# PART 9 — PRE-COMMITMENT

Filled in **before** the run.

## 9.1 What counts as a rule candidate

A pattern is promoted to **rule candidate** only if all four hold:

1. It survives in the **clean exhaustive band `30 < H ≤ 60`** — not only in sampled strata, and not
   only in the contaminated band.
2. It is **scale-invariant** (A1 algebra) or its scale dependence is stated as part of the rule.
3. Its **matched control fired** (C0 passed, PC5 showed the control can distinguish).
4. It is stated **in the framework's own objects** — flanks, `(c,a)` invariants, `ν₂`, gaps — not
   in an imported vocabulary (`feedback-n8-no-prereg-no-imports`).

A rule candidate is graded `[EMPIRICAL — scope]`. It becomes `[VERIFIED-INSTANCE]` only when
exhaustively checked over a named finite band. **It never becomes `[PROVED]` by this route.**

## 9.2 Outcome table — decided now

| outcome | conclusion, committed |
|---|---|
| `C1` fails | Implementation error. Run stops. Nothing is reported. |
| Any `|S| = 0` set found in `30 < H ≤ 60` | **Counterexample to Existence at order 8 via the grid door.** Highest-priority result; verify in exact `Fraction`, then in Lean, before anything else is written. |
| PC1–PC6 all fire, A2 shows pooled shift > resolution | A2 is a rule candidate; report shift with scope, and the conditional-on-invariant version (§7 subspace clause). |
| PC4 fails to fire at 1/20 | A2 is **UNINFORMATIVE**. Report as such. No A2 null may be quoted. |
| A3 proxy pairs found (expected under P5) | A3-as-submitted is **falsified**; report the frequency and the two mutual informations. This is a *result about the spec*, and it is reported, not quietly dropped. |
| A3′ coarseness collapse found | Rule candidate: `S` factors through something strictly coarser than `I`. Characterise the quotient; this is the most promotable outcome in the list. |
| A3′ zero collapse found | `S` separates `I`-classes at this band; stated conditionally with the band. |
| A4′ matches the independence prediction | No joint effect detected at `Δ ≥ 0.009` over the declared scope. Conditional phrasing mandatory. |
| A5 indistinguishable from gap-matched control | AP-specialness for `S` not detected beyond gap multiset, at the declared `n` and floor. **Does not** license "AP is not special". |
| A6 `Δ_j` inside the random-`j` distribution | Which element is dropped not detected to matter for `S` at this `n`. P6 still stands as the proved direction. |
| A7 monotone in `e` everywhere | `e`'s role reduces to magnitude in the band examined — but the known rank-2/3 cases predict otherwise, so this outcome would itself flag an implementation error. Check against `three_largest_v1.py` before reporting. |
| A8 invariant under `ν₂` permutation | Only the `ν₂` multiset detected to matter; conditional phrasing. |
| Any axis underpowered per §5 | Reported as **underpowered**, never as null. |

## 9.3 The rule against post-hoc axis selection  `[binding]`

- The axis list is **frozen** at A1, A2, A3′ (+ proxy arm), A4′, A5, A6, A7, A8, A9 by this
  document. An axis added after data is seen is a **new pre-registration**, a new document, and its
  results may not be pooled with these.
- The primary statistic is **frozen** at `T = |S(ds)|`. Promotion of any secondary statistic to
  primary after the run is a deviation and must be listed as one.
- The `H` bands are **frozen**. Extending `H` after seeing a result at `H = 60` is a new
  pre-registration.
- **No sub-band, residue class, or set family may be selected after the run** to carry a result. If
  a subset looks special, that is a hypothesis for a *new* pre-registration, tested on a *disjoint*
  band. The `p^{-0.36}`-from-three-points failure was exactly this.
- **Deviations are disclosed, not avoided.** Any departure from this document is listed in the
  run's deviation list with its reason. A disclosed deviation is acceptable; an undisclosed one
  voids the run.

---

## Run manifest — write these before executing

| file | contents |
|---|---|
| `experiments/n8/prereg_witness_instrument_v1.py` | P1–P6 assertions, six PASS lines. Must pass first. |
| `experiments/n8/witness_perturb_v1.py` | the sweep; reads seeds from its header; writes the three outputs below |
| `experiments/n8/witness_perturb_v1.out` | per-axis results, every number carrying its scope |
| `experiments/n8/witness_perturb_v1_positives.jsonl` | §8.1, append-only |
| `experiments/n8/witness_perturb_v1_strata.csv` | realised per-stratum counts, `skipped_collision` counters |

**Grade of everything this manifest can produce: `[EMPIRICAL — scope]` or `[VERIFIED-INSTANCE]`.
Nothing here proves anything.**
