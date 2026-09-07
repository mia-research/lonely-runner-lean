# PRE-REGISTRATION v1 — n = 8 extension of the Theorem 5.2 / Conjecture 5.2-H mining scan

**Written:** 2026-09-07
**Status at time of writing:** NO n = 8 statistic has been computed. See §0 for the exact,
exhaustive list of what *was* computed before this file was written, and why each item is
outcome-independent.
**Harness under extension:** `LonelyRunner/scripts/phase5_residue_structure.py`
(+ `phase6_residual_arithmetic.py`, `phase6b_density_separator.py` for the derived strata,
`phase3b_lrc_realisable.py` for the DI/ModDI classifier).
**Manuscript anchors:** `lrc_proof_allN_v11_8.md` — Conjecture 5.2-H (l.586), Theorem 5.2-S
(l.591), Corollary 5.2-S' (l.623), Theorem 5.2-P (l.632), Remark 5.2-P (l.659),
Remark 5.2-V (l.686), Theorem 5.2-U (l.723), Remark 5.2-C (l.991), Lemma 5.2-D (l.1006).

---

## 0. WHAT WAS COMPUTED BEFORE THIS SPEC WAS WRITTEN (disclosure)

Ordering is the mechanism, so the pre-spec computation is itemised rather than summarised.
Three classes of computation were run. **None of them evaluates `N_joint`, the pigeonhole
predicate, or any residue statistic at n = 8.**

**(a) Control reproduction on the PUBLISHED n ≤ 7 range.** Required by §5; a control that has
not been shown to fire cannot be registered as a control. Results are in §5.1. This is
re-derivation of already-published numbers, not new data.

**(b) Definitional disambiguation on the PUBLISHED n ≤ 7 range.** The manuscript and the
harness use the phrase "LRC-shape" for two different sets. Resolved in §2.4. Again n ≤ 7 only.

**(c) Enumeration sizing at n = 8: tuple COUNTS and a COST PROXY only.** Explicitly computed:
the number of `(G_speeds, A_speeds, p)` tuples surviving the admissibility filters, broken down
by `(k_G, k_A)`, by `δ`, and by speed-pool size `S ∈ {8, 9, 10}`; the `classify_lrc` label
(DI / ModDI / neither), which is a function of `(n, G, A, p)` alone; and
`Σ |I_G|·L_A·p` as a runtime proxy. `|I_G|` enters only as a scalar in the cost sum.
No `I_A` intersection, no band set `B`, no `N_joint`, no pigeonhole predicate, no per-input
record was produced or inspected. Sizing scripts are in the session scratchpad and are
superseded by the run script named in §6.3.

**What this disclosure buys:** the enumeration bounds in §1 were chosen with knowledge of
*how many* n = 8 inputs each bound admits and *how long* each costs, and with knowledge of
which `(k_G, k_A)` shapes the DI/ModDI definition forces. They were chosen with **no**
knowledge of how any of them behaves under the pigeonhole predicate. That is the ordering
this document exists to fix.

---

## 1. OBJECT and ENUMERATION SPACE

### 1.1 Object

The object is the **joint fine-cell configuration** of a Theorem 5.2 invocation, i.e. the pair
of sets

- `I_G := good_cell_idx(G_speeds, n, L_G) ⊆ [0, n·L_G)`,
- `I_A := good_cell_idx(A_speeds, n, L_A) ⊆ [0, n·L_A)`,

together with the band map `α₀ ↦ [α₀·L_A·p, (α₀+1)·L_A·p)` and its β-projection
`B ⊆ [0, n·L_A)`, at `n = 8`. The target is `N_joint := |B ∩ I_A|` and the derived question is
whether `N_joint = 0` (a counterexample to the abstract non-emptiness statement) can occur in
the LRC-relevant shape. Definitions are taken verbatim from
`phase5_residue_structure.py::good_cell_idx` and `::compute_residue_structure`.

### 1.2 Tautology / disjointness of construction

Three features are used to stratify the outcome. Their construction relative to the target:

| feature | constructed from | disjoint from `N_joint`? |
|---|---|---|
| `δ := k_G + k_A − (n−1)` | `(n, k_G, k_A)` only — cardinalities | **YES**, fully disjoint |
| `lrc_class ∈ {DI, ModDI, neither}` | `(n, G_speeds, A_speeds, p)` — arithmetic side conditions | **YES**, fully disjoint |
| pigeonhole predicate `\|B\| + \|I_A\| > n·L_A` | the *same* band set `B` and target set `I_A` that define `N_joint` | **NO** — shares construction |

The δ-discriminator and the DI/ModDI classifier are object-level, disjoint-construction
features; the outcome cells in §3 that use them are valid tests.

The pigeonhole predicate is **not** a disjoint-construction feature and must never be reported
as an independent predictor of `N_joint`. Its relationship to `N_joint` is a *theorem*
(Theorem 5.2-P: `|B| + |I_A| > n·L_A ⟹ B ∩ I_A ≠ ∅ ⟹ N_joint ≥ 1`), not an empirical
correlation. Consequences, fixed now:

- The Remark 5.2-P table cell "pigeonhole holds AND `N_joint = 0`" is **impossible by
  theorem**. It is not evidence. It is an implementation check: see §5.3.
- The n ≤ 7 phrase "perfect empirical separation" (PHASE5_FINDINGS l.9, Remark 5.2-P l.661)
  overstates what the 0-cell shows. Half of that "separation" is forced. The n = 8 report must
  not repeat the phrase. What is genuinely empirical is only the *rate*
  `#{pigeonhole holds} / #{stratum}` and the identity of the residual set.

### 1.3 Enumeration space — n = 8, PRIMARY scope

```
n                 = 8                                   (single value; not pooled with n ≤ 7)
SPEED_POOL        = {1, 2, ..., 10}                      (S = 10)
G_speeds          ⊆ SPEED_POOL, 1 ≤ k_G ≤ 6, sorted, distinct
A_speeds          ⊆ SPEED_POOL, 1 ≤ k_A ≤ 6, sorted, distinct
G_speeds ∩ A_speeds = ∅
PRIMES            p ∈ {2, 3, 5, 7, 11, 13, 17, 19}
```
Admissibility filters, taken verbatim from `phase5_residue_structure.py::main` lines 202–224:
```
I_G ≠ ∅                                    (Theorem 5.2 hypothesis μ(G ∩ [0,1)) > 0)
I_A ≠ ∅                                    (Theorem 5.2 hypothesis μ(A) > 0)
gcd(p, L_G) = 1                            (Theorem 5.2 hypothesis)
p ∉ G_speeds, p ∉ A_speeds                 (harness filter — see §1.6 hole H5)
p < n·L_G                                  (HARD REGIME — this is the object of study)
gcd(p, gcd(G_speeds ∪ A_speeds)) = 1       (harness filter — primitivity)
```
**The `n·L_G·L_A·p ≤ 5 000 000` cap on line 220 is REMOVED. See §1.5.**

### 1.4 Justification of each bound — principled vs convenient

A bound is **principled** if it is forced by the definition being tested, inherited unchanged
from the control so the two runs are comparable, or set by a resource limit stated in advance
and independent of the outcome. A bound is **convenient** if the space of alternatives was
searched and the one retained was the one under which a desired result held. No bound below
was selected by that procedure; §0 records that no outcome statistic existed when they were
chosen.

**B1. `k_G ∈ [1,6]`, `k_A ∈ [1,6]` — FORCED for the δ = 0 stratum; conventional for δ ≥ 1.**
DI requires `|slow| = n − 2 = 6` and `k_A = 1`, so `(k_G, k_A) = (6, 1)`.
ModDI requires `r := k_A − 1 ∈ [1, n−3] = [1,5]` and `k_G + r = n − 2 = 6`, so
`k_A ∈ [2,6]`, `k_G ∈ [1,5]`. In both cases `k_G + k_A = 7 = n − 1`, i.e. `δ = 0`.
Therefore on the δ = 0 stratum the caps `k_G ≤ 6`, `k_A ≤ 6` are **not restrictions at all** —
they are the definition of DI/ModDI at n = 8. For the δ ≥ 1 stratum they *are* a free choice;
recorded as hole **H3**.

**B1'. This bound is the whole reason the scan needs designing.** Transplanting the n ≤ 7
caps `k_G ≤ 3`, `k_A ≤ 2` to n = 8 gives `k_G + k_A ≤ 5 < 7`, hence **zero LRC-shape inputs at
n = 8**. A scan run at the inherited caps would produce 8,787 admissible n = 8 tuples, all of
them `δ ≤ −2`, i.e. entirely inside the region already handled unconditionally by
Theorem 5.2-S (`δ ≤ −1`), and would report "no counterexample at n = 8" while having tested
nothing that Conjecture 5.2-H is about. That is the concrete form the frame error takes here.

**B2. `SPEED_POOL = {1,…,10}` — inherited from the manuscript's own prior scope.**
Remark 5.2-C (l.992–1004) already publishes an exhaustive search at "slow speeds ≤ 10". Using
the same ceiling makes the n = 8 result commensurable with a bound the manuscript has already
committed to, and it is a larger pool than the control's `{1,…,8}`, so it cannot be the
smallest pool at which a desired outcome appears. Additionally, `δ ≤ S − (n−1) = 10 − 7 = 3`,
which **exactly matches the δ-range of the n ≤ 7 counterexamples** (`δ ∈ {1,2,3}`,
counts 69 / 333 / 279). Matching the discriminator's own range to the control is the reason
`S = 10` rather than `S = 9` (`δ ≤ 2`) or `S = 8` (`δ ≤ 1`).

**B3. `p ∈ {2,…,19}` prime — inherited unchanged from the control.** Comparability with
Remark 5.2-P is the point of the arm. Two admissions: (i) Theorem 5.2 requires only
`gcd(p, L_G) = 1`, not primality, so restricting to primes is a scope restriction not present
in the theorem (hole **H4**); (ii) `p ≤ 19` is a hard ceiling — hole **H2**. Note that at
n = 8 with `k_G` large, `L_G` is large, so `p < n·L_G` is essentially never binding and
`p ≤ 19` is the *only* operative constraint on `p`. Stated so no reader mistakes the hard-regime
condition for a live filter here.

**B4. `n = 8` alone; results never pooled with n ≤ 7.** Every number this scan produces
carries the scope tag in §4.4.

**B5. Nested-subset robustness is MANDATORY and pre-committed.** Because
`S = 8 ⊂ S = 9 ⊂ S = 10` are nested, every outcome cell in §3 will be reported **three times**,
sliced by `max(G_speeds ∪ A_speeds) ≤ 8`, `≤ 9`, `≤ 10`. This is free (one run, three slices)
and it removes the "the bound was chosen so the pigeonhole succeeds" objection mechanically:
if a cell's answer changes with `S`, the run says so in its own primary table. Pre-committed
sizes (from §0(c), outcome-free): total admissible tuples 28,890 / 88,287 / 258,814; δ = 0
tuples 4,308 / 20,430 / 69,387; DI+ModDI tuples 4,122 / 19,464 / 66,044.

### 1.5 The `M ≤ 5 000 000` cap is removed — and this is a change from the control

`phase5_residue_structure.py` line 220 silently discards any input with
`n·L_G·L_A·p > 5·10⁶`. Two facts:

1. In `compute_residue_structure`, `M` is computed (line 122) and **never used**. The actual
   cost of the function is `O(|I_G| · L_A · p)`, not `O(M)`. The cap is a vestige of
   `phase3b_lrc_realisable.py` line 228, where a literal `for mpp in range(M)` loop existed.
   It is therefore not a cost control in phase5; it is an undeclared filter.
2. At n = 8, `S = 10`, the cap would discard **10,688 of 258,814** admissible tuples (4.1%),
   concentrated at large `L_G`·`L_A` — precisely the large-modulus end of the space.

**Decision, fixed now:** the cap is removed. Runtime is instead controlled by the declared
budget in §6. The run must additionally report the count of inputs it would have dropped
(expected 10,688 at `S = 10`) and re-report all §3 cells restricted to `M ≤ 5·10⁶`, labelled
`[cap-matched control arm]`, so the n = 8 numbers can be compared like-for-like with the n ≤ 7
publication if anyone needs that comparison. If the removal-vs-cap comparison changes any §3
cell, that is itself a reportable finding about the control's scope.

### 1.6 UNEXAMINED regions of the n = 8 input space — stated in advance

| id | region left unexamined | why it matters |
|---|---|---|
| **H1** | speeds > 10 | Conjecture 5.2-H is for all integer speeds. Nothing here bounds the unbounded-speed case. `δ ≥ 4` requires `S ≥ 11` and is therefore entirely unexamined. |
| **H2** | `p > 19` (with `p < n·L_G` still holding) | Large `p` is partly covered analytically by Theorem 5.2-U / Corollary 5.2-U'; the intermediate band `19 < p < n·L_G` where 5.2-U's disjoint-band hypothesis fails is untested at n = 8. |
| **H3** | `k_G > 6` or `k_A > 6` in the δ ≥ 1 stratum | These caps are conventional, not forced. δ ≥ 1 with very unbalanced `(k_G, k_A)` is untested. Irrelevant to δ = 0, where the caps are forced. |
| **H4** | composite `p` coprime to `L_G` | Theorem 5.2 permits it; the harness does not test it, at n ≤ 7 or n = 8. |
| **H5** | `p ∈ G_speeds ∪ A_speeds` | Excluded by harness lines 215/217. Not a Theorem 5.2 hypothesis. Inherited from the control unchanged; a genuine hole in both. |
| **H6** | `n ≥ 9` | Out of scope by construction. |
| **H7** | inputs with `I_G = ∅` or `I_A = ∅` | Correctly excluded — these violate Theorem 5.2's positive-measure hypotheses. Listed for completeness, not a defect. |

---

## 2. STATISTICS COMPUTED PER INPUT

All are functions of `(n, G_speeds, A_speeds, p)` alone and are computable without reference
to any outcome. Definitions are reused **verbatim** from the existing harness; deviations are
flagged.

### 2.1 Primary (from `phase5_residue_structure.py::compute_residue_structure`, unchanged)

| field | definition | transfers to n = 8 unchanged? |
|---|---|---|
| `L_G`, `L_A` | `lcm_list(G_speeds)`, `lcm_list(A_speeds)` | yes |
| `cIG`, `cIA` | `\|I_G\|`, `\|I_A\|` via `good_cell_idx` | yes — `good_cell_idx` tests `1 ≤ (m // (L//v)) % n ≤ n−2`, i.e. `1 ≤ · ≤ 6` at n = 8; no n-dependence beyond that |
| `n_band_betas` | `\|B\|` | yes |
| `N_joint` | `\|B ∩ I_A\|` — **`phase5` line 147 assigns the full intersection size**, not a 0/1 indicator, despite the local variable name `N_joint_indicator` and the docstring | yes; naming defect noted, value is correct |
| `res_G_mod_LG`, `res_G_mod_LG_full` | `\|{a mod L_G : a ∈ I_G}\|`, and whether it equals `L_G` | yes |
| `n_band_betas_mod_LA`, `n_missed_LA` | band β-residues mod `L_A`, and the complement count | yes |
| `target_in_missed_LA`, `targets_all_missed_LA` | Stage-1 mechanism indicators (PHASE5_FINDINGS §"Two-stage") | yes |
| `lrc_class` | `classify_lrc(n, G, A, p) ∈ {DI, ModDI, neither}` | **conditionally** — see §2.3 |

### 2.2 Derived, computed in the same pass (not a second post-hoc script)

| field | definition | note |
|---|---|---|
| `delta` | `k_G + k_A − (n−1)` = `k_G + k_A − 7` | Remark 5.2-V's δ. Integer. |
| `pigeon` | `(n_band_betas + cIA) > n·L_A` | Theorem 5.2-P's predicate. Boolean, exact integer comparison. |
| `slack` | `n_band_betas + cIA − n·L_A` | **signed integer**; `pigeon ⟺ slack > 0`. Note `phase6::deficit = −slack` with the opposite sign convention; `slack` is used here and the sign convention is stated on every reported number. |
| `vmax_all` | `max(G_speeds ∪ A_speeds)` | needed for the §1.4-B5 nested slices |

### 2.3 Where the n ≤ 7 definition does NOT transfer unchanged — flagged

- **`classify_lrc` ModDI branch, `r ≤ n − 3`.** At n = 8 this permits `r ≤ 5` hence
  `k_A ≤ 6`, versus `r ≤ 4`, `k_A ≤ 5` at n = 7. The function is n-parametric and needs no
  edit, but the *reachable* `(k_G, k_A)` set changes, which is why §1.4-B1 exists. This is the
  only substantive n-dependence in the classifier.
- **`classify_lrc` DI branch, `len(G_speeds) == n − 2`.** Requires `k_G = 6` at n = 8, versus
  `k_G = 5` at n = 7 — unreachable under the control's `k_G ≤ 3`. Again no code change, but the
  control never exercised this branch at n ≥ 6. Pre-registered check in §5.4.
- **`phase6::fine_structure` line 96, `shift_res_mod_LA`.** The code computes
  `{(r * L_A // L_G) % L_A}` (integer division applied to `r*L_A`), whereas the `phase5`
  docstring (l.12) describes `((r * L_A) mod (n·L_G·L_A)) // L_G mod L_A`. These are not the
  same map. `shift_res_mod_LA` is a **reporting-only** diagnostic; it feeds no §3 outcome cell.
  It is carried forward unchanged for continuity and is labelled "diagnostic, definition
  disputed" wherever printed. It must not be used to support any n = 8 claim.
- **Float fields in `phase6`/`phase6b`** (`cover_density`, `expected_overlap`,
  `cell_density_product`, `band_overlap_ratio`, `coverage_density`, `target_density`) — see §8.

### 2.4 "LRC-shape" means two different things — resolved before the run

The manuscript and the harness disagree, and the disagreement is invisible from the published
numbers. Verified by re-running the n ≤ 7 enumeration (§0(a),(b)):

| definition | n ≤ 7 count | pigeonhole holds | pigeonhole fails | `N_joint = 0` |
|---|---|---|---|---|
| `lrc_class ∈ {DI, ModDI}` | **5,517** | **5,464** | **53** | 0 |
| `δ = 0` | **8,388** | 8,305 | 83 | 0 |

**The published triple 5,517 / 5,464 / 53 is the `DI ∪ ModDI` definition, not `δ = 0`.**
Remark 5.2-V (l.692) labels its column "`δ = 0` (LRC-shape)" and puts 53 in it; the 53 comes
from `phase6::stratify` line 208, which tests `r["lrc_class"] in {"DI","ModDI"}`. Under the
literal `δ = 0` reading the correct entries would be 83 and 8,388. Also verified:
`DI ∪ ModDI ⊆ {δ = 0}` strictly — 5,517 of the 8,388 (2,871 inputs have `δ = 0` but classify
as `neither`; zero inputs classify as DI/ModDI with `δ ≠ 0`).

**Decision, fixed now:** the n = 8 run reports **both strata separately and never merges
them**. `LRCSHAPE_STRICT := lrc_class ∈ {DI, ModDI}` (the published definition) and
`DELTA0 := δ = 0` (the manuscript's stated definition). Every §3 cell is evaluated on both.
Pre-committed n = 8 stratum sizes at `S = 10` (outcome-free, from §0(c)):
`LRCSHAPE_STRICT` = 66,044 (DI 1,452 + ModDI 64,592); `DELTA0` = 69,387.

This discrepancy is a **finding about the manuscript**, independent of anything n = 8 produces,
and is reportable as such. It does not change the truth of Remark 5.2-P's claim; it changes
what set that claim is about.

---

## 3. PRE-COMMITTED OUTCOME CELLS

Scope tag `[n=8, S≤10, k_G≤6, k_A≤6, p≤19 prime, hard regime p<n·L_G, no M cap]` is implicit
on every statement below and must be written out on every number the run reports.

Each cell is evaluated **twice**, once on `LRCSHAPE_STRICT` and once on `DELTA0` (§2.4), and
each of those **three times**, on the nested slices `S ≤ 8 / 9 / 10` (§1.4-B5). A cell that
fires under one definition or one slice and not another is reported as firing, with the
qualification attached; it is not resolved by choosing the definition that gives the cleaner
answer.

### Cell A — some LRC-shape n = 8 input has `N_joint = 0`

**Meaning.** A direct counterexample to Conjecture 5.2-H in its own stated scope
(`p < n·L_G` and `k_G + k_A = n − 1`).

**Conclusion licensed, pre-committed.** Conjecture 5.2-H is **FALSE as stated**. Theorem 12.1
is not merely conditional on it — it is conditional on a false statement, and every §10.1/§11.1
invocation routed through Conjecture 5.2-H must be re-derived or the conjecture re-scoped.
Corollary 5.2-S' must be withdrawn as written. The counterexample is the finding; it is
reported with its full input tuple, is re-verified independently by exact rational interval
arithmetic (`phase3b::joint_good_intervals` on the reconstructed full speed set), and is
checked against Lemma 5.2-D (a 5.2-D-certified input is still unconditionally fine for
Theorem 12.1 even if it kills 5.2-H). **This cell fires ⟹ this is §1 of the report and
nothing computed afterwards may be presented as mitigating it.** Any subsequent analysis is
labelled `EXPLORATORY`.

### Cell B — all n = 8 LRC-shape inputs satisfy the pigeonhole (`slack > 0` for every one)

**Meaning.** Theorem 5.2-P alone discharges Conjecture 5.2-H throughout the scanned n = 8
LRC-shape space; the "53-residual" phenomenon of n ≤ 7 has no n = 8 analogue in scope.

**Conclusion licensed, pre-committed.** `Conjecture 5.2-H holds unconditionally on
[scope tag], via Theorem 5.2-P, for all N inputs.` **That is the entire claim.** Explicitly
NOT licensed, and named here so it cannot be written later: that the residual phenomenon is
absent at n = 8 (it is absent *in this scope*); that the pigeonhole "always" holds under
LRC-shape; that Theorem 12.1 becomes unconditional; that n = 8 is "clean" or "closed". Holes
H1–H5 are restated verbatim in the report next to the number.

**Mandatory accompanying readout — a magnitude is not a verdict.** If Cell B fires, the report
must additionally state, per `(k_G, k_A)` and per `p`:
`slack_min := min slack` over the stratum, and the count at `slack ∈ {1,2,3}`. If `slack_min`
is small and decreasing in `vmax_all` or in `L_A/L_G`, the structure is in the *margin*, not in
the counterexample count, and the report says so and registers the next probe (larger `S`).
A Cell-B fire with `slack_min` unreported is an incomplete run, not a result.

### Cell C — some n = 8 LRC-shape inputs fail the pigeonhole but have `N_joint ≥ 1`

**Meaning.** The n = 8 analogue of the 53 residuals: Layer 2 (arithmetic alignment) is load-
bearing at n = 8 and Theorem 5.2-P does not suffice.

**Conclusion licensed, pre-committed.** `Theorem 5.2-P discharges K of N n = 8 LRC-shape
inputs on [scope tag]; the remaining R require direct verification, which was performed
(N_joint ≥ 1 for all R).` Conjecture 5.2-H then holds on the scope by 5.2-P ∪ direct check,
exactly as at n ≤ 7. The residual set `R` is **characterised, not just counted**: its `p`
histogram, `cIG` distribution, `(k_G, k_A)` shape, `lrc_class` split, and Stage-1 vs Stage-2
mechanism split (`targets_all_missed_LA`) are reported. The n ≤ 7 residual signature for
comparison is: 53 inputs, `p` = {2:30, 3:21, 5:1, 7:1}, `n` = {4:2, 5:28, 6:23},
`lrc_class` = {ModDI:34, DI:19}. Whether the n = 8 signature matches is a stated comparison,
not a conclusion drawn afterwards.
**If `R` is large enough that direct verification is the real workhorse** (say `R/N` exceeds
the n ≤ 7 rate of 53/5517 = 0.96% by more than an order of magnitude), the pre-committed
reading is that **Theorem 5.2-P weakens with n** and the report registers that as the finding,
with `R/N` as a function of `n` across n ∈ {4,5,6,8} — not as a footnote to a "still no
counterexample" headline.

### Cell D — the δ discriminator at n = 8

**Sub-cell D1 (holds as at n ≤ 7):** every `N_joint = 0` input has `δ ≥ 1`, and no LRC-shape
input has `N_joint = 0`.
**Conclusion:** `The δ-discriminator of Remark 5.2-V extends to n = 8 on [scope tag], with
δ ∈ [−5, +3] examined and δ ≥ 4 unexamined (H1).` Report the counterexample δ-histogram
alongside the n ≤ 7 one (`{1:69, 2:333, 3:279}`).

**Sub-cell D2 (fails):** some `N_joint = 0` input has `δ = 0`. This is Cell A; Cell A's
conclusion governs and D2 is not reported separately.

**Sub-cell D3 (vacuous — pre-registered because it is the likely structural trap):** the
n = 8 δ ≥ 1 stratum contains **no** `N_joint = 0` inputs at all. Then the discriminator is
untested at n = 8, because a discriminator between "CE" and "non-CE" says nothing when the CE
class is empty. **Conclusion:** `The δ-discriminator is UNTESTED at n = 8 on [scope tag]: the
δ ≥ 1 stratum yielded 0 counterexamples, so the n ≤ 7 δ-separation is neither confirmed nor
refuted here.` It is explicitly not "the discriminator holds at n = 8". Pre-committed sizes of
the δ ≥ 1 stratum at `S = 10` (outcome-free): δ=+1: 46,912; δ=+2: 17,544; δ=+3: 2,688; total
67,144.

**Sub-cell D4 (partial):** counterexamples occur at δ ≥ 1 but the δ-histogram is qualitatively
different from n ≤ 7 (e.g. concentrated at a single δ). Reported as a *shape* comparison with
no verdict beyond the histograms; registers the next probe.

### Cell E — must-not-fire (implementation check, not evidence)

`pigeon = True` AND `N_joint = 0` for any input, at n = 8 or in the n ≤ 7 control. This is
impossible by Theorem 5.2-P (§1.2). **If it fires, the run is void and the defect is in the
code**, and the correct output is the bug, not a mathematical claim. `phase6::main` line 344
already asserts the n ≤ 7 version of this; the n = 8 runner must carry the same assertion.

---

## 4. POWER AND SCOPE

### 4.1 The scan is exhaustive, so "power" means coverage, not detection probability

There is no sampling and no noise: within the scope of §1.3 every admissible tuple is
evaluated and `N_joint` is an exact integer. Detection probability for any effect **inside**
the scope is therefore 1, and for any effect **outside** it is 0. No p-values, no z-scores,
no surrogate null is appropriate or will be computed. The honest power statement is the list of
holes H1–H7 (§1.6) plus the largest input actually reached (§4.3).

### 4.2 Cells that are under-powered at the chosen bounds — stated now

- **Cell D is under-powered by construction if D3 obtains.** The δ-discriminator can only be
  tested at n = 8 if the δ ≥ 1 stratum produces counterexamples. Nothing in the design
  guarantees that. D3 is pre-registered precisely so a vacuous test cannot be written up as a
  confirmation.
- **δ ≥ 4 has zero power** (needs `S ≥ 11`; H1).
- **The δ ≥ 1 stratum's `(k_G, k_A)` coverage is incomplete** (H3): at `S = 10`, `δ ≥ 1`
  requires `k_G + k_A ≥ 8` with both ≤ 6, so shapes like `(7,1)` or `(1,7)` are absent.
- **Cell A has power 1 within scope and 0 outside it.** A non-fire is a bounded statement about
  66,044 (or 69,387) inputs. It is not evidence about unbounded speeds, and the report may not
  phrase it as one (`feedback_conditional_negatives_phrasing`).
- **Comparison of n = 8 against "n ≤ 7" is not a comparison against n = 7.** The published
  5,517 LRC-shape inputs are distributed n = {4: 623, 5: 2,263, 6: 2,631} and
  **n = 7 contributed exactly ZERO**, because `k_G ≤ 3, k_A ≤ 2` gives `k_G + k_A ≤ 5 < 6 = n−1`.
  The 53 residuals likewise sit at n ∈ {4,5,6} only. Corollary 5.2-S' (l.628) describes the
  direct-verification range as "`n ≤ 7`"; for the LRC-shape claim the true range is `n ≤ 6`.
  **The n = 8 run therefore skips n = 7 in the LRC-shape series and this gap must be stated on
  every trend claim.** Filling n = 7 (`k_G + k_A = 6`, `k_G ≤ 5`, `k_A ≤ 5`) is registered as a
  separate arm, NOT part of this pre-registration, and its results may not be merged into this
  run's tables.

### 4.3 Largest input actually reached

At `S = 10`, `k_G = 6`: `L_G` can reach `lcm` of six speeds from {1,…,10}, up to 2,520;
`n·L_G` up to 20,160. With `k_A = 6`, `L_A` up to 2,520 and `n·L_A` up to 20,160. The largest
band-space modulus `n·L_G·L_A` reaches order `5·10⁷`, and the largest `M = n·L_G·L_A·p` order
`10⁹` — all of which the removal of the §1.5 cap admits, and none of which is enumerated
directly (cost is `|I_G|·L_A·p`). The largest single-input work is bounded by the §6 budget.
**The run must report the actual observed maxima** of `L_G`, `L_A`, `n·L_A`, `cIG`, `cIA`,
`n_band_betas`, and `M`, so §4.3 is a measured statement and not this estimate.

### 4.4 Scope tag — mandatory on every number

```
[n=8 | speeds ∈ 1..10 | k_G ∈ 1..6, k_A ∈ 1..6 | p prime ≤ 19 | gcd(p,L_G)=1 | p < n·L_G
 | I_G, I_A ≠ ∅ | p ∉ G ∪ A | primitive | no M cap | stratum: LRCSHAPE_STRICT or DELTA0]
```
No number from this run may be stated without it. Numbers from the n ≤ 7 control carry the
control's own tag (`speeds ∈ 1..8, k_G ≤ 3, k_A ≤ 2, p ≤ 19, M ≤ 5·10⁶`) and the two sets of
numbers are never placed in the same column without both tags visible.

---

## 5. CONTROL, PLANTED CONTROL, AND FALSIFICATION

### 5.1 Matched control — the n ≤ 7 reproduction. ALREADY RUN; IT FIRES.

Re-running `phase5_residue_structure.py`'s enumeration and `compute_residue_structure` at the
published bounds (`n ∈ {3,4,5,6,7}`, speeds 1..8, `k_G ≤ 3`, `k_A ≤ 2`, `p ≤ 19`,
`M ≤ 5·10⁶`) reproduces:

| quantity | published | reproduced |
|---|---|---|
| total inputs | 38,664 | **38,664** ✔ |
| counterexamples `N_joint = 0` | 681 | **681** ✔ |
| pigeonhole holds (all strata) | 34,825 | **34,825** ✔ |
| CE with pigeonhole holding | 0 | **0** ✔ (forced; §1.2) |
| LRC-shape (`DI ∪ ModDI`) | 5,517 | **5,517** ✔ |
| … pigeonhole holds | 5,464 | **5,464** ✔ |
| … pigeonhole fails (the residuals) | 53 | **53** ✔ |
| CE δ-histogram | {1,2,3} | **{1:69, 2:333, 3:279}** ✔ |
| 53-residual `p`-histogram | {2,3} + outliers {5,7} (Remark 5.2-P) | **{2:30, 3:21, 5:1, 7:1}** ✔ |

Wall time 9.1 s. `reports/phase5_residue_structure.csv` on disk has 38,664 data rows,
consistent.
**Additional control requirement for the n = 8 run:** the runner script must re-execute this
reproduction in the same process, from the same code path, and abort before touching n = 8 if
any row above disagrees. A run that does not carry its own control output is void.

*Documentation defect found by the control (reportable independently of n = 8):*
`PHASE5_FINDINGS_2026_05_27.md` line 65 states the 53 residuals "all have `p = 2`". They do
not — 30 do. Remark 5.2-P (l.678) is correct.

### 5.2 What the matched control preserves and destroys

This is an exhaustive deterministic enumeration; there is no shuffle and none is appropriate.
A permutation control here would be an invalid null: `N_joint` is determined by
`(n, G, A, p)`, so permuting anything either changes the input (making it a different, equally
valid input, not a null) or leaves it fixed. The control that *is* matched is the one above:
same code path, same statistic, same admissibility filters, different `n`. It preserves every
structure of the pipeline and varies only the quantity under test. Any n = 8 number that
cannot be produced by the identical code path that reproduces the table in §5.1 is out of
scope of this pre-registration.

### 5.3 Planted control — the CE-detection path must be shown to be reachable

The cells that matter most (A, D2) report **zero** at n ≤ 7. A zero from an unreachable code
branch is worthless. Two injections, both mandatory, both run before n = 8:

**P1 — the CE detector fires.** Inject the smallest known counterexample
`n = 3, G = [3], A = [1,5], p = 2` (PHASE5_FINDINGS l.41, `verify_smallest_ce.py`). The
harness must return `N_joint = 0`, `n_band_betas = 12`, `n·L_A = 15`, `cIA = 1`,
`slack = 12 + 1 − 15 = −2` (pigeonhole fails), `targets_all_missed_LA = 1`. If it does not,
the run is void.

**P2 — the "LRC-shape counterexample" cell is reachable.** This is the control that the n ≤ 7
study did not carry. Take P1's input and force it through the LRC-shape branch by overriding
`lrc_class := "DI"` and `δ := 0`, then run the §3 stratification. Cell A **must fire**. This
demonstrates that `#{LRC-shape ∧ N_joint = 0} = 0` is an empirical zero and not a branch that
cannot be entered. **If P2 does not fire, the reported zero in Cell A is uninformative and the
n = 8 run means nothing** — full stop, per the rule that a control that cannot fire invalidates
the null.

**P3 — the δ ≥ 1 CE path is reachable at n = 8 specifically.** Inject a synthetic record with
`n = 8`, `δ = +2`, `N_joint = 0` into the stratifier and confirm the D-cell histogram counts
it. Guards against an n-dependent stratification bug making D3 fire spuriously.

**P4 — Cell E's assertion is live.** Inject a record with `pigeon = True, N_joint = 0` and
confirm the runner aborts. Guards against a silently disabled assertion.

### 5.4 Additional pre-run check: the DI branch has never been exercised at k_G = 6

`classify_lrc`'s DI branch requires `k_G = n − 2`, which the control (`k_G ≤ 3`) reached only
for `n ≤ 5`. At n = 8 it requires `k_G = 6` and is expected to label 1,452 inputs at `S = 10`
(§2.4). Before the main run, hand-verify **three** DI-labelled n = 8 inputs against
`phase3b_lrc_realisable.py::classify_di` (an independently written implementation of the same
conditions) and require agreement. Disagreement between the two implementations voids the
`lrc_class` stratification and forces the run to report `DELTA0` only.

### 5.5 Falsification

The **hypothesis under test** is: *Conjecture 5.2-H's LRC-shape restriction is the operative
one — no LRC-shape input, at any n in scope, has `N_joint = 0`.*

**It is falsified by a single LRC-shape n = 8 input with `N_joint = 0`** (Cell A). One input.
No aggregate, no rate, no threshold. The pre-committed response is Cell A's, and it is not
negotiable after the fact.

The **secondary hypothesis** — *Theorem 5.2-P alone suffices under LRC-shape* — is already
false at n ≤ 7 (53 residuals) and is not under test. What is under test is whether its failure
rate is stable in `n`; Cell C fixes the reading.

**What would NOT falsify anything, stated now so it is not later treated as if it did:** a
clean Cell B or D1. Those are bounded positive statements over 66,044 inputs on a scope with
seven named holes. They do not close Conjecture 5.2-H, do not make Theorem 12.1
unconditional, and do not license the words *closed*, *settled*, *no structure*, *generic*, or
*clean* (`feedback_closure_grade_2026_07_28`).

---

## 6. EXACTNESS, FEASIBILITY, AND THE RUN SCRIPT

### 6.1 Exactness — no-float rule

The entire signal path is integer. `good_cell_idx`, `lcm_list`, `gcd`, the band construction,
`B`, `I_A`, `N_joint`, `slack`, `pigeon`, `delta`, `classify_lrc` — all Python `int`, all exact,
no division except floor division on integers.

**Float carve-out, declared:** `phase6`/`phase6b` diagnostics `cover_density`,
`expected_overlap`, `cell_density_product`, `band_overlap_ratio`, `coverage_density`,
`target_density`, and the Remark 5.2-V correlation ratio `N_joint / expected_overlap`. These
are **analytic-size-only reporting quantities**; none enters an outcome cell in §3, none gates
a branch. **Condition on the carve-out:** if the n = 8 report asserts any *threshold* on one of
them (as Remark 5.2-V l.709–713 does for n ≤ 7 with "at least 2.4", "never exceeds 10.07",
"at least 0.36"), that quantity must be recomputed as a `fractions.Fraction` and the threshold
stated exactly. A float-derived threshold claim is not admissible.

### 6.2 Feasibility

Calibration from the §5.1 control: 38,664 inputs, `Σ|I_G|·L_A·p = 2.08·10⁸`, wall 9.1 s
single-core CPython ⇒ ≈ 2.3·10⁷ cost-units/s.

| scope | inputs | cost proxy `Σ\|I_G\|·L_A·p` | projected wall (1 core) |
|---|---|---|---|
| n ≤ 7 control | 38,664 | 2.08·10⁸ | 9 s (measured) |
| n = 8, `S = 8` | 28,890 | 1.35·10⁹ | ≈ 1 min |
| n = 8, `S = 9` | 88,287 | 1.23·10¹⁰ | ≈ 9 min |
| **n = 8, `S = 10` (PRIMARY)** | **258,814** | **8.12·10¹⁰** | **≈ 59 min** |
| — of which `δ = 0` | 69,387 | 2.07·10¹⁰ | ≈ 15 min |
| — of which `δ ≥ 1` | 67,144 | 4.86·10¹⁰ | ≈ 35 min |

Single-core CPython is sufficient; the run is embarrassingly parallel over `k_G` if wanted.
**Declared budget: 4 hours wall.** If exceeded, the run is stopped and reported at whichever
nested slice (`S ≤ 8`, then `S ≤ 9`) completed, with the scope tag amended — **never by
dropping inputs mid-scope**, which would reintroduce a silent filter.

### 6.3 Run artefacts (fixed now)

```
experiments/n8_mining/run_n8_scan_v1.py        runner: control (§5.1) -> plants (§5.3)
                                               -> n=8 primary -> §3 cells, all slices
experiments/n8_mining/n8_scan_v1.csv           one row per input, all §2 fields + delta,
                                               pigeon, slack, vmax_all, M
experiments/n8_mining/RESULTS_v1.md            §3 cells in pre-registered order, scope tag on
                                               every number, holes H1-H7 restated, control
                                               and plant outputs quoted verbatim
```
`RESULTS_v1.md` must open with the §3 cell that fired and its pre-committed conclusion.
Anything not in §3 goes under a heading literally titled `EXPLORATORY (post-hoc, not
pre-registered)`.

---

## 7. PRE-COMMITMENT SUMMARY (the table a reader checks the run against)

| outcome | conclusion, fixed 2026-09-07 | may NOT be concluded |
|---|---|---|
| **A** — LRC-shape `N_joint = 0` exists | Conjecture 5.2-H false as stated; Cor. 5.2-S' withdrawn; re-derive 5.2-H invocations; check each CE against Lemma 5.2-D | that it is "an edge case"; anything computed after the fire is EXPLORATORY |
| **B** — all LRC-shape satisfy pigeonhole | 5.2-H holds on [scope tag] via Thm 5.2-P, N inputs; `slack_min` per `(k_G,k_A,p)` reported | that the residual phenomenon is absent at n = 8; that Thm 12.1 is unconditional; "clean"/"closed" |
| **C** — some fail pigeonhole, all `N_joint ≥ 1` | 5.2-P discharges K/N, R verified directly; R characterised and its signature compared to the n ≤ 7 53 | that R is "small" without stating R/N against 0.96%; that 5.2-P is "tight" |
| **D1** — δ discriminator holds | δ-discriminator extends to n = 8 on [scope tag], δ ∈ [−5,+3] | that it holds for δ ≥ 4 or for n ≥ 9 |
| **D3** — δ ≥ 1 stratum has no CE | δ-discriminator is **UNTESTED** at n = 8 | that it "holds at n = 8" |
| **D4** — different δ shape | report both histograms, register next probe | any verdict |
| **E** — pigeonhole holds with `N_joint = 0` | run void, code defect, report the bug | any mathematical claim |
| **control §5.1 mismatch** | n = 8 numbers mean nothing; abort | anything |
| **plant P2 does not fire** | Cell A's zero is uninformative; run void | anything |

**If the effect lives in a subspace this scan does not project onto:** the scan projects onto
`N_joint > 0 ?` and `slack > 0 ?`. An effect could live instead in (i) the *distribution* of
`slack` near 0 as `vmax_all` grows — captured by the mandatory `slack_min` readout in Cell B;
(ii) the Stage-1 / Stage-2 mechanism split (`targets_all_missed_LA` vs within-residue misses),
which changes character without changing any count — reported in Cell C unconditionally, and
also for the δ ≥ 1 stratum whether or not it contains counterexamples; (iii) the residue
geometry `res_G_mod_LG` / `n_missed_LA`, which is where the n ≤ 7 mechanism was actually
located. All three are recorded per input in `n8_scan_v1.csv` regardless of which cell fires,
so a "nothing fired" outcome still leaves the subspace data on disk. **A run whose only output
is a count is an incomplete run.**

---

## 8. OPEN ITEMS THIS SPEC COULD NOT PIN DOWN FROM THE EXISTING HARNESS

1. **`shift_res_mod_LA` (phase6 l.96) contradicts its own docstring (phase5 l.12).** Which map
   was intended is not recoverable from the code. Quarantined as reporting-only (§2.3); feeds
   no outcome cell.
2. **Remark 5.2-C's 20,403 LRC-realisable inputs** come from a different harness
   (`LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md`, `joint_fine_cell_harness.py`) with
   different bounds ("slow speeds ≤ 10"). That number is **not** reproducible from the phase5
   pipeline and is not part of this control. Whether the 20,403 set contains the 5,517 set is
   unknown and untested here.
3. **Why `SPEED_POOL = 1..8` and `PRIMES ≤ 19`** in the original harness — no justification is
   recorded anywhere in the scripts, findings files, or manuscript. Inherited, not endorsed.
4. **Why `M ≤ 5 000 000`** — no justification recorded; demonstrably vestigial in phase5
   (§1.5). Removed here, with a cap-matched control arm retained for comparability.
5. **Why `p ∉ G_speeds ∪ A_speeds`** — not a Theorem 5.2 hypothesis; no justification recorded
   (hole H5). Inherited unchanged so the control is exact.
6. **Whether Theorem 5.2 intends `p` prime.** The statement at l.580 says "positive integer
   with `gcd(p, L_G) = 1`". The harness restricts to primes. §10.1/§11.1 supply `V = p·q` with
   `p` prime, so primality is a property of the *call sites*, not of Theorem 5.2. Left as a
   scope restriction (H4), flagged, not resolved.
7. **Whether Remark 5.2-V's "δ = 0" column label or its 53 entry is the error** (§2.4). Both
   readings are internally coherent; only the author can say which was meant. The run reports
   both strata and does not choose.
8. **`native_decide` / Lean parity.** Nothing in this scan touches the Lean tree. Whether any
   n = 8 outcome would need Lean formalisation is out of scope of this pre-registration.
