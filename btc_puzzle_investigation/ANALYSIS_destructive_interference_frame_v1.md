# The destructive-interference frame: where a "beam" can and cannot exist

**Date:** 2026-07-30. **Nothing run. Nothing promoted. No grade moves.**
Origin: user's recurring intuition — *"all these null / within-noise results. I keep thinking of
destructive interference. If the analogy holds, the right beam gets signal out of the noise."*

**Prior-art check run FIRST** (per the ADDENDUM-1 near-miss lesson). The literal instrument
already exists in five places and this document does **not** re-derive them:
`spectral_matched_filter_v1.py` (set-level coherent character sum, "the literal interference
instrument"), `angular_interference_scaling_v1.py` (coherence scaling: `log N(S)` vs `log M`,
slope 1 = incoherent, slope 2 = coherent), `coord_interference_v1.py` + `masked_structure_findings_v7.md`
(joint `(x,y)` 2-D transform, exact `μ₃` resonance, magnitude generic at `p≤1009`),
`xy_interference_U_v1.py` + `_v16.md` (the complete `U(a,b,c)`; "no constructive interference in
magnitude", CM = non-CM), `conservation_spectrum_v1.py` (Koopman soft modes).
And `POSITIVE_FINDINGS_MASTER_v4.md` already carries the analogy as a **binding discipline rule**:

> *"In this problem `flat`/`generic` most often means the right basis to see the interference has
> not been found yet."*

**What is new here is not the analogy — it is taking the analogy's own conservation law seriously
enough to let it rule some searches OUT.** The record uses the rule defensively (do not declare
closure). Used offensively it makes a sharp, falsifiable prediction about *what shape* the beam
must have, and it refutes the most tempting version of the search.

---

## 1. The analogy, made exact (not a metaphor)

| optics | this project | status |
|---|---|---|
| amplitude `A = Σ a_j e^{iφ_j}` | character sum `Σ_d F(d)e_n(-ad)` | definitional |
| destructive interference at a detector | a complete sum over a group = 0 | **identity** |
| intensity conservation `∫\|A\|²` fixed | **Parseval** `Σ_a\|Corr(a)\|² = ‖F‖₂²` | exact |
| bright fringe elsewhere | the energy has to be *somewhere* | exact |
| aperture / mask | incomplete sum, short window | — |
| phase plate / matched filter | conjugate the known phase before summing | — |
| lock-in detection (phase reference) | **signed** pooling across a family | — |
| caustic (energy on a thin set) | tail / measure-zero structure in `d` | — |

The analogy is exact because the conservation law is exact. That is also why it can adjudicate
against itself, which §2 does.

---

## 2. The analogy REFUTES the most natural version of the search — and does it with its own tool

The tempting reading: *"the nulls are cancellations, so the energy is hiding at a frequency we
haven't looked at."* **For the leakage question this is false, and Parseval is what makes it false.**

`spectral_concentration_closure_v1.md` proves (given the cited KS/Weil bound) that for any readout
`F = ψ∘f` with `f` rational of degree `≤ D`, **uniformly in `a`**:
`|Corr_F(a)| = O_D(p^{-1/2+o(1)})`.

Now do the energy accounting the analogy demands. There are `n ≈ p` frequencies. Each holds
`O(polylog/p)` of the energy. Total: `O(polylog)` — and `‖F‖₂² = Ω(1)`. **The Parseval budget is
already fully accounted for by the uniform floor.** There is no unexplained energy anywhere in the
`d`-spectrum. A break needs `|Corr(a₀)| = Ω(1)` — one frequency holding `Ω(1)` of the budget, i.e.
`p/polylog` times brighter than the proved bound allows. That is not a slack issue.

**Corollary that kills a whole class of proposals: "wrong basis" is NOT an escape for complete sums.**
Any alternative lens `g` on `ℤ/n` (wavelet, Ostrowski/continued-fraction, Farey, lattice) expands in
characters, and `|Σ_d g(d)F(d)| ≤ ‖g‖_A · max_a|Corr(a)|·n`. The bound is uniform over `a`, so it
survives *every* transform with small Wiener norm — including interval indicators (`‖·‖_A ~ log p`).
Changing basis cannot manufacture a fringe that the uniform bound forbids.

`[INHERITED — PROVED given CITED KS/Weil]`. ⚠ Inherits the standing (D2) caveat: the KS/Weil
citation chain has an unverified link (3 failed `citation-verifier` runs). Not re-graded here.

**So: in the box {complete sum over `d`} × {`L²`/correlation statistic} × {bounded-degree readout},
the interference analogy is refuted, by conservation. The nulls there are not cancellations hiding
energy; the energy is genuinely spread.** Say this plainly — it is the analogy earning its keep.

---

## 3. The box has exactly three walls, and the beam must exit through one

### Wall 1 — complete sum → **APERTURE** (short windows / incomplete sums)
The bound `√p·polylog` is *true but vacuous* the moment the window `W` has `|W| ≪ √p`, because the
trivial bound is `|W|`. On a short window, structure could be **total** and no character-sum estimate
says a word. Record's own name: trichotomy regime **(b)**, "UNTOUCHED", grep for `incomplete sum` /
`short scalar` = **0 hits** at the time it was written.
Artifacts: `PREREG_incomplete_shortscalar_v1/v2.md`; `AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md`
(decision statistic `T_dev` measured **underpowered and non-monotone**; fix known — per-law `G_ℓ` + Holm
becomes primary). Blocked on an `experiment-designer` gate that failed twice (§2a applies).

### Wall 2 — `L²`/mean statistic → **CAUSTIC** (the tail)
A caustic is where an interference pattern concentrates on a thin set: the *average* is untouched,
the local intensity diverges. Every statistic in the record is mean-based; **HNP/LLL attacks are
caustic-exploiting** — they need a thin set where a relation is exact, never an average bias.
A `√p` correlation bound bounds no tail event. Record: *"every statistic is MEAN-based; LLL/HNP live
in the TAIL"*; `#17` is the record's only tail-shaped anomaly, **and its Rayleigh null is flagged as
probably the wrong null** (complex-Gaussian gives `P(|U|<ε)~ε²`; a low-dim/real trace distribution
gives `~ε`).

**★ Walls 1 and 2 are the same wall.** Both say: *a thin set in `d`-space, where full-group `L²`
statistics are vacuous by construction.* That is the single sharpest output of this frame:

> **The beam is not a frequency. It is a REGION.**
> Frequencies are proved dark (§2). Regions are not covered by any bound in the record.

### Wall 3 — bounded degree → **FAMILY** (moments with a main term)
Trichotomy regime **(c)**. Statistics over a family of primes/curves can beat `√p` when a main term
survives. `E[u⁴]` vs `1/8` is the record's first real instance. This is also where §4 lives.

*(Regime (a), multiplicative degeneracy, is blocked: `n` is prime = P14.)*

---

## 4. The second, independent application: the CURVE-STRUCTURE nulls are pooled INCOHERENTLY

§2–§3 concern *leakage*. A different family of nulls asks *is the curve special* — twist-orbit signed
spectrum (12 primes), magnitude spectrum (12 primes), monodromy `E[u⁴]` (12 primes), row-budget, the
`A==0` candidate. These pool **per-prime p-values** (then Bonferroni), or pool `|·|`. **That is
incoherent detection: it discards the sign/direction and keeps only intensity.** In physics this is
exactly how you lose a signal that is below noise per trial — you must average with a phase reference
(lock-in), and if the reference is missing, averaging destroys the signal along with the noise.

**This is not hypothetical. The record has already caught one instance.** The D4 finding
(`RESULT_n1_120deg_exact_v1.md`): a first sweep reported stratum-C `g=0` everywhere — a **false null**
— because `e₃ = −p·e₁` holds only at `p≡3 mod 4`; at `p≡1 mod 4` the closure is `α↦ᾱ` and
`e₃ = +p·e₁`. **An unaccounted arithmetic phase, flipping with `p mod 4`, produced a clean null across
a pooled family.** That is the user's mechanism, confirmed, on this project, with a named artifact.

**Candidate alignment phases** (all cheap, all arithmetic, all already in the record):
`χ₂(-1)` / `p mod 4`; `p mod 12` (the stratum); the Jacobi sign law's `±` (`p mod 3`);
`h(−p)` parity; the `m`-law's `ζ₆^{3−[28/π]₆}`; `t mod 3`.
**Common coordinate across differing `n`:** `a/n ∈ [0,1)` — the standard rescaling that makes
family/Katz–Sarnak stacking well-posed. The record notes Katz–Sarnak is cited and that **4 of the 5
standard RMT statistics were never measured**; a rescaled coherent stack is the same move.

---

## 5. The third application: the noise floor is itself coherent

Two distinct failures, both already logged, both are "your background is not white":

1. **Forced components set the variance.** `Σ_a|V(a)|² = n(n−1)`, `Σ_a V(a)V̄(a+b) = n(nδ_b−1)`
   (curve-INDEPENDENT), bispectrum `≡0` forced by parity. Where a statistic contains a forced part,
   the forced part dominates and the free residue is buried. Drill rule *"count only UNFORCED hits"*
   is this, stated combinatorially. Interference version: **project onto the free subspace before
   measuring, not after.**
2. **A structure-breaking null replicates the artifact.** `feedback_residue_vs_component_tautology`
   (the 6–7σ phantom); `kfold_gate` misuse guard 5. A shuffle that destroys forced anti-symmetry
   makes the null *incomparable*, not conservative.

**★ And the consequence nobody has checked: every power claim in the record is a power claim against
a COHERENT alternative.** Every PLANT is a coherent plant ("PLANT fires 4–6×", "4.9–10.9×"). If the
true alternative is phase-scrambled along the pooling axis, those plants **overstate** the power by an
unknown factor, and every "power confirmed ⇒ scoped-real null" inherits that scope silently.

---

## 6. Ranked probes

Ordered by (decidable artifact) × (cost) × (can it only produce a scope correction).

**P0 — THE ANTI-COHERENT PLANT.** *(recommended first; cannot manufacture a positive)*
Take pipelines that reported "power OK, PLANT fires N×" (twist-orbit signed + magnitude, monodromy,
row-budget). Re-run the **identical** plant machinery with the plant's sign flipped along the pooling
axis (by `p mod 4`; by `p mod 3`; and a random-per-prime sign as the floor). Measure detection rate.
- **Outcome A (pipeline still fires):** the nulls are scoped to both alternative classes. The
  interference worry is bounded, in writing, with a number. Strengthens the existing nulls.
- **Outcome B (pipeline goes blind):** every null it produced is scoped to *coherent alternatives
  only*, and §4's re-analysis is **mandatory, not optional**. A scope correction to a stack of
  existing results — no new claim, no false-positive risk.
- Artifact: a detection-rate table, plant × alignment × pipeline. Decidable. Uses code on disk.

**P1 — COHERENT (phase-aligned) RE-POOL of existing per-prime data.** §4. Data on disk. Signed stack
in the `a/n ∈ [0,1)` coordinate under each candidate alignment. **Scan = characterization only**
(anomaly-drill rule: output is a symmetry type / eigenvector / subspace, never a verdict), then a
pre-registered confirmatory test on held-out primes. Falsifier: the same alignment on `j≠0` controls
must NOT reproduce it. ⚠ This is the run where the user's false-positive tolerance is actually spent —
it is a scan over alignments and it *will* produce hits by chance. `kfold_gate` guard 1 (no
seed-shopping) applies: fix the OOS prime set before looking.

**P2 — MEASURE THE PHASE, not the intensity.** `a ↦ θ_a` is the record's **free** variable
(`V(a) = 2i√p·sin(θ_a+60°)`; absolute angle free, relative angle frozen at 120°). Every completed
twist-orbit test measured a function of `θ` **through the forced envelope**. Ranked `3′` in
`SYNTHESIS_..._ADDENDUM_1_v1.md`; **never run**; instrument exists
(`n1_twisted_eigenvalues_v1.sage`). Statistics: spacing/Wigner, `Δ₃`, `Σ²`, 2-pt correlation — the
**4 unmeasured RMT statistics** — on `{θ_a}` directly. This is §5.1 (project onto the free subspace)
made concrete.

**P3 — THE MATCHED FILTER, measured rather than argued.** The one remaining single-point escape is
*"a `d`-side function with `‖·‖_A ≳ √p` which must be CHEAP; constructing one requires knowing the
spectrum you are matching"*. We now know the spectrum's form. So **construct the optimal (phase-
conjugate) `g` explicitly at small `p` and measure `‖g‖_A` vs `p`**; fit the exponent. `polylog` ⇒ the
escape is open and large; `~√p` ⇒ the escape is quantitatively closed. Converts an open-ended
existence question into a finite measurement with a fitted exponent. ⚠ Check against
`spectral_matched_filter_v1.py` before writing anything — that script is the set-level version.

**P4 — THE APERTURE.** Wall 1. `PREREG_incomplete_shortscalar_v2.md` with the self-audit's inversion
applied (per-law `G_ℓ` + Holm primary, `T_dev` demoted to characterization) and the owed `≥10⁴`-rep
calibration. Gate-blocked; §2a's provisional branch is available if `experiment-designer` is still
unavailable, with all four conditions.

**P5 — THE CAUSTIC.** Wall 2. Extreme-value / tail statistics as an instrument class (never used).
First move is the cheap one already named: re-test `#17` against the **correct symmetry-type null**
(`~ε` for a real/low-dim trace distribution, not Rayleigh's `~ε²`).

---

## 7. What this frame does NOT license

- It does **not** reopen the spectral-concentration door. §2 closes the frequency search using the
  analogy's own conservation law. Proposals of the form "look at frequency X instead" are answered.
- It does **not** convert any existing null into a positive. P0/P1 can only produce a **scope
  correction** or a **characterization**; neither is a finding.
- It does **not** license a dismissal either: a null re-derived as "the detector was on a node" is
  still a null *of that detector*, and §2's refutation is scoped to its own box (complete × `L²` ×
  bounded-degree), with the (D2) citation caveat live.
- ⚠ **Gate owed:** every probe in §6 is a sweep/scan and requires `experiment-designer`
  pre-registration before it runs (CLAUDE.md §2). Nothing in §6 has been run.

---

## 8. One-line summary

The interference analogy is exact, and taken to its own conclusion it says: **frequencies are dark by
conservation (§2) — the beam, if there is one, is a REGION in `d`-space (§3, walls 1+2 are one wall)
or a PHASE ALIGNMENT across the prime family (§4), and the reason we would not have seen either is
that every pooled statistic in the record detects incoherently and every power claim is calibrated
against a coherent plant (§5).**
