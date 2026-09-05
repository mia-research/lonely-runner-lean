# RESULT — H-5 |V|-signature: the one-sided #E-leak cannot explain the Semaev CM relation-yield lever (do-not-close #5, cheaper arm DISCHARGED)

**Date:** 2026-08-24
**Author:** ZCode (Claude), Move 7 of the supervisor intersection-menu triage
(`ANALYSIS_supervisor_intersection_menu_triage_v1.md`).
**Task:** do-not-close #5 offers two discharges — a bracket-matched re-run at all levels, **or**
a derivation showing the hypothesized one-sided #E-leak cannot grow with |V| as observed. This is
the derivation arm (analytical + re-analysis of frozen data; **no new run**).
**Inputs (all on disk, frozen):**
- `semaev_cm_relation_yield_v4.log` — the **leaky headline run** (fixed twist B=1 design; T1_j0 =
  0.207→0.834 across |V|=4..8, 24 model primes p∈[523,823], m=3). This is the run whose |V|-growth
  the master's §IX.H-5 flags as unexplained.
- `semaev_cm_relation_yield_v4_results.jsonl` — the **corrected rebuild** (randomized twist B;
  T1≈0), used to estimate the #E-sensitivity β and to validate the pipeline.
- Schedule SHA-256 `f92cb4bb…` (`_SCHEDULE_semaev_cm_relation_yield_v4.json`).
- Scripts (this work): `analyze_h5_V_signature_v1.py`, `analyze_h5_leaky_gap_v2.py`.
**Grade:** `[VERIFIED — scoped mechanism refutation]`. The named mechanism (one-sided #E-gap leak)
is quantitatively excluded as the driver of the lever, on the frozen leaky run, m=3, |V|∈{4..8}.
This does **not** promote H1 to a real signal (see §5). M25/N22 stay **DISPUTED**; the H-5 owed
list narrows by one arm and the seam is relocated (§6).

---

## 1. The statistic and the frozen invariance the derivation turns on

`T1_j0(p) = logQ_j0 − logQ_ctrl`, where `logQ = log(mean_K quo)`, `quo = #{(x₁,…,x_m)∈V^m : the
points sum to the target}` (`I.vector_space_dimension()`; a relation-yield count over a factor base
of size |V|). j0 = curve (A=0, B=1), j-invariant 0, μ=6; the control = the **nearest-#E** non-CM
curve (greedy). Pooled over primes → T1_j0(|V|).

**Key structural fact:** `build_curves(p, …, seed=1000+p)` depends only on `p`. Therefore the j0
curve, the five non-CM curves, **and the nearest-#E match are IDENTICAL across every |V| level** —
only `Dmax` and `K` change. Verified: the matched control is |V|-invariant for **22/22** primes,
and the printed `#Egap` is byte-identical across levels (e.g. p=523: 0.0287 at |V|=4,5,6).

## 2. Analytical derivation — the leak is flat at leading order

Standard index-calculus yield heuristic: `quo ≈ c·|V|^m / #E`, so `logQ ≈ m·log|V| + a_p −
log(#E)`. Both curves in the difference share the **same |V|**, so the growth term `m·log|V|`
**cancels**:

  T1_j0(|V|) = [−log #E_j0] − [−log #E_ctrl] + (curve-structural) = **β·log(#E_j0/#E_ctrl)** + (structural)

The first term is the **#E-gap leak**. Its size is bounded exactly:

  |T1_leak| = |β|·|log(#E_j0/#E_ctrl)| ≤ |β|·(#Egap),  with **#Egap frozen across |V|**.

The forced law A1 (`quo ∝ 1/#E`) is `β = −1` at most; the empirical β (from the corrected run,
non-CM curves, within-prime OLS of logQ on log #E) is **−0.104 (|V|=4), −0.146 (|V|=5)** — i.e.
|β| ≈ 0.1–0.15 ≪ 1. So the leak's |V|-signature lives **entirely in β(|V|)** times a **frozen small
gap**, and is bounded above by #Egap even at the theoretical maximum β = −1.

**Prediction (pre-registered in `analyze_h5_leaky_gap_v2.py` before reading the numbers):** the
#E-leak is flat/small; if T1_j0 grows monotonically while the #Egap-explained part does not, the
leak cannot explain the lever. Call it a leak artifact only if the #Egap channel reproduces ≥50% of
the 0.207→0.834 span **and** grows across |V|.

## 3. Result on the frozen leaky run — four independent angles

| angle | finding | leak verdict |
|---|---|---|
| **Correlation** T1_j0(p) ⟂ #Egap(p) | Pearson r = 0.054 / 0.022 / 0.058 / 0.027 / 0.044 (|V|=4..8); Spearman 0.062 / 0.024 / −0.005 / −0.041 / −0.066 | lever does **not** track the gap |
| **Growth decomposition** | #E-gap channel (slope·mean#Egap) explains **1.8%** of the |V|-growth; the #Egap-independent intercept explains **98.2%** | growth is not the gap |
| **Magnitude ceiling** (β=−1, generous) | \|T1_leak\| ≤ mean #Egap = **0.024**; observed T1_j0 = 0.207–0.834 = **8.5×–34×** the ceiling, ratio **grows** with |V| | leak too small by ≥1 order |
| **Empirical #E-channel** (C4 control) | pure non-CM #E-gap pair → C4 = 0.011/0.032/0.051/0.072/0.071, **non-significant** (perm_p 0.14–0.30), despite a **larger** gap than the j0 match — 3×–12× below T1_j0 | leak too small, independently |

All four agree. The observed lever (T1_j0 = 0.207→0.834, perm_p 0.0000, 21–22/24 positive) and its
monotone |V|-growth are **not** produced by the one-sided #E-gap leak.

**Sanity/pipeline validation:** on the corrected rebuild (`…_v4_results.jsonl`) the same code
reproduces the audit's null to 3 decimals — T1_j0 = **−0.0103 (|V|=4), +0.0117 (|V|=5)**, n=22
(audit: −0.010 / +0.012) — and finds B=1 **not** at the #E-edge (0/22 one-sided), because that run
randomizes B.

## 4. Verdict — do-not-close #5's cheaper arm is discharged

The derivation asked of do-not-close #5 is delivered: **the one-sided #E-leak cannot grow with |V|
as observed — it cannot even produce the base level.** Per the supervisor's framing, this is
outcome (a): *the derived leak signature is flat/bounded while the observed growth is monotone, so
the leak cannot explain the signal; the H1 leg rehabilitates conditional on a proper rebuild.*

## 5. What this does NOT establish (discipline — no over-claim)

Refuting a mechanism ≠ confirming the claim. This result does **not** show the lever is a real CM
relation-yield signal. Established: the audit's **stated** mechanism (#E-gap leak) is not the
driver. **Both facts still stand:** the leaky lever (0.83) and the corrected-run null (0). What
changed is the *explanation* of the discrepancy — it is **not** the #E-gap.

The corrected run changed **three** things at once (F1 randomize twist B; F2 #E-bracket; F8
random_point sampling). This analysis excludes the **F2 #E-gap channel** as the carrier. It does
**not** separate:
- **prime-drop selection** — bracketing drops un-bracketable (edge-#E-position) primes (7/12 for
  B=1); this is selection on #E_j0's *absolute* position, **distinct** from #Egap (the nearest-match
  distance the correlation test used), so it is not excluded by §3.
- **F1** — a genuine B=1 / special-twist (sextic class 0) effect suppressed by randomizing B. This
  is the project's documented one-way suppression risk; it is **not** excluded.
- **F8** — the random_point vs `gens()[0]`-multiples sampling change; the audit notes F8 was never
  isolated from F2.

## 6. The seam, relocated and sharpened

Before: *"is the lever the #E-leak?"* → **answered: no** (§3–§4).
Now: *"what produces the lever, and why does the corrected run go null if it is not the #E-gap?"*
The three unseparated causes (prime-drop / F1 / F8) are the live question.

**Leading alternative mechanism (named, not asserted):** a **μ₆ automorphism-multiplicity** effect.
j0 (j=0) carries 6 automorphisms (P4/P8: μ₆/GLV); a decomposition solution (x₁,…,x_m)∈V^m generates
an orbit of automorphism-related solutions **when V contains the automorphism images**, and larger
|V| raises that chance — inflating `quo` for μ=6 relative to μ=2 in a way that **grows with |V|**
and is **orthogonal to #E**, matching the observed signature. This is the recurring *"just
GLV/automorphism closes a different object"* demarcation (cf. M40, N30). **Decisive follow-up:** it
is cryptographically load-bearing whether the |V|-growth is **independent** relations (a genuine
yield lever, feeds N11/N12 yield→cost) or **automorphism-equivalent duplicates** (useless for index
calculus — same linear relation). Distinguish by recomputing `quo` modulo the automorphism action
(orbit-reduced solution count) on the fixed-B=1 design.

## 7. Owed / next (each its own gate)

1. **Isolate F1 vs F8 vs prime-drop** on the fixed-B=1 design: add **only** #E-bracketing (F2),
   keep B=1 and `gens()[0]` sampling; if the lever survives, F2/prime-drop are exonerated and the
   effect is real-or-F1/F8; if it dies, cross-check against §3 (a genuine puzzle, since §3 says the
   #Egap channel is inert). **New run → mandatory `experiment-designer` pre-registration.**
2. **Orbit-reduced quo** (§6) — decides real-lever vs automorphism-duplicate. Symbolic/archival on
   the existing design where possible; a new count is a new run → pre-register.
3. This result is the derivation arm of do-not-close #5; the **re-run arm** remains a valid separate
   discharge and is unaffected.

## 8. Reconciliation with `AUDIT_semaev_v4_method_result_conclusion_v1`

The audit inferred "#E-leak" from two **indirect** signals: the effect vanishing under the
corrected run, and quo being #E-sensitive (C4≠0). It did not test T1↔#Egap correlation or the leak
magnitude on the leaky run. §3 supplies both directly and they do not support #E-gap causation.
The audit's own load-bearing worry — *"did the fixes SUPPRESS a real effect?"* — is therefore
**reopened**, not by refuting its null (which stands) but by removing the #E-gap as the reason the
null appears. The audit's B=1 isolation (T1=−0.014, n=5) is consistent with this: bracketing
**drops** the edge primes (selection), a distinct channel from the #Egap the isolation's survivors
carry.

---

*Scope: model primes p∈[523,823], m=3, |V|∈{4,…,8}, the frozen f92cb4bb schedule. No 256-bit,
ECDLP, or key-recovery claim. Grades: the leak refutation is `[VERIFIED — scoped]`; H1-as-signal
remains `[DISPUTED]`; the μ₆-multiplicity mechanism is a `[NAMED candidate]`, untested.*
