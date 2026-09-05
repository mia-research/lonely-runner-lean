> **⚠ CORRECTED 2026-08-13 — see `CORRECTION_semaev_cm_yield_mechanism_literature_v1.md`.**
> §2's LFD citation is **mis-applied**: the Last-Fall-Degree / solving-degree literature is about
> **extension/binary fields** (Weil descent), NOT prime-field curves — verified against sources. secp is a
> prime field. The **conclusion** (R1 yield ≠ secp lever) survives on a corrected, more fundamental basis
> (prime-field summation-poly index calculus is non-competitive with generic √p to begin with). **§4 is
> RETRACTED** (P2 is not "the lever probe"). §1/§3 grade downgraded `[DERIVED]` → `[HEURISTIC — testable]`.
> Read the correction alongside this file.

# ANALYSIS — R1's CM relation-yield mechanism: a Weil/Frobenius point-count bias, DECOUPLED from the lever quantity (solving degree). The real lever question is sharpened, not closed.

**Date:** 2026-08-13. Mechanism/transfer analysis of `RESULT_semaev_cm_relation_yield_v4.md` (A1 candidate-lever).
**Grades:** yield mechanism `[DERIVED — Weil point-count, decidable prediction stated §3]`; yield≠lever
separation `[CITED — LFD literature, inherited grade, §2]`; the μ₆-solving-degree lever question `[OPEN]`.
This is a **transfer analysis**, not a closure of the CM/Semaev avenue — it moves the target to the
correct invariant and pre-commits the two probes that decide it.

---

## 0. The finding in one paragraph

R1 measures **yield** = the number of `𝔽_p`-rational Semaev decompositions of a random target into
factor-base points. That count is a **complete character sum on a curve/variety** (the same mechanism the
`[PROVED]` `ANALYSIS_correlation_hierarchy_weil_closure_v1.md` uses): its mean is set by the geometry, and
the **CM Frobenius `π∈ℤ[ω]` shifts a lower-order term systematically** — a real, plausibly scale-free bias.
But index-calculus **cost** is governed by a *different* invariant — the **solving degree / last-fall
degree** of the Gröbner/Macaulay system — which the modern literature shows **stays exponential for
prime-field curves**. Yield and solving degree are separable; R1 moved the wrong one. So the A1 "candidate
lever" is, at the mechanism level, a **structural curiosity unless the μ₆ symmetry also lowers the solving
degree** — which R1 never tested and which is the actual lever question (§4).

## 1. The yield mechanism `[DERIVED]` — why CM raises decomposition count

**Object.** For a target `T` and factor base `V`, the decomposition count is
`Q(T) = #{ (P₁,…,P_m) ∈ V^m : P₁+…+P_m = T }` (m=3 in R1). This is the number of `𝔽_p`-points on the
fibre over `x_T` of the Semaev variety `{S_{m+1}(x₁,…,x_m,x_T)=0}`, restricted to `V^m`.

**Why CM biases it.** `Q(T)` is a **complete character sum over the group** `E(𝔽_p) ≅ ℤ/n`:
`Q(T) = (1/n) Σ_ψ ψ(−T)·(Σ_{P∈V} ψ(P))^m` over additive characters `ψ`. The main term `|V|^m/n` is common
to CM and non-CM at matched `#E`. The **deviation** is a curve character sum, `O(√p)` per the Weil
mechanism (`..._weil_closure_v1.md §2`), and its SIGN/size is controlled by the Frobenius eigenvalues.
For a j=0 curve the Frobenius is the Eisenstein integer `π = a+bω`, `N(π)=p`, whose **argument obeys the
120° law** — so the lower-order term of `Q` carries a systematic CM phase that a #E-matched non-CM curve
(generic Frobenius) does not. This predicts a **systematic mean excess**, exactly what R1 sees
(`T1(j0)>0`, 21–22/24 primes, all `|V|`), and a **per-prime heterogeneity** tracking `arg(π)` / the
sextic residue class — exactly the structured spread R1 flagged as "prime-dependent modulation beyond #E"
(547,601,631,769 high; 541,751,823 low).

**Decidable prediction (probe P1, §5):** the per-prime `T1(j0)` should correlate with a **Frobenius/CM
invariant** of that prime's curve (the sextic residue symbol of `b`, or `arg(π) mod 60°`, or the sextic
Jacobi sum `J(χ₆,χ₆)`), NOT with `#E` (matched, C4-null). Testable on the **existing v4 per-prime data** —
no new sweep. If it tracks, the mechanism is the Frobenius channel and it is **scale-free** (secp's `π`
is a specific Eisenstein integer, same structure).

## 2. Yield is NOT the lever quantity `[CITED — LFD literature]`

Index-calculus total cost `≈ (# relations needed) × (cost to solve one Semaev system)`.
- Yield raises **decompositions per target**, reducing how many targets you try — a **linear/log factor**
  in the relation-collection stage.
- The **binding cost** is solving one Semaev system: a Gröbner/Macaulay computation whose complexity is
  the **solving degree**. Modern consensus (Last Fall Degree / Castelnuovo–Mumford regularity —
  Huang–Kosters–Yang–Yeo ~2015; Caminata–Gorla; Semaev–Tenti) shows this **stays exponentially large for
  prime-field curves**; the earlier first-fall-degree sub-exponential optimism was wrong. `[CITED]` —
  inherited from `ANALYSIS_external_literature_survey_reconciliation_v1.md §3`; a grade promotion on this
  would require `citation-verifier`.

**Consequence.** A `2.3×` (or even `poly(|V|)`) yield advantage multiplies the *cheap* stage and leaves
the *exponential* stage untouched. **A yield lever is not an index-calculus lever** unless it also lowers
the solving degree.

> **Graded separation (closure-bar, per `feedback_closure_grade`):** *Object* — the R1 yield channel
> (decompositions per target). *Class of algorithm it fails to lever* — prime-field Semaev index calculus,
> whose complexity is the solving degree. *Power* — the argument is structural (cost factorization) +
> `[CITED]` LFD; it does not rest on a measurement. *Scope* — this says the **yield** advantage is not a
> lever; it does **NOT** say μ₆ cannot help index calculus (that is §4, open).

## 3. What this does and does not close

- **Explains** the A1 effect (yield grows, log shape): a Weil/Frobenius point-count bias with the CM phase;
  the log-diminishing increments are consistent with a bounded lower-order character-sum term, not an
  unbounded channel. `[DERIVED, pending P1]`
- **Does NOT close** the CM/Semaev avenue. It relocates the lever question from yield to **solving degree**
  (§4). The suppression-bias guard applies: "yield is off-target" is a scoped separation, not "μ₆ is dead."

## 4. ★ The REAL lever question (OPEN) — does μ₆ symmetry lower the SOLVING DEGREE?

R1 never measured solving degree. The LFD results are for **generic** prime-field curves; the j=0 Semaev
system is **not generic** — it carries the `ω`-action `S_{m+1}(βx₁,…,βx_m,βx_T)` quasi-homogeneity (an
exact algebraic symmetry, scale-free). A symmetric ideal can have **lower Castelnuovo–Mumford regularity /
last-fall degree** than a generic one (the symmetry supplies syzygies). **Whether the μ₆ symmetry lowers
the solving degree of the j=0 Semaev system is untested and is the actual lever question** — the only one
whose answer could clear the scale wall by a *mechanism* argument (per `PLAN_semaev_R1_lever_completion §1`).
This is where the CM/Semaev avenue is genuinely live.

## 5. Two pre-committed probes (to `experiment-designer` before running)

- **P1 — yield mechanism (confirm the Frobenius channel), existing v4 data.** Correlate per-prime `T1(j0)`
  (v4 §3 tables, |V|=6/7/8) against Frobenius/CM invariants of each cell's curve (sextic residue of `b`;
  `arg(π) mod 60°`; sextic Jacobi sum), with a matched null and the C4 #E-control. Decidable: tracks ⇒
  Weil/Frobenius mechanism confirmed & scale-free; null ⇒ mechanism is elsewhere.
- **P2 — the lever probe (solving degree under μ₆).** Measure the **last-fall / solving degree** (Macaulay
  matrix fall degree) of the j0 vs #E-matched non-CM Semaev system across `|V|` and `m` where tractable.
  Does the ω-symmetry lower it, or is it CM-invariant (confirming LFD generically)? This — not yield — is
  the transfer-deciding measurement. Firing control: a system with a planted symmetry that provably lowers
  the fall degree.

**Net:** R1's positive is real and its mechanism is (predicted) a scale-free Frobenius point-count bias —
but it is the wrong invariant for a lever. The investigation should pivot from **yield** to **solving
degree under μ₆**, which is the live, transfer-relevant, untested question.
