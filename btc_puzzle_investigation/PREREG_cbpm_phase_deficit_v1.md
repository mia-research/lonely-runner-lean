# PRE-REGISTRATION — c=±b diagonal PHASE probe + caustic re-test of the −13.99σ deficit

**Status: `[PROVISIONAL — experiment-designer unavailable]`.** The mandatory pre-registration gate
(experiment-designer, context-isolated) could not run: it terminated on a session limit (attempted
2026-08-11; resets ~21:50 Australia/Brisbane). Per CLAUDE.md §2a this spec is written by the main
model and carries all four provisional conditions: PROVISIONAL tag (here, in the grade slot), the
self-audit below naming its uncovered sections, the gate recorded as **owed**, and **no grade
promotion** on any result run against this spec until the gate clears and re-reviews it.

## SELF-AUDIT — what this un-isolated spec does and does NOT cover (§2b)

- **Mechanical layers (self-audit sufficient, with the artifact):** the statistic definitions, the
  power arithmetic, exactness/no-float, and "does the plant fire" — these are checked here and are
  decidable from the run.
- **Frame layers (self-audit is NOT sufficient — isolation is the mechanism; these are UNCOVERED):**
  1. **Matched-control adequacy** — THE known failure point on this exact machinery (the
     phase-within-triple +10.36 false positive from an analytic per-block null under-counting variance
     ~2.85×). This spec mandates a global-repartition null and the flat-Z-across-N tell, but *whether
     that control is adequate* is precisely a frame judgment a same-model author cannot self-clear.
  2. **Object/disjointness** — whether the c=±b "phase on the free subspace" is genuinely free of the
     forced conservations, or leaks a forced component.
  3. **Scope / falsification / pre-commitment** adequacy.
  These three are flagged UNCOVERED; any result touching them stays PROVISIONAL until the gate reviews.

## OWED
`experiment-designer` pre-registration of this spec — attempted 2026-08-11, failed (session limit),
**owed**. Re-run when the limit resets; treat this spec as the draft it reviews, not as its output.

---

## Object
`U(a,b,c)=Σ_d e_p(b·x_d + c·y_d)·e_n(a·d)` on `E: y²=x³+7`, prime-order `⟨G⟩` of order `n=m`.
Forced conservations (to be VERIFIED gate-free first, §T1a.0): `Σ_a|U(a,b,c)|²=n(n−1)` per (b,c);
`Σ_{b,c}|U|²=p²(n−1)`. FREE variable = phase/angle `θ_a` (`V(a)=2i√p(sinθ₁+sinθ₂)`). a-axis graded by
the c₂ cubic-residue partition (p≡7 mod12: residue root-orders [1,1,2,2] vs non-residue [3,3,6,6]).

## T1a — c=±b diagonal / c-axis as a PHASE test on the free subspace

**T1a.0 (gate-free, run FIRST — characterization, not a verdict):** verify the forced conservations
hold on the c=±b diagonal (identity checks, exact integer args); confirm any L²-magnitude fidelity is
forced-equal there (so it is excluded as a statistic). Output: which subspace is forced vs free on the
diagonal. This is a structural computation, needs no matched-null and no gate.

**T1a.1 (statistic; needs the gate before its verdict counts):** on the c=±b diagonal, after projecting
OUT the forced conservations, a PHASE-alignment statistic on `θ_a` (a gauge-invariant real-part isotype
of the free residue), stratified by the c₂ cubic-residue class of a. NOT a magnitude fidelity. Question:
does a non-separable phase alignment exist on the diagonal that neither marginal (c=0 or b=0) shows?
- **Matched control (frame-UNCOVERED):** GLOBAL-REPARTITION null (NOT analytic per-block), sharing the
  μ6/conservation forcing; TELL to watch and report = flat per-prime Z across a ≥10× N range.
- **Firing control** must fire; **count only UNFORCED**; OOS primes fixed before looking.
- Output = characterization (symmetry type/eigenvector/subspace), never a verdict.

## T1b — caustic / correct-null re-test of the −13.99σ deficit

**T1b.0 (gate-free, run FIRST):** characterize the actual small-|U| tail distribution — is
`P(|U|<ε) ~ ε²` (Rayleigh/complex-Gaussian) or `~ε` (real/low-dim trace)? Fit the tail exponent
empirically per prime. This is a distributional characterization, gate-free, and it directly decides
whether the deficit's current Rayleigh null is the wrong null.
**T1b.1 (needs the gate):** re-test the −13.99σ deficit against the correct symmetry-type null from
T1b.0; add tail/extreme-value statistics and the imaginary-part isotype (ΣIm²) as a distinct object.

## Power / scope / exactness (mechanical — self-audit sufficient)
Curves: y²=x³+7 prime order, p≡7 mod12 (secp class) for the c₂ grading; scan on 2 small, confirm on 3
larger fixed before looking. `x_d,y_d,d,a,b,c` integer; the character-sum complex value is the allowed
ranked statistic (no key in the arg path); verdict = integer permutation p-value. `check_no_float`
applies to the signal path.

## Pre-commitment (mechanical parts; frame parts PROVISIONAL)
| outcome | conclusion |
|---|---|
| forced conservations hold on diagonal (T1a.0) | magnitude excluded; proceed to phase statistic only |
| tail exponent differs from the assumed null (T1b.0) | new marginal-shape fact; re-scope the null and run T1b.1 — the deficit's status is NOT pre-judged (it survived a shape-preserving null, so shape alone need not touch it) |
| phase statistic ≈ global-repartition control, plant fired | PROVISIONAL scoped null (frame-uncovered) |
| phase statistic ≫ control, survives OOS | PROVISIONAL characterization; NO grade promotion until gate clears |
| flat Z across N | variance miscalibration — STOP, the null is under-counting variance |
