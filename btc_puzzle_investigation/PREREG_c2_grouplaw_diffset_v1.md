# PRE-REGISTRATION (DRAFT) — C2: χ₂/χ₆ on the group-law difference-set of a band-random point set

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer frame-gate]`.** Grade `[PENDING GATE]`.
Executes handoff item **C2** (`NEXT_SESSION_PROMPT_2026-08-01_v2.md`): *"χ₂ and χ₆ on the GROUP-LAW
difference `x(Pᵢ−Pⱼ)` … never read because the run mis-tagged them [parity-void]."* Unblocked by the
C-NEG recalibration (`RESULT_shortscalar_cneg_recalibration_v1.md`, Step 1), which built and calibrated
exactly this object's null and confirmed χ₂/χ₃/χ₆ legal here.

## §0. Scope / counter-prior
Constructed scalars, secp p/G, no keys/pool. A quiet arm is a **bound** (Rule 5), never a closure.
The **specifically new content** is χ₂ and χ₆ — odd characters, legal on the group-law difference
(`x(−Q)=x(Q)`), that no run on this object has ever read.

## §1. Object, sampling, disjointness (FRAME)
**Object:** for M points, the group-law difference multiset `D = { x(Pᵢ−Pⱼ) : i<j }`, `T=C(M,2)`.
`x(Pᵢ−Pⱼ) = x([dᵢ−dⱼ]G)`, and `x(−Q)=x(Q)` gives one canonical value per unordered pair ⇒ **χ₂, χ₃,
χ₆ all legal** (verified in Step 1: φ-closed ⇒ E₃=E₆=0 exact; E₂ not forced).
**Arm sampling — BAND-RANDOM (not contiguous):** `Pᵢ=[dᵢ]G`, `dᵢ` **uniform** in `[2^{k−1},2^k)`. The
difference scalars `dᵢ−dⱼ` are then generically **all-distinct** (birthday collisions ≲2 at k≥40),
so `D` has **multiplicity 1** — the contiguous-block collapse that killed the sum object (differences
`[i−j]G` degenerate) does **NOT** occur here. This is the deliberate design choice that keeps the null
matched.
**Structure under test:** the joint-set fact that the difference *scalars* are band-confined
(`|dᵢ−dⱼ| < 2^k`) — a property of the SET, the only kind that can survive the ECDLP scramble.
**Disjointness:** feature = χ of a difference *point*; target = band-confinement of the scalar set.
Nonlinear, no shared component ⇒ not fired by construction.

## §2. Statistics and decision
Readouts **χ₂, χ₃, χ₆**; magnitudes E₂/E₃/E₆ = |Σχ|² (exact integer forms, Step 1 Appendix A). Cells =
3 readouts × the k-ladder.
1. Rank each arm statistic vs the matched null (§3) → exact `Fraction` p; **all per-cell p uncorrected.**
2. **SCREEN (two-sided 99th):** p≤0.005 or ≥0.995.
3. **GATE = OOS:** candidate only if same tail on **≥5 fresh seeds** (arm + null re-drawn). Look-elsewhere
   handled by 5/5-OOS, not FWER (Holm reported secondary only).
4. **C-NEG** per the recalibrated **n≥20** rule (Step 1): a single high draw is not a fire.
5. **Bound** (Rule 5): below 95th on all seeds → report measured floor ε*.

## §3. Matched control (FRAME; Rule 3) — why the uniform-random null is adequate HERE
**Primary null = uniform random curve points** (QR-rejection on x³+7, no scalar mult ⇒ uniform group
element, cofactor 1); same group-law-difference statistic over M points. This is Step 1's null, already
n≥20-calibrated on this exact object.
- **Immune to the two prior null defects (state explicitly for the gate):** (a) *multiplicity* — both
  arm (band-random) and null (uniform) have **all-distinct** differences, so no forced combinatorial
  structure is unmatched (contrast the contiguous-sum 133× collapse); (b) *deterministic-vs-iid /
  pool-imbalance* — both arm and null are **random point sets** (arm's dᵢ random within a band, not a
  deterministic orbit), and the null is **freshly generated, not a bootstrap**, so neither the
  equidistribution mismatch nor the `L²δ²` pool inflation (which invalidated R-CONTIG's iid null) can
  arise. The contrast is purely band-confined vs whole-group difference *scalars*.
- **Secondary control (isolates scale):** a band-random set at a **different** k (shuffled band) —
  distinguishes "band-confinement leaks" from "this specific k leaks." Reported, not gating.
- **C-GLV** φ-closed ⇒ E₃=E₆=0 exact (instrument + legality). **C-PLANT** cubic/quadratic-biased set ⇒
  fires. **C-NEG** Step-1 n≥20. **FORBIDDEN:** differences of random `F_p` integers (not curve
  x-coords ⇒ misaligned; artifact kill).

## §4. Plant-fires (MECHANICAL) — C-PLANT constructibility + power curve at δ∈{0,½δ*,δ*,2δ*}.

## §5. Power / bound (Rule 5)
`|Σχ|²` over T=C(M,2) differences detects a coherent single-class excess `ε* = 2√V₉₉/T ~ 1/M` from the
measured null V₉₉. **Reported per M as the measured ε*.** M-ladder for a tighter floor (O(M²) — see §10).
Odd-character (χ₂/χ₆) and even (χ₃) reported separately; each is the specifically-new axis for χ₂/χ₆.

## §6. Scope (FRAME; Rule 4)
secp p/G; k∈{40,64,96,128,160,200}; no "generic" label on a secp anomaly without the secondary/
control-curve evidence. Deferred: contiguous-difference (degenerate), triples, other characters.

## §7. Falsification (FRAME)
- **Candidate** ⇒ screens two-sided 99th AND 5/5-OOS vs the uniform null → characterize (anomaly-drill),
  never a verdict; χ₂/χ₆ being the new axis, a hit there is the item-C2 payoff.
- **Bounded** ⇒ magnitude + ε*, channel open below.
- **Kill:** fails OOS; C-PLANT dead; C-NEG miscalibrated; reproduced by the forbidden `F_p` null; or the
  secondary shuffled-band control fires equally (⇒ generic difference-set fact, re-scoped not named).

## §8. Exactness (MECHANICAL) — pure int; integer quadratic forms; ranks integer counts. Reuses the
Step-1 signal-path harness (`shortscalar_cneg_recalibration_v1.py` group-law-difference machinery).

## §9. Pre-commitment / freeze
Frozen: band-random sampling; χ₂/χ₃/χ₆; k-ladder; M per stage (Stage A M=400); R_null≥2000, pool P;
two-sided-99th + same-tail-5/5-OOS + bound-95th rule; uniform-random null (primary) + shuffled-band
secondary + `F_p` forbidden; C-GLV/C-PLANT/C-NEG; seeds. SHA-256 on freeze.

## §10. Compute plan (Rule 2)
Per arm at M: M scalar-mults + C(M,2) group-law differences + 2·C(M,2) char modexps (χ₂,χ₃; χ₆ derived).
Null via Step-1 pool-precompute (C(P,2) difference-classes ONCE, draws are integer subset-sums).
`pow`≈75–90µs. Stage A M=400: 6 arms·2·C(400,2)≈957k modexp (single-response). M≥1024 background/logged.
Sampled estimator if C(M,2)>10⁶. **M=6.25×10⁶ NOT in ladder** (Step-1 projection, never run).
