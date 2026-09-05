# PRE-REGISTRATION v2 — C2: χ₂/χ₆ on the group-law difference-set of a band-random point set

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer RE-gate]`.** Grade `[PENDING GATE]`.
Supersedes v1, which the gate FAILED with 2 blocking defects (retained as the record). Executes
handoff item **C2**. Object legality / disjointness / look-elsewhere / scope were gate-CLEAN in v1 and
are unchanged; only §3/§4/§5/§7/§9/§10 change.

## §0.1 Change log — v1→v2 (experiment-designer, 2 blocking + 3 non-blocking)
- **BLOCKING 1 — pooled-null vs fresh-arm re-introduces `T²/C(P,2)` inflation.** v1's null reused
  Step-1's **pool** (subset draws) while the arm was fresh ⇒ the pooled null's mean carries
  `≈T²/C(P,2)` (≈40% inflation at M=400/P=640) that the fresh arm lacks ⇒ systematic LOW tail
  replicating OOS (the measured R-CONTIG failure). **Fix:** §3 below — Stage A at **M=80** (inflation
  ≈1.5%, negligible, and C-NEG-calibrated) with an explicit **fresh-vs-pool null-clean check**; the
  M-ladder freezes **P ≥ 10·M** per rung (inflation ≤1%). The false "not a bootstrap" claim is deleted.
- **BLOCKING 2 — plant fires E₃ only, leaving χ₂/χ₆ (the whole point) uncontrolled.** **Fix:** §4 adds
  a **χ₂-biased plant** (fires E₂) and a **μ₆-joint-class-biased plant** (fires E₆); §5 pins `ε*`
  **per channel** from each form, not ported from E₃.
- **N1** shuffled-band secondary: reconciled to **reported, not gating**, and reframed as a
  **k-dependence** test (a real band effect weakens as the band widens), NOT a genericity kill (a
  shuffled band is still band-confined, so it cannot certify "generic"). §7 updated.
- **N2** ±birthday-collision watch-item at largest-M/smallest-k added to §3.
- **N3** full M-ladder frozen numerically in §9.

## §0.2 Re-gate refinements (frozen; experiment-designer FRAME-CLEAN on v2)
1. **Fresh-vs-pool pass criterion (numeric):** draw 60 fresh M-uniform sets; PASS iff their mean
   percentile-rank vs the pool null is ∈ **[0.42, 0.58]** on each of E₂/E₃/E₆. It is a **gross-error
   net** for a mis-set P; the **fine bound is the P≥10·M arithmetic** (residual ≤1%). FAIL ⇒ abort /
   enlarge P (§7 kill).
2. **Arm regenerated FRESH per OOS seed; the null pool may stay fixed.** This fresh-per-seed property
   (v1 §2, load-bearing) is what makes a fixed pool safe — a fresh arm cannot replicate the same tail
   5/5 off a fixed pool offset. Frozen here explicitly (v2 subsumes v1 §2).
3. **Ladder gate = the P≥10·M arithmetic** (per-rung empirical check optional); a residual few-%
   inflation is **conservative** for bounds (higher V₉₉ → looser ε*) and cannot fire a false 5/5.
4. **Seeds (frozen):** arm/null 20260802; OOS seeds {20260802, 31337, 27182818, 16180339, 14142135};
   controls 20260802.
5. **Stage A pool P=640** (reuse Step-1's calibrated pool; 1.5% inflation, checked) — this IS the M=80
   rung; nominal P=10M=800 is the ladder default, 640 used at Stage A for the Step-1 calibration reuse.

## §1. Object / sampling / disjointness (FRAME — gate-CLEAN in v1, unchanged)
Group-law difference multiset `D={x(Pᵢ−Pⱼ):i<j}`, `Pᵢ=[dᵢ]G`, `dᵢ` **uniform** in `[2^{k−1},2^k)`.
χ₂/χ₃/χ₆ legal (`x(−Q)=x(Q)`; C-GLV E₃=E₆=0 exact). Band-RANDOM ⇒ differences all-distinct
(multiplicity 1) — no contiguous-collapse. Structure under test = band-confinement of the difference
scalar set. Feature (χ of a difference point) disjoint from target (scalar band-size).

## §3. Matched control (FRAME) — CORRECTED null
**Primary gating null = M uniform random curve points**, group-law-difference statistic. Two regimes,
frozen:
- **Stage A: M=80, pool P=640** (Step-1's calibrated null). Inflation `T²/C(P,2)=3160²/204480≈49` vs
  `T=3160` ⇒ **≈1.5%, negligible**. **Mandatory pre-run check (mechanical):** draw ~40 **fresh**
  M-uniform sets, rank their E₂/E₃/E₆ against the pool null; require them ≈uniform (fresh-arm and
  pool-null indistinguishable). If the fresh sets sit systematically off, the pool null is not usable
  at these params — abort and enlarge P. This directly tests the Defect-1 axis C-NEG is blind to.
- **M-ladder (M∈{80,400,1024}): freeze `P = 10·M`** ⇒ inflation `T²/C(P,2)=(M²/2)²/(50M²)=M²/200`,
  i.e. `≤1%` of `T`. Pool precompute `C(P,2)` differences ONCE per rung (M≥400 is background/logged).
- **C-GLV** φ-closed ⇒ E₃=E₆=0 exact (E₂ not forced — see §4). **C-NEG** Step-1 n≥20 (valid for
  E₂/E₃/E₆ — the recalibration calibrated all three). **FORBIDDEN:** differences of random `F_p`
  integers.
- **N2 watch:** at the largest-M/smallest-k cell verify arm and null ±birthday-collision counts match
  (or cap `M·2^{−k/2}`), so a band-induced combinatorial effect is not mis-read as curve structure.

## §4. Plant-fires (MECHANICAL) — one plant PER CHANNEL (Defect 2)
Each must fire its channel above the null 99th and be void at δ=0; power curve at δ∈{0,½δ*,δ*,2δ*}:
- **E₃ plant:** cubic-class-0 excess (existing) → fires E₃.
- **E₂ plant:** quadratic (QR) excess — bias `n₊−n₋` → fires `E₂=(n₊−n₋)²`.
- **E₆ plant:** **joint μ₆-class** excess — bias one of the 6 `(b,c)` cells → fires
  `E₆=A₆²+A₆B₆+B₆²`. (A pure cubic or pure quadratic bias does NOT fire E₆; verify the joint plant
  does and the marginal plants do not.)

## §5. Power / bound (Rule 5) — PER CHANNEL
Report `ε*` separately for each readout from its own null V₉₉ and its own form:
`E₂=(n₊−n₋)²` (`ε₂*` from a QR-imbalance), `E₃=A₃²−A₃B₃+B₃²` (`ε₃*=2√V₉₉/T`), `E₆=A₆²+A₆B₆+B₆²`
(`ε₆*` from a μ₆-class imbalance). No porting the E₃ constant to E₂/E₆. Each `ε*` cross-checked by its
§4 plant's firing threshold. The χ₂/χ₆ floors are the specifically-new deliverable.

## §6. Scope (FRAME — gate-CLEAN, unchanged) — secp p/G; k∈{40,64,96,128,160,200}; no "generic" label
without control-curve evidence; contiguous-difference / triples deferred.

## §7. Falsification (FRAME) — updated per N1
- **Candidate** ⇒ screens two-sided 99th AND same-tail 5/5-OOS vs the uniform null → characterize; a
  χ₂/χ₆ hit is the item-C2 payoff.
- **Bounded** ⇒ per-channel magnitude + ε*, open below.
- **k-dependence (secondary, reported not gating):** a genuine band-confinement effect should **weaken
  as k widens** (larger band → closer to whole-group). The shuffled-band control measures this trend;
  it is **not** a genericity kill (a shuffled band is still band-confined and cannot certify "generic").
- **Kill:** fails OOS; a channel's own plant (§4) dead; C-NEG miscalibrated; reproduced by the
  forbidden `F_p` null; or the fresh-vs-pool check (§3) fails (⇒ null-inflation artifact, not curve).

## §8. Exactness (MECHANICAL, unchanged) — pure int; integer quadratic forms; reuses Step-1 harness.

## §9. Pre-commitment / freeze — **M-ladder frozen: {80, 400, 1024}**, `P=10·M` per rung (Stage A
M=80/P=640 with the fresh-vs-pool check); χ₂/χ₃/χ₆; k-ladder; R_null≥2000; two-sided-99th +
same-tail-5/5-OOS + bound-95th; uniform null (primary) + shuffled-band secondary (reported) + `F_p`
forbidden; C-GLV + 3 per-channel C-PLANTs + C-NEG; seeds. SHA-256 on freeze.

## §10. Compute plan (Rule 2) — CORRECTED
Per arm at M: M scalar-mults + C(M,2) group-law differences + 2·C(M,2) char modexps. Null:
pool-precompute `C(P=10M,2)` difference-classes ONCE per rung. Stage A M=80/P=640: precompute
C(640,2)=204,480 pairs (~40s, as in Step 1); arms trivial. M=400/P=4000: C(4000,2)=8.0M pairs → 16M
modexp (~20 min, **background/logged**). M=1024/P=10240: background. Sampled estimator if C(M,2)>10⁶.
**M=6.25×10⁶ NOT in ladder.** The fresh-vs-pool check (§3) and the 3 plants (§4) run before the arms.
