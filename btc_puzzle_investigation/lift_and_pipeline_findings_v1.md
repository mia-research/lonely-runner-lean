# Lift (amicable duality) + 100k pipeline characterization — findings v1 (2026-07-12)

Two edges, correctly scoped per the integer-selection vs curve-calculation split:
- **Edge 1** = the lift / amicable-duality question (curve side).
- **Edge 2** = full-power characterization of the deterministic production map (100k).

## SELF-AUDIT (adversarial pass over the last ~6 turns)
- **F6 [WRONG CLAIM]:** Eisenstein-angle peaks (sectors 4,10) attributed to the (π_p)
  lattice shortest-vector direction — VERIFIED FALSE (shortest vec at sectors 11/5).
  Fabricated mechanism; observation real, mechanism now UNEXPLAINED.
- **F4 [SKIPPED AVENUE dressed as complete] — the consequential one:** recipe battery
  used only MARGINAL detectors. Marginals CANNOT distinguish LCG/MT from uniform (their
  signature is JOINT/lattice/serial — cf. CLAUDE.md "a marginal null never settles a
  structural object"). ⇒ my "generation-recovery is data-blocked" was WRONG: (1) never
  tested the joint signature; (2) conflated MT-state-recovery (needs 624 words) with the
  whole avenue — MWC1616 multi-draw + a joint/lattice-signature battery are RUNNABLE NOW,
  un-run. **Generation-recovery is NOT closed.**
- **F2/F3/F5 [method-insufficient; conclusions survive proper re-run]:** Fourier only
  k=0..11 (full 8191-scan still flat, max 0.033@k=2343); GLV-of-norms only linear Pearson
  (mod-q MI still ~flat, but q=7 +0.023 flicker un-nailed vs single-shuffle null);
  constructed-key matrix used MEAN of the categorical sextic (wrong stat; caught the
  extreme forced case by luck only).
- **F7/F8 [scope]:** some CM tests on full-size (~2²⁵⁶) not small-key regime; MOV
  embedding-degree wall asserted not computed; Cheon unmentioned (N/A here).
- **F1 [CLEARED]:** 100k n/k/D == n_exact — pipeline-map used the correct decomposition.
- **NET:** F6 and F4 are both the "under-audit the convenient null" failure mode. The
  consequential correction: generation-recovery REOPENED — build the JOINT-signature
  battery + MWC1616 multi-draw (runnable now), not the kangaroo.

## Edge 1 — amicable duality as a DLP lift

**Analysis (the deliverable, rigorous):**
- CM gives an EXACT iso `E(𝔽_p) ≅ ℤ[ω]/(π_n) ≅ 𝔽_n`; with `G↦1`, `[d]G↦d`. So under
  the CM iso, `d` IS the 𝔽_n-coordinate of the point — the DLP is linear in this
  coordinate, and **ECDLP hardness = this iso is not effectively computable.**
- **Anomalous** = `#E(𝔽_p)=p` (order = characteristic); that is exactly when the
  p-adic elliptic log linearizes the whole group. The **amicable** pair is
  `#E(𝔽_p)=n`, `#E(𝔽_n)=p`: each curve's order is the OTHER's characteristic,
  neither equals its own ⇒ "characteristic-crossed anomalous."
- The formal-group route is provably blind here: `ψ(P)=log([n]·lift)` descends only
  mod `n·pℤ_p`; since `gcd(n,p)=1`, `n` is a p-adic unit, `n·pℤ_p=pℤ_p` = whole
  image ⇒ the map is **identically zero**. (Conceptually: the order-n group is
  prime-to-p = étale; the log sees only the connected/ p-divisible part.)
- The amicable route (use `π_n`, where `n` is the characteristic) fails on a
  **characteristic mismatch**: our points are char-p; reaching the char-n formal
  group needs a char-0 lift of an order-n point to an actual n-torsion point of
  `E₀/ℚ(ω)`, and the specific such point IS the DLP. Circular.
- **What CM actually buys:** GLV `√6` speedup constant, nothing linearizing.
  A new attack would need a linearization of the ÉTALE (order-n) part — not the
  p-adic log, not a low-embedding-degree pairing (ord_n(p) is huge here).

**Toy (`sssa_boundary_demo_v1.py`), honest status:** projective group law verified
== affine (control ✓); a genuine j=0 anomalous curve found (`y²=x³+2/𝔽₆₁`, #E=61).
The full numerical `d`-recovery was NOT achieved — the lift came out non-generic
(`v_p(log)=2` not 1), a p-adic-precision subtlety needing proper ℚ_p arithmetic.
Not claimed as working. The analysis above stands on its own.

### Amicable corner GROUNDED (2026-07-12) — corrects "only place with genuine unknown"
Concrete toy exploration (small j=0 amicable pairs; our b=7 pair is (67,79)):
- structure real & elegant: `t_p+t_n=2` always; `π_n=π_p−1`.
- **DLP-transfer obstruction now DEMONSTRATED not asserted:** E(𝔽_n) has order p,
  gcd(n,p)=1 ⇒ **no n-torsion** ⇒ the order-n scalar has zero image on the char-n side.
  E(𝔽_n) is a FIXED group independent of d ⇒ carries **zero bits of d**. Char-n formal
  group needs an n-divisible scalar; it isn't.
- other routes off it (2nd n-torsion eigenspace, Weil pairing) hit the huge-embedding-
  degree wall (MOV). Amicable arithmetic relates curve CONSTANTS, never the scalar.
- **Correction:** the amicable corner is NOT a seam — blocked by the same char-mismatch,
  now shown. What touches the DLP: only the generic walk (kangaroo) + small interval +
  √6 GLV/negation; nothing structural (MOV/SSSA/Weil/index-calc all need features secp
  lacks). A structural break = a research breakthrough, not a computation.

## Edge 2 — 100k-powered characterization of the curve-calculation map

`pipeline_map_char_v1.py`. Mutual information (bits, exact joint counts) between
POINT features and DECOMPOSITION/integer features, over 100k triples, **null-
subtracted** (shuffle removes the finite-sample MI bias). This is a property of the
deterministic map ⇒ synthetic d is exactly the right instrument.

- Only real channel: `(X·Y) mod 2⁶ ↔ D mod 2⁶` = **REAL 0.0027 bits (z=4.4)** — the
  known inert `(X·Y)~D` construction-residual coincidence, now quantified. Absent at
  parity/low bits (b≤4 at floor), washes out by b=8.
- Search-relevant targets `d,k,n`: at floor (real channel <0.005 bits, |z|<2.6) —
  **nothing search-relevant leaks even at 100k power.**
- **Bias caught:** raw MI at b=8 was 0.53 bits — almost entirely finite-sample
  estimator bias (256×256 cells at N=100k); null-subtraction gives ~0.002 real.
  Reporting 0.53 would have been bias-as-signal.
- **Meta (validates the 82-vs-100k framing):** the 100k resolves a 0.003-bit channel
  invisible to 82 keys; used for the MAP/production question it is the correct,
  full-power instrument, and it confirms the pipeline inert to ~10⁻³ bits.

### Edge 2 REDONE in the curve-native (ℤ[ω]) basis — `edge2_cm_native_v1.py`
v1 above used RAW BITS of X,Y — the wrong basis for a CM curve (a ℤ[ω] resonance
would be invisible to bit-MI). Redone with CM-native features of the point [d]G:
chi6(X),chi3(X),chi2(X),chi6(Y) (sextic/cubic/quadratic = Eisenstein/twist/angular
residues), at 100k power, null-subtracted + calibrated.
- Marginals uniform (characters sound/equidistributed).
- MI vs d%{3,6}, n/k/D %6: **all ~0 real bits**; two flickers (chi2(X)↔D%6 z=3.1;
  chi6(Y)↔d%3 z=2.2) carry ~0.0001 bits = noise over 20 comparisons.
- **Resonance scan** MI(chi6(X); d mod m), m∈{2..84}: NO peak (max z=0.3) — no harmonic.
- **Interference** (chi6(X),chi6(Y)) 6×6: χ²=19 on 35 df (more uniform than random),
  cells within 4% of flat — no forbidden/enhanced sectors.
⇒ the map is INERT in the ℤ[ω] basis too: DLP wall holds in the curve-native basis,
not just bits. Scoped null (these features, this power). NOTE: a continuous per-point
"angle" is not well-defined (scalar is an integer d, argument 0); deeper CM features
(Eisenstein-lift 2D coord of X, pairing-based) not yet tried.

### Edge 2 "test smarter" — CONSTRUCTED-key detectability matrix — `edge2_constructed_probe_v1.py`
Instead of random keys (which average structure away), CONSTRUCT families with a known
structure and map which toolkit detectors catch it. L=48, 1500/family, two-sample
permutation p; LIGHT = p<0.01. Detectors: Hamming, smoothCount(<10³), decZeros, Farey_n,
sextic χ₆(X([d]G)).

| family vs uniform | Hamming | smoothCount | decZeros | Farey_n | sextic |
|---|---|---|---|---|---|
| S6 forced point-sextic=0 | . | . | . | . | **LIGHT** |
| SM smooth (control) | . | **LIGHT** | **LIGHT** | . | . |
| LH low-Hamming (control) | **LIGHT** | **LIGHT** | **LIGHT** | **LIGHT** | . |

- **Controls fire** (SM→smooth, LH→Hamming, both cascade) ⇒ the toolkit detectors WORK;
  this CALIBRATES every null reported (real absence, not blind detector).
- **Point-structure ⊥ key-structure, BOTH directions:** forcing the point's sextic
  sector (S6) leaves zero key-side trace (all p>0.27), lighting only its own sextic;
  key structure (SM,LH) never lights sextic (p=0.89,0.96). The point's CM sector and
  the key's integer structure are DECOUPLED — the DLP wall shown constructively.
- **Consequence:** a point-side observable (exposed-pubkey CM structure) cannot
  constrain the key's integer structure or vice-versa. The ONLY exploitable structure
  = a KEY-side generation bias, and those detectors are now calibrated (fired hard on
  smooth/low-Ham). On the 82 real keys the sole flicker through this calibrated set is
  the smoothness lean (p=0.058). φ(n)-averaging not addressed (needs a per-key
  construction the framework doesn't obviously give).

### Generation-recipe signature battery — `recipe_signature_battery_v1.py`
Generate keys per recipe (bit-length matched to the 82 real), fingerprint on the
calibrated detectors, match the 82 real. MEDIAN p over 20 draws (single-draw p is
noisy — an MT-vs-uniform "split" at p=0.004 was pure sampling noise, corrected).
- **uniform / MT_getrandbits / LCG64 → CONSISTENT** (mutually indistinguishable — good
  PRNGs are built to be identical in these detectors).
- **smooth_select / decimal_select / lowHam → DISTINGUISHABLE** (min median p=0.000).
- **Smoothness question SETTLED:** real keys REJECT smooth_select (p=0.000); the faint
  p≈0.06 lean sits inside the good-PRNG band (uniform's own smooth_ct median 0.09) ⇒
  weak fluctuation, NOT a smooth-selection recipe. Verdict: real keys = good PRNG, no
  selection bias. Limit: battery can't identify WHICH PRNG (needs stream/seed recovery).

### Malformation / perturbation sensitivity — `malform_sensitivity_v1.py`
Perturb the construction, trace into (X,Y) and (n,k,D):
- **Curve map = full AVALANCHE:** any δ (1…10¹²) or single-bit flip flips ~half of X,Y's
  256 bits (110–146). DLP mixing shown by perturbation; no point-locality.
- **Decomposition = piecewise-CONTINUOUS (opposite):** same δ leaves (n,k) fixed, D
  absorbs it linearly (ΔD=δ); Farey cell width ~A/n² (~10¹⁵ here, confirmed to a small
  constant); only a high-bit flip jumps the cell.
- **Malformed (n,k,D) self-corrects:** non-coprime (2n,2k)→reduces to (n,k); D<0 stays
  in-cell; only D-past-wall or k>n moves cell. Canonical decomposition re-centers.
- **Consequence:** (n,k,D) is locality-preserving (D a free linear axis in a width-A/n²
  cell), the point is an avalanche ⇒ can't borrow point-locality to shortcut the
  within-cell D search; cell-pinning stays the ~n² resolution problem.

### CM-constructed patterns — `cm_construct_patterns_v1.py` (answers "do ℤ[ω]-property keys leave a CM pattern?")
- **(A) ENDOMORPHISM = exact detectable pattern.** d→λd: `x([λd]G)=β·x([d]G)` **30/30
  exact**, y fixed, χ₆(X) shifts by the constant χ₆(β)=4. The CM DOES imprint the point
  — but only along the units, relating d↔λd (both full-size) ⇒ = GLV, no search leverage.
- **(B) intrinsic F_n mult class = NO imprint.** cubic-residue scalars (d=c³ mod n) vs
  random: point sextic sector identical (χ²=1.1, 5df); Eisenstein-lift angle identical.
  Scalar mult isn't a point ring-hom ⇒ the scalar's ℤ[ω] class is decoupled from output.
- **Eisenstein 2-D lift built** (owed): reduce X against the (π_p) lattice; its ANGLE is
  the genuine per-point CM angle. Finding: angle NON-uniform (sectors 4,10 ~3× enhanced)
  = real hexagonal-ℤ[ω] lattice geometry, but **scalar-independent** (cubic≡random) ⇒
  curve-lattice property, not a channel to d.
- **NET answer:** CM creates exactly ONE detectable pattern = the endomorphism (λ↔β) =
  GLV = the √6 already banked; every other ℤ[ω] scalar property is DLP-decoupled from the
  output. Constructing ℤ[ω]-structured keys buys GLV's leverage and no more.

### Deep CM probes — `cm_deep_probes_v1.py` (user threads: Eisenstein-in-frames, GLV-of-norms, mode-k=1)
- **P1 Eisenstein lift angle in frames:** a DISTINCT feature (nearly independent of the
  sextic sector — sextic-forcing barely moves it), with real curve-lattice structure
  (sectors 4,10 ~3× = hexagonal ℤ[ω] short-vector dirs), but CURVE-FIXED: uniform/S6/
  smooth families all share it (χ²≈9<19). Distinguishes nothing the sextic couldn't.
- **P2 GLV-of-NORMS (the one thread NOT behind the DLP):** clean null. d=N(α) keys have
  GLV reps same size as random (126.80 vs 126.75 bits); corr((d1,d2),(a,b)) all <0.011.
  GLV(d)=Babai reduction of the integer d mod n ⇒ FORGETS the α·ᾱ factorization. Norm/
  multiplicative origin decoupled from the GLV coordinate (even though GLV is scalar-only).
- **P3 FOURIER-FLATNESS (mode-k=1=G):** χ₆(x([d]G)) over d=1..8192 is spectrally FLAT —
  every low freq incl k=1 at the white-noise floor (k=1: 0.006 vs floor 0.011, no peak).
  "G=mode 1" fails in the ADDITIVE sense; the survival law's k=1 is MULTIPLICATIVE, the
  point group's modes ADDITIVE, DLP = the wall between. Curve spectrum does NOT see the
  keys' multiplicative skeleton.
- **SYNTHESIS:** keys' multiplicative skeleton ⊥ curve's additive/CM structure at EVERY
  tested level (scalar mult class, norm structure, GLV decomp, Fourier spectrum); the sole
  meeting point is the endomorphism (λ↔β=GLV=√6). The DLP flattens everything else.

## Powered smoothness test (Vectors 1+3 follow-up) — `smoothness_powered_v1.py`
Rigor: bit-matched null (100k), Group A(<20 bit, degenerate)/B(>=20 bit, 63 keys) split,
decimal-confound control (exclude {2,5}), Bonferroni, effect+CI, exact trial division,
reproduces prior M1. Question: is the recurring smoothness lean real+exploitable in the
larger keys?
- PRIMARY (Group B, Omega<=1e4 all primes): real 3.81 vs null 3.26, eff +0.55, p2=0.054
  (real at null's 97.5 pct); Bonferroni x6 -> 0.32. Borderline, not significant.
- Decimal confound: exclude {2,5} -> eff +0.31, p=0.12; exclude 2 -> p=0.057. Substantial
  part is carried by 2,5 (decimal).
- Localization: Group B (0.054) NOT stronger than all-82 (0.038 @1e3) -> not large-key-specific.
- **EXPLOITABILITY (largest prime factor, the metric that matters):** after removing all
  factors <=1e6, >=20-bit keys have cofactor median 33 bits (max 129); 18/63=29% sqrt-smooth
  vs uniform density rho(2)=1-ln2=30.7%. **Keys' largest-prime-factor distribution MATCHES
  uniform.** The +0.5 excess is in TINY factors (2,3,5=decimal), leaves the large prime
  cofactor generic. => "restrict search to smooth numbers" does NOT apply.
- Scoped-open: ~50 high-entropy keys can't push p=0.054 to a clean yes/no; the non-decimal
  residual (+0.31, p=0.12) is what more solved keys would settle. Toy F_n^x spectrum
  (`mult_spectrum_toy_v1.py`) shows smooth ints DO have index-calculus lattice structure
  (z up to 12) but cubic/CM mode SUPPRESSED (z=-1.6) = multiplicative not CM, and needs the
  keys to be exploitably smooth (they are not, per the cofactor metric).

## Joint-signature battery + MWC lane solver (F4 reopened avenue) — 2026-07-12
`joint_signature_battery_v2.py` (v1 caught with FAILED controls: LFSR BM=1207 not 23 due
to bit-order reversal + LCG control emitting high bits; fixed in v2), `mwc_lane_solver_v1.py`.
CONTROL-FIRST: interpret only after the target detector fires.
- **Validated detectors:** LFSR→BM=23 (fires), pow2-LCG-low→ladder=32 (fires), MWC stream→
  lane-solver recovers (fires), random→rejected.
- **REAL puzzle-1..70 stream vs 100k-MT distribution (BM/serial/ladder):** real INSIDE the
  100k band on all (BM z=-0.50, ac1 z=-1.68, ladder both 0). LFSR/pow2-LCG detectors do NOT
  fire on real ⇒ ruled out. Real indistinguishable from MT19937 by these.
- **MWC lane solver on real:** no recipe (streamorder×wordorder×5 mult pairs×offsets, +per-key)
  satisfies the MWC recurrence. Control-backed negative. SCOPE: tests raw-32b-concatenation
  recipe; the float→int floor(random()*range) multi-draw recipe NOT covered (naive single-draw
  ruled out prior); 5 mult pairs not exhaustive.
- **Why these detectors can't catch MT/MWC generally:** BM/serial/ladder are WEAKNESS tests;
  MT/MWC pass them by design. Catching MT needs untempering (624 contiguous words; have ~75 =
  DATA-BLOCKED). Catching MWC needs the lane solver (built, validated, negative on main recipes).
- **State:** ruled out LFSR, pow2-LCG-low, V8-MWC(main recipes); MT data-blocked; un-built =
  large-modulus truncated LCG (FHKLS), MWC float-recipe, non-index order. Stream = MT-class.
  Generation-recovery NARROWED, not closed.

## MWC float-recipe solver (task 1 of 2) — `mwc_float_solver_v2.py`
v1 control FAILED (partial outputs between keys create lane GAPS; consecutive-recovery
assumed no gaps). v2 fixed: reconstruct each output's stream INDEX from per-key output
counts, seed recovery from a genuinely consecutive pair, propagate over gaps.
- CONTROL fires: MWC float-recipe keys recover (True); random rejected (False).
- REAL: no multiplier makes the real indexed lane satisfy the MWC recurrence.
⇒ V8-MWC1616 now ruled out under BOTH main recipes (raw-concat + float-top-bits),
each control-validated. SCOPE: 5 mult pairs (not every V8 version), these 2 recipes.

## Truncated-LCG lattice (task 2 of 2) — `truncated_lcg_lattice_v1.py`
Pure-Python LLL + Babai built. CONTROL (brute-l0 path, k=8,12): recovers planted low bits
of a truncated multiplicative LCG (validates s_i model + l_0-pins-all-low-bits). LLL/Babai
path built for large k but validated via brute-l0 (small k), not a large-k plant.
- **Puzzle fit poor:** named LCGs (Java 2^48/glibc/minstd) WIDTH-EXCLUDED (modulus<key size,
  can't single-draw >48-bit keys) -> 63 keys >=48 bit rule them out by state size, no lattice.
  Large-modulus (m>2^160) unknown-(a,c): variable-width keys don't fit fixed-truncation FHKLS;
  recovering unknown (a,m) from ~70 truncated outputs = Stern/Contini-Shparlinski (research-grade).

## GENERATION-RECOVERY STATE after both tasks (all runnable attacks control-validated)
- RULED OUT (validated detector fired on target, not on real): LFSR (BM), pow2-LCG-low
  (ladder), V8-MWC1616 raw-concat + float recipes (lane solvers).
- WIDTH-EXCLUDED by state size: named small-modulus LCGs (Java/glibc/minstd) for >48-bit keys.
- DATA-BLOCKED: MT19937 untempering (needs 624 contiguous words, have ~75).
- RESEARCH-GRADE / poor-fit: large-modulus unknown-(a,m) truncated LCG; MWC other V8 versions;
  non-index generation order.
NET: the runnable PRNG-recovery attacks are exhausted with firing controls; the real stream is
MT-class. What remains needs more solved keys (MT) or research-grade lattice work (large LCG).
Not "closed" — narrowed to data-blocked + research-grade.

## TEST ON BOTH SETS (real 82 + 100k), all validated detectors — `test_on_both_v1.py`
Same pipeline (select bit-length integer -> curve); 100k = known MT19937 through it.
Ran every generation-recovery detector on BOTH sets + synthetic positive controls.
Validated detectors (controls fire: LFSR->BM=23, LCG->ladder=32, MWC-solver->recovers):
| detector | LFSR | LCG-low | MWC | uniform/MT | 100k-MT | REAL |
|---|---|---|---|---|---|---|
| BM | 23 | 1206 | 1212 | 1206 | 1207±1 | 1207 |
| ladder | 0 | 32 | 0 | 0 | 0 | 0 |
| MWC solver | - | - | hit | - | 0/20 | no |
=> REAL indistinguishable from known-MT 100k on EVERY validated detector; both differ from
LFSR/LCG/MWC. Real keys behave exactly like keys we KNOW are MT19937, through the identical
pipeline. (Caught another broken control: quick mwc_raw_hit read False on known-MWC=wrong
alignment; re-ran with the validated solver.) Recovery still gated: 100k carries OUR seed;
creator's MT state needs ~624 contiguous words of the CREATOR's output (have ~75); small-seed
search already null. Characterization = real≡known-MT; recovery = needs more contiguous keys.
