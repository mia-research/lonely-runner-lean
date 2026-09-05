# PREREG — Semaev CM relation-yield across the six sextic twists (P1++)

**Date:** 2026-08-14 · **Status:** PRE-REGISTERED — spec frozen, **NO new data seen**, no verdict.
**Lineage:** extends R1 (`RESULT_semaev_cm_relation_yield_v4.md`, b=1 only) and P1
(`RESULT_semaev_yield_frobenius_channel_P1_v1.md`, Outcome C on b=1, Im(J) lead unconfirmed).
**Object question (pre-registered):** (a) is the CM relation-yield excess present for **all six**
sextic twists of j=0, or only for b=1? (b) does the excess depend on the twist class /
induced Frobenius rotation (the phase-mechanism test P1 could not run with b fixed)?
**Model-scale only. No secp / no ECDLP claim.** Every number below inherits §6 SCOPE.

---

## §0 SCOPE BANNER (stamped on every number the run emits)

- Curves `E_b : y² = x³ + b` over `𝔽_p`, `p ≡ 1 (mod 3)` (j=0 / μ₆ CM family).
- Primes: **all `p ≡ 1 (mod 3)` in `[512, 1024]`** (the run reports N; expected N ≈ 36).
- Six sextic twists per prime: `b_k = u^k`, `u = least primitive root mod p`, `k = 0..5`.
  **`k=0 ⇒ b=1` (the R1 curve).** k=0 = sixth-power class (canonical); {k=1..5} = the other five
  classes (the *set* is canonical; individual k∈{1..5} labels depend on u — used only categorically).
- `m = 3` (3-decompositions). `|V| = 6` PRIMARY (+ `|V| = 8` SECONDARY on a subset).
- Targets: **ALL on-curve x-coordinates** (deterministic, no PRNG, no "decomposable" filter).
- Signal path exact int / GF(p) throughout (§8). Nothing here transfers to 2²⁵⁶.

---

## §1 OBJECT

**Measured object.** For a curve `E_b` and factor base `V` (a set of `|V|` x-coordinates on `E_b`),
the Semaev 3-relation yield
`Q(E_b) = #{ (x₁,x₂,x₃, x_T) ∈ V³ × Targets(E_b) : S₄(x₁,x₂,x₃,x_T) ≡ 0 (mod p) }`,
i.e. the total count, over all on-curve targets, of ordered base-triples whose sign-appropriate
sum lands on the target (Semaev's 4th summation polynomial vanishing). This is the *count*, not a
solve; no Gröbner basis. The per-twist, #E-controlled excess is
`T1_k[p] = log Q(E_{u^k})  −  log Q(E_noncm(k))`, where `E_noncm(k)` is a **non-CM** curve
(`j ∉ {0,1728}`) with #E matched to `#E(E_{u^k})` (§1C). The object is `T1_k` as a function of the
twist label `k` and of the twist's induced **Frobenius rotation** (Eisenstein `π ∈ ℤ[ω]`, `N(π)=p`).

**Tautology / shared-construction audit (done pre-run, decidable).**
- `Q` and `#E` share a *mechanical* link: summed over all targets, `Σ_T Q_pointwise(T)` is `|V|³·(sign
  multiplicity)`, so the target-*mean* of Q scales as `|V|³ / #E`. This is the confound the whole
  design must kill. **It is removed by within-pair #E matching** (the `|V|³/#E` term cancels in
  `T1_k = logQ_CM − logQ_nonCM` when #E is matched). If matching is imperfect the residual leaks →
  this is the make-or-break, handled by control C2 (§3, §1C).
- `Q` (enumeration over V³) and the Frobenius invariant `B_j` (Eisenstein ω-coefficient, §1C) are
  **different computations on the same curve** — no shared construction. The phase test (§2b) is
  therefore not a tautology.
- The **feature is disjoint from the matching variable**: `T1_k` is the *residual* structure after
  #E is matched out; that residual is exactly the object of interest, not a proxy for #E.

---

## §1C THE TWIST / #E CONFOUND — how it is separated (make-or-break)

Within one prime the six twists have six **different** `#E_k = p+1 − t_k`, where `t_k = 2·Re(π ζ^k)`
rotates by 60° per twist (`ζ` a primitive 6th root). So "twist class k" is entangled with `#E`.
Three explicit moves, all pre-committed:

**(i) Per-twist #E-matched pairing (removes the #E MAIN effect).** For each twist `k`, `E_noncm(k)`
is drawn from a pool of ≥60 random non-CM curves (`a,b ≠ 0 ⇒ j∉{0,1728}`, nonsingular
`4a³+27b² ≠ 0`) at that prime, taking the **nearest #E** to `#E_k`. Admission requires relative gap
`|#E_k − #E_noncm| / p ≤ 2/√p` (control **C2**, adopted verbatim from R1). If the pool has no curve
within cap, expand the pool once (logged); if still none, **DROP that (p,k) cell and record it** — no
silent filtering. Result: `T1_k` is a **#E-controlled excess** (the `|V|³/#E` term is cancelled to
within the residual gap; C2 bounds that residual).

**(ii) Cross-prime decorrelation of twist-axis from #E (pooling check, pre-committed thresholds).**
The phase coordinate `B_k` (oriented Im, §1C-iii) and the confounded coordinate `t_k` (=2Re, i.e. the
#E axis) are, over equidistributed `arg(π)` (Hecke) and over the six 60°-spaced twists, geometrically
orthogonal (Re ⟂ Im). Pre-registered decorrelation checks over the pooled `6N` rows:
  - `|Spearman(B_k, #E_k)| < 0.15`  → the phase axis is separated from #E. **If ≥ 0.15 ⇒ confound NOT
    separated at this scale ⇒ mechanism test reported inconclusive (Outcome 5, §9).**
  - `|Spearman(categorical-k, #E_k)|` reported (expected ≈ 0; k=0's #E varies with p, k=1..5 traces
    are u-permuted per prime).
  Both are computed and printed **before** any T1↔twist statistic is read.

**(iii) Twist enters TWO ways, by role.**
  - **Categorical label** `k ∈ {0..5}` — used for the robustness sign tests and the "b=1 artifact"
    discriminator (k=0 vs pooled k∈{1..5}). Only the *set* {1..5} and the singleton {0} are used,
    so u-dependence of individual labels is irrelevant.
  - **Induced Frobenius rotation** — used for the phase-mechanism test. Exact-integer coordinate:
    fix the primary `π = a + bω` (`p = a²−ab+b²`, `a ≡ −1, b ≡ 0 (mod 3)`, gauge `b>0`). The six
    associate Frobenii are `π·unit`, with exact traces `{±(2a−b), ±(a+b), ±(2b−a)}` and exact
    ω-coefficients `B ∈ {a, −a, b, −b, a−b, b−a}`; `Im(π·unit) = B·√3/2`, so **the rank of oriented
    Im across the six twists = the integer `B`**. Each twist's *measured* trace `t_k` (from point
    count) is matched to the associate of equal trace (generically distinct; if two associate traces
    collide at a prime, flag & drop the prime), assigning that twist its exact `B_k`. `#E`-axis
    coordinate = `t_k` (= 2·Re). **`B_k` (Im) and `t_k` (Re) are the separated axes.**

**If separation fails** (C2 fails on ≥⅓ of twists, or decorrelation |ρ|≥0.15): the run reports
"twist effect not separable from #E at this scale" and makes **no** mechanism claim (Outcome 5).

---

## §2 STATISTIC (exactly one PRIMARY; the phase test is the pre-registered PRIMARY-for-(b))

**PRIMARY (robustness, question a) — pooled non-base sign test.**
Per prime define the integer event
`E[p] := [ Π_{k=1..5} Q(E_{u^k})  >  Π_{k=1..5} Q(E_noncm(k)) ]`
(product over the five NON-base twists; `sign(Σ_k log-ratio) = sign(ΠQ_CM − ΠQ_nonCM)`, a pure
integer comparison — no float). Statistic `W = Σ_p E[p]`, one prime = one independent Bernoulli
(within-prime correlation is absorbed by aggregating the 5 twists to a single per-prime sign).
Null: `W ~ Binomial(N, 1/2)`, one-sided (CM excess ⇒ W large). Exact binomial p-value.
*This single statistic answers "is the excess present beyond b=1."* Its Binomial(½) null is valid
**only if C2 holds and C4 does not fire** (§4) — stated as a dependency, not assumed.

**Supporting (reported alongside, not the primary):**
- k=0 replication: sign test of `[Q(E_1) > Q(E_noncm(0))]` across primes (replicates R1 at b=1).
- Per-twist: six sign tests `[Q(E_{u^k}) > Q(E_noncm(k))]`, Bonferroni α/6, for the per-k breakdown.

**PRIMARY-for-(b) (twist/phase dependence) — targeted, aimed AT the predicted axis.**
Per prime, Spearman rank-correlation `ρ_p = Spearman( T1_k , B_k )` over the six twists (T1_k ranked
by the exact ratio `Q_CM/Q_nonCM`; `B_k` the exact oriented-Im integer). Pooled statistic
`R = (1/N) Σ_p ρ_p`. Two-sided (gauge on `B`'s sign ⇒ magnitude is gauge-invariant; sign reported,
its match to the Weil prediction flagged exploratory). This aims the statistic at the oriented Im
axis (the P1 lead) rather than a diffuse 6-way omnibus (which would be a low-power max-over-cells).
- **Diagnostic (not the mechanism claim):** `Spearman(T1_k, t_k)` (the #E/Re axis). Significance here
  = residual #E leakage (a warning), NOT the phase mechanism.
- **Subspace guard (pre-committed, exploratory, multiplicity-flagged):** also report
  `Spearman(T1_k, f)` for `f ∈ {t_k(=Re), B_k(=Im), Re of π², Im of π²}` (low twist-harmonics). A
  null on `B_k` is reported as "no dependence on the oriented-Im axis at power §5", **never** "no
  twist/phase structure"; the panel is scanned for leads only (α Bonferroni, exploratory).

---

## §3 MATCHED CONTROL (null reproduces every structure except the tested coupling)

**Robustness PRIMARY null.** The `E_noncm(k)` at matched #E **is** the control curve: it reproduces
#E (hence the `|V|³/#E` mechanical term), the identical V-selection rule, |V|, target rule, m — and
differs only in carrying no j=0/μ₆ structure. Under H0 the per-pair log-ratio sign is symmetric, so
`W ~ Binomial(N,½)`. Validity rests on **C2** (residual #E gap unbiased) and is calibrated by **C4**
(§4). **Adequacy check reported per twist:** median relative #E gap and its cap `2/√p`, plus the
*signed* gap median (must be ≈0; a biased sign of the residual gap would forge a spurious W).

**Twist-dependence PRIMARY null.** Within each prime, **permute the assignment of the six T1_k values
to the six twist coordinates `B_k`** (stratified / within-prime permutation, 6! = 720 per prime). This
preserves the six T1 values (marginal), the six `B_k` with their `#E`/`t_k` linkage (marginal +
linkage), and destroys **only** the T1↔twist pairing. Pooled exact-stratified permutation null for
`R` (independent within-prime permutations; 200,000 draws, seed recorded; p-value = integer count /
draws). This null does NOT destroy any symmetry the readout has by construction (it permutes an
external label against the readout), so it is not a self-defeating shuffle.

---

## §4 PLANTED CONTROL (must fire, else UNINFORMATIVE → halt)

**P+ robustness (must fire).** Replace `Q(E_{u^k}) ← round(c · Q(E_noncm(k)))`, `c = 1.5`
(log-excess ≈ 0.405) for all twists, keep non-CM as measured. PRIMARY `W` must reject at α (W ≈ N).
If not → instrument/aggregation broken → **halt**.

**P− robustness calibration (must NOT inflate) = C4.** nonCM-vs-nonCM: replace the CM twist's Q with
a **second independent** non-CM curve's Q (matched #E). PRIMARY re-run must sit in the null band
(reject rate ≈ α over ≥1000 repeats). **If C4 fires, the #E-matching is biased and PRIMARY is
confounded — do not believe a positive PRIMARY** (this is R1's C4, adopted verbatim).

**P+ twist-dependence (must fire).** Synthesize `T1_k = α_p + δ·(B_k/√p) + noise` with `δ` set so
per-prime `ρ_p ≈ 0.35` (above the §5 MDE); stratified permutation must reject at α with ≥80% power
over repeats. If not → the phase test is underpowered / null uninformative → **halt** on (b).

**P− twist-dependence calibration.** Random `B` labels (permute within prime): stratified permutation
fires at ≈ α (≥1000 repeats). Confirms no baseline inflation.

---

## §5 POWER (computed now, not after)

- **Robustness PRIMARY** (`W ~ Bin(N,½)`, one-sided α=0.05, N≈36): reject if W ≥ 24. Power to detect
  a per-prime positive rate `q`: q=0.75 → ~0.88; q=0.66 → ~0.47. **MDE ≈ q = 0.72** for 80% power at
  N=36. Because W uses the PRODUCT over 5 twists, a genuine per-twist mean log-excess μ>0 pushes q
  toward 1 (sum of 5 positive-mean logs) ⇒ near-unit power if the effect is real (R1's b=1 excess was
  ~2.3×). *If N < 30 the run reports the recomputed MDE before concluding.*
- **Per-twist sign tests** (Bonferroni α/6 ≈ 0.0083, N≈36): reject if #pos ≥ 25; ~80% power at
  per-twist q ≈ 0.78. Underpowered to distinguish q=0.6 from 0.5 per twist — stated.
- **Twist-dependence** (`R`, stratified permutation, N≈36): null per-prime ρ has sd ≈ 1/√5 ≈ 0.447,
  so SE(R) ≈ 0.447/√36 ≈ 0.075. **MDE ≈ |R| = 0.21** for 80% power (two-sided α=0.05). Six points per
  prime give low per-prime power; pooling N primes recovers it — this is why the design pools.
- **Decorrelation check** power: with 6N ≈ 216 rows, |Spearman| ≥ 0.15 is resolvable — adequate to
  police the confound.

---

## §6 SCOPE (inherited by every number)

`p ≡ 1 mod 3` in `[512,1024]` (N reported, ≈36); six sextic twists per prime; `u` = least primitive
root; non-CM pool ≥60 per prime, `j∉{0,1728}`; `|V|=6` (PRIMARY), `|V|=8` (secondary subset of ≤12
primes for the |V|-growth check R1 reported); `m=3`; targets = all on-curve x; V = the `|V|` smallest
`x∈{0..p−1}` with `x³+ax+b` a nonzero QR (identical rule all curves). Statistic S₄ = resultant of the
two `S₃` quadratics (§8). **Model scale; no claim propagates to secp256k1 / 2²⁵⁶ / ECDLP.**

**Factor-base fairness (user item 5).** The V-selection RULE is identical in form for every curve
(CM, non-CM, every twist): the smallest on-curve x's from 0 up, with the canonical (least) y. V
**necessarily differs as a set** across curves — it must lie on the curve — but the *criterion* is
twist-neutral and does not encode k (it references only "on E_b", the minimal object requirement).
|V| and m are code-asserted equal across all classes at every prime (control C3, from R1).

---

## §7 FALSIFICATION (written before the run)

- **H_robust abandoned** if PRIMARY `W` fails to reject (W < 24 at N=36) **while** P+ fired and C4 did
  not — i.e. the CM excess is not present across the sextic axis at MDE q=0.72.
- **"b=1 artifact" concluded** if k=0 sign test rejects (b=1 replicates R1) **but** PRIMARY (pooled
  k∈{1..5}) does NOT reject — the excess is specific to `y²=x³+1` (special factorization
  `x³+1=(x+1)(x²−x+1)` / small rational points), not a general j=0/CM property.
- **H_phase abandoned** if `R` permutation p > 0.05 with P+ fired — no oriented-Im dependence at
  MDE |R|=0.21. (Reported as a magnitude bound on that axis, NOT "no phase mechanism"; the subspace
  panel is inspected.)
- **Mechanism test VOID** (not a null) if decorrelation `|Spearman(B_k,#E_k)| ≥ 0.15` or C2 fails on
  ≥⅓ of twists → confound not separated at this scale.

---

## §8 EXACTNESS

Signal path is **int / GF(p) only**:
- #E by exact Legendre-symbol point count (`pow(rhs,(p−1)//2,p)`); trace `t = p+1−#E` integer.
- Semaev `S₄(x₁,x₂,x₃,x_T) mod p` = resultant of the two quadratics `S₃(x₁,x₂,X)=AX²+BX+C`,
  `S₃(x₃,x₄,X)=A'X²+B'X+C'` (a=0 case: `A=(x₁−x₂)²`, `B=−2((x₁+x₂)x₁x₂+2b)`, `C=(x₁x₂)²−4b(x₁+x₂)`):
  `S₄ = (A C'−A'C)² − (A B'−A'B)(B C'−B'C)`, all integer mod p. Q = integer count of `S₄ ≡ 0`.
- Robustness sign = integer comparison of products `ΠQ_CM` vs `ΠQ_nonCM`. No log, no float, decides.
- Twist coordinate `B_k`, trace matching, decorrelation Spearman: exact integer ranks.
- **Float carve-outs (analytic, none in the decision path):** (1) permutation p-values are
  integer-count / draw-count ratios (Monte-Carlo of an exact integer statistic); (2) `2/√p`,
  `√3/2`, angle `arg(π)` are display / threshold constants, never a key in the arithmetic; (3) MDE /
  power numbers are analytic. **No PRNG in the signal path** (targets = all on-curve x, deterministic;
  the non-CM pool is drawn by a recorded seed but its curves' #E are exact and the seed selects
  candidates only, not counts — disclosed). Per project no-float rule: compliant.

---

## §9 PRE-COMMITMENT TABLE (filled before the run)

| # | Outcome (PRIMARY W · k=0 · phase R · decorrelation) | Pre-committed conclusion |
|---|---|---|
| 1 | W rejects (+) · all 6 per-twist + · R null · |ρ(B,#E)|<0.15 | **CM excess is a GENERAL μ₆ effect, twist-independent (robust; NOT a b=1 artifact).** R1 generalizes across the sextic axis. |
| 2 | W rejects (+) · R rejects · tracks `B_k` · decorrelation OK | **CM excess present AND Frobenius-phase modulated** — oriented-imaginary (Weil) mechanism supported on the cross-twist axis (P1's Im(J) lead confirmed). Report R's sign; Weil-sign match = exploratory. |
| 3 | k=0 rejects (+) · W does NOT reject | **R1 effect is a b=1 ARTIFACT** (special factorization / small rational points of `y²=x³+1`), not general CM. |
| 4 | W null · k=0 null · P+ fired · C4 clean | **No CM excess reproduced at this scope/config** (fails to replicate R1 even at b=1). Conditional null; report MDE + re-examine instrument. |
| 5 | |ρ(B,#E)| ≥ 0.15 OR C2 fails ≥⅓ twists | **Confound not separated at this scale — mechanism test VOID** (not a null). Robustness (W) may still stand if C2 held on its pairs. |
| 6 | W rejects (+) · per-twist mixed · R null | Excess general but **heterogeneous across twists**; report per-twist, no phase claim (exploratory follow-up). |
| — | P+ (robust or phase) does NOT fire | **UNINFORMATIVE — halt** the affected arm; null carries no evidence. |
| — | C4 fires | #E-matching biased; **PRIMARY confounded**, do not read a positive W. |

**Compute budget (user item, ~minutes).** N≈36 primes × (6 CM twists + 6 matched non-CM) curves;
per curve ~(p/2) targets × |V|³=216 S₄-evals ⇒ ~4.7×10⁷ S₄-evals total + ~2×10⁷ Legendre ops for
#E/pool matching. Pure-Python estimate ≈ 3–5 min at |V|=6. Fallbacks if over budget (pre-committed,
in order): |V|=5, then p∈[512,900] (N≈26 — recompute & report MDE), then K=96 seeded targets/curve
(disclose PRNG carve-out). `|V|=8` secondary runs on ≤12 primes only.

---

### Post-run audit hooks (for the auditor of the completed run)
Report: (1) did W / R / k=0 statistics stay as defined here? (2) any (p,k) cell dropped — logged?
(3) C2 per-twist median & signed gap; (4) C4 status; (5) P+ fired (both arms)? (6) decorrelation
ρ(B,#E) value; (7) scope stamped on every number; (8) conclusion = the §9 row that fired, verbatim;
(9) any float in the decision path. List every deviation; a disclosed deviation is not a defect.
