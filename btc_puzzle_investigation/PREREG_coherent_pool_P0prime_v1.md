# PREREG — P0′, the COHERENT (phase-aligned) cross-prime pool [lock-in]

**FROZEN pre-registration. No data seen.** Written before any P0′ pool value is
computed. Grades HELD. This is a **curve-STRUCTURE calibration probe**: it asks
whether a per-prime signed curve score is *cross-prime sign-coherent*. **No
leakage / key-recovery / ECDLP claim; no key set is in the signal path.** Output
is a CHARACTERIZATION (direction / count / bounded magnitude), never an avenue
verdict or a closure (anomaly-drill protocol, binding).

Companion to `PREREG_anticoherent_plant_P0_v1.md`, whose §5 names exactly this
missing instrument: *"a statistic that pools across primes WITH a sign … against
which a coherent plant adds and an anti-coherent plant cancels … a different
statistic … that needs its own prereg."* This is that prereg.

---

## 0. Headline (from reading the instrument code, before any pool value)

The four existing detectors (`twist_orbit_spectrum_run_v1.py`,
`twist_orbit_magnitude_run_v1.py`, `twist_orbit_monodromy_run_v1.py`,
`row_budget_v3_run.py`) are **sign-blind**: each plant statistic factors through a
magnitude / even moment, so for any per-prime sign `s_p ∈ {±1}`, `S(s_p·plant) =
S(plant)` — flip-sensitivity `INV = 0` exactly (established mechanically in the P0
prereg §2, machine-exact). They discard phase.

**P0′ is the first statistic in the suite with `INV > 0`:** a SIGNED cross-prime
pool `W(A) = Σ_p s_p^A · q_p`, where `q_p` is an **exact integer** per-prime
signed score and `s_p^A` a **pre-committed** per-prime alignment sign. A coherent
(phase-aligned) effect ADDS across primes; an anti-coherent one CANCELS. The pool
is ranked against a **per-prime sign-permutation null** with an **exact integer**
p-value (all `2^k` sign patterns enumerated).

**Two code facts fixed the design before any data (both verified against the
actual instruments, §1a, §6):**

1. **Candidate (i) — the signed twist-spectrum coefficient `V̂(χ)(p)` — is FATALLY
   ILL-POSED as a coherent pool.** Because `V(-a) = -V(a)` is FORCED
   (`twist_orbit_spectrum_run_v1.py` docstring L8–9; C-ODD check L165), `V` is an
   **odd** function, so the sign of every per-class value depends on which of
   `±a` is chosen as the class representative — a choice fixed by the arbitrary
   generator `g = primitive_root(n)` (L96, class indexing L97–102, L113–115).
   **Verified numerically (p=127):** the coefficient at the *fixed* admissible
   character χ₃ is `V̂(χ₃) = +161.95 − 222.32i` under `g=3`, `−169.62 − 496.92i`
   under `g=6,7`, `−237.84 − 190.72i` under `g=12`, `+153.37 + 87.50i` under
   `g=23` — its real part flips sign across generators — while the magnitude
   multiset `{|V̂(χ_j)|²}` is invariant across all of them. So `Σ_p V̂(χ)(p)`
   sums signs fixed by "the smallest primitive root of `n_p`", a nuisance
   unrelated to any coherence hypothesis: the pool is **incoherent by
   construction → zero power** (a null-mismatch artifact). Only EVEN functionals
   of the twist spectrum are generator-invariant, and those are exactly the
   sign-blind statistics. **Candidate (i) is rejected on object-level evidence.**

2. **Candidate (ii) — the row-budget signed score — IS well-posed.** `q_p` is
   built from `N_LOW`, an **integer count** of low-power modes of `|U(a)|²`
   (`row_budget_run_v1.py` L110–115), compared to the MN-μ6 null mean. `|U(a)|²`
   is magnitude — invariant under `a→-a` and under the μ6 relabeling — so `N_LOW`
   is orientation-free and generator-invariant, and its sign (char has MORE vs
   FEWER low modes than the μ6-symmetric null) is a genuine, arithmetically
   meaningful, curve-derived signed quantity. This is the workable primary. The
   pool line `Z = Σ z_p/√k` already exists (`row_budget_run_v1.py:226`,
   `row_budget_v3_run.py:214`) as a **diagnostic**; P0′ promotes it to the
   **firing statistic** against a sign-permutation null.

**Scope consequence, stated plainly (constraint 6):** because the twist-spectrum
channel has NO generator-invariant signed reduction (its forced odd symmetry
permits only sign-blind even functionals), the well-posed signed pool necessarily
lives in the **row-budget low-tail channel**, not the twist-spectrum channel.
P0′ therefore tests coherent phase in the row-budget channel; the twist-spectrum
channel's inability to carry a signed pool is itself a characterization of that
channel (its odd symmetry gauges the sign away), not a verdict.

---

## 1. OBJECT

The object is the **per-prime signed curve score** `q_p` and whether its **sign
is coherent across a family of primes** — i.e. whether the row-budget low-tail
deviation of the CM curve `y²=x³+7` (j=0, μ₆) points in a *consistent
arithmetic direction* across primes, or scrambles.

Named exactly:

- `charTotal_p = Σ_{f∈FREQS(p)} N_LOW_char(p,f)` — total low-mode count of the
  real curve's additive-character orbit spectrum (`row_budget_run_v1.py:110–115`,
  frozen frequency list per prime).
- `nullTotal_p = Σ_{f} Σ_{r=1..R} N_LOW_muN6(p,f,r)` — same, summed over the `R`
  MN-μ6 relabelling replicates (`:152`, the PRIMARY null).
- **per-prime signed score** `q_p = R·charTotal_p − nullTotal_p ∈ ℤ` (exact
  integer; `sign(q_p) = sign(z_p)`, since `z_p ∝ Nbar_char − Nbar_muN6.mean() =
  (R·charTotal − nullTotal)/(R·m)`).
- **alignment sign** `s_p^A ∈ {±1}` from a pre-committed arithmetic rule `A`.
- **pooled object** `W(A) = Σ_p s_p^A · q_p ∈ ℤ`.

A monolithic-coherent curve has all `sign(q_p)` equal (channel pushes one way for
every prime); an incoherent curve has `sign(q_p)` ~ fair coin. The question is
which.

### 1a. Disjointness / tautology (constraint 6)

**This is a curve-structure test with NO key set in it — structural, not
leakage.** The *feature* is the alignment sign `s_p^A`: for the primary
(monolithic) alignment `s_p ≡ +1`, a constant that shares **no construction** with
`q_p`; for the exploratory `p mod 4` alignment, a pure residue of the prime `p`,
computed with **no curve data**, hence disjoint from the character sums that build
`q_p`. There is therefore **no feature/target construction-sharing** of the
`r = v − w`-vs-`w` type (`feedback_residue_vs_component_tautology`). The one
residual risk — that `sign(q_p)` is FORCED constant by a conservation law rather
than by a real coherent effect — is guarded twice: by the **null-vs-null
self-test** (must be ~50/50, §4) and by the **anti-coherent-must-collapse** plant
(§4). "Forced ≠ featureless": a forced `q_p = 0` prime contributes `sign = 0` and
is dropped from `k` (count only UNFORCED contributions, drill rule).

---

## 2. STATISTIC (exactly one primary) + the `INV > 0` algebra

**PRIMARY** = the signed cross-prime pool at the pre-committed alignment `A`:

```
W(A) = Σ_p s_p^A · q_p          (exact integer; k = #{p : q_p ≠ 0})
```

ranked (two-sided) against the per-prime sign-permutation null (§3), reported as
`|W(A)|` with the **exact integer p-value**
`p(A) = #{ε ∈ {±1}^k : |Σ_p ε_p q_p| ≥ |W(A)|} / 2^k`.
The display form `Z(A) = W(A)/√k` is monotone in `W(A)` at fixed `k`, so it
changes no ranking and no verdict (`√k` is display-only; §8).

**PRIMARY ALIGNMENT (pre-committed, single, non-degenerate on the held-out set):**
`A0 = MONOLITHIC`, `s_p ≡ +1`. Phase reference = the score's own natural
orientation, referenced to `+1`. Rationale: on the confirmation stratum S every
"p mod k" alignment is CONSTANT (§6: `p≡7 mod12 ⟹ p≡3 mod4, ≡1 mod3`; trace
`t≡1 mod6`; `h(−p)` odd for all `p≡3 mod4`), so the monolithic pool is the
**unique non-degenerate per-prime-sign lock-in** available there — not an
arbitrary pick. A genuinely varying arithmetic alignment would require a
curve-derived finer residue whose `±1` reduction is a post-hoc choice, which
this prereg **declines** for the firing decision (scan-then-pick ban) and confines
to an EXPLORATORY arm (§9).

### The `INV > 0` algebra (this is the whole point — it contrasts the four sign-blind statistics)

For any per-prime flip pattern `σ ∈ {±1}^k`, replacing `s_p → σ_p s_p`:
```
W(σ∘A) = Σ_p σ_p s_p^A q_p
INV = |W(σ∘A) − W(A)| = |Σ_p (σ_p − 1) s_p^A q_p| = 2·| Σ_{p : σ_p = −1} s_p^A q_p |.
```
`INV > 0` **whenever the flip set `{p : σ_p = −1}` contains any prime with
`q_p ≠ 0`.** The pool does NOT discard the per-prime sign — flipping one prime's
sign moves `W` by `2 s_p q_p ≠ 0`. This is flip-SENSITIVE by construction.

**Contrast — the four existing statistics have `INV = 0` exactly** (P0 prereg §2,
machine-exact):

| detector | plant statistic `S(p)` | why `S(s_p·plant)=S(plant)` |
|---|---|---|
| spectrum | `max_{j≡3(6)} |FFT(W)[j]|²` | `|s_p·FFT|² = s_p²|FFT|² = |FFT|²` (`s_p²=1`) |
| magnitude | `max_{j≡0(6),≠0} |FFT(tile)[j]|²` | input is an energy; `|·|²` kills the AC/global sign |
| monodromy | `E[u⁴]`, `u=V/(2i√p)` | even moment (`u→−u ⇒ u⁴` fixed); plant is a sign-free distribution |
| row-budget (as fired) | per-prime `z20 > 6` | magnitude `N_LOW`; firing is per-prime, never the signed cross-prime pool |

P0′ takes the row-budget signed *residual* `q_p` (which the four detectors throw
away) and pools it WITH a sign. `INV_{P0′} > 0`; `INV_{four} = 0`. That gap is the
reason P0′ can see coherent phase and they cannot.

**SECONDARY (characterization only, never the verdict):** the pure sign-coherence
count `Σ_p s_p^A · sign(q_p) = (#aligned − #anti-aligned)`, exact binomial
p-value. The magnitude pool `W(A)` and the sign pool agree in spirit; the sign
pool is reported as a **domination-immunity cross-check** (a single huge `q_p`
cannot fire the magnitude pool against the sign-permutation null — see §5 — but
the sign pool makes that explicit).

---

## 3. MATCHED NULL

**Per-prime sign-permutation (sign-randomization) on the exact integer scores.**
Draw `ε ∈ {±1}^k`; form `W_ε = Σ_p ε_p q_p`. Enumerate **all `2^k` patterns**
(k ≤ ~22 ⇒ ≤ 4·10⁶, trivially exhaustive) for an **exact integer p-value**.

- **Preserves:** every `|q_p|` **exactly** (each prime's score magnitude, hence
  its per-prime power); and it never re-touches per-prime data, so the FORCED
  per-point μ₆/μ₃/neg symmetries baked into the row-budget instrument (the MN-μ6
  null already commutes with `d→±λ^i d`, `row_budget_run_v1.py:49–66,82–100`)
  are **untouched**. The sign flip acts ONLY on the cross-prime axis.
- **Destroys:** ONLY the cross-prime joint sign pattern — the exact quantity a
  coherent phase would imprint.
- **Alignment-independence (clean):** for a fixed alignment `A`, `s_p^A ε_p` is
  again uniform `±1`, so the null law of `W(A)` depends only on the `{|q_p|}`
  multiset — identical across alignments. Only the OBSERVED `W(A)` carries the
  alignment; the null is common. This is exactly *"a control that reproduces every
  structure the data has except the one being tested."*

**Negative calibration control (part of the null validity):** NULL-vs-NULL — take
one MN-μ6 replicate per prime as a pseudo-`char`, recompute `q_p'`, pool under A0.
Its sign pattern must be ~50/50 and `p` ~ Uniform. If NULL-vs-NULL fires
(`p < 0.05`), the pool carries a forced directional bias → **VOID** (the pool is
mis-calibrated; a "coherent" reading would be a construction artifact, not a
curve effect).

---

## 4. PLANTED CONTROLS (must-fire + must-collapse + VOID)

All three gates must pass or the run is **VOID** (no positive, no scoped null, no
scope claim).

**PC-COH (coherent plant MUST fire).** Inject a synthetic score vector
`q_p^coh = +E` for every prime (`E` a fixed positive integer of known size).
Pool under A0: `W = Σ (+1)(+E) = kE > 0`. Its sign-permutation p-value must be the
minimum, `p = 2/2^k` (k=12 ⇒ 4.9e-4; k=10 ⇒ 2.0e-3) — the pool detects a fully
coherent effect at the floor. Graded-size arm: with `E` scaled so a fraction `π`
of primes carry the coherent sign (§5), the pool must reach `p < 0.05` at the
pre-committed `π` floor. **If PC-COH does not fire → VOID** (the pool is not a
working lock-in).

**PC-ANTI (anti-coherent plant MUST collapse).** Inject
`q_p^anti = χ₄(p)·E` (sign follows `p mod 4`; on a residue-balanced set this is a
balanced `±1` pattern) and pool under the MONOLITHIC reference A0:
`W = E·(#{p≡1(4)} − #{p≡3(4)}) ≈ 0`. Its p-value must be **non-significant**
(`p ≳ 0.3`) — the pool goes blind to an effect whose sign is orthogonal to the
reference. **If PC-ANTI does NOT collapse (coherent and anti-coherent pools give
the same p) → VOID** (the sign is not actually being read; the flip-injection is
broken). PC-ANTI is the load-bearing control: it certifies `INV > 0` operates in
code, distinguishing "no coherence in the data" from "the pool cannot see the
sign."

**VOID rule (single, decidable):** VOID if PC-COH fails to fire, OR PC-ANTI fails
to collapse, OR NULL-vs-NULL fires (§3). A VOID run claims nothing — no
characterization, no null, no scope statement.

**Anomaly-drill compliance (constraint 4, binding):** every number below carries
POWER + SCOPE; the output is a characterization (direction / aligned-count /
bounded magnitude / symmetry axis), never a closure; a positive is NAMED only
after it survives the out-of-sample retest (§7, §9); only UNFORCED primes
(`q_p ≠ 0`) enter `k`.

---

## 5. POWER (detectable coherent floor + KS / 1/√p scope)

The sign-permutation null on `k` unforced primes has minimum two-sided
`p = 2/2^k`. **Detectable-coherence floor:** to reach `p < 0.05` (pre-Holm) the
pool needs the aligned count `a` with `2·Σ_{i≥a} C(k,i)/2^k < 0.05`:

- **k = 12 (held-out stratum S):** need `a ≥ 10/12` aligned. `p(10/12)=158/4096
  =0.0386` ✓; `p(9/12)=598/4096=0.146` ✗.
- **k = 10 (discovery, row-budget set):** need `a ≥ 9/10`. `p(9/10)=22/1024
  =0.021` ✓; `p(8/10)=112/1024=0.109` ✗.

**Power vs coherence strength `π` (per-prime probability of the coherent sign;
`π=0.5` under the null), k=12, `P(≥10 aligned | Binom(12,π))`:**

| `π` | 0.60 | 0.70 | 0.80 | 0.85 | 0.90 |
|---|---|---|---|---|---|
| power | 0.083 | 0.253 | 0.558 | ~0.75 | 0.889 |

**Pre-committed power statement:** at k=12 the pool detects **STRONG** coherence
(`π ≳ 0.85`) with ~0.75–0.89 power; **MODERATE** coherence (`π ≈ 0.70`) at ~0.25;
**WEAK** coherence (`π ≲ 0.60`) essentially not. A null therefore bounds only
`π ≲ 0.85` at usable power — it does NOT bound weak coherence and does NOT close
the avenue (§7). The remedy is larger `k` (more held-out primes), stated now, not
after.

**Domination-robustness (a feature of this null, quantified):** if one prime
dominates (`|q_1| ≫ others`), then `W_ε ≈ ε_1 q_1` for ~all patterns, so
`|W_obs| ≈ |W_ε|` and `p ≈ 1` — a single-prime spike CANNOT fire the pool. This is
the structural guard against the project's recurring "two junk rows drive the
fit" failure; it is why the sign-permutation null (not a Gaussian Stouffer
threshold) is the matched one. A mandatory leave-one-out check (drop the largest
`|q_p|`; verdict must persist) is reported alongside.

**KS / 1/√p scope context.** Each per-prime score is built from character sums
whose correlation is `O_D(p^{-1/2+o(1)})` uniformly (`spectral_concentration_
closure_v1.md`, INHERITED — PROVED given the CITED KS/Weil bound; ⚠ D2 caveat:
the KS/Weil citation chain has an unverified link — 3 failed `citation-verifier`
runs — inherited, not re-graded). So each `z_p` is an `O(1)` fluctuation with a
per-prime signal at the `1/√(orbit)` floor; **P0′ cannot manufacture a per-prime
effect beyond that floor.** What a lock-in buys is the `√k` amplification of a
*common-direction bias* in the SIGNS of whatever per-prime effect exists — the
test is about sign coherence, not per-prime magnitude, and inherits the KS floor
as its per-prime ceiling.

---

## 6. SCOPE (inherited by every number this run emits)

**Curve:** `y² = x³ + 7` over `F_p`, j=0, μ₆ CM. **Channel:** row-budget low-tail
`N_LOW` at `ρ < 0.01` (`THRESH=0.01`, `row_budget_run_v1.py:27`); PRIMARY null
MN-μ6; `R = 64`.

- **DISCOVERY set (may be partly SEEN ⇒ EXPLORATORY only):** the 10 row-budget
  model primes `{163, 211, 349, 433, 577, 991, 2089, 4159, 9319, 19231}`, frozen
  frequency list SHA `9695989b…`. **`p mod 4` VARIES here** (`{163,211,991,4159,
  9319,19231}≡3`; `{349,433,577,2089}≡1` — verified), so the exploratory `p mod 4`
  alignment is meaningful on this set only; `p mod 3 ≡ 1` constant (verified) →
  degenerate, excluded.
- **CONFIRMATION set (HELD-OUT; frozen firing decision):** stratum S = 12 primes
  `p ∈ [823, 2731]`, `p ≡ 7 mod 12`, `n = #E(F_p)` prime with `6 | n−1`
  (`stratum(p%12==7, 12, 547)`). These primes have **never** been run through the
  row-budget instrument → genuinely out of sample. Requires a NEW frozen
  frequency list + per-prime `(n, β order-3, λ)` with `C-EQ-int = 0`, whose
  SHA-256 is recorded at freeze time BEFORE any pool value. On S, `p mod 4 ≡ 3`,
  `p mod 3 ≡ 1`, `t ≡ 1 mod 6`, `h(−p)` odd are ALL constant (verified /
  genus-theory CITED) ⇒ **only A0 (monolithic) is non-degenerate here**; A0 is
  the confirmation firing test.
- **Alignment family:** PRIMARY A0 = monolithic (`s_p ≡ +1`), confirmable on S.
  EXPLORATORY (discovery only, Holm m=2): `{A0, A1 = χ₂(−1)/p mod 4}`.
- **Pool null:** exact `2^k` sign-permutation enumeration (k=12 confirmation,
  k=10 discovery). **NOT in scope:** real-data leakage, key recovery, ECDLP, secp
  scale, the twist-spectrum signed coefficient (rejected §0/§1a), any
  varying-arithmetic alignment on the homogeneous S, any claim beyond the
  row-budget low-tail channel.

No number produced by this run may be quoted without this scope line.

---

## 7. FALSIFICATION (pre-committed, before the run)

Decided by the held-out A0 pool p-value on stratum S, AFTER the three gates
(PC-COH fires, PC-ANTI collapses, NULL-vs-NULL ~50/50) pass. Conditional-negative
phrasing is mandatory on any null (bind to method + sample + floor).

- **VOID** — any gate fails (§4). No positive, no null, no scope claim.
- **CHARACTERIZED POSITIVE** — `p_A0(S) < 0.05` **AND** the sign direction matches
  the discovery pool **AND** it survives leave-one-out (§5): report as
  *"the row-budget low-tail channel of `y²=x³+7` carries cross-prime
  monolithic sign-coherence, direction D (char has MORE/FEWER low modes than the
  μ6-symmetric null), aligned count a/12, exact p = …/4096, scoped to [S, N_LOW
  ρ<0.01, MN-μ6, R=64]."* NAMED only after this OOS survival (drill rule). The
  anomaly drill then CONTINUES — characterize which primes align, the direction's
  arithmetic axis, the magnitude — it does NOT close or convert to a leakage
  claim. Grade `[EMPIRICAL — SEEN-in-discovery, OOS-CONFIRMED-on-S; structural,
  scoped]`.
- **SCOPED NULL** — `p_A0(S) ≥ 0.05`: report as *"no cross-prime monolithic
  sign-coherence detected at k=12 in the row-budget low-tail channel; power to
  detect π≥0.85 ≈ 0.89, π≈0.70 ≈ 0.25, π≲0.60 not detectable (§5). This bounds
  only strong coherence and does NOT close the coherent-phase avenue: weak
  coherence is out of power, and varying-arithmetic alignments are untestable on
  the arithmetically homogeneous S (§6)."* Grade `[EMPIRICAL null — scoped to
  method+sample+power floor; conditional]`.
- **DISCOVERY-POSITIVE, CONFIRMATION-NULL** — a discovery hit that does NOT
  replicate on held-out S is **NOT named**: reported as a candidate that failed
  the OOS retest (drill rule: two chance patterns have died this way before).

**What refutes P0′'s own premise:** if PC-ANTI does not collapse while PC-COH
fires, the pool is not reading the sign (INV inoperative in code) → VOID and the
instrument is rebuilt before any reading. If NULL-vs-NULL fires, the "coherence"
is a forced construction bias, not a curve effect → VOID.

---

## 8. EXACTNESS (NO FLOAT IN THE SIGNAL PATH)

- **The decision path is EXACT INTEGER end-to-end.** `charTotal_p`, `nullTotal_p`
  are sums of integer `N_LOW` counts; `q_p = R·charTotal_p − nullTotal_p ∈ ℤ`;
  the alignment sign `s_p^A` is an exact integer (`+1`, or `+1 if p%4==1 else −1`
  — pure `%`); the pool `W(A) = Σ s_p^A q_p ∈ ℤ`; the p-value is an exact integer
  count over `2^k` enumerated `±1` patterns divided by `2^k`. **No float decides
  the verdict.**
- **Float carve-out (pre-existing, sanctioned, no new float in the decision).**
  Float is confined to the row-budget FFT that produces `|U(a)|²` and the `N_LOW`
  threshold `|U(a)|²/(n−1) < 0.01` (`row_budget_run_v1.py:112–115`) — already
  sanctioned in `PREREG_row_budget_lowtail_v1.md` (float FFT / counted-not-keyed;
  a magnitude ranked against a permutation null, never a threshold on a key). The
  P0′ pooling layer reads only the resulting INTEGER counts and adds **no** new
  float in the signal path. `Z(A)=W(A)/√k` is display-only and monotone (a
  `# noqa: float`), not in the decision.
- **Injection points named (so the plant/alignment stay exact and key-free):**
  the plant scores `q_p^coh=+E`, `q_p^anti=χ₄(p)·E` are injected at the pool layer
  as exact integers; the alignment `s_p^A` at the pool layer as `p%4`; nothing is
  injected into the row-budget signal path (`(b·x_d+c·y_d) mod p`,
  `row_budget_run_v1.py:148`, remains untouched `int`).
- `check_no_float.sh` (AST checker, `check_no_float.py`) MUST pass on the new
  pool driver before the run — the driver holds only `int`/`%`/`//` ops and the
  `2^k` enumeration, with the sole `# noqa: float` on the cosmetic `√k`.

---

## 9. OOS / MULTIPLICITY protocol

- **Discovery/confirmation partition (fixed before any data):** controls (PC-COH,
  PC-ANTI, NULL-vs-NULL) validated on the DISCOVERY primes; the FROZEN firing
  decision is A0 on the HELD-OUT stratum S. No seed-shopping: the S prime list is
  fixed by `stratum(p%12==7,12,547)` and frozen with its freq-list SHA before the
  pool is computed (`kfold_gate` guard 1).
- **Multiplicity:** the CONFIRMATION firing test is a SINGLE pre-committed test
  (A0 only — A1/`p mod 4` is degenerate on S), so Holm is trivial there. The
  DISCOVERY family `{A0, A1}` is EXPLORATORY, Holm-corrected `m=2`
  (`p_(1) < 0.025`, `p_(2) < 0.05`), and produces CHARACTERIZATION only, never a
  named result (partly SEEN data). Any discovery hit must survive the held-out A0
  test on S before naming (drill rule 4).
- **OOS retest before naming (binding):** no direction/axis is named until it
  reproduces on S. A discovery-only hit is logged as an unconfirmed candidate.
- **Reproduce the count, not the tally:** the aligned-count `a/k` and the exact
  p-value are recomputed with an independent RNG stream for the row-budget null
  replicates; the LAW (sign direction) must survive, per the v33 `42/42→35/35`
  lesson.

---

## 10. PRE-COMMITMENT grade table (filled BEFORE the run)

Read the three gates first (§4), then `p_A0(S)` (§7). All grades HELD until the
run; nothing here is promoted.

| outcome (pre-committed rule) | reported as | grade if it occurs |
|---|---|---|
| any gate fails (PC-COH no-fire, or PC-ANTI no-collapse, or NULL-vs-NULL fires) | VOID — instrument not reading the sign / forced bias; rebuild | `[VOID — no claim]` |
| `p_A0(S) < 0.05` AND direction matches discovery AND survives LOO | CHARACTERIZED POSITIVE: monolithic sign-coherence, direction D, `a/12`, exact `p=…/4096`, scoped | `[EMPIRICAL — OOS-CONFIRMED on S; structural, scoped; drill continues, NOT a closure]` |
| `p_A0(S) ≥ 0.05` | SCOPED NULL: bounds `π≲0.85` at power; does NOT close the avenue (weak coherence out of power; varying alignments untestable on homogeneous S) | `[EMPIRICAL null — scoped to method+sample+power; conditional]` |
| discovery A0 or A1 fires but S does not confirm | UNCONFIRMED CANDIDATE — failed OOS retest, not named | `[EXPLORATORY — did not replicate; no name]` |
| candidate (i) twist-spectrum pool | not run — ill-posed (generator-gauged sign, §0/§1) | `[REJECTED pre-run — object-level, file:line + numeric evidence]` |

**Global pre-commitments:**
- The PRIMARY firing statistic is `W(A0)` on the HELD-OUT S with the exact
  `2^k` sign-permutation p-value. Nothing else issues a verdict.
- A SCOPED NULL is a scoped fact about this method/sample/power — it is **not**
  "the channel is incoherent" and **not** a closure of the coherent-phase avenue.
- A CHARACTERIZED POSITIVE is a **structural** statement about the curve's
  low-tail channel — it is **not** a leakage / key-recovery / ECDLP claim, and it
  opens an anomaly drill (name the axis, the aligned subset, the magnitude), it
  does not end one.
- Candidate (i) remains rejected: its signed coefficient's sign is a
  generator-choice artifact of a FORCED odd symmetry; only sign-blind even
  functionals of the twist spectrum are generator-invariant.

---

## Provenance

- Instruments read and verified line-by-line: `twist_orbit_spectrum_run_v1.py`
  (odd symmetry L8–9/L165; `primitive_root` gauge L96–102/L113–115; `Tstat`
  `|·|²` L125–134), `row_budget_run_v1.py` (`N_LOW` L110–115; MN-μ6 null
  L49–100/L152; Stouffer diagnostic L226), `row_budget_v3_run.py`
  (Stouffer diagnostic L214; SEEN/UNSEEN L221), `check_no_float.py`.
- Object-level verifications run BEFORE freezing (no coherence value computed):
  (a) generator-gauge of `V̂(χ₃)` at p=127 across `g∈{3,6,7,12,23}` — sign of the
  real part flips, magnitude multiset invariant ⇒ candidate (i) rejected;
  (b) stratum homogeneity — row-budget 10 primes `p mod 4 ∈ {1,3}` (varies),
  `p mod 3 ≡ 1`; stratum S `p≡7 mod12 ⇒ p mod 4 ≡ 3, p mod 3 ≡ 1` (constant).
- Companion: `PREREG_anticoherent_plant_P0_v1.md` §5 (names this instrument),
  `ANALYSIS_destructive_interference_frame_v1.md` §4 (alignment candidates), §5
  (coherent-detector requirement).
- Exactness rule: `btc_puzzle_investigation/CLAUDE.md` "NO FLOATING POINT IN THE
  SIGNAL PATH"; enforcement `check_no_float.sh` / `check_no_float.py`.

**FROZEN pre-registration. No data seen.**
