# PREREG — Two-Key Joint-Carry ε ↔ coordinate-flap synergy: reduction ruling + genuinely-distinct test (v1)

**Status: FROZEN pre-registration. No data seen. Do not edit after first data touch — bump to v2.**
Date frozen: 2026-08-13. Scope curve: secp256k1 (j=0, CM by Z[ω], p≡7 mod 12, n prime,
GLV λ³≡1 mod n canonical `LAM=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72`,
β³≡1 mod p). Prior gated result this extends: `RESULT_joint_fiber_carry_mi_v1.md` (executed
`PREREG_joint_fiber_carry_mi_v1.md`).

---

## (a) REDUCTION RULING — one form reduces EXACTLY to v1; a second is a v1-class replay; only the JOINT/synergy object is genuinely distinct

**Setup (verify the algebra, done here before freeze).** For a KNOWN fixed scalar `d₁` and an UNKNOWN
scalar `d₂`, tool-7's boundary bit is `ε = [ r₁ + r₂ ≥ n ]`, `r₁ = d₁·λ mod n` (KNOWN),
`r₂ = d₂·λ mod n` (UNKNOWN). Since `r₁,r₂ ∈ [0,n)`, `r₁+r₂ ∈ [0,2n)`; writing
`r_sum := (d₁+d₂)·λ mod n = (r₁+r₂) mod n`:
- if `r₁+r₂ < n` then `r_sum = r₁+r₂ ≥ r₁` (as `r₂≥0`) ⇒ `ε=0`;
- if `r₁+r₂ ≥ n` then `r_sum = r₁+r₂−n < r₁` (as `r₂<n`) ⇒ `ε=1`.
So **`ε = [ r_sum < r₁ ] = [ (d₁+d₂)·λ mod n < r₁ ]`** — verified. `ε` is a function of `d_sum := d₁+d₂`
alone (`r₁` known), computed by scalar-ring arithmetic in `Z/n`. **Branch fixed at `j=1` (`r = d·λ`)** —
v1 recorded this branch keeps `ε` balanced (`Pr[ε=1]≈0.49`) even on the small puzzle keys.

The three natural feature choices, ruled on individually:

| candidate feature | is it new vs v1? | ruling |
|---|---|---|
| **F0 = `b_eps(x_{P_sum})`** (sum-point flap) | `x_{P_sum}=x([d_sum]G)`; the statistic `MI(ε ; b_eps(x_{P_sum}))` is v1's own `MI(ε ; b_eps(x([d]G)))` under `d↦d_sum`, threshold `r₁≈⌊n/2⌋`. Same feature-map **form**, same target **form** (scalar-threshold bit of that point's scalar), just relabelled inputs on a shifted (full-range) key set already covered by v1's constructed-full arm. | **REDUCES EXACTLY to v1. Not registered.** |
| **F1 = `b_eps(x_{P₂})`** (unknown-summand flap) | This is *literally the feature v1 ran* (v1's actual run used `b_eps(x_{P₂})`). The target here is `[ (d₂+d₁)·λ mod n < r₁ ]` = a fixed-shift reparameterization of v1's `[d₂·λ mod n ≥ ⌈n/2⌉]`. A shift by the known constant `d₁` inside `Z/n` relabels the threshold bit; it injects **no cross-point structure**. | **v1-class replay, no new content. Not registered.** |
| **F2 = the PAIR `(A,B)`, `A=b_eps(x_{P₂})`, `B=b_eps(x_{P_sum})`, with the sum-marginal `B` CONDITIONED OUT** | v1 measured (via its run) `MI(ε;A)≈0` and (via the F0 reduction) `MI(ε;B)≈0`. It **never measured the conditional / synergy** `MI(ε ; A | B)`. This object is a strictly richer feature (`B` reads `y_{P₂}` through the group-law translation — see proof) and is exactly the coordinate-side place the *addition* carry would live. | **GENUINELY DISTINCT. REGISTERED as primary.** |

**Registered PRIMARY feature = the conditional (synergy) object `MI(ε ; A | B)`** — "the joint triple with
the sum-marginal conditioned out." (The tool-7 triple `(b_eps(P₁),b_eps(P₂),b_eps(P_sum))` degenerates:
`d₁` is fixed ⇒ `b_eps(x_{P₁})` is a per-arm **constant** with zero per-instance variance, so the triple
collapses to the pair `(A,B)`.)

**One-paragraph distinctness proof (registered feature F2 is not the F0 sum-point reduction).**
The v1 reduction bites only on features that are a function of `x_{P_sum}` **alone**. F2 is not: the pair
`(A,B)` reads `A=b_eps(x_{P₂})` in addition to `B=b_eps(x_{P_sum})`, and `x_{P₂}=x(P_sum − P₁)` is **not a
function of `x_{P_sum}` alone** — subtracting the fixed point `P₁` under the group law uses `y_{P_sum}`, and
two points sharing an x-coordinate (`P_sum` and `−P_sum`) map to different `x_{P₂}`. Equivalently, going the
other way, `x_{P_sum}=x(P₂+P₁)` is not a function of `x_{P₂}` alone (`P₂` and `−P₂` give different sums), so
`B` is a genuinely new coordinate bit unavailable from v1's x-only `A`. Because BOTH marginals `MI(ε;A)` and
`MI(ε;B)` are already null (v1 + the F0 reduction), any signal in `MI(ε;A|B)` is **pure cross-point synergy**
— the coordinate shadow of the *addition* `P₂+P₁=P_sum` in which the scalar carry `ε` physically sits — and
that synergy is unmeasured by v1. ∎

**Frame correction (surfaced, not skipped).** The task also asked to prove F2 "is not a function of `d_sum`
alone." **With `d₁` fixed this is unachievable and is not the correct criterion.** `d₁` fixed ⇒ everything per
instance (`P₂`, `P_sum`, `A`, `B`, `ε`) is a deterministic function of the single unknown scalar `d₂` (hence
of `d_sum=d₂+d₁`); no feature built from these points can fail to be a function of `d_sum`. That determinism is
precisely the v1 "DLP-tautology" concern (reason 2), and it is **defused by the decisional-bit framing, not by
statistical independence**: `ε`, `A`, `B` are each 1 bit, the joint feature `(A,B)` is 2 bits ≪ `log₂N` (no
plug-in saturation), and the firing plant fires — exactly the regime in which v1 validly ran its own
decisional test on a feature that is itself a function of `d`. The operative, achievable, and correct
distinctness criterion is therefore **"not a function of `x_{P_sum}` alone"** (proved above); imposing "not a
function of `d_sum` alone" would forbid the entire decisional paradigm v1 already validated. This spec registers
F2 under the correct criterion and records that F0/F1 do not clear it.

---

## THE REGISTERED TEST — cross-point synergy: does the summand-flap predict the carry bit BEYOND the sum-flap?

### 1. OBJECT
Whether the **coordinate-channel** flap pair `(A,B)` = `(b_eps(x_{P₂}), b_eps(x_{P_sum}))` — each an exact
integer function of one x-coordinate ALONE, no `d`/`λ` in its path (`int1_frame_operator_v1.build_secp`,
`RESULT_linchpin_s_gate_v2.md`) — carries **synergistic** information about the **scalar-channel** two-key
GLV coupling-carry bit `ε(d_sum)` beyond what the sum-point flap `B` alone carries (which is v1-null). The
object is the **conditional dependence** `ε ⊥̸ A | B`, i.e. a coordinate shadow of the *addition* `P₂+P₁=P_sum`
where the tool-7 scalar carry lives. It is NOT the DLP; it is a decisional-bit conditional-predictivity
question. Feature and target share only the abstract `Z[ω]`/λ structure — that is *why it is worth testing and
not a tautology* (extracting `ε` from the coordinates is the DLP). **Tautology check:** feature = coordinate-
field maps of public points; target = scalar-ring wrap of `d_sum`; disjoint construction, no `r=v−w` (§(c)).

### 2. STATISTIC (exactly one primary)
**PRIMARY (targeted, df=2):**
`Î_prim = Î( ε ; A | B )` = `Σ_{b∈{0,1}} p̂(B=b)·Î( ε ; A | B=b )`, the plug-in **conditional** mutual
information (bits), from exact rational counts on the stratified `2×2×2` table (`ε × A`, one 2×2 per `B`
stratum). Aimed AT the predicted synergy (df=2, low-df for power — NOT a max-over-cells). Distribution under
`H₀`: the matched permutation distribution (Section 3). The float `log₂` is used ONLY as a monotone scalar
ranked against that null; the reported p-value is the exact integer count `#{perm : Î_perm ≥ Î_prim}/#perm`.

**SECONDARY (pre-registered, df=3, NOT verdict-driving):** the joint `Î_sec = Î( ε ; (A,B) )` on the `2×4`
table — a cross-check that the pair predicts `ε` at all. Since both marginals are null, `Î_sec ≈ Î_prim`
(the joint is ≈ pure synergy); reported with its own `MI_min`, ranked against the SAME null, never overrides
the primary.

### 3. MATCHED CONTROL (null)
**Null:** `(A,B)` carries no information about `ε` beyond the forced μ₆/μ₃ + GLV symmetries.
**Construction — μ₆-canonicalized, orbit-deduplicated label permutation (on the varying unknown `d₂`):**
- **Precondition (before the test):** canonicalize each `d₂` to its μ₆-orbit representative (fold the 6-fold
  GLV-orbit × negation, `d₂ ↦ canonical of {±λ^a d₂ mod n : a∈{0,1,2}}`), then **dedup** so no two retained
  keys share a GLV orbit or negation pair. Report post-dedup `N`. (Real 82 keys are all `≪ n`, distinct
  orbits ⇒ expected drop ≈ 0, as in v1.)
- **Null draws:** permute the target labels `ε` across retained keys; leave each key's `(A,B)` **untouched**.
  Rank `Î_real` against `≥10⁴` such permutations (Monte-Carlo; reported p = exact integer count / #perm).

**Preserves / destroys.** Preserves each point's per-point μ₃-forced `eps` value on BOTH points (the readout's
by-definition symmetry is never touched — this is the fix for the "6–7σ soft-shadow" null-mismatch), the `ε`
Bernoulli marginal, and the full joint `(A,B)` distribution. Destroys ONLY the `ε↔(A,B)` coupling. Dedup on
`d₂`-orbits ⇒ permutation cannot reconstruct within-orbit forcing. *d₁-translation note:* the fixed generic
shift `d₁` puts the `d_sum` values off any single μ₆-orbit aligned with `d₂`'s, so `d₂`-orbit dedup suffices;
a retained pair that are μ₆-images under the joint action is dropped (see §7 void). A fresh-random-key
surrogate is INVALID (if the coupling were a property of random keys it would show in fresh keys too).

### 4. PLANTED CONTROL (must fire — into the CONDITIONED-IN channel A)
The plant must fire the *conditional* statistic, so it is injected into `A` (planting into `B` would leave
`Î(ε;A|B)≈0` and fail to fire — recorded so the control cannot be silently mis-built):
- **Strong plant (MUST fire):** `A_plant = ε XOR Bernoulli(q=0.25)`, `B` real. True `Î(ε;A_plant|B) ≈
  Î(ε;A_plant) = 1−H₂(0.25) ≈ 0.189` bits (`B ⊥ ε` on real data). `G ≈ 2N·MI·ln2`: at N=82 `G≈21.5`, df=2,
  `χ²_{.99,2}=9.21` ⇒ perm-p ≈ 0; at N=10⁴ p ≈ 0. Expected fired `Î ≈ 0.189` bits.
- **Floor plant (calibration):** `A_plant = ε XOR Bernoulli(q≈0.30)` ⇒ `Î ≈ 0.122` bits = the primary
  `MI_min` at N=82; confirms the instrument resolves at its stated df=2 floor.

**Rule:** if the strong plant does NOT fire (perm-p > α) at a given N, the instrument is dead at that N ⇒ the
real result on that arm is **VOID**, no null claimed.

### 5. POWER
KS floor: `O(√p/n) ≈ 2^128/2^256 = 2^−128` (Kohel–Shparlinski per-key bias). No feasible sample approaches it;
the test finds only GROSS coupling. Detectable MI at 80% power, α=0.01:
- **PRIMARY df=2** (noncentrality `λ_nc ≈ 13.9`): `MI_min ≈ λ_nc/(2N ln2) ≈ 10.0/N` bits.
  - Real arm, N=82 (post-dedup, report exact): **`MI_min ≈ 0.122` bits**. Subtler synergy is BELOW power.
    (2×2×2 at N=82 is sparse: `Pr[flap]≈0.21` ⇒ the `B=1` stratum holds ≈17 keys; plug-in bias is real but
    rank-shared with the null. Honest floor stands at 0.122 bits.)
  - Constructed arm, N=10⁴: `MI_min ≈ 1.0×10⁻³` bits (⇔ `2^−10.0`) — still ~`2^118` above the KS floor.
- **SECONDARY df=3** (`λ_nc ≈ 15.5`): `MI_min ≈ 11.2/N` ⇒ 0.136 bits (N=82), 1.1×10⁻³ (N=10⁴).

**A null is scoped to "MI < MI_min(N)", NEVER "no coupling" — the KS floor `2^−128` is uncrossed.**

### 6. SCOPE (inherited by every number the run emits)
- Curve secp256k1 only. `eis`/`eps`/`s` per `int1_frame_operator_v1.build_secp` / `RESULT_linchpin_s_gate_v2.md`;
  `A,B = [eps(x_{P₂})≠0], [eps(x_{P_sum})≠0]`. Group law `P_sum = P₂ + P₁` exact (int mod p).
- Target: single two-key coupling-carry bit `ε = [ (d₁+d₂)·λ mod n < r₁ ]`, branch `j=1`, with **fixed known
  `d₁`** chosen so `r₁ = ⌊n/2⌋` (`d₁ = ⌊n/2⌋·λ⁻¹ mod n`) ⇒ `ε` balanced, `Pr[ε=1]≈r₁/n≈1/2`.
- **Real arm:** solved BTC-puzzle keys as the `d₂` set, AFTER μ₆-dedup — report exact post-dedup `N` (≤82).
- **Constructed arm:** MT19937 → select-bitlen → scalar pipeline (known-generator `d₂` set), `N` stated;
  identical maps and identical fixed `d₁`.
- Every reported `MI/p` carries `(arm, N, MI_min)`.

### 7. FALSIFICATION (written before the run)
- **Of the SYNERGY hypothesis:** strong plant fired AND `Î_prim` within the matched null (perm-p > 0.05) on
  BOTH arms at stated N ⇒ scoped NULL: "no gross summand-flap → carry synergy beyond the sum-flap, with
  `MI ≥ MI_min(N)`, on secp256k1 at these N." Does NOT close the channel (`2^−128 ≪ MI_min`).
- **Of the TEST (voids the run, no null claimed):** strong plant does NOT fire at a given N.
- **Positive voided:** real `Î` exceeds null but the orbit-dedup precondition was violated (same-orbit /
  negation-pair / joint-μ₆-image keys retained) ⇒ forced-symmetry artifact; re-run after dedup.
- **Positive that CONTRADICTS theory (bug-hunt, not a leak claim):** `Î_prim` is a two-point group-law-coupled
  coordinate correlation, bounded by `bilinear_closure_proof_v1.md` Corollary B1 (`|S|/n² = O(p^−1/2) = O(2^−128)`,
  `[PROVED given KS]`). Any real-data `Î_prim ≥ MI_min ≈ 0.12` bits exceeds that bound by ~127 orders ⇒ it must
  be an instrumentation/dedup/exactness defect FIRST; it is not reported as a leak until the bug-hunt clears.

### 8. EXACTNESS
Signal path int/Fraction only:
- `r₁ = d₁·λ mod n`, `r_sum = d_sum·λ mod n`: int. `ε = [ r_sum < r₁ ]`: integer comparison.
- Group law `P_sum = P₂ + P₁`: exact `int` mod `p` (slope via modular inverse `pow(·,p−2,p)`), no float.
- `A,B`: exact integer Eisenstein lift `eps∈{0,+,−}` (`int1_frame_operator_v1`), flap indicator `[eps≠0]`;
  `s<3/16` gates by integer cross-product (no true division).
- Counts int; `p̂` Fraction; all balance/ratio compares by integer cross-product.
- **Float carve-out (justified):** the `log₂` inside MI and the ordering of `Î` values — an analytic monotone
  on already-exact rational counts, used ONLY to produce a scalar RANKED against the matched permutation null
  (constraint 1 permits exactly this). No key-derived value is thresholded by a float; the reported p-value is
  an exact integer permutation count. Tie risk in the float rank is negligible and carries no key in path.
  `check_no_float.sh` must exit 0 with flags only in the statistic/plant/reporting layer.

### 9. PRE-COMMITMENT (grade slots, filled before the run)
| Outcome | Conclusion | Grade |
|---|---|---|
| Strong plant fires + `Î_prim` perm-p<0.05 on BOTH arms + dedup clean + bug-hunt clears | Candidate cross-point carry synergy; MI=… bits [95% CI], scope secp256k1, N=…; **contradicts Cor B1 ⇒ treat as bug until independently reproduced**; NOT PROVED. Next probe: cell-decompose which `B`-stratum carries it; replicate on fresh constructed keys | **EMPIRICAL (pending bug-hunt)** |
| Strong plant fires + `Î_prim` perm-p<0.05 on ONE arm only | Arm-scoped positive, explicit non-replication flag; likely power/artifact until reconciled (test-on-both-sets) | **EMPIRICAL (non-replicating)** |
| Strong plant fires + `Î_prim` perm-p>0.05 BOTH arms | `MI < MI_min(N)`; no gross summand→carry synergy at scope. State POWER (`MI_min`) + SCOPE. Consistent with & bounded by Cor B1. Explicitly NOT a closure (KS floor `2^−128` uncrossed) | **VERIFIED-scope (null)** |
| Strong plant does NOT fire | Instrument dead at N; test uninformative; no grade on real data | **VOID** |
| Feature = F0 `b_eps(x_{P_sum})` alone (had it been registered) | Identical statistic to v1 under `d↦d_sum`; adds nothing | **REDUCES-TO-v1 (not run)** |
| Feature = F1 `b_eps(x_{P₂})` alone | v1-class replay (fixed-shift target reparam.); no cross-point content | **REDUCES-TO-v1 (not run)** |

SECONDARY `Î_sec` (joint `2×4`): reported with its own `MI_min` and perm-p under the same null; informs the
"does the pair predict at all" cross-check but NEVER overrides the primary.

---

## (c) DISJOINTNESS ARGUMENT (one paragraph, load-bearing)
`A=[eps(x_{P₂})≠0]` and `B=[eps(x_{P_sum})≠0]` are computed from `x_{P₂}` and `x_{P_sum}` **as field elements
in F_p** via the Eisenstein lift (μ₃/CM structure of each point's coordinate) — established to have **no `d`,
no `λ`** in the computational path. `x_{P_sum}` is obtained by the **exact group-law addition** `P₂+P₁` over
`F_p`, which uses the fixed public point `P₁` and the coordinates of `P₂`; `d` is never touched. The target
`ε = [ (d₁+d₂)·λ mod n < r₁ ]` is computed from the scalar `d_sum` **in the ring Z/n** via multiplication by
`λ` and an integer threshold `r₁` set by the known `d₁`. Feature (coordinate field `F_p`) and target (scalar
ring `Z/n`) reach the common secret `d₂` by **disjoint operations in disjoint rings**; neither is a component
of the other, and there is no `r=v−w` identity. Extracting `ε` from `x_{P₂}`/`x_{P_sum}` would require
inverting the coordinate-to-scalar map, i.e. the DLP — which is why a correlation surviving the μ₆-matched,
orbit-deduped permutation null is a genuine sub-question, and its ABSENCE at `MI_min(N)` is a scoped null, not
a closure. `d₁` known only *selects the threshold* `r₁` (balance) and the fixed translate `P₁`; `d₂` is never
re-injected into the feature.

## Grade scoping vs the bilinear theorem (constraint 6)
`Î_prim` is a bilinear/addition-coupled coordinate correlation ⇒ a **null is CONSISTENT WITH and BOUNDED BY**
`bilinear_closure_proof_v1.md` Cor B1 (`[PROVED given KS]`, true coupling `≤ O(2^−128) ≪ MI_min`), and is graded
**VERIFIED-scope** (power + scope stated; NOT a closure, KS floor uncrossed). A **positive would CONTRADICT**
that theorem and is graded **EMPIRICAL (pending bug-hunt)** — an instrumentation defect until independently
reproduced. This spec moves no grade up on a citation.

**Owed gates:** `citation-verifier` on the Cap-Law `¾:⅛:⅛` / `eps=0⟺core` inputs and on the KS input to Cor B1
before any grade moves up on them; `compile-diff` if folded into a master.
