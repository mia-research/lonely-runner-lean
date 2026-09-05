# v35 — Selection rule (v33/v34) + three follow-up investigations

> **v35 ADDS §8–§10 (a second session, same day).** §1–§7 are v34 verbatim. The three new
> investigations, all with firing controls:
> - **§8 — the twist decomposition.** "FLD==CRV" (which v33/v34 dismissed as chance) tested the
>   WRONG object; the right object is `B = Σ over the SEXTIC TWIST's x-set`. Re-examined properly:
>   the dismissal survives (3/15 where parity allows vs generic 1.61), but a *different* cell it
>   exposed — `A=0` on the curve — looked enriched (8/27, p=0.002) and then **died out-of-sample**
>   (1 vs 1.07, p=0.66). Third chance-pattern this arc killed only by out-of-sample retest.
> - **§9 — the `x/y` "formal-log" readout** (a proposed cheap partial of the 0.93 joint shadow)
>   **sits at the KS √p floor**, exactly as `deg(x/y)=3` predicts; planted control grows 6→18.
> - **§10 — the `C_T` 2-3% coupling.** The proposed "flap-translation shear" mechanism is **refuted
>   analytically**: the addition-carry factorizes `C_1⊗C_1` with **λ₂=λ₃=1/3 EXACTLY, θ-independent**
>   — the 120° shear never reaches the carry (rounding is in lattice coords, a product domain). The
>   2-3% is finite-n; the n needed to see a true coupling is tabulated.
>
> Scripts: `_twist_split_B_v1.py`, `_A_zero_matched_null_v1.py`, `formal_log_xovery_readout_v1.py`,
> `ct_shear_prediction_v1.py`. Signal paths exact int/`Fraction`; float confined to the documented
> carve-outs (character-sum magnitude, matched-null rate, spectral eigenvalue).

---

# v34 — The μ₆ selection rule, its field-level refinement, and one open conservation

> **SUPERSEDES v33 — COUNT CORRECTION (§4). v33 headlined the open law as `64/64` with the
> unforced regime as `42/42` and out-of-sample `20/20`. Those numbers were INFLATED by mixing
> denominators:** `42 = 22 (p≡7 mod 8, in-sample) + 20 (ALL p≡3 mod 4, out-of-sample)`. The
> out-of-sample `p≡7 mod 8` count is **13**, not 20. **Correct: the 64 `p≡3 mod 4` primes split into
> 29 FORCED-nonzero (`p≡3 mod 8` — parity-obstructed, carrying ZERO information) + 35 UNFORCED, and
> the law holds 35/35 (22 in-sample + 13 out-of-sample).** Caught by an independent `memory-drafter`
> audit and re-verified by direct re-run. **The law itself is unaffected** — 35/35 exact zeros where
> nothing forces them, against a generic prediction of ≈1.86 across the in-sample 22. **Only the
> tally was wrong. Headlining `64` counted the forced regime as if it were evidence** — the exact
> inflation this document's own §4 parity analysis identifies. All other sections are v33 verbatim.

**Date:** 2026-07-17 · **Scripts:** `isotypic_selection_rule_v1.py`, `_sigma_chi2_scan_v1.py`,
`_field_bigrading_v1.py` (all three pass `check_no_float.py`; exact `int`/`Fraction`/`Z[ω]` throughout,
no float anywhere including the reporting columns).
**Pre-registered** before any data was seen (`experiment-designer`, this session). Governed by the
Anomaly-Drill rule (`POSITIVE_FINDINGS_MASTER_v2.md` header).

> ## ⚠ SCALE BANNER
> Everything measured here is at **p = 127 → 14000**. secp is `p ≈ 2²⁵⁶`. Nothing below has **any**
> power against a structure that switches on near `2²⁵⁶` (§X.5). Every law stated as `[VERIFIED]` or
> `[EMPIRICAL]` is scoped to that range, to `y²=x³+7`, to `p ≡ 1 mod 6`, and to `n = #E(F_p)` prime.

---

## 0. What this drill was

The arc had accumulated a set of **exact zeros** — `σ⊥s_y`, the `Σψχ₃s_y=0` GLV zero, the
`eis_p`/`eis_n` cross-energy zeros, "± flap counts exactly equal", the linear x-lift→scalar-lift
channel. Each was recorded separately, and each was used as a *wall* ("no first-order coupling").

A selection rule is two-sided: it says which channels **must** vanish and therefore which are
**allowed** to be nonzero. Nobody had written the table. This drill writes it.

**Result in one line:** those zeros are not five facts. They are **one** rule — and the rule has a
**field-level refinement that is strictly stronger than the curve-level one**, whose failure mode
is the sextic twist. One conservation survives unexplained and is the deliverable.

---

## 1. Claim S — the μ₆ selection rule on the curve `[PROVED]` + `[VERIFIED at p=547]`

`Aut(E) = μ₆ = ⟨[−1],[λ]⟩` acts on points: `[−1]:(x,y)→(x,−y)`, `[λ]:(x,y)→(βx,y)`. For `n` prime
the action is **free** on `E∖{O}` (verified directly in `orbits_of`, asserted per orbit, not argued).

**Bidegree.** `F` has bidegree `(j,k) ∈ ℤ/2 × ℤ/3` iff `F([−1]P)=(−1)^j F(P)` and `F([λ]P)=ω^k F(P)`.

**Claim S.** `Σ(F,G) := Σ_{P≠O} F(P)conj(G(P)) = 0` whenever `bidegree(F) ≠ bidegree(G)`.
*Proof:* reindex `P→uP`, `u∈μ₆`; `Σ = χ_F(u)conj(χ_G(u))·Σ` for every `u`; if the characters differ
some `u` gives a factor `≠1`. ∎ **Three lines. The run does not upgrade this — it checks the
implementation and the bidegree assignments.**

**Verified:** p=547, **54 cross-bidegree pairs, 0 violations**, computed as a *direct* sum over all
`P≠O` (an orbit-decomposed sum would assume the mechanism and be vacuous).

**Controls fired.** `PC-1`: `T(s_y,s_y)=m=91` ✓. `PC-2`: `T(s_y, s_y·h)=⌊m/2⌋=45` **exactly**, a
known nonzero at *matching* bidegree — so the Gram can see a nonzero and its zeros are informative.

**What Claim S absorbs.** `σ⊥s_y` (σ is `(0,0)`, `s_y` is `(1,0)`), the eis parity zeros, the linear
lift→scalar zero. **One rule, not five walls.**

### 1a. Correction to the intuition that opened this drill
`x → βx` is the action on a **field element**; `β∈F_p` is **not** `ω∈ℂ`. So `x` as a ℂ-valued readout
has **no μ₃ grading** — it has an *energy profile*. Measured: `x`, `eisx`, `nrm`, `sxt_z6` all come
back **ungraded**. `eisx`'s defect set is **exactly the flap** (`eis(βx)=ω²eis(x)` iff `eps(x)=0`),
so the grading defect and the flap are the same object. **An ungraded readout is not "structureless" —
report which isotypic components carry its energy.**

**Derived predictions, both confirmed at every prime:** `χ₂(β)=1` always ⇒ `chi2x` is `(0,0)` for
every `p`; `chi2y`'s `j` tracks `p mod 4` via `χ₂(−1)=(−1)^{(p−1)/2}`.

---

## 2. Claim F — the FIELD-level rule `[PROVED]` + `[VERIFIED 336/336, 180/180]`

**This is the load-bearing result of the drill.** For `F,G` functions of `x` alone,
`#{y : y²=x³+7} = 1+χ₂(x³+7)`, so **every `j=0` pairing splits exactly**:

```
Σ(F,G) = Σ_x F·conj(G)  +  Σ_x F·conj(G)·χ₂(x³+7)
         └─ FIELD: pure F_p lattice/character geometry, ZERO curve content ─┘
                                 └─ CURVE: Weil-scale character sum ─┘
```

**Reporting the total as one number attributes a LATTICE fact to CURVE arithmetic.** This is the
drill's central proxy guard and is mandated on every `j=0` entry hereafter.

**The symmetry.** `p ≡ 1 mod 6` ⇒ `F_p*` contains `μ₆(F_p)=⟨β,−1⟩`, acting **by multiplication**.
Give each x-readout a **field bidegree** `(i,k)`: `F(−x)=(−1)^i F(x)` (field parity), `F(βx)=ω^k F(x)`.

> **`Aut(E)` reaches `x` only through μ₃** — `[−1]` moves `y`, not `x`. **The field-level group is
> strictly larger than the curve's.** And the extra `ℤ/2` is not curve-induced:
> ```
> βx  :  (βx)³+7 = x³+7          weight INVARIANT  ⇒  μ₃ survives on the curve
> −x  :  (−x)³+7 = −(x³−7)       ⇒ the SEXTIC TWIST y²=x³−7
> ```
> **Field negation exchanges E with its sextic twist.**

**Claim F.** (F1) FIELD `= 0` unless `(i,k)_F = (i,k)_G` — **6 sectors**.
(F2) CURVE `= 0` unless `k_F = k_G` only — **3 sectors**, because `χ₂(x³+7)` is μ₃-invariant but not
negation-invariant.

**`FIELD: 6 sectors. CURVE: 3 sectors. The missing ℤ/2 IS the twist.`**

**Verified** (p=127→1249, 16 primes): **(F1) 336 mismatched pairs → 0 violations. (F2) 180
mismatched-weight pairs → 0 violations.** Measured field bidegrees: `sigma`=`(1,0)` at every prime;
`eps`=`(0,0)` at every prime; `chi2`=`(1,0)` at `p≡3 mod 4` and `(0,0)` at `p≡1 mod 4`, exactly
tracking `χ₂(−1)`.

### 2a. Two recorded facts collapse into one
- `B1 = Σ_{x∈F_p*} σ(x) = 0` — σ is `(1,0)`, the constant `1` is `(0,0)` ⇒ **mismatch**.
- `⟨σ,χ₂⟩_FIELD = 0` at `p≡1 mod 4` — χ₂ is then `(0,0)` ⇒ **mismatch**.

**These are the same selection rule.** `B1=0` was on record with a bespoke argument ("σ odd + `F_p*`
negation-closed"); it is a special case. **Confirmed `B1=0` at 49/49 primes.**

### 2b. Non-forced FIELD zeros are accounted for
240 non-forced FIELD pairs, **72 exactly zero anyway**. Of those, **56 are ordinary `F_p*` character
orthogonality** (`Σχ=0` for nontrivial χ — a *larger* group than μ₆; class-M readouts are `F_p*`-graded,
class-L lattice readouts are not). **The remaining 16 are the class-L × class-M cross-class pairs** —
`(chi2,sigma)`×8, `(chi2,eps)`×4, `(chi3,eps)`×2, `(chi6,sigma)`×2 — i.e. **exactly one live object**,
below.

---

## 3. DISSOLVED — "± flap counts are EXACTLY equal" `[the conservation was a conflation]`

The record (`v15`) says the ± flap counts are exactly equal, forced by `σ(−x)=−σ(x)` + `F_p*`
negation-closed. **That mechanism is a statement about the FIELD, and does not transfer to the curve**,
because `x→−x` maps `X(E)` to the x-set of the **twist**. Two different sums:

```
(B1) = Σ_{x∈F_p*} σ(x)          [field]  = 0   PROVED, and a case of Claim F (§2a)
(B2) = Σ_{P≠O}    σ(x_P)        [curve]
(B2) = (B1) + C = C ,    C := Σ_x σ(x)·χ₂(x³+7)     — verified EXACTLY at 49/49 primes
```

**`(B2) = C ≠ 0` generally.** The curve flap counts are **not** equal; they differ by `C`. Measured
`C²/p ≤ ~3.7` over p=127→6000 (`C` reported with the exact rational `C²/p`, no float), consistent with
the Weil reference `|C| ≤ ‖σ‖_W·2√p`.

**Per the Anomaly-Drill rule, dissolution is a POSITIVE result: it dissolves into a sharper law.**
The sharper law is `(B2)=C`, and the *mechanism* for `C≠0` is now explicit: **the curve part lost the
`ℤ/2` that annihilates the field part, and it lost it to the sextic twist.** `C` is a **magnitude with
its reference scale**, not "no structure".

**Retract:** do not restate "± flap counts exactly equal" without saying **field**. On the **curve**
it is false, and `C` measures the failure.

---

## 4. ★ OPEN — an exact conservation with its mechanism ruled out `[EMPIRICAL, 35/35 UNFORCED]`

The one live cross-class object (§2b). At `p≡3 mod 4`, `σ` and `χ₂` **share** field bidegree `(1,0)`,
so Claim F does **not** force the zero. Structure of the object:

- `σχ₂` is μ₃-invariant (`σ(βx)=σ(x)`, `χ₂(β)=1`) **and** field-even at `p≡3 mod 4` (odd×odd)
  ⇒ **`σχ₂` is μ₆(F_p)-invariant**; the flap is μ₆-stable ⇒ `6 | flap` (verified) ⇒
  **`FLD = 6·S`**, `S` a sum of `ORB := flap/6` signs ⇒ **parity obstruction `S ≡ ORB (mod 2)`**
  (pre-registered; verified at every prime).

**The law:**
```
⟨σ,χ₂⟩_FIELD = 0   ⟺   p ≢ 3 (mod 8)                    [p ≡ 1 mod 6, n prime]
```
Three regimes, all exact:

| regime | `FLD` | count | status |
|---|---|---|---|
| `p ≡ 1 mod 4` | `= 0` | 19/19 | **FORCED** by Claim F (field-parity mismatch). |
| `p ≡ 3 mod 8` | `≠ 0` | 29 primes | **FORCED nonzero** by the ORB parity obstruction. **Carries ZERO information — must not be counted as evidence.** |
| `p ≡ 7 mod 8` | `= 0` | **35/35** | **NOT FORCED. ← the finding** |

**The only informative cells are the 35 unforced ones.** The 64 `p≡3 mod 4` primes split
`29 forced-nonzero + 35 unforced`. **v33 headlined `64/64`; that counted the parity-obstructed regime
as if it were evidence, and is corrected here.** A forced-nonzero result cannot fail, so it confirms
nothing.

**Power.** In the `p≡7 mod 8` regime, parity *permits* `S=0`; a generic signed sum would give
`Σ 2/√(2π·ORB) ≈ 1.86` expected zeros across the in-sample primes. **Observed: 22/22 in-sample.**
This is an exact law, not a magnitude.

**Out-of-sample.** The `p mod 8` pattern was found **post-hoc** (by reading a table), so it was
re-tested with the hypothesis fixed on fresh primes `[8000,14000)`: **13/13 unforced** (v33 wrote
`20/20`, which was the count of *all* `p≡3 mod 4` primes in that range, not the `p≡7 mod 8` ones —
the denominator-mixing that produced the inflated `42`). **Total unforced: 35/35.**

**Sub-law, also 64/64 (`H1`):** `ORB = flap/6` is **even ⟺ p ≡ 7 mod 8`**. This is a **Cap-Law-level
lattice fact** (the flap cardinality mod 12) that is **not in the record** and is independent of any
curve arithmetic. `p mod 8` is `χ₂(2)` — the supplementary law.

### 4a. The mechanism hunt — the natural candidate is RULED OUT
If some `c∈F_p*` gave `σχ₂(cx) = −σχ₂(x)` for all `x`, then `S=−S=0`, and no such `c` could exist when
`ORB` is odd — which would explain both regimes at once. **Exhaustive search over every `c∈F_p*` at
p=127, 823, 967, 991 (all `≡7 mod 8`, all `S=0`): NO SUCH `c` EXISTS.**

**Whatever enforces `S=0` at `p≡7 mod 8` is not a multiplicative sign-flip.** This narrows the hunt and
does not close it.

**Named next probes** (in order): (i) is `S=0` forced by a *non-multiplicative* involution of the flap
— e.g. a lattice reflection of the rhombus `P`, or a Gauss-reduction tie-break symmetry? (ii) `H1` is a
statement about `#flap mod 12`; derive it from the Cap Law's continuum geometry — the `p mod 8`
dependence must enter through the **reduced-basis orientation** or through `rdiv`'s round-half-up
convention. (iii) Does the law survive `p ≡ 1 mod 4` in a twisted form, i.e. is there a `p mod 8` law
for `⟨σ,χ₃⟩` or `⟨eps,χ₂⟩`? (iv) Re-run at `p > 10⁵` — every number here is `p < 14000`.

**Scope.** All of §4: `y²=x³+7`, `p≡1 mod 6`, `n` prime, `p ∈ [127,14000)`, 64 primes, `σ` orientation
fixed by a **100%-agreement pre-flight** (not the record's data-dependent majority vote). Sign of `σ`
flips under reduced-basis relabeling; `FLD=0` is invariant under that flip (`0=−0`), so **the law is
relabeling-invariant** — but `⟨σ,F⟩ ≠ 0` values are not, and carry their orientation.

---

## 5. ★ BUG in the existing codebase `[VERIFIED — fixed in the new scripts, NOT yet in the original]`

**`int1_frame_operator_v1.py:41`:**
```python
beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2
```
The β calibration uses the **single hardcoded probe `x=12345`**. Since **`12345 = 3·5·823`**, at
**`p=823`** the probe is `x≡0`, the test degenerates to `(0,0)==(0,0)`, and `b1` is returned with
**nothing tested**. At p=823 that is the **wrong root**:

| root | exact `ω²` relation | carry classes |
|---|---|---|
| `b1=648` (returned) | **0/822** | `{core:1, eps=2: 822}` — garbage |
| `b2=174` (correct) | **822/822** | `{core:619, flap:204}`, flap/822 = **0.248 ≈ ¼** ✓ Cap Law |

**Among `p ≡ 1 mod 6`, p=823 is the unique affected prime** (the other divisors of 12345 are 3 and 5).
**secp is unaffected** (`12345 ≢ 0 mod p`). Any small-prime sweep that included p=823 and used
`int1_frame_operator_v1.build` produced garbage there, silently.

**The Cap Law is NOT contradicted** — p=823 was never a counterexample. The `[PROVED]` grade stands.

**Fix** (applied in `isotypic_selection_rule_v1.py` / `_sigma_chi2_scan_v1.py`): calibrate against many
nonzero probes and **assert exactly one root qualifies**.

**Detection credit:** the pre-registration mandated *reporting* `#{x : eps(x)=2}` rather than assuming
it empty, and mandated a **100%-agreement** orientation pre-flight rather than the record's majority
vote. Both fired. The record's own `flap_sign_parity_v1.py` picks orientation by
`USE_PLUS = plus >= minus` — a data-dependent vote that would have **silently absorbed** this.

---

## 6. What this does and does not establish

**Does.** (i) The exact zeros of this arc are **one** μ₆ selection rule (Claim S), plus a strictly
stronger **field-level** rule (Claim F) whose group is **larger than `Aut(E)`**. (ii) The field/curve
split is mandatory: **6 sectors on the field, 3 on the curve, and the missing ℤ/2 is the sextic twist.**
(iii) "± flap counts equal" is a **field** fact; on the curve it fails by `C`, a Weil-scale sum.
(iv) One exact conservation (`p≡7 mod 8`) survives with its natural mechanism exhaustively ruled out.
(v) A real bug in the codebase, with its blast radius bounded.

**Does not.** This is **lift/field geometry** — class L × class M. `σ` is an x-only readout and sits
inside the Part V bounded-degree bound already; **none of this moves the leakage frontier, and no claim
here bears on ECDLP.** It does not touch the joint-SET / multi-key frontier (§X.7), the cheap-partial
`(x,y)` shadow (§X.1), or the amicable transfer (§X.3). **And the scale banner is total: every number
is `p < 14000`; secp is `2²⁵⁶`.**

**The positive payoff is the allowed-channel map.** A selection rule names where coupling **can** live.
The curve part is unforced in every μ₃-matched channel — including the ones the field rule kills. That
is a sharper statement of *where to look* than "no first-order coupling", which is what these zeros
were previously used to say.

---

## 7. Reproduction
```
python3 isotypic_selection_rule_v1.py --quick     # bidegree table, Gram, controls, field/curve split
python3 _sigma_chi2_scan_v1.py 100 6000           # B1/B2/C, the FLD/CRV columns, exact C^2/p
python3 _field_bigrading_v1.py 100 1300           # Claim F: (F1) 336/336, (F2) 180/180
```
All three pass `python3 check_no_float.py`. Controls `PC-1`/`PC-2` fire inside
`isotypic_selection_rule_v1.controls`. The `n`-prime filter is pre-registered and skipped-candidate
counts are printed per class.

---
---

# SESSION 2 (same day) — three follow-up investigations

Scope banner (§ top) governs all three: measured at `p ≤ 30000` (§8), `p ≤ 2503` (§9),
`p ≤ 100003` (§10). Nothing has power at `2²⁵⁶`.

---

## 8. The "FLD==CRV" object — dismissed for the right reason after testing the WRONG one

**Prompt (user):** "Mathematical fluke and coincidence????? I think those need more investigations."
Correct — "coincidence" was a dismissal word, and I had tested the wrong object.

**The algebra.** `1 − χ₂(x³+7)` is `0` on E's x-set, `2` on the twist's (never `1`: no 2-torsion).
So, splitting the `j=0` field sum by which curve `x` lives on:
```
A := Σ_{x : χ₂(x³+7)=+1} σ(x)χ₂(x)   (E's x-set)   ;   B := Σ_{x : χ₂(x³+7)=−1} σ(x)χ₂(x)   (TWIST)
FLD = A + B ,   CRV = A − B   [exact identity, verified]     ⇒     FLD==CRV  ⟺  B = 0
```
So "are two numbers equal" (a chance-y question) was the wrong frame. **The object is `B`, a
structured pairing over the sextic twist's x-set**, with its own parity obstruction (`σχ₂`
μ₆(F_p)-invariant at `p≡3 mod 4`, twist x-set μ₃-stable but not negation-stable ⇒ `3|B`,
`B/3 ≡ N_W mod 2`). *(`_twist_split_B_v1.py`; `3|A`, `3|B`, and the parity obstruction asserted in-run,
no violations, p<9000.)*

**Result: the dismissal survives.** The 11 `B=0` primes over p<9000 split:
- **8 "everything vanishes"** (`A=B=0`, all `p≢3 mod 8`) — the established `FLD=0` law (§4) plus `A=0`.
- **3 twist-only zeros** (`B=0, A≠0`, as opposed to the everything-vanishes case): **p = 163, 547, 907, all `p≡3 mod 8`.** So p=547 IS in
  a real category — but the rate is **3/15 where parity permits, vs a generic 1.61.** Not a law.

**A different cell it exposed looked real, then died out-of-sample.** `A = ½·⟨σχ₂,1⟩` over the actual
curve points; Claim S does not force it. In-sample (p<9000) `A=0` at **8/27 where `NE` even vs a
MATCHED-null 2.22, p=0.002** — the μ₆-equivariant orbit null, not a point shuffle (`_A_zero_matched_null_v1.py`).
**But hypothesis frozen and tested on fresh `[9000,30000)`: 1 observed vs 1.07 expected, p=0.66.**
The 15-prime first out-of-sample window (`[9000,16000)`, p=0.39) had almost no power because `P(A=0)~1/√NE`
falls with p; the extended 37-prime window settled it. **Post-hoc selection across ~40 pairings — the
third chance pattern this arc that only out-of-sample retest killed** (with `FLD==CRV`@547 and the v34
`C=0⇒p≡1 mod 4`). **Discipline confirmed: an exact zero at small p is a coincidence until frozen +
retested out-of-sample.**

---

## 9. The `−x/y` "formal-logarithm" cheap readout sits at the KS √p floor  `[VERIFIED + PROVED|KS]`

**Proposal (user):** `T=−x/y` is the local uniformizer at `O`; the formal group log is
`L(T)=T+3T⁷+(735/13)T¹³+…` (VERIFIED `= Σ 7^k C(3k,k)/(6k+1) T^{6k+1}`); dropping higher terms,
`d ≈ T/T_G = (x·y_G)/(y·x_G) mod p` is a cheap linear shadow of `d` — a candidate cheap partial of
the 0.93 joint (x,y) shadow (§X.1).

**Theory caveat (stated so the null is read right).** `L` linearizes the **formal group over `Z_p` =
`E₁(Q_p)`, the kernel of reduction** — where `T` is `p`-divisible and the series converges. For
`P_d∈E(F_p)`, `T(P_d)` is a generic `F_p` element (no valuation, no convergence) and `P↦−x/y` is **not
a homomorphism**; `L([d]P)=d·L(P)` needs `[d]G∈E₁(Q_p)`, and getting it there is the DLP. The
construction works exactly when **`#E(F_p)=p`** (anomalous — Smart/Satoh–Araki/Semaev); **secp has
`#E=n≠p`** (verified), which is why anomalous is a checked door (Part III/V).

**Still a legitimate cheap joint readout — so tested.** `deg(x/y)=3` (simple poles at the three
2-torsion points, simple zero at `O`) ⇒ KS Thm 1+eq(3): `|Σ ω(P)ψ(b·x/y)| ≤ 6√p` ⇒ `e_p(b·x/y)` is
at the floor. **Measured** (`formal_log_xovery_readout_v1.py`, `C/floor` = max-over-`a` aligned
correlation / generic scale):

| p | 211 | 433 | 733 | 1051 | 1669 | 2503 |
|---|---|---|---|---|---|---|
| `x/y` raw | 1.25 | 1.06 | 1.10 | 1.33 | 1.30 | 1.21 |
| `e_p(x/y)` | 1.34 | 1.11 | 1.26 | 1.31 | 1.30 | 1.39 |
| `e_p(xy)` (best cheap on record) | 1.39 | 1.48 | 1.24 | 1.35 | 1.36 | 1.25 |
| **PLANTED aligned control** | **6.10** | **8.12** | **10.27** | **12.49** | **14.97** | **18.04** |

**Flat at 1.05–1.4, indistinguishable from `e_p(xy)` and from noise; the planted control grows
6→18 (test has power). Theory and data agree: `−x/y` captures no fraction of the 0.93 shadow beyond
the generic floor.** A scoped null (p≤2503) with a firing control — NOT a closure of §X.1; the shadow
still requires an aligned readout (⇒U⇒DLP).

---

## 10. The `C_T` 2-3% coupling — the "flap-shear" mechanism refuted, exactly  `[PROVED]`

**Proposal (user, Investigation 1):** the 2-3% `λ₂≠λ₃` split of the addition-rounding transfer
operator `C_T` is the geometric shear of the flap translation by `R₁,R₂` at `θ=50.55°`.

**Refuted analytically — and the refutation is a sharper law.** `C_T`'s carry is rounded in **lattice
coordinates** (`state()` in `ct_tensor_structure_v1.py`: the Babai coefficients `c₁,c₂`), and the
fundamental domain in lattice coordinates is **the product box `[−½,½)²` for ANY basis `R` (any θ)**.
The 120° shear is absorbed into the fixed non-orthogonal basis and never reaches the carry. For
i.i.d.-uniform lift points the coordinate-1 carry process `{round(a₁ₖ+a₁ₖ₊₁)}` depends only on the
`a₁`'s, coordinate-2 only on the `a₂`'s, and the two are **independent** ⇒ `C_T=C₁⊗C₁` exactly.

**Exact computation** (`ct_shear_prediction_v1.py`, rational integration over `[−½,½]³`):
```
C₁ = [[7/9, 1/9, 1/9],
      [2/3, 1/3, 0  ],      stationary 3/4 : 1/8 : 1/8      eigenvalues {1, 1/3, 1/9}
      [2/3, 0,   1/3]]
C₁⊗C₁ eigenvalues (EXACT) = 1¹, (1/3)², (1/9)³, (1/27)², (1/81)¹
  ⇒  λ₂ = λ₃ = 1/3  EXACTLY (doubly degenerate)  ⇒  predicted split = 0, and θ-INDEPENDENT
```
**The derivation contains no `θ` and no `R₁,R₂`.** The doubly-degenerate `1/3` is forced by the tensor
structure (`1·⅓` and `⅓·1`), which is why v2's `C_T` drill saw the block split into one swap-even +
one swap-odd channel. **Mechanism refuted: the shear predicts zero coupling, not the 2-3%.**

**So what IS the 2-3%?** A deviation of the arithmetic `{x_d}` from the i.i.d.-uniform model. The
empirical split **decays with n** — `|λ₂−λ₃|` = 0.047, 0.034, 0.027, **0.0113** at n = 558, 3353,
8393, **99666** (p=100003 reproduces DRILL 01's 0.011) — consistent with the analytic 0, not a fixed
coupling. DRILL 01's matched surrogate already reproduced it (z=+0.13).

**Required n to detect a TRUE arithmetic coupling** (estimator floor `|λ₂−λ₃|_noise = C·n^{−0.584}`,
DRILL 01's exponent, anchored at (99666, 0.0113) ⇒ C≈9.4; need floor `< ε`):

| coupling ε (as % of 1/3) | 3% | 1% | 0.3% | 0.1% | 0.03% |
|---|---|---|---|---|---|
| required n | 1.2e5 | 8.1e5 | 6.3e6 | 4.2e7 | 3.3e8 |

**At 2-3% (DRILL 01's scale) n~10⁵ is exactly at the floor — uninformative.** A 0.1% coupling needs
n~10⁷ (= §X.6's next probe). This converts "why is there a 2-3% gap?" into: the gap is finite-n noise
around a θ-independent exact tensor law, and any residual arithmetic coupling below the floor needs the
tabulated n to see. **Not a closure — a bounded magnitude with its required sample size** (§X.6 stays
open, now with a power budget).

---

## SESSION 2 — reproduction
```
python3 _twist_split_B_v1.py 100 6000                # A/B twist split, parity obstruction, B==0 count
python3 _A_zero_matched_null_v1.py                   # A==0: in-sample 8/27 p=.002, OUT-OF-SAMPLE p=.66
python3 formal_log_xovery_readout_v1.py              # x/y readout at the KS floor; planted control 6->18
python3 ct_shear_prediction_v1.py                    # C_1 exact, tensor square, shear=0, required-n table
```
Signal paths exact int/`Fraction` (readout values, `A`,`B`,`σ`,`χ₂`, carry states). Float only in the
documented carve-outs — character-sum magnitude (§9), matched-null rate (§8), spectral eigenvalue
(§10) — never as a threshold on data. `check_no_float.py` flags those carve-out lines; the signal paths
they sit around are exact.
