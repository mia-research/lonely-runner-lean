# v33 — The μ₆ selection rule, its field-level refinement, and one open conservation

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

## 4. ★ OPEN — an exact conservation with its mechanism ruled out `[EMPIRICAL, 64/64]`

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

| regime | `FLD` | status |
|---|---|---|
| `p ≡ 1 mod 4` | `= 0` | **FORCED** by Claim F (field-parity mismatch). 19/19. |
| `p ≡ 3 mod 8` | `≠ 0` | **FORCED nonzero** by the ORB parity obstruction. Carries no information. |
| `p ≡ 7 mod 8` | `= 0` | **NOT FORCED. 42/42. ← the finding** |

**Power.** In the `p≡7 mod 8` regime, parity *permits* `S=0`; a generic signed sum would give
`Σ 2/√(2π·ORB) ≈ 1.86` expected zeros across those primes. **Observed: 22/22 in-sample.** This is an
exact law, not a magnitude.

**Out-of-sample.** The `p mod 8` pattern was found **post-hoc** (by reading a table), so it was
re-tested with the hypothesis fixed on fresh primes `[8000,14000)`: **20/20**. Total **64/64**.

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
