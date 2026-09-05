# RESULT — Amicable-partner correspondence, Tier A exact arm (v1)

**Spec:** `PREREG_amicable_correspondence_bits_v3.md` (pre-data), deviations D1–D8 in
`PREREG_amicable_correspondence_bits_v1_DEVIATIONS.md`. v1/v2 of the spec are frozen.
**Code:** `amicable_correspondence_tierA_v1.py`, `amicable_tierA_analyze_v1.py`.
**Raw:** `amicable_tierA_results_200000.json`, `amicable_tierA_run_v2.log`. **Date:** 2026-07-23.

> ## TIER A LINE — quote verbatim beside every number below
> `E_7 : y² = x³ + 7`, `p ≡ 1 mod 3`, `11 ≤ p < 200000`, `n = #E(F_p)` prime: **108 amicable 2-cycles ×
> 2 orientations = 216 curves**, 216 matched non-amicable controls, `Σn = 3.47 × 10⁷`,
> `max n = 198901`, `mean n = 80275`, divisor cells per unit 4 to 102. Contrast floor **0.065**.
> Max `p` is **17.60 bits**; secp is **256 bits**. This run spans none of that gap.

---

## 1. Validity gates — all pass, statistics may be read

| gate (v3 §9 cells 6, 9) | requirement | result |
|---|---|---|
| **P1 plant ladder** | fires for every `k \| (n−1)`, `k > 6`, every curve | **0 missed `k` on 432/432 curves** |
| §2A inequality `\|image\| ≤ (n−1)/\|Γ*_inv\|` | violated nowhere (a violation is a bug) | **0 violations** |
| `DEG(N_const)` | true on every curve | **true on 432/432** |
| `DEG`-true hypothesis feature reported firing | must be zero | **0** |

**Instrument validation (independent of the spec's own gate).** The `Γ*` routine was checked against
brute force over **all** `t ∈ (Z/n)*`, not only divisor-subgroup generators: agreement on every case
tested. On planted labels at `p = 907` the routine recovered **exactly** `Γ_k` for all 12 divisor orders
`k ∈ {7,14,21,23,42,46,69,138,161,322,483,966}`, with `|image| × |Γ*| = n−1` exact in each. The
statistic therefore detects a planted symmetry of any order with no false negatives — which is what
makes the null below informative rather than uninformative.

The CM point counter was validated **1123/1123** against the `O(p)` character sum below 20000
(2 ambiguous, resolved by exact fallback) before being used as the sole source of `n` above 20000.
`check_no_float.sh` passes on both run scripts.

---

## 2. ARM-A — exact arm

**Every one of the four frozen hypothesis features returned its forced value on every curve, in both
orientation strata, on both arms.**

| feature | `Γ*_forced` | `\|Γ*\|` observed (amicable, 216) | `\|Γ*\|` observed (control, 216) | fires |
|---|---|---|---|---|
| `ΦA` `χ_n(x̄³+7)` | `μ₂` | `2` on 216/216 | `2` on 216/216 | 0/216 |
| `ΦB` `χ_n(δ)` | `{1}` | `1` on 216/216 | `1` on 216/216 | 0/216 |
| `ΦC` `δ` | `{1}` | `1` on 216/216 | `1` on 216/216 | 0/216 |
| `ΦD` `±`-class of `dlog_{G̃}(Q(P))` | `μ₂` | `2` on 216/216 | `2` on 216/216 | 0/216 |

Orientation strata (D3), all four features: `p<n` amicable 0/108, control 0/108; `p>n` amicable 0/108,
control 0/108. `Γ*_inv = Γ*` on every row (no `σ ≠ id` equivariance was found for `ΦD`).
`orbit_exact` false on all 216/216 for all four — the configuration D7 predicted for the
character-valued features, and the reason the v2 firing rule had to be amended before the run.

**Contrast.** Both arms are at zero, so no Fisher test is defined and **no amicability attribution is
available in either direction** from the exact arm.

**Status against §9.** This satisfies the *exact-arm* precondition of **cell 5** (exact arm at forced
value everywhere, gate clean, `DEG` clean, P1 fires). **Cell 5 is not yet reached**: it additionally
requires the Tier B graded arm within the M1 null on ≥18/21 units and P2 firing, and **Tier B has not
been run**. The correct present statement is an exact-arm null with demonstrated power, with the
approximate-symmetry question open.

Scoped statement, in the mandatory form:

> Among the 4 frozen partner-side features, on `E_7/F_p` for the 108 amicable 2-cycles with
> `p < 200000` (both orientations), **no symmetry beyond `μ₆`-forced was detected exactly.**

**This is not a closure of the amicable channel and may not be written as one.** The approximate
(graded) arm is untested at every scale, and the four blind spots of §5 below are unaddressed.

---

## 3. ARM-B — channel-width statistics

*Reported separately from ARM-A and never merged with it. **Every number in this section was computed
where `φ` is computable, i.e. in-frame only. None transports to secp by computability** — there `φ`
costs a discrete log. A structural law about the map could transport, but only by proof.*

### A2-1 — the family-level floor: `Γ*(ρ)`, `ρ(P) = (x mod n, y mod n)`

**`Γ*(ρ) = {1}` on 216/216 amicable and 216/216 control curves.** → **§9 cell 12.**

Because every T1-legal feature factors as `Φ = f ∘ ρ`, giving `Γ*_inv(ρ) ⊆ Γ*_inv(Φ)`, this is a
statement about the **whole legal family**, not about the four members enumerated in §2:

> At this tier the T1-legal family has **no free symmetry**. Any beyond-ceiling symmetry a legal
> feature possesses must be manufactured by `f`, not inherited from the reduction `ρ`.

`[EMPIRICAL, Tier A]`. Not a closure.

**Injectivity of `ρ`, by stratum — a direct confirmation of the D3 argument:**

| stratum | amicable | control |
|---|---|---|
| `p<n` (reduction is the identity on `[0,p)`) | `ρ` injective **108/108** | **108/108** |
| `p>n` (collision set of size `p−n = t_p−1`) | `ρ` injective 73/108 | 81/108 |

The `p<n` rows are injective without exception, exactly as D3 predicted. Had v1's unit rule survived,
the entire `p>n` stratum — the only place where `ρ` collides at all — would have been excluded from the
frame.

### A2-2 — does the GLV/μ₆ action descend affinely through `r(x) = x mod n`?

**No, and the result is exact rather than statistical: there are ZERO unforced agreements.**

| arm | observed agreements | predicted forced no-wrap set `⌊(p−1)/β⌋+1` | curves mismatching | unforced |
|---|---|---|---|---|
| amicable | 1673 / 17,293,464 | 1673 | **0 / 216** | **0** |
| control | 2948 / 17,347,518 | 2948 | **0 / 216** | **0** |

Every agreement, on every one of the 432 curves, is exactly the set `{x : βx < p}` — the `x` for which
`βx` does not wrap mod `p`, so that `r(βx) = βx = β·r(x)` holds arithmetically and the fitted `(u,v) =
(β, 0)` is satisfied for free. **Full descent occurs on 0/216 curves in both arms.** The apparent arm
difference (1673 vs 2948) is entirely `β` varying between curves and carries no information.

> ## ⚠ A2-2 RECLASSIFIED — the statistic is ALGEBRAICALLY FORCED, not a measurement
> **This supersedes the §9 cell 14 reading first written here.** The identity above is not special to
> `β`: it holds for **every** multiplier `m`, so A2-2 carries **no information about μ₆/GLV** and no
> information about amicability.
>
> **Proof.** Take `x` non-collision, so `r(x) = x`. Write `mx = kp + (mx mod p)`, `k = ⌊mx/p⌋`. With the
> fitted `(u,v) = (m,0)`, agreement at `x` ⟺ `(mx − kp) ≡ mx (mod n)` ⟺ `n \| kp` ⟺ `n \| k`
> (as `gcd(p,n)=1`). And `k < n` in both orientations (`m < p`; if `p > n` then `x < n` so
> `k < mn/p < n`). Hence agreement ⟺ `k = 0` ⟺ `mx < p` — exactly the no-wrap set, **for every `m`**.
>
> **Verified exhaustively:** over **all** `p−1` multipliers at `p,n =` (67,79), (79,67), (907,967),
> (967,907) — agreement `≠` no-wrap set on **0** multipliers in every case.
>
> **Consequence for the plants.** `B1` (`β := 1`) and `B2` (random multiplier) are two instances of this
> same identity — `B1` is the case `mx = x < p` always, giving full agreement; `B2` is a generic `m`,
> giving its no-wrap set. **Neither can fail**, so they are not a two-sided control and they do **not**
> validate A2-2. The earlier note in this section claiming they did is withdrawn.
>
> **What survives:** the Tier A numbers are correct as arithmetic — zero unforced agreement on 432/432
> curves. What does not survive is reading them as evidence *about the GLV action*. The registered
> question — whether the μ₆ action descends through the legal reduction — is **not answered by this
> statistic** and needs a non-forced replacement under a new pre-registration. §9 cell 14 is **not
> entered.**

---

## 4. Disclosures

1. **`ΦD` does different work on the two arms; its contrast is limited accordingly.** `⊥`-rate is
   **8,666,102/17,331,924 ≈ 0.500** on the amicable arm versus **13,050,816/17,383,614 ≈ 0.751** on the
   control. The cause is structural, not incidental: on the amicable arm `#Ẽ(F_n) = p` is prime so `G̃`
   generates the whole group and `x̄` lands iff `x̄³+7` is a QR (≈ half); on the control arm `#Ẽ(F_n)` is
   composite (216/216 verified) and `⟨G̃⟩` may be proper, so more points are unreachable. Any future
   `ΦD` contrast must carry this.
2. **`N0` measured, confirming D8.** `|image(N0)| = 2` on 432/432 curves — it is a coarsening of `ΦA`,
   **redundant rather than degenerate**. Retained as a disclosed diagnostic, counted in no tally and no
   `K`. The degeneracy role is carried by `N_const`, which triggered `DEG` on 432/432.
3. **A bug found and fixed mid-implementation.** The `ΦD` equivariance routine assumed the reference
   value invertible mod `#Ẽ(F_n)` — true on the amicable arm (prime), false on controls (composite).
   It now seeks a unit reference and returns undetermined if none exists. The pre-fix run was discarded,
   not analyzed.
4. **Sanity check passed:** `#Ẽ(F_n) = p` on 216/216 amicable rows and `≠ p` on 216/216 control rows.

---

## 5. Declared blind spots — restated verbatim from spec §7, mandatory beside the null

> **What this design cannot falsify, stated now:** (i) features outside the frozen §2 list; (ii) effects
> below the measured `e_min` (ARM-A) or below 0.0079 support resolution (A2-3); (iii) effects appearing
> only at `p ≫ 200000`; (iv) non-group-structured fibre patterns that are neither exact `Γ_k`-orbits nor
> `t_k`-approximate — partially covered by the reported fibre-size multiset, by neither statistic.

Additionally, from the Tier A line: this run reaches **17.60 bits** against secp's **256**. A structure
switching on near `2²⁵⁶` would not appear here and **no statement in this document has power against
that hypothesis.** `F1` (the amicable pair itself) is exact at full scale and is neither strengthened
nor weakened by anything above.

---

## 6. Open after this run

1. **Tier B graded arm (§2b) + P2** — the approximate-symmetry question, untested. Required before
   §9 cell 5 can be reached.
2. **A2-3** (support of `δ_ρ`, how far the legal reduction is from intertwining the two group laws) —
   Tier B, not run.
3. **`p ≫ 200000`** — the exact arm at `10⁶` is a pre-declared option (`Σn ≈ 3.94 × 10⁸`, ~23× Tier A)
   requiring a new DEVIATIONS entry, never a run-time judgment call.
4. **Features outside the frozen §2 list** — a new feature requires a new pre-registration; it may not
   be added to this grid and re-run.
