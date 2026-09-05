# DEVIATIONS — `PREREG_flap_a_invariance_v1.md`

Disclosed per §1.2 / §5 of the frozen spec. Each entry: what changed, why, and what it costs.

---

## D1 — `D_int` VOIDed by its own PC-dep-NEG control; replaced by the centred form

**Detected:** validation run, `n = 20000`, `B = 999` (see D2).

**What fired.** PC-dep-NEG plants the *same* `θ` in every `a` (`h = K`), so the across-`a`
dispersion is zero by construction and the statistic must stay silent. It did not:

```
PC-dep-NEG (h=K, common shift)   D_int rank=0 -> FIRES   [must NOT fire]
```

**Cause — an error inside the frozen spec, not in the implementation.** §1.1 defines

```
D_int = Σ_a ( n·FF_a − rowF_a·colF_a )²
```

and asserts it "is a monotone transform of Cochran's `Q` on the log-odds." **It is not.** Cochran's
`Q` is a *centred* sum of squares; the expression above is *uncentred*. It therefore measures total
deviation magnitude, and a shift common to all `a` inflates it without any heterogeneity being
present. This is precisely the proxy-reported-as-object failure PC-dep-NEG was written to catch, and
the spec's own pre-committed rule applies:

> **PC-dep-NEG** | `D_int` fires at `h = K` | **VOID.** `D_int` is reading a common mean shift, i.e.
> a **proxy** for the intended object. Replace the statistic and re-register.

**Replacement (this file is the re-registration of the statistic only; every other element of the
frozen spec — object, nulls, plants, power, scope, falsification, outcome table — is unchanged).**
Exact integers, kept integral by scaling with `K`:

```
D_cen = K·Σ_a dev_a²  −  (Σ_a dev_a)²        ==  K² · (centred sum of squares)
M_cen = max_a | K·dev_a − Σ_a dev_a |        ==  K  · max_a |dev_a − mean|
```

`θ̄` (the pooled-mean companion, `|Σ_a dev_a|`) stays **uncentred** — it is a mean statistic and per
PC-dep-NEG it *must* fire under a common shift. The three-cell family and `α* = 1/60` are unchanged.

**Cost.** `D_cen` has `K−1 = 31` effective degrees of freedom rather than `K = 32`; the §5 power
numbers shift by `√(32/31) = 1.6%`, i.e. `τ_min` `4.6·10⁻³ → 4.7·10⁻³`. Recorded, not material.

**What this does NOT change.** No hypothesis, no null, no scope, no falsification condition. The
prior single-`a` T1 result is untouched.

---

## D2 — validation run at `n = 20000`, `B = 999` was seen; declared EXPLORATORY

To detect D1 the pipeline had to be executed. The run used `n = 20000, B = 999` — **not** the
pre-committed confirmatory allocation (`n = 10⁶`, `B = 9999`, §5). Everything observed in it is
hereby declared **exploratory and in-sample**, and may not be cited as a confirmatory result:

- gates G2/G3/G5/G6, PC-max, PC-id all passed (0 exceptions); PC-dep-arith fired; PC-FP = 3/100;
- the observed `θ_a` summary at that `n` (`mean −0.0034`, `sd 0.0365`, range `[−0.069, +0.056]`);
- the VOIDed `D_int` cells.

**The confirmatory arm remains `n = 10⁶`, `B = 9999`, run with `D_cen`/`M_cen`, and its outcome table
is the one frozen in §8.** Because `n = 20000` and `n = 10⁶` draw from the same pool seed
(`SEED_POOL = 424242`), the confirmatory pool *contains* the validation pool as a prefix; this is
disclosed rather than reseeded, so that the `a`-sample hash and the §6.2 fixed parameters stay as
frozen. The effect is that ~2% of the confirmatory pool has been seen through a VOIDed statistic.

---

## D3 — ARM-0 recorded the signed/absolute classifier densities (as §0.1 required)

Confirmed on `2¹²` gate abscissas × 32 values of `a`: absolute-value form mean density
**0.24957**, signed form mean density **0.12549**. This settles §0.1: the completed run
(`flap_grouplaw_run_v1.out`, density `16273/65536 = 0.2483`) used the **absolute-value** form, which
is what `flap_grouplaw_transition_v1.py:47` implements and what this experiment tests. The
divergence from `PREREG_flap_grouplaw_transition_v1.md` §0 (which specifies the signed form) is a
pre-existing deviation **of that spec**, now measured rather than inferred.

---

## D4 — ARM-0 gate pool `n_g = 2¹²`, not `2¹⁶`

**Spec (§4 G2/G3):** `n_g = 2¹⁶ = 65536`. **Taken:** `n_g = 4096`, applied to **all** `K = 32` values
of `a` (131072 `μ₆`-invariance checks, 0 exceptions). Reason: cost; the gate is detector sanity, not a
confirmatory statistic. **Cost:** the G3 quarter-density band `|4·nf − n_g| ≤ 6·isqrt(3·n_g)` is
looser in absolute terms than intended. G2 is a zero-exception identity, so the smaller pool reduces
coverage, not kind.

---

## D5 — `check_no_float.sh` does **not** pass on `flap_a_invariance_v1.py`

**Spec (§4 G1):** *"`check_no_float.sh` passes"* — written as a hard, unconditional gate.
**It does not pass.** Flagged: lines 172, 238, 240, 241. Each inspected individually:

- **line 172** — a `print` of the mean gate density. The G3 **decision** is line 169,
  `abs(4*nf − ng) > 6*isqrt(3*ng)`, pure integer. The float appears only in the displayed number.
- **lines 238/240/241** — `θ_a = log(CC·FF/(CF·FC))`, `τ̂`, and their mean/SD: **exactly** the
  quantities §9 declares as the named float carve-out.

Every flagged line lies inside the pre-declared carve-out and **none is in a decision path**. The
primary and secondary decisions (`D_cen`, `M_cen`, the `θ̄` integer companion, every permutation rank,
`fires()`) are integer throughout, with `fires()` comparing `(1+rank)·60 ≤ (B+1)` by integer
cross-multiplication.

**Recorded as a deviation rather than as a pass**, because the spec wrote G1 unconditionally and the
tool reports FAIL. For contrast, `kden_ramanujan_comb_v1.py` passes the same check clean (`OK`).

---

## D6 — PC-dep-α power sweep run at `B = 999`

**Spec (§4.2/§5):** `B = 9999`. **Taken:** `B = 999` for the PC-dep-α sweep **only**; the
confirmatory arm (`D_cen`, `M_cen`, `θ̄`) used the full `B = 9999`. With `B = 999` the minimum
attainable `p` is `1/1000 < α* = 1/60`, so **no firing decision changes**. Reason: the sweep is
`3 h-values × ≤10 α × 100 reps` ranked evaluations; a 10× larger ensemble changes cost, not decisions.

---

## D7 — Arms NOT run (disclosed, not silently filtered)

- **Null-I cross-check** (§2, §5): `K_I = 4` disjoint pools at `n = 10⁷`. **Not run** (≈ 1 h,
  dominated by `2·10⁷` QR modexps). **Consequence, material:** the shared-pool caveat on `θ̄` (§1.4)
  is **not discharged**. The confirmatory null rests on Null-P alone, and the outcome-table row
  *"Agreement ⇒ the shared-pool coupling is not driving Null-P"* was never tested. Any `θ̄` bound
  must carry this.
- **§1.5 EXPLORATORY stratification** of `θ_a` by `enorm(eis_p(a))` deciles / orbit-minimal
  bit-length: **not run**; **G7** (stratifier `μ₆`-invariance) consequently not run, as it gates only
  those stratifiers.
- **Reference panel** (§6.1, `a ∈ {1,2,3,ρ,β,ρ+1,a₀}`): **not run.** The prior completed run's `a₀` is
  therefore not placed against the confirmatory `θ_a` distribution.

---

## Not deviations (recorded to prevent later drift)

`K = 32`, `n = 10⁶`, `B = 9999`, `α* = 1/60`, `SEED_A = 20260723`, `SEED_POOL = 424242`, the
`bit_length ≥ 200` filter, `μ₆`-orbit distinctness (G6), and `A_plant` = first `K/4` entries of the
hashed `a_sample_v1.txt` — all as frozen. `a_sample_v1.txt` was written and SHA-256'd
(`fdadbe8c…c908e6`) **before** the pool was generated.
