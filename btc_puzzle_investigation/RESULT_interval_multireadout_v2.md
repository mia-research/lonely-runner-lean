# RESULT — interval confinement, extended: larger `M`, group-law difference, and a readout axis that turned out void

**Executes:** the three extensions to `PREREG_interval_cubic_structure_v1.md` (freeze SHA-256
`8bea62ab67857b0b7aafecac139e8e3fa1f8477bd0442f261ead94193cb4045d`) agreed 2026-07-31.
**Scripts:** `interval_multireadout_v3.py`, `oos_group_retest_v1.py`. **Log:** `run_multireadout_v3b.log`.

> `[EXPLORATORY — user-authorised gate relaxation]`. No `experiment-designer` sign-off.
> **No grade moves on any number here.**

**Constructed scalars only. No puzzle keys. No generator pool.**

---

## 1. Headline

> **`[EMPIRICAL — bounded magnitude, powered, controls fire, OOS-retested]`**
> Confining `d` to `[2^{k−1}, 2^k)` produces **no cubic-class concentration** in either the
> **field** difference `x_i − x_j` (above a **≈1.4%** single-class excess, `M = 400`) or the
> **group-law** difference `x(P_i − P_j)` (above **≈4.3%**, `M = 160`), at
> `k ∈ {40, 64, 96, 128, 135, 160, 200}`, `R = 3000`, at secp256k1's own `p`.

The `M = 400` field bound **tightens `RESULT_interval_cubic_structure_v1.md`'s 7.7% by ~5×**.

## 2. Field difference — all null (`M = 400`, `C(400,2) = 79,800` pairs)

Null `E₃`: median 49683, 95th 209232, **99th 332553**.
Controls: **C-PLANT** `E₃ = 3184023` (100.0) **FIRES**; **C-GLV** `E₃ = 0` **exact**;
**C-NEG** `E₃ = 56343` (54.0) quiet.

| `k` | 40 | 64 | 96 | 128 | **135** | 160 | 200 |
|---|---|---|---|---|---|---|---|
| `E₃` | 27567 | 134679 | 159213 | 18369 | 69357 | 114624 | 62247 |
| pctile | 31.7 | 85.7 | 89.7 | 22.6 | **61.9** | 80.1 | 58.1 |

**No arm reaches the 95th.** MDE: `E₃ = 9δ²/4` at 79800 pairs ⇒ firing needs `δ ≈ 384` on an
expected 26600 per class = **≈1.4% excess**.

## 3. Group-law difference — one in-sample fire, **killed out-of-sample**

`M = 160`. Null `E₃`: median 11388, 95th 46731, **99th 71307**.
Controls: **C-PLANT** (100.0) FIRES; **C-GLV** `E₃ = 0` **and** `E₆ = 0` exact; **C-NEG** `E₃` 38.5 quiet.

| `k` | 40 | 64 | 96 | **128** | 135 | 160 | 200 |
|---|---|---|---|---|---|---|---|
| pctile | 8.3 | 42.7 | 23.1 | **99.4 → FIRE** | 9.4 | 37.3 | 2.6 |

**`k = 128` fired the pre-committed rule. It is not a finding.**

1. **Family-wise, it is unremarkable.** 7 arms at a 99th-percentile threshold give
   `1 − 0.99⁷ ≈ 6.8%` chance of ≥1 fire. The prereg stated this and declined to correct it.
2. **OOS retest, 5 fresh seeds (pool AND arms fresh), `oos_group_retest_v1.py`:**

| seed | 11 | 22 | 33 | 44 | 55 |
|---|---|---|---|---|---|
| `k=128` pctile | 1.6 | 27.5 | 41.9 | 55.5 | 8.5 |

> **`k=128` fires 0/5. Every arm fires 0/5.** The candidate is dead. **Fifth chance pattern
> killed by the pre-committed OOS rule** (after `k=t`, `p=2731` multiplicativity, `max|u|`, `S3_max`).

MDE at `M = 160` (12720 pairs): `δ ≈ 178` on 4240 expected = **≈4.3% excess**.

## 4. ★ Axis 2 (`χ₂`, `χ₆`) — void on ONE object, valid on the OTHER

Full argument: `ANALYSIS_diffset_readout_parity_void_v1.md`.

- **Field difference: `χ₂` and `χ₆` are structurally unusable.** `x_i − x_j` and `x_j − x_i` differ
  by sign; for `χ(−1) = −1` the symmetrized sum vanishes identically and the unordered version
  depends on index order. Only `χ₃` (even, `χ₃(−1) = +1`) is well-posed. **Among characters of
  order dividing 6, `χ₃` is the only nontrivial readout available on a field difference set.**
- **Group-law difference: the void does NOT apply.** `x(P_j − P_i) = x(−(P_i − P_j)) = x(P_i − P_j)`
  — negation preserves `x`, so each unordered pair yields **one canonical** value and `χ₂`, `χ₆`
  are well-posed. *(This corrects the blanket `[parity-void]` tags printed on the group arm.)*

**The C-GLV control separates the two objects exactly:**

| | field | group |
|---|---|---|
| `E₃` | 0 exact | 0 exact |
| `E₆` | **292** — β-closure broken by unordered pairing | **0 exact** — closure intact |

Same `β`, same code, different object, behaving precisely as the parity argument requires.

**★ The parity analysis prevented a false positive in this very run.** On the field arm, `k=200`
gave `E₆ = 536493` against an `E₆` 99th of 353761 — it would have printed **FIRE**. It is an
index-order artifact of pairing an odd character with a negation-closed set, not a signal.
`E₂` at `k=160` (226576) is the same. Had `E₆` not been tagged void beforehand, this run would
have reported a spurious hit at the field arm.

## 5. ★★ AUDIT — a control defect running through EVERY result in this line

**`C-NEG` as specified is ONE draw tested against the 95th percentile. Under a perfectly correct
null that fails 5% of the time by construction.** It is a false-alarm generator, and it is used
in `RESULT_interval_cubic_structure_v1.md`, in §2/§3 above, and in the spectral run of §7.

**Demonstrated.** The spectral run (§7) voided on `C-NEG = 96.0 pctile`. Re-specified as **20
independent full-range draws**, the same null gives **0/20 above the 95th** (min 2.8, median 70.5,
max 91.5). **The void was the control misfiring, not the null.** A single draw cannot distinguish
a 1-in-20 event from a defect.

> **Repair, required for any future run in this line:** `C-NEG` must be `n ≥ 20` independent draws
> with their percentiles checked for uniformity — not one draw against a quantile.

**Consequence for §2/§3 above: none of the verdicts change.** Every `C-NEG` there passed, and a
control that errs toward false *alarms* cannot manufacture a false *pass*. The arms were read only
where the control passed, so the null verdicts stand.

**Consequence for the `E₆ = 65101` (99.7 pctile) flag raised on the group arm:** it is one draw of
six control readings taken across two arms × three statistics, so `P(≥1 above 99.7%) ≈ 1.8%` — the
same single-draw artifact class. **Still unresolved, and still blocking**: `E₆` on the group object
must not be used until re-calibrated with the `n ≥ 20` rule.

### 5a. The null construction itself was audited and PASSED

Suspecting that resampling `M` points from one fixed pool under-disperses the null (draws share
~36% of their points at `M=400`, `N_pool=1100`), the pool-subsample null was compared against a
**fresh-iid-points** null at `M = 150`:

| null | median | 95th | 99th |
|---|---|---|---|
| pool-subsample (n=600) | 7959 | 36651 | 50484 |
| **fresh points (n=150)** | 9093 | 33084 | **48657** |

Ratio of 99th percentiles **0.96**. **No material under-dispersion; the `E₃` nulls are sound.**
*(For `σ_max` the fresh draws sit mildly high — median percentile 70.5 over 20 draws — so the pool
null is slightly optimistic there. Not enough to fire at the 95th in 20 tries, but recorded.)*

## 6b. ★ SPECTRAL PUSH — `E₃` is a RANK-1 statistic, and the full spectrum is also null

`E₃ = ¼|1ᵀC1|²` is exactly the **all-ones projection** of `C_{ij} = χ₃(X_i − X_j)`. Bounding `E₃`
bounds **one mode**; coherent structure orthogonal to all-ones passes it untouched. *(§1's headline
and §2–§3 are therefore correctly scoped only by §6's "marginal cubic-class counts" line; read
that way, not as "no cubic structure".)*

`σ_max(C)`, `M = 400`, `R = 600`, gmpy2 exact class path, SVD as a **monotone statistic ranked
against a matched null** (the folder's float carve-out):

- **null**: median 39.546, 95th **40.045**, 99th **40.313** (Marchenko–Pastur `2√M = 40.0` ✓)
- **resolution**: a planted coherent block covering **6% of the set is RESOLVED** (99.8 pctile);
  4% is below the floor. **The record's `N = 82` run resolved only ≥24%** — a **4× improvement**,
  bought purely by constructed scalars.
- **C-NEG**: 0/20 above 95th (the repaired control) — **PASS**

| `k` | 40 | 64 | 96 | 128 | **135** | 160 | 200 |
|---|---|---|---|---|---|---|---|
| `σ_max` | 39.668 | 39.976 | 39.838 | 39.243 | 39.211 | 39.597 | 39.377 |
| pctile | 66.8 | 92.3 | 83.0 | 12.5 | **9.7** | 56.5 | 29.7 |

> **No arm reaches the 95th.** The difference-set channel is null across the **whole spectrum**,
> not merely in its rank-1 mode, down to a 6%-coherent-block resolution.

## 6. Scope — what is and is not bounded

**Bounded:** marginal cubic-class counts of the pairwise difference multiset, field and group-law,
at the stated MDEs and lengths.

**Not bounded, explicitly:** phase structure; orientation-odd channels; joint/triple objects;
oriented objects such as `x(P_i + P_j)` where `+` and `−` genuinely differ (**the correct way to
run a readout axis** — §4); `χ₂`/`χ₆` on the group arm (§5); non-uniform sampling within an
interval; intervals not of the form `[2^{k−1}, 2^k)`; and `M` beyond 400/160.

**`M` is bounded by compute, not by sample.** The detectable excess falls like `1/M`, and the
scalars are constructed, so `M = 2000` (≈0.3%) is a matter of CPU. This is the property no design
built on a fixed key set can have.

## 7. Cost note, recorded

`interval_multireadout_v2.py` recomputed every pairwise character on every null draw: ~60M modular
exponentiations at a **measured 84.7 µs** each — an 85-minute field pass, killed after 70 minutes
with no output (it was also piped through `tail`, which buffered everything). v3 precomputes one
pool-wide difference table (`C(N_pool,2)` exponentiations, 49s), after which the null **and** the
greedy plant are table lookups. Field pass: **114s**. Group pass: **28s**. The optimization had
been reasoned out earlier in the session and simply not implemented.
