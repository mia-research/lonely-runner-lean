# NOTE — E3 splits exactly into an even and a CHIRALITY component; 89.3% of the real reject is chirality, and BOTH documents used to bound E3 measured the other 10.7%

**Date:** 2026-09-01. **Register:** diagnostic NOTE, not a verdict. **Scripts:**
`scratchpad/e3_parity/e3_even_odd_null_v1.py` (+ `.json`, `run_v1.log`). Exact integer arithmetic; the
only floats are display percentiles.
**⚠ POST-HOC.** The percentiles in §3 were computed *after* seeing the real data's decomposition. They
are a **diagnostic**, not a test. **No grade moves on this NOTE.** A `experiment-designer` prereg + OOS
is owed before the chirality statistic can carry any grade (CLAUDE.md §2).
**§1–§2 are exact algebra and documentary fact, and are NOT post-hoc.**

---

## 1. The exact decomposition `[PROVED — integer identity]`

From `e3_owed_measurement_v1.py :: stats3` verbatim, with `(a,b,c)` the cube-class counts of the
`T = C(82,2) = 3321` pairwise field differences and `A3 = a−c`, `B3 = b−c`:

> `E3 = A3² − A3·B3 + B3²`  (the Eisenstein norm form `N(A3 + B3·ω)`)

which splits **exactly** and orthogonally as

> **`E3 = ¼·(2A3 − B3)² + ¾·(B3)²  =  ¼·EVEN² + ¾·ODD²`**
> `EVEN := 2A3 − B3 = 2a − b − c = 1ᵀC1`  — fixed by the swap `ω ↔ ω²`
> `ODD  := B3 = b − c`                     — **negated** by `ω ↔ ω²` (**chirality**: the Galois swap of
> the two primes above 3 in `ℤ[ω]`, i.e. `χ₃ ↔ χ̄₃`)

*Terminology guard: this `ODD` is **not** the record's "orientation-odd" (`PREREG_diffset_cubic_v1` §
Subspace caveat: the `i↔j` swap / S_diff's channel, genuinely absent since `χ₃(−1)=1`). It is a
different, previously unnamed splitting **inside** E3.*

**On the three measured objects (exact, verified):**

| object | `(a,b,c)` | `EVEN` | `ODD` | `E3` | EVEN share | ODD share |
|---|---|---|---|---|---|---|
| **secp field-difference** (the reject) | 1082, 1057, 1182 | **−75** | **−125** | 13125 | **10.7 %** | **89.3 %** |
| secp group-law (the null arm) | 1093, 1110, 1118 | −42 | −8 | 489 | **90.2 %** | 9.8 % |
| non-CM `E′`, same prime `P` | — | ±12 | ±70 | 3711 | 1.0 % | 99.0 % |

## 2. Both documents used to bound E3 measured `EVEN` `[VERIFIED — documentary + arithmetic]`

**(a) `RESULT_spectral_decomp_v1.md` states a false identity.** It asserts

> *"**Identity:** `E₃ = ¼|1ᵀC1|²` — E3 is the all-ones projection of `C`."*

`spectral_decomp_meta_v1.json` records `allones = 0.9146341463414683`, which is **exactly `75/82`** ⇒ its
`|1ᵀC1| = 75 = |EVEN|`. So `¼|1ᵀC1|² = 1406.25`, **not** `13125`. **The all-ones projection is `¼EVEN²`
— 10.7 % of E3 — not E3.**

Its measurements are correct and reproduce here (§3): all-ones at the **65.1st** percentile of its own
null; I get `EVEN` at the **64.0th** of a different null. What does not follow is its conclusion —

> *"E3's secp anomaly was a marginal phenomenon, not coherent; the diffset avenue on this surface is
> bounded at the spectral level."*

That conclusion is drawn from the component carrying **10.7 %** of the anomaly. The other **89.3 %** was
never spectrally tested. (Its `σ_max` arm is a separate, genuine bound, but at resolution `k ≥ 20`
= 24 % of the key set, `p = 0.131`, FAIL-TO-REJECT — not a null.)

**(b) The group-law arm probes the near-orthogonal direction.** `RESULT_grouplaw_e3_real82_v1` was
pre-registered predicting the group-law object would *"fire harder … because the group law is where CM
acts."* It came back `E3_gl = 489`, 13.03rd pctile, `p = 0.26`. But it is **90.2 % EVEN**, while the
field-difference reject is **89.3 % ODD**. The two arms are **not measuring the same channel**, so the
group-law null is **not** evidence against the field-difference reject. The failed prediction is
evidence about the *mechanism* (the CM-native operation does not carry it in the EVEN direction), not
about the reject.

## 3. Diagnostic percentiles against the FROZEN structural null `[POST-HOC — no grade]`

The null is regenerated from the original frozen seed `20260818` with the identical `rand_curve_x` RNG
stream, so set `i` here is set `i` of the 20 000-set frozen run. (`qr_bit` is skipped: `cube_marginals`
sums over the QR bit and consumes no RNG, so the sets are bit-identical.) `N = 2000` subsample:

| statistic | real | null median | percentile | one-sided `p` |
|---|---|---|---|---|
| `E3` (validation) | 13125 | 2217 | 97.8 | 0.022 |
| `EVEN = |2a−b−c|` | 75 | 54 | **64.0** | **0.36** |
| **`ODD = |b−c|`** | **125** | **32** | **99.3** | **0.007** |

- **Validation passes:** `E3` reproduces the frozen run (97.8 vs 98.24 at `N=20000`; two-sided
  `p = 0.0354` vs one-sided 0.022 here). `EVEN` at 64.0 independently reproduces the spectral
  document's 65.1 from a different null.
- **The chirality component is sharper than `E3` itself** (`p = 0.007` vs `0.022`): pooling it with a
  null `EVEN` term dilutes it. Real `|b−c| = 125` against a null median of **32**.
- Full `N = 20000` confirmation run in flight (`run_v2_N20000.log`).

**Multiplicity, stated plainly:** `ODD` was selected after seeing the 89/11 split. A minimum ×2
selection correction gives `p ≈ 0.014`; the honest correction must be re-derived over the whole
pre-registered family `{E2, E3, E6}` × `{EVEN, ODD}`, which has **not** been done here.

## 4. What this does and does not change

**Does:** (i) exhibits an exact orthogonal splitting of E3 nobody had written down; (ii) shows the two
documents that bounded/deflated E3 both measured the 10.7 % component — one via a **false stated
identity**, one via a near-orthogonal object; (iii) supplies exactly the *"more resolution from the same
82 keys"* that `RESULT_e3_owed_measurement_v1.md` §4 named as the only way past the `N=82` power ceiling
— and a **sharper** statistic than the two probes it named (group-law, triples).

**Does not:** move any grade; establish the chirality reject (post-hoc, uncorrected); say anything about
keyspace, extractability, or the DLP. E3 remains a set-statistic on a fixed 82-key public set.

## 5. Owed

1. **`experiment-designer` prereg** for the chirality statistic `|b−c|` — pre-committed decision rule,
   the corrected family-wise scheme over `{E2,E3,E6} × {EVEN,ODD}`, a firing control (plant in the
   `b−c` direction specifically), and the band-matched known-MT OOS arm (`q_MT` for `ODD`).
2. **Re-run the CM contrast on the chirality component**: secp `|b−c| = 125` vs non-CM `E′` `|b−c| = 70`
   at the same prime — the CM-mediation claim should be re-tested on the component that carries the
   effect, not on the pooled statistic.
3. **`RESULT_spectral_decomp_v1.md` needs a correction header** — the §Object identity is false and its
   headline conclusion's scope must be restated as bounding the EVEN/all-ones mode only.
4. Re-run the group-law arm's interpretation in `POSITIVE_FINDINGS_MASTER_v14.md` Part V §2: "the
   CM-native marginal channel does not reject" should read "does not reject **in the EVEN direction**,
   which is 90 % of that object and 11 % of the field-difference object."

*No ECDLP content. No keyspace claim. Exact arithmetic.*
