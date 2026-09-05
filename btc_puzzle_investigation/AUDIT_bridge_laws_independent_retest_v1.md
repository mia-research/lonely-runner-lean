# AUDIT — independent-sample retest of the bridge laws, and resolution of the `P(s=0)` flag

**Date:** 2026-07-24 · Audits `RESULT_bridge_mechanism_and_constant_v1.md` §3–§4 and its
`DEVIATIONS` items 1 and 3. Script: `scratchpad/audit_retest_v1.py`. Exact integers only.

**Why this audit was owed.** (E1)–(E4) were found *after* seeing the empty joint cells and were
confirmed **on the sample that suggested them** — the result file said so and flagged the debt. A
second flag was a `P(s=0)` deficit running below `1/3` in both discovery samples (`z = −1.92`
combined), which would, if real, have invalidated the `5/9` constant.

## 1. Independence of the audit sample

| | discovery | **audit** |
|---|---|---|
| seed | `4096` / `1729` | **different** |
| `p` size | 26-bit | **32-bit** |
| draws per `p` | all valid twists | **one twist per `p`, chosen uniformly** |
| `N` | 12000 | **40000** |

The one-twist-per-`p` design makes draws independent across `p`, which was the suspected cause of the
deficit. (Observed: `37390` primes yielded 1 valid twist, `2610` yielded 2 — so the discovery samples
carried at most 2 correlated draws per `p`, not 4.)

## 2. Result — every law replicates

| law | violations |
|---|---|
| **(E1)** `e(ν′)+e(π̄′) ≢ 2 (mod 3)` | **0 / 40000** |
| **(E2)** `s=0 ⟺ e(ν′)+e(π̄′) ≡ 1 (mod 3)` | **0 / 40000** |
| **(E3)** `e(π̄′)−e(ν′) ≡ (t−1)/3 (mod 3)` | **0 / 40000** |
| **(E3b)** primarizing unit sign `= +1` always | **0 / 40000** |
| **(E4)** `c₃=0 ⟺ (s=0 or 9 ∣ t−1)` | **0 / 40000** |
| **(E5)** `c₃ ≡ s·(t−1)/3 (mod 3)` (closed form) | **0 / 40000** |

> **The post-hoc debt from `DEVIATIONS` item 1 is discharged.** (E1)–(E5) are now verified on a sample
> independent of the one that produced them, at a different scale and with independent draws.
> Grade moves to `[VERIFIED — 0 violations / 52000 across two independent samples, 26- and 32-bit p]`.
> They remain **verified, not proved**: the derivation sketch from `μ(λ)=A+B`, `e=(μ+1)/3` and
> `μ(π̄′)−μ(ν′)=μ(u(t−1))` with `3∣t−1` is still **not completed**.

## 3. The `P(s=0)` flag — did not replicate, and reversed sign

| sample | `P(s=0)` | `z` vs `1/3` |
|---|---|---|
| discovery A (`N=20000`, all twists) | `0.3301` | `−0.98` |
| discovery B (`N=12000`, all twists) | `0.3253` | `−1.70` |
| **audit (`N=40000`, one twist/`p`)** | **`0.3385`** | **`+2.18`** |

The deficit **reversed direction**. Pooled over all three: `24044/72000 = 0.3339`, `z = +0.35`.

> **The flagged systematic is not supported.** Whether the discovery-sample deficit was correlated-twist
> structure or ordinary fluctuation is **not determined** by this audit — only that it does not
> replicate and does not persist in sign.

**Consequences for the constant:**

| quantity | audit sample | pooled |
|---|---|---|
| `P(c₃=0)` vs `5/9 = 0.5556` | `0.5594`, `z=+1.55` | `40010/72000 = 0.5557`, `z = +0.08` |
| association ratio vs `5/3 = 1.6667` | `1.6729` | — |
| `{s=0} ⊥ {9∣t−1}` | `(T,T) = 4547` vs `4530.1` expected | — |

> **`P(c₃=0) = 5/9` and ratio `5/3` move from `[CONSISTENT, not verified]` to `[VERIFIED]`**, on the
> pooled evidence (`z = +0.08`) plus the independent sample (`z = +1.55`).
>
> **With one caveat kept explicit.** `5/9` follows from (E4) **only if** `P(s=0) = P(9∣t−1) = 1/3`.
> (E4) itself and the independence of the two events are exact/verified, and plugging the *measured*
> rates into inclusion–exclusion reproduces the observation almost exactly
> (`0.3385 + 0.3346 − 0.3385·0.3346 = 0.5598` vs observed `0.5594`). But **uniformity of `s` over all
> three classes is still not established**: the audit sample gives `13539/13097/13364`,
> `χ² = 7.43` on 2 df (`p ≈ 0.024`). That mild deviation is unexplained. So the *structure* (E4 +
> independence) is the verified object; `5/9` is the value it takes **when `s` and `9∣t−1` are
> equidistributed**, which is consistent but not itself pinned down.

## 3b. Machinery controls re-run at scale (closes `DEVIATIONS` item 6)

The `ℤ[ω]` controls had only ever been run at 8–18 bit `p`, and the later arms imported the machinery
by `exec` without re-running them. Re-run at **32-bit `p`**:

| control | result |
|---|---|
| **K0** Eisenstein cubic reciprocity `χ_ν(π̄′) = χ_π̄(ν′)` | **1500/1500 PASS** |
| **K1** Gauss `2` cubic residue mod `n` ⟺ `n = a²+27b²` | **400/400 PASS** |
| **K3** `ω²+ω+1 ≡ 0` in both fields | **1500/1500 PASS** |

`DEVIATIONS` item 6 (imported machinery unvalidated at the scales actually used) is **discharged**.

## 4. Net

- Laws (E1)–(E5): **replicated independently**, debt discharged, still verified-not-proved.
- `5/9` / `5/3`: **upgraded to `[VERIFIED]`**, with the `s`-uniformity caveat stated above.
- `P(s=0)` systematic: **withdrawn** as unsupported; `s`-uniformity itself remains open
  (`χ² = 7.43`, 2 df, unexplained).
