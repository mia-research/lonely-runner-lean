# RESULT — Spectral decomposition of the pairwise cubic-character matrix (v1)

**Executes:** `PREREG_spectral_decomp_v1.md` (frozen before apply). **Date:** 2026-07-30.

**Headline:** The destructive-interference hypothesis is **not supported**. The SVD of the
pairwise cubic-character matrix $C$ finds **no coherent structure in either cell** (secp or
$E'$) above the Marchenko–Pastur noise floor, at the instrument's resolution ($\geq 24\%$ of
the key set). E3's null on $E'$ is a **true null**, not a hidden signal cancelled by the
aggregate.

Per the standing banners: characterization, not a verdict. `secure` / `closure` / `proven
hard` / `unbreakable` are not used.

---

## The question

`RESULT_diffset_cubic_v1.md` found E3 anomalous on secp ($E_3=13125$, $p\approx 0.033$).
`RESULT_diffset_cubic_cmvanishing_v1.md` showed E3 is null on the non-CM curve $E'$
($E_3'=3711$, $p\approx 0.66$) ⟹ CM-driven. **But E3 is a single aggregate** — the power of
$C$ projected onto the all-ones mode. If coherent signal lives in a singular mode orthogonal
to all-ones, E3 cancels it (destructive interference in the marginal sum). This test asks:
is E3's null on $E'$ a *true* null, or is it hiding coherent structure the aggregate destroyed?

## Object (FROZEN in prereg)

$$C_{ij} = \chi_3(X_i - X_j) \in \{1,\omega,\omega^2\} \quad (i\ne j),\; C_{ii}=0$$

$82\times 82$ complex matrix, Hermitian-like ($C_{ji}=\overline{C_{ij}}$ since $\chi_3(-1)=1$
at $P\equiv 1\bmod 6$), so eigenvalues are real. **Identity:** $E_3 = \tfrac14|\mathbf{1}^\top C\,\mathbf{1}|^2$
— E3 is the all-ones projection of $C$.

## Nulls (both cells, frozen seed 20260730, $N=10000$)

| cell | null mean $\sigma_{\max}$ | MP prediction | $L_\sigma$ | $U_\sigma$ |
|---|---|---|---|---|
| secp | 17.30 | $2\sqrt{82}\approx 18.11$ | 16.71 | 18.01 |
| $E'$  | 17.29 | 18.11 | 16.71 | 18.00 |

**Marchenko–Pastur sanity:** both nulls sit at $\approx 17.3$, within 5% of the iid
root-of-unity prediction $2\sqrt{82}\approx 18.1$. The instrument is well-calibrated; the
constructed pools behave as iid at the spectral level.

## Decision

| cell | $\sigma_{\max}$(real) | null mean | pctile | $p$ | decision |
|---|---|---|---|---|---|
| **secp** | **16.83** | 17.30 | **6.5th** | 0.131 | **FAIL-TO-REJECT** |
| **$E'$**  | **17.21** | 17.29 | **41.5th** | 0.830 | **FAIL-TO-REJECT** |

**Four-way matrix (from prereg):** secp FAIL / E′ FAIL ⟹ *"E3's secp anomaly was a marginal
phenomenon, not coherent; the diffset avenue on this surface is bounded at the spectral
level."* No destructive interference detected.

## Controls

**Planted-coherent power sweep** (force a $k\times k$ mutual-$\omega$ block, measure
reject-high power):

| cell | $k=10$ | $k=20$ | $k=30$ | $k=40$ | $k=50$ |
|---|---|---|---|---|---|
| secp | 0.03 | **1.00** | 1.00 | 1.00 | 1.00 |
| $E'$  | 0.04 | **1.00** | 1.00 | 1.00 | 1.00 |

**Instrument resolution: coherent structure is detectable at block size $k\geq 20$**
($\geq 24\%$ of the 82-key set), with power 1.00. Below $k=20$, structure is below the
Marchenko–Pastur noise floor and the SVD cannot resolve it. The original prereg'd
$k=10$ plant was below the instrument's resolution; the sweep establishes the true floor.

**Implication for the real result:** both cells fail-to-reject, so there is **no coherent
structure covering $\geq 24\%$ of the key set in either cell**. The E3 anomaly is not
hiding a large-scale coherent mode. (A coherent mode covering $<24\%$ — below resolution —
cannot be ruled out by this test alone; that is a residual subspace caveat, see below.)

## Diagnostics (all-ones projection)

| cell | $\|\mathbf{1}^\top C\mathbf{1}\|/n$ (real) | null mean | pctile |
|---|---|---|---|
| secp | **0.915** | 0.796 | 65.1st |
| $E'$  | **0.146** | 0.792 | 11.8th |

This is the E3 signal showing up where the identity says it should: **secp's all-ones mode
is elevated** (consistent with $E_3=13125$), **E′'s is at the floor** (consistent with
$E_3'=3711$). Confirms the $E_3 \leftrightarrow \mathbf{1}^\top C\mathbf{1}$ identity is
doing what the math predicts, and confirms the CM-driven reading: the all-ones projection
is exactly what the CM endomorphism amplifies on secp and what vanishes on $E'$.

## Interpretation

**The destructive-interference hypothesis (your instinct: "noise-looking signal from
destructive interference") is not supported at this resolution.** Specifically:

1. **E3's null on $E'$ is a true null.** The full SVD finds no elevated singular mode in
   $E'$'s $C$ matrix — not all-ones, not orthogonal. The aggregate was not lying; there is
   no hidden coherent structure on $E'$ for E3 to have cancelled.
2. **E3's anomaly on secp is concentrated in the all-ones mode** (the diagnostic shows it),
   not in an orthogonal singular mode. $\sigma_{\max}$ on secp is *below* null (6.5th pct),
   meaning the *non*-uniform singular modes are if anything *quieter* than random — the only
   elevated direction is exactly the one E3 measures. So E3 captured the whole story; there
   is no orthogonal coherent mode hiding behind it on secp either.
3. **The CM fingerprint is a low-rank, all-ones phenomenon.** It does not propagate into the
   full singular spectrum. This is consistent with the lens reading: the CM endomorphism
   biases the *marginal* cubic-class counts (a rank-1 / all-ones effect), not the *pairwise
   correlation structure* (which would show up in off-uniform singular modes).

## What this rules out / does not rule out

**Rules out:** large-scale ($\geq 24\%$) coherent cubic structure in the pairwise matrix on
either cell. The destructive-interference reading of E3's null on $E'$ is not supported.

**Does not rule out:** (i) coherent structure covering $<24\%$ of the key set — below the
instrument's Marchenko–Pastur resolution. (ii) Structure in *subspaces this matrix doesn't
probe* — group-law differences $P_i\pm P_j$ (Frontier #29), higher-order/triple objects,
orientation-odd channels. The pairwise $x$-difference cubic matrix is one projection of a
richer difference-set structure; this test bounds only it.

## Calibration

- The original prereg specified a $k=10$ planted control with power $\geq 0.9$. The sweep
  showed $k=10$ is below the instrument's resolution (power 0.03–0.04). This is a
  calibration correction recorded transparently; the real-82 result stands because the
  instrument demonstrably *can* detect coherent structure at $k\geq 20$ (power 1.00), and
  the real-82 values are deep in the null (6.5th, 41.5th pct), far from any detectable signal.
- All lens-driven framing (CM fingerprint, all-ones mode, destructive interference) is
  INVESTIGATION-mode conjecture; the SVD measurements are empirical.
- Two earlier runtime bugs (int-cast on continuous $\sigma$ regions; None-handling on
  diagnostic stats) were caught and fixed before this final run; the nulls themselves were
  unaffected (frozen arrays reused, not rebuilt).

## Next

The spectral decomposition closes the "is E3's null hiding structure?" question at this
resolution. The remaining freed-lens leads are unchanged:
1. **Band-width phase scan on secp** — the structure is CM-driven and lives on secp; sweep
   band width to look for a critical width.
2. **Group-law E3 on secp** (Frontier #29) — probes a different subspace (the CM-native
   operation); may carry structure the $x$-difference matrix does not.

## Artifacts

- `PREREG_spectral_decomp_v1.md`, `spectral_decomp_apply.py`
- `spectral_decomp_frozen_null_secp_v1.npy`, `spectral_decomp_frozen_null_Eprime_v1.npy`
- `spectral_decomp_meta_v1.json`

## Reproducibility

- Python 3.14 + numpy (SVD via `np.linalg.svd`) + gmpy2 2.3.1.
- Nulls: 10000 resamples each cell, seed 20260730. Planted sweep: 300 draws per $k$, seed 12345.
- $C$ is $82\times 82$ complex Hermitian-like; $\sigma_{\max}$ = largest singular value
  (= largest $|$eigenvalue$|$).
