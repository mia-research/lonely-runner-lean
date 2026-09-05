# Larger primes on the `I` lens, and arrangement correlations — the semicircle null's blind side

**Date:** 2026-07-30. Scripts: `phase_family_scan_v1.py` (`--fams I`), `arrangement_correlation_v1.py`.
**Grade: `[EXPLORATORY — EMPIRICAL, scoped]`.** ⚠ same user-authorised gate relaxation.

---

## 1. Task 1 — the `I` (inverse-phase) lens at larger `p`: power confirmed, result still null

Prediction from `RESULT_phase_family_and_tail_v1.md` §4: null grows `≈ 4 ln n`, a matched plant grows
`≈ 0.64n`, so **sensitivity improves with `p`** and the efficient move is bigger primes, not more.

| p | N | R(0) pctile | data max `k≠0` | null mean/max | ge | plant 1.0 | **floor** |
|---|---|---|---|---|---|---|---|
| 823 | 829 | 0.00 % | 20.11 | 21.86 / — | 5/6 | 14.3× | 0.5 |
| 1303 | 1249 | 0.00 % | 21.07 | 21.55 / — | 3/6 | 20.2× | 0.5 |
| **4831** | 4903 | 0.00 % | 26.28 | 28.72 / 32.85 | 4/6 | **56.9×** | **0.25** |
| **6199** | 6043 | 0.00 % | 30.74 | 29.96 / 34.17 | 2/6 | 40.6× | **0.25** |
| **8191** | 8011 | 0.00 % | 28.70 | 29.83 / 32.33 | 5/6 | **92.7×** | 0.5 |

- **Power confirmed as predicted:** detection floor `1.0 → 0.5 → 0.25`; full-plant ratio 14× → 93×.
- **Still NULL.** Data max at or below the null mean at 4 of 5; `ge` uniform.
- **The `k=0` dark fringe persists at 0.00 % up to `p = 8191`** — every one of the `N−1` other
  inverse-phase rates is brighter than the linear one. Consistent with it being the `2√p` cap.
- **Scope, tightened:** a single-cell inverse-phase component aligned at **≳25 %** of the matched-odd
  optimum would have been detected at `p ∈ [4831, 6199]`. Below that, still blind.

## 2. Task 2 — arrangement correlations (the semicircle null's explicit blind side)

The semicircle null bounds the `|V|` **marginal** and is silent on correlations that leave every order
statistic intact. The mirror-image null is the class permutation, which preserves the `|V|` multiset
**exactly** and destroys only arrangement. Statistic: `C(σ) = corr(u(a), u(σ(a)))`.

**Which maps are forced, stated before running:**
- `σ(a) = a+b` (translations) — **FORCED**: `Σ_a V(a)V̄(a+b) = n(nδ_b−1)` is curve-independent, so
  `Σ_a u(a)u(a+b) = n(nδ_b−1)/(4p)`. Diagnostic only.
- `σ(a) = λa` — the Wiener–Khinchin dual of the multiplicative spectrum, already tested null.
  Diagnostic only.
- `σ(a) = a⁻¹, a², a³` — neither additive nor multiplicative translations. **Intended as the live tests.**

**Pooled over 9 primes (823 … 4831), R = 200:**

| map | class | pooled z | signs | max\|z\| |
|---|---|---|---|---|
| `a+1` | diag (forced) | +0.02 | 4/9 | 0.06 |
| `2a` | diag (dual) | −1.08 | 2/9 | 1.63 |
| **`a⁻¹`** | **live** | **+1.48** | 7/9 | 1.27 |
| `a²` | *(see §3)* | −0.02 | 2/9 | **0.02** |
| **`a³`** | **live** | **+0.06** | 5/9 | 1.88 |

**NULL** on both live maps. Nothing reaches `|z| = 2` pooled.

## 3. ★ `a²` was a MIS-SPECIFIED test — forced to exactly zero, and the cause is the recurring one

`C(a²)` returned **−0.00000 with null sd 0.00000** — data *and* null identically zero, to machine
precision, at every prime. Not a null measurement; a **forced identity**:

> `u` is ODD (`u(−a) = −u(a)`) and `a ↦ a²` is EVEN (`(−a)² = a²`). Pairing `a` with `−a`:
> `u(a)u(a²) + u(−a)u(a²) = u(a)u(a²) − u(a)u(a²) = 0`. **Every even index map annihilates
> identically against an odd readout.**

⇒ **Correction to §2's classification: only ODD index maps carry non-forced arrangement information.**
`a⁻¹` and `a³` are odd and were genuine tests; `a²` never was.

**★ This is the THIRD time this session that the forced oddness of the readout has decided what is
measurable**, always by the same even/odd annihilation:
1. the quadratic chirp — an odd `±1` sequence cannot track an even phase, capping alignment at
   `≈0.16n` (`RESULT_chirp_hologram_plane_v1.md` §5);
2. the phase-family selection rule — odd phase **and** a bijection (`RESULT_phase_family_and_tail_v1.md` §2);
3. `a²` here.

**Standing rule for this object: check the parity of any proposed probe against the oddness of `u`
before running it. Even ⇒ forced zero ⇒ zero information.** Costs nothing to check, and has now
silently mis-specified three probes.

## 4. Scope

- **NULL** for the `I` lens at `p ≤ 8191` down to 25 % alignment, and for odd-map arrangement
  correlations at 9 primes. Bounded magnitudes, **not closures**.
- **Untested:** alignment below 25 %; multi-cell / distributed phase structure; odd maps beyond
  `a⁻¹, a³`; and the joint of arrangement × marginal (each null is blind to what the other tests, so
  neither bounds a structure that trades between them).
