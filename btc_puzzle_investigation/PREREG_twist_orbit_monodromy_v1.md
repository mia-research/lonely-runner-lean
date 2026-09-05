# PREREG — the 4th-order monodromy discriminator: is `E[u⁴] = 1/8` (full SU(2))?

*2026-07-26. **Written before any out-of-sample moment is examined.** Arms HELD pending
`experiment-designer` sign-off (CLAUDE.md §2b). Continuation of the twist-orbit track: the 2nd/3rd-order
arrangement is forced-or-null (`RESULT_twist_orbit_forced_landscape_v1.md`), so the first UNFORCED
higher object is the 4th moment — a symmetry-TYPE question. No leakage/ECDLP claim.*

## §0 — What is tested

`u(a) = V(a)/(2i√p) ∈ [−1,1]` (real; `V` purely imaginary). The record models `|V|/√p` as the trace of
a **2-dim SU(2)** object (the 120° lock collapses the 4-dim `H¹(A_new)` to effectively 2-dim), and the
forced `E[u²]=1/4` confirms that normalization. The monodromy GROUP of the `χ₂(y)⊗χ_a` family is read
from the higher even moments:

| monodromy | `E[u²]` | `E[u⁴]` | `E[u⁶]` |
|---|---|---|---|
| **full SU(2)** (Sato–Tate, `C_k/4^k`) | 1/4 | **1/8 = 0.125** | 5/64 = 0.0781 |
| torus-normalizer / CM (uniform angle, `binom(2k,k)/4^k`) | 1/2 | **3/8 = 0.375** | 5/16 = 0.3125 |

`E[u²]` is **FORCED** `= n/(4p)` (Parseval; instrument check, not evidence). `E[u⁴]` is the **first
unforced moment** and a **factor-3 discriminator** between the two monodromy types.

> **PRIMARY: the exact rational `E[u⁴](p) = n·Σ_j R(j)² / (16 p²(n−1))`**, `R(j)=Σ_k c_k c_{k+j}` the
> integer autocorrelation of the y-Legendre sequence `c_k=χ₂(y_{[k]G})`.
> **Pre-committed prediction: `E[u⁴](p)` within the iid-SU(2) finite-`L` band, centered on 1/8.**

**Exactness (folder OVERRIDE satisfied with zero signal-path float):** `E[u⁴]` is an exact rational —
`Σ_a|V(a)|⁴ = n·Σ_j R(j)²` (derivation: `|V(a)|²=Σ_j R(j)ζ_n^{aj}`, `Σ_a|V|⁴ = nΣ_j R(j)R(−j)`), all
integers. No FFT, no float in the statistic. The only float is the SU(2)/uniform **null simulation**
(the reference distribution, not the data).

## §1 — Assumption audit

| # | assumption | status |
|---|---|---|
| K1 | `u=V/(2i√p)` real, `\|u\|≤1` | `V` purely imaginary (forced); cap `\|V\|≤2√p` `[VERIFIED, 120 primes]` |
| K2 | `E[u²]=n/(4p)` FORCED | `Σ_a\|V\|²=n(n−1)` (Parseval); instrument check, **excluded from evidence** |
| K3 | `E[u⁴]` exact rational, `Σ_a\|V\|⁴=nΣR(j)²` | derived + verified (`monodromy_preview_v1.py`, 7 primes) |
| K4 | iid-SU(2) is the right null for the marginal | arrangement is NULL (`RESULT_twist_orbit_spectrum/magnitude`), so the `L` traces are ≈exchangeable ⇒ their moments match iid draws from the limiting law |
| K5 | full-SU(2) prediction is `E[u⁴]=1/8` for THIS 2-dim object | confirmed by the forced `E[u²]=1/4` (a 4-dim object would give `E[u²]≠1/4`) |
| K6 | finite-`p` deviation shrinks with `p` under SU(2); a true reduction is a constant offset | the discriminator for outcome (c) below (trend test) |

## §2 — Instrument / null

- **Signal path (exact int/Fraction, no float):** `c` (Legendre), `R(j)` (integer autocorrelation),
  `E[u⁴]=Fraction(n·ΣR², 16 p²(n−1))`, `E[u²]=Fraction(n,4p)`, `E[u⁶]` via `nΣ_{j₁,j₂}R(j₁)R(j₂)R(−j₁−j₂)`.
- **NULL (matched, simulation):** draw `L` iid `θ~`Sato–Tate `(2/π)sin²θ`, `u_i=cos θ_i`, form `Ê[u⁴]`;
  repeat `R_sim` → the iid-SU(2) band per `L`. The empirical **exact** `E[u⁴](p)` is placed in this band.
  A parallel **uniform-angle** simulation gives the CM/torus band (centered 3/8).

## §3 — Sample (REUSE frozen S)

Same `twist_orbit_spectrum_FREEZE_v2.json` (SHA `7cde99fe…`), 12 primes `p∈[823,2731]`, `p≡7 mod12`
(SIN — `u` well-defined). In-sample `{127,163,211,349,397,433,547}` reported separately (design preview,
already seen). **The moment object is disjoint from both prior channels** (it is the value distribution,
not the arrangement), so reuse of S is a new orthogonal read.

## §4 — Controls

| id | control | must produce |
|---|---|---|
| **PLANT-SU2** | feed `L` iid Sato–Tate `u` into the estimator | `E[u⁴]` inside the SU(2) band (~1/8) |
| **PLANT-UNIF** | feed `L` iid uniform-angle `u` | `E[u⁴]` at ~3/8, **outside** the SU(2) band (discriminator has power) |
| **C-FORCED** | `E[u²]=n/(4p)` exact | agreement; FORCED ⇒ instrument only |
| **C-CROSS** | `Σ_a\|V\|⁴` via exact `nΣR(j)²` vs a direct float FFT `Σ\|FFT(c)\|⁴` | agree to float precision |
| **C-NOFLOAT** | signal-path moment code exact (Fraction/int) | passes |

⚠ NOT a control: any leakage reading. This identifies a monodromy group; it says nothing about ECDLP.

## §5 — Pre-committed readings

| outcome | conclusion |
|---|---|
| `E[u⁴]` within the iid-SU(2) band at S, and the deviation from 1/8 shrinks with `p` | **full SU(2) monodromy** for the `χ₂(y)⊗χ_a` family `[EMPIRICAL — SEEN-DATA]`. Confirms the `A_new`-channel picture: the twist destroys absolute rigidity, angles equidistribute Sato–Tate. Symmetry type = SU(2). The twist-orbit value distribution is monodromy-generic |
| `E[u⁴]≈3/8` (uniform band) | **torus-normalizer / CM-reduced** monodromy — angles equidistribute UNIFORMLY, a genuinely different symmetry type. (Preview makes this unlikely, but it is the pre-committed alternative) |
| `E[u⁴]` **systematically below** the SU(2) band AND the deviation does NOT shrink with `p` | a **sub-SU(2)** deviation — name the candidate finite group from the `(E[u⁴],E[u⁶])` pair; flag a follow-up computing the theoretical finite-`p` SU(2) moment to separate reduction from a finite-`p` correction |
| PLANT-UNIF fails to separate | halt (discriminator underpowered at this `L`) |

**Falsification (once):** `E[u⁴]` outside the iid-SU(2) band at a majority of S primes refutes "full
SU(2)". Output = the identified monodromy type + moment sequence, never an avenue verdict
([[feedback_anomaly_drill_protocol_2026_07_17]]).

## §6 — Scope

`p∈[823,2731]`; the `χ₂(y)` 2-dim trace `u=V/(2i√p)`; even moments to 6th order. Identifies a symmetry
type; does not test arrangement (done), the cap, or leakage. secp scale out of reach.

## §7 — Status
**Arms HELD** pending sign-off. Deviations → `PREREG_twist_orbit_monodromy_v1_DEVIATIONS.md`.
