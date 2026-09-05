# PREREG — the MAGNITUDE channel: is `|V(a)|²` arranged with structure over `Q=(ℤ/n)^×/μ₆`?

*2026-07-26. **Written before the magnitude arrangement is examined out-of-sample.** Arms HELD pending
`experiment-designer` sign-off (CLAUDE.md §2b). Companion to `PREREG_twist_orbit_spectrum_v2.md` (the
SIGNED channel, null) — shares its validated machinery; only the NEW object is spelled out. No
leakage/ECDLP claim.*

## §0 — Why this is the one remaining free 2nd-order object

The signed test (odd chars on `V`) was null (`RESULT_twist_orbit_spectrum_v1.md`). The forced-object
sweep (`RESULT_twist_orbit_forced_landscape_v1.md`) then established, **exactly**, that the other
low-order arrangements are FORCED:

- **2-pt additive autocorrelation** `Σ_a V(a)V̄(a+b) = n(nδ_b−1)` (curve-independent; verified exact,
  5 primes) — the frame/Gram identity again.
- **3-pt multiplicative bispectrum ≡ 0**, forced by odd parity (`ρ̂` supported on odd chars, odd·odd =
  even ⇒ `ρ̂(χ₁χ₂)=0`; verified even-char mass `~1e-16`).
- **2-pt multiplicative autocorrelation** = Wiener–Khinchin dual of the (measured, null) signed power
  spectrum — not independent.

The lone **free** 2nd-order object is the arrangement of the **energy** `E(a)=|V(a)|²`. Because `|V|` is
`μ₆`-invariant, `E` is a well-defined function on the `L=(n−1)/6` classes; its spectrum lives on the
**even, `μ₃`-trivial** characters (`j≡0 mod 6`). The DC term (`j=0`) is the forced Parseval constant
`Σ_a|V(a)|²=n(n−1)` and is **EXCLUDED**. Preview (in-sample, design only): null-ish (perm-ranks
40–506/600) — this prereg gets the **out-of-sample** verdict.

> **PRIMARY.** `Tmag(p) = max_{j≡0 mod6, j≠0} |Ê(χ_j)|²`. **Pre-committed prediction: within the
> class-energy permutation band at every S prime.**

## §1 — Assumptions (only the deltas from v2)

| # | assumption | status |
|---|---|---|
| M1 | `E(a)=|V(a)|²` is `μ₆`-invariant ⇒ one value per class, spectrum on `j≡0 mod6` | forced (magnitude is `μ₆`-invariant even though signed `V` is not) |
| M2 | the arrangement of `E` (non-DC even chars) is **FREE**, not forced | preview: `Tmag` varies, permutation non-degenerate ⇒ free ✓ |
| M3 | DC `= n(n−1)` is forced and EXCLUDED | Parseval, verified |
| M4 | this channel is well-defined for **both** `p≡1` and `p≡7 mod12` (magnitude ignores the sign) | ⇒ unlike the signed channel, no COS/SIN restriction needed; **S is still `p≡7 mod12`** for comparability |

## §2 — Instrument / null (reuse v2 machinery)

- `E_c = |V(g^c)|²`, `c=0..L−1`, exact `V∈ℤ[ζ_n]` signal path; float only in the FFT statistic, ranked
  against the permutation null (`check_no_float.sh` OK on `twist_orbit_magnitude_run_v1.py`).
- **NULL:** permute the `L` class-energies (preserves the exact energy multiset = the magnitude
  marginal the record measured; destroys only arrangement). p-value = exact integer rank, `R=3000`.

## §3 — Sample (REUSE the frozen S)

Same `twist_orbit_spectrum_FREEZE_v2.json` (SHA `7cde99fe…`): the 12 out-of-sample primes
`p∈[823,2731]`, `p≡7 mod12`. No new freeze; the sample was fixed before either channel was read
out-of-sample. In-sample `{127,163,211,547}` (the SIN in-sample primes only) reported separately.

## §4 — Controls (validated in test-fires)

PLANT-POS (even admissible char at empirical scale) fires 6.5–9.3×; PLANT-NEG in-band; C-PARSEVAL
(`DC=n(n−1)`); C-CROSS (independent enumeration); C-NOFLOAT. ⚠ NOT a control: any leakage reading.

## §5 — Pre-committed readings

| outcome | conclusion |
|---|---|
| `Tmag` within band at **every** S prime | the **magnitude arrangement is structureless** beyond `μ₆` at this scale — a scoped bound. With the signed null + the forced landscape, **the entire 2nd-order arrangement is accounted for** (null or forced). Next frontier: **4th-order** (the trispectrum / `E[u⁴]` monodromy discriminator — SU(2) vs reduced), the first unforced higher object |
| an even `χ*` fires on S | NAME it (order, cross-prime persistence); `[EMPIRICAL — SEEN-DATA]`, not leakage; reproduce the count; retest out-of-sample |
| PLANT fails | halt |

**Falsification (once):** `Tmag` within the class-energy permutation band at every S prime refutes
"the magnitude arrangement is structured" at this scale/power. Output = characterization / bounded
magnitude, never an avenue verdict.

## §6 — Status

**Arms HELD** pending sign-off (the one NEW risk to check: is the magnitude arrangement forced? Preview
says no — confirm). Deviations → `PREREG_twist_orbit_magnitude_v1_DEVIATIONS.md`.
