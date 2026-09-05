# Consolidated spectral / RH-programme audit (2026-07-11)

Completing the review of the spectral work, re-deriving load-bearing steps and
re-testing the "confirmed" claims with matched nulls and the conductor-shadow
project-out. Two ledgers as in `BASE_AUDIT_v1.md`: the CM arithmetic (solid) and
the RH programme (two fatal gaps). This doc records the file-by-file verdicts and
the two corrections this session produced.

## File-by-file verdict

| File | Claim | Verdict |
|---|---|---|
| `radial_selfadjointness.md` | `A` idx (1,0), `Ĥ` idx (1,1) on [1,∞); (0,0) on ℝ; circle/line obstruction | **CORRECT** — every deficiency index independently re-derived |
| `nt_spectral_rework_findings.md` | κ, `μ(n_t)=0` liability, 1.5× CM support; "tight frame" retracted | **CORRECT** |
| `secp256k1_Lfunction_intersections.md` | `κ_fin=1.9815`, `r(N)=6Σχ₋₃(d)`, `ζ_K=ζ·L(χ₋₃)`, function-field HP | **CORRECT** (arithmetic) |
| `adelic_recasting_v1.md` | `C_ℚ=ℝ₊×Ẑ*`; `ℂ*=ℝ₊×S¹`; μ₆ decoration | **CORRECTED → v2**: μ₆ is the *finite* ray-class χ, not the archimedean S¹ (Pontryagin-dual); conductor stays finite |
| `zfr_rank2_findings.md` | ZFR Appendix-B rank-2 does NOT reproduce (flat, PR≈10) | **CORRECT** — confirmed (my `thread_dilution_v2.py` also flat) |
| `vertical_zfr_replication.md` F1,F2 | low-prime F orthogonal (theorem); large-prime mode rank-1 | **CORRECT** |
| `vertical_zfr_replication.md` **F3** | "CM common mode rank-3 = sextic, CONFIRMED" | **NOT genuine sextic** — but see `INTEGRITY_AUDIT_v1.md`: earned only after 3 passes; it is the `1/√p` envelope (clean same-sample envelope-preserving random-char null: real *below* null, z=−1.1/−1.5), NOT the order-6-Dirichlet "0 above null" I first (faultily) cited |
| `cm_imprint_ramified_prime_findings.md` | CM imprints n_t at ramified prime; freq 0.76 vs 0.42 baseline | **CORRECT**, known-in-principle (Cojocaru/Lee–Sheen) |
| `layering_cleanroom_ledger.md` | L1 solid, L2 mixed (frame-optimality FALSE), L3 broken | **CORRECT**; L4 `N(𝔣)=441` is the known-wrong (drops the 2-part) — study uses `N(𝔣)=7056` |

## Correction 1 — the μ₆ conflation (adelic v1 → v2)

μ₆ decorating ψ is the **finite** ray-class character `χ = −(28/π)₆⁻¹` (derived,
thread A), on the non-archimedean ideles mod `𝔣`; the archimedean `S¹` carries the
*continuous* ∞-type angle (`θ_p=50.55°`, generic). Dual, not equal. ⇒ "the CM place
carries both, no finite places needed" overreaches: the conductor (hence `log N`,
the zero density) is finite-place. Fixed in `adelic_recasting_v2.md` and
`SPECTRAL_REALIZATION_v1.md`.

## Correction 2 — the "CM rank-3 sextic common mode" (Finding 3) is a null artifact

`thread_cm_commonmode_v1.py`. Finding 3 counts character-correlation eigenvalues
above the **iid Marchenko–Pastur edge** `(1+√γ)²` and reports "SEXTIC 3 above,
Dirichlet 1 above, ratio 3 = |μ₆|/|μ₂|." But character values are not iid, and the
**more-rigid, more-numerous μ₆ characters have a higher matched-null edge** — so they
poke above the *iid* edge for a null reason. Tested against a **matched shuffle null**
(permute each character's values across primes; preserves per-character marginal,
destroys cross-character correlation):

```
family   d   n   MPedge | real top-4          | matched-null top-4     | #>null
QUAD     8  281  1.366  | 1.178 1.171 1.075 …  | 1.259 1.158 1.087 …    | 0
SEXTIC  16  281  1.534  | 1.293 1.195 1.171 …  | 1.301 1.236 1.189 …    | 0
```

Real top eigenvalues sit **at or below** the matched null for both families —
**0 genuine common modes**, not 3 vs 1. (My sextic top `[1.293,1.195,1.171]`
matches the finding's `[1.269,1.174,1.106]` magnitudes, so the same object is being
measured; the matched null accounts for all of it.) This parallels the audited ZFR
large-prime result (real sits *below* the matched null) and the dilution result
(the only real CM "common mode" is the rank-1 χ₋₃ shadow). *Caveat:* my
reconstruction uses order-6 characters mod `q≡1 mod 6`, not the finding's exact
`F_{q²}`-on-Eisenstein-primes construction; the methodological point (matched null,
not iid edge) and the matching magnitudes make the direction clear, but a byte-exact
refutation needs the finding's own script.

## The unifying picture (three constructions tested)

*Scoped:* across the three constructions **tested here**, no genuine multi-rank CM
spectral common mode was detected — a statement about these tests, not a proof of
non-existence (see `RESULTS_LEDGER_v1.md` B4–B5; the general "axis exhausted"
reading is `[conjecture]`, `INTEGRITY_AUDIT_v1.md`):
- **ZFR low-prime features** → flat/orthogonal in the reconstruction (PR≈10; the
  paper's rank-2 did not reproduce, likely a `|χ|`/`Reχ` code variant — B5).
- **CM character correlations** (Finding 3) → real top ≈ matched null (z=−1.5); the
  "3 above the iid edge" was the `1/√p` envelope (B4).
- **The one real CM common mode found** (dilution, `f_q(ℓ)=cos(2π a_ℓ/q)`) →
  **rank-1 χ₋₃ conductor shadow** (align 0.997; project it out → 1/d floor; the
  public CM discriminant −3, from `a_ℓ=0` on inert primes) — this positive stands.

So every "CM common mode / sextic spectral gap" reduces to either (a) the known
rank-1 χ₋₃ conductor character, or (b) a wrong-null counting artifact. This does
**not** touch the curve's genuine sextic structure — the μ₆ Grössencharacter, the
derived χ, the formal-group μ₆-sparsity, the amicable pair — which are exact,
independent curve facts (Ledger A), untouched by anything here.

## Net

- **CM arithmetic study:** solid, gap-free (re-confirmed).
- **RH programme:** two fatal gaps (Moment-Pumping, operator indices) — does not
  prove RH; audited files are otherwise mostly correct and honestly self-corrected.
- **Two corrections this session:** the μ₆-is-finite conflation, and the CM-rank-3
  null artifact. Both tighten the picture; neither touches the exact curve results.
