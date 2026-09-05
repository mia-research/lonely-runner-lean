# PREREG — P0, the anti-coherent plant (sign-flipped plant across the pooling axis)

**FROZEN pre-registration. No data seen.** Written before any P0 run. Grades HELD.
No leakage / key-recovery / ECDLP claim: this test measures **synthetic-plant detection
rates only**, never a real-data readout.

Object under audit: the four pipelines that each reported "power OK, PLANT fires N×" —
signed twist-orbit spectrum (`twist_orbit_spectrum_run_v1.py`), magnitude spectrum
(`twist_orbit_magnitude_run_v1.py`), monodromy (`twist_orbit_monodromy_run_v1.py`),
row-budget (`row_budget_run_v1.py` / `row_budget_v3_run.py` + `row_budget_core_v1.py`).

---

## 0. Headline of this spec (pre-run, from reading the instrument code)

**A defect was found in the P0 spec by reading the code, and it is registered here rather
than hidden: the P0 mechanism — "flip the plant's sign along the pooling axis (`p mod 4` /
`p mod 3` / random-per-prime) and see if detection changes" — is a NO-OP on all four
pipelines' detection statistics, for reasons intrinsic to those statistics.** The
alignments `p mod 4`, `p mod 3`, random-per-prime are all *per-prime* sign assignments
`s_p ∈ {+1,−1}`; every pipeline's plant statistic factors through a magnitude / even
moment that is invariant to a per-prime scalar sign. Therefore the flip changes the
statistic by **exactly zero** (machine-exact, verified below), and the resulting
detection-rate table cannot distinguish a coherent from an anti-coherent alternative.

- The spec's claim **"cannot manufacture a positive leakage finding" HOLDS** — trivially,
  because the test only ever reports detection rates of *synthetic* plants and never reads
  real leakage. (§7, §9.)
- But the spec **also cannot produce a meaningful Outcome A or Outcome B** on pipelines
  1–3 (and on row-budget's per-prime firing criterion): the flip has **zero power**
  (§5). Reading a forced "still fires" as "the nulls are scoped against anti-coherent
  alternatives" would be a **null-mismatch artifact** — the readout is invariant to the
  very symmetry (sign) the plant is flipping.

This prereg therefore registers **INV** (the flip-sensitivity gap, §2) as the *primary*
statistic — the decidable artifact that catches the vacuity — and makes the detection-rate
table a **secondary** readout, admissible only in cells where INV > 0. It also registers a
**must-fire signed-pool positive control** (§4) that distinguishes "the statistic is
sign-blind" (a real, reportable scope fact) from "our flip-injection code is broken" (a
VOID bug).

---

## 1. OBJECT

The object is **the scope of the four pre-existing nulls with respect to the sign of a
planted alternative along the prime-pooling axis** — i.e. whether each pipeline's
*detection machinery* can see a per-prime sign pattern in an injected effect.

Named exactly, per pipeline, the plant statistic `S(p)` whose sign-sensitivity we probe is:

| pipeline | plant statistic `S(p)` | code (file:line) | plant object (what the sign multiplies) |
|---|---|---|---|
| spectrum (signed) | `T = max_{j≡3 mod6} \|FFT_{n-1}(W)[j]\|²` | `twist_orbit_spectrum_run_v1.py:125-134` | `rho_plant = scale·exp(iπs/L)` (`:204-206`) |
| magnitude | `Tmag = max_{j≡0 mod6, j≠0} \|FFT_{6L}(tile)[j]\|²` | `twist_orbit_magnitude_run_v1.py:35-44` | `tone = base + 3·amp·cos(2πs/L)` (`:79-82`) |
| monodromy | `E[u⁴] = n·ΣR(j)² / (16 p²(n-1))`, `u=V/(2i√p)` | `twist_orbit_monodromy_run_v1.py:39` | PLANT-UNIF: an iid **distribution** (`:55, :79-81`) |
| row-budget | `N_LOW = #{a≠0 : \|U(a)\|²/(n-1) < 0.01}`; verdict `z_p` (signed), pool `Z=Σz_p/√k`, fire `z20>6` per prime | `row_budget_run_v1.py:110-115,177`; `row_budget_v3_run.py:113,176` | eps-carrier: `sp[order[:k]] = 1.0` (`row_budget_v3_run.py:57-60`) |

**Tautology / disjointness note.** The feature (the per-prime sign `s_p`) and the target
(does detection change) are disjoint from the real signal path, so there is no
feature/target construction-sharing tautology. The risk here is the **opposite**: the
target may be *structurally invariant* to the feature (see §2), which is a zero-power
defect, not a tautology.

---

## 2. STATISTIC (exactly one primary)

**PRIMARY = `INV_cell`, the flip-sensitivity gap of the pipeline's own plant statistic
under the per-prime sign flip, per (pipeline × alignment) cell:**

```
INV_cell = max over scoped primes p of  |S_flip(p) − S_coh(p)| / max(|S_coh(p)|, tiny)
```

where `S_coh(p)` is the pipeline's plant statistic with coherent sign (`s_p ≡ +1`, the
existing baseline) and `S_flip(p)` is the identical machinery with the plant multiplied by
`s_p ∈ {+1,−1}` set by the alignment. `INV_cell` is a pure number ≥ 0.

**Distribution / expected value under the algebra of each statistic (pre-computed):**
`INV_cell = 0` whenever `S` is invariant to a per-prime scalar sign. This is provable, not
conjectural, for three of the four pipelines:

- **spectrum:** `rebuild_W` is **linear** in `rho` (`:118-122`), and `Tstat` returns a sum
  of squared moduli `|FFT(W)[j]|²` (`:131`). For `s_p ∈ {±1}`,
  `Tstat(rebuild_W(s_p·rho_plant)) = Σ_j |s_p·FFT(rebuild_W(rho_plant))[j]|² = s_p²·T = T`
  since `s_p² = 1`. **`INV = 0` exactly.** (Verified numerically: `INV = 0.000e+00`,
  machine-exact, at `L=138`, both signs.)
- **magnitude:** input `Ecls`/`tone` is already an **energy** (magnitude, `:31,:79-82`) and
  `Tmag` takes `|FFT|²` (`:41`). Flipping the AC part (`cos → −cos`) or the whole tone
  (`tone → −tone`, DC bin `j=0` excluded) leaves every admissible `|FFT[j]|²` unchanged.
  **`INV = 0` exactly.** (Verified numerically: `INV = 0.000e+00` for both the AC-flip and
  the whole-plant-negation.)
- **monodromy:** `E[u⁴]` is an **even moment** (`u → −u ⇒ u⁴` unchanged, `:39`), and the
  plant is PLANT-UNIF — an iid *distribution* with **no sign to flip** (`:55, :79-81`).
  Any per-prime sign is invisible. **`INV = 0` exactly.**
- **row-budget:** `N_LOW` counts `|U(a)|²` below a threshold (magnitude, `:110-115`); the
  eps-carrier sets entries to the constant `1.0` (`row_budget_v3_run.py:57-60`) and has no
  signed anti-form (setting to `−1.0` gives the identical `|U|²`, hence identical
  `N_LOW`); and the firing criterion is the **per-prime** `z20 > 6` (criterion 4,
  `row_budget_v3_run.py:176`), applied prime-by-prime, never the signed cross-prime pool.
  **`INV = 0`** for the plant machinery as written.

**SECONDARY (admissible only where `INV_cell > τ_INV`):** the detection-rate table
`R_flip[pipeline × alignment] = (#scoped primes whose flipped plant fires under the
pipeline's own rule) / (#scoped primes)`, compared to the coherent baseline `R_coh`.

`τ_INV = 1e-9` (relative). Below it, the flip is treated as a no-op and the cell is VACUOUS.

**Why INV is the primary, not the detection rate.** The detection rate is the quantity the
P0 deliverable names, but it is *uninterpretable* until we know the statistic can see the
sign at all. INV is the gate that makes the whole table decidable; it is a single scalar
per cell, computed from exact/near-exact quantities, and its pre-committed value (0 vs >0)
sorts every cell into VACUOUS vs informative before any detection rate is read.

---

## 3. MATCHED CONTROL / null

The "null" this test interrogates is each pipeline's **own** pre-registered permutation /
simulation null (signed-value permutation for spectrum; class-energy permutation for
magnitude; iid-SU(2) simulation for monodromy; MN-μ6 / MN-neg / MN-free relabellings for
row-budget). P0 does **not** introduce a new data null; it re-runs the existing null with a
sign-flipped plant.

**What the flip preserves / destroys (the matched-control audit of P0 itself):**
- The per-prime sign flip `s_p` **preserves** every magnitude/energy/even-moment structure
  the statistic reads — by construction it multiplies the plant by `±1` and the statistic
  discards that factor (§2). This is exactly the failure archetype in the charter: *a
  control that preserves a symmetry the readout has by definition is an invalid probe of
  that symmetry.* Here the flip **destroys nothing the statistic can see**, so it is a
  null probe with **no contrast**.
- The flip **destroys** cross-prime sign coherence — but only a statistic that **pools
  across primes with a sign** can register that. Of the four pipelines, only row-budget
  has a signed cross-prime pool (`Z = Σz_p/√k`, `row_budget_run_v1.py:226`,
  `row_budget_v3_run.py:214`), and its *firing criterion* (z20>6) is per-prime, not that
  pool. So no pipeline's firing decision is exposed to the destroyed coherence.

**Consequence, pre-registered:** the matched-control audit predicts `INV_cell = 0` for all
four pipelines under all three alignments — i.e. the P0 probe is null-mismatched to every
one of the four statistics. This is the pre-committed expectation, not a post-hoc reading.

---

## 4. PLANTED CONTROL (must-fire) + VOID rule

Two positive controls, both must fire, or the run is VOID (no A/B/scope claim issued).

**PC1 — the coherent baseline must reproduce the reported "fires N×".** Re-run each
pipeline's existing coherent plant (`s_p ≡ +1`) on its calibration primes and reproduce the
frozen baseline firing:

| pipeline | must reproduce | source |
|---|---|---|
| spectrum | PLANT-POS `Tp > 3·p95` at p = 127/163/211, ratios ≈ 4.1× / 4.5× / 6.3× | `RESULT_twist_orbit_spectrum_v1.md` §1 POWER |
| magnitude | PLANT-POS `Tp > 3·p95`, ratios ≈ 4.9×→10.9× (L=138→348) | `RESULT_twist_orbit_magnitude_v1.md` §1 POWER |
| monodromy | PLANT-UNIF center ≈ 0.375, separated above the SU(2) band (`ucen > hi`) | `RESULT_twist_orbit_monodromy_v1.md` §5 |
| row-budget | chirp → N_LOW = 0 exactly; tone/eps=1 → N_LOW = n−1 exactly; z20 > 6 for p ≥ 577 | `RESULT_row_budget_lowtail_v3.md` §1,§3 |

If PC1 does not reproduce (ratios materially off, extremes not exact) → **VOID**: the
instrument is not the one that produced the baseline; no scope claim may be issued.

**PC2 — the signed-pool positive control must fire (this is the load-bearing one for P0).**
Build a *purpose-made* signed cross-prime pooling statistic `Z_sign = Σ_p s_p·δ(p)/√k`,
where `δ(p)` is a **known, injected** per-prime effect of known size `E` (e.g. a constant
shift `δ(p) = E` added to a signed per-prime score). Run it twice:
- **coherent** (`s_p ≡ +1`): `Z_sign` must exceed its own null band (fires).
- **anti-coherent** (`s_p` set by `p mod 4`): `Z_sign` must **collapse toward 0** (goes
  blind).

PC2 proves the flip-injection actually flips a sign and that a *signed* statistic can be
made blind by the anti-coherent alignment. **If PC2's anti-coherent arm does NOT collapse
(the coherent and anti-coherent `Z_sign` are equal), the flip code is broken → VOID.**
PC2 is what lets us read `INV = 0` on the four real pipelines as *"their statistic is
sign-blind"* (a real scope fact) rather than *"our flip did nothing because of a bug."*

**VOID rule (single, decidable):** if PC1 fails on any pipeline, that pipeline's cell is
VOID; if PC2 fails, the entire P0 run is VOID. A VOID run claims **no null, no scope
correction, no strengthening** — full stop.

---

## 5. POWER (with the detectable-effect floor per pipeline)

Power is stated for the quantity P0 exists to measure: **the ability to distinguish a
coherent from an anti-coherent planted alternative.**

| pipeline | min detectable anti-coherence (this probe) | why | baseline (coherent) plant power |
|---|---|---|---|
| spectrum | **∞ (undetectable)** — power = 0 | `T = s_p²·T`, `INV ≡ 0` exactly (§2) | detects a single admissible char carrying ≳ 6% of arrangement energy at >95% (`RESULT..._spectrum_v1.md` POWER) |
| magnitude | **∞ (undetectable)** — power = 0 | `Tmag` of an energy, `INV ≡ 0` exactly (§2) | fires 4.9×→10.9× p95; comparable even-char concentration detected across S |
| monodromy | **∞ (undetectable)** — power = 0 | `E[u⁴]` even; plant is a distribution with no sign (§2) | separates torus/CM `3/8` from the SU(2) band (`ucen > hi`) |
| row-budget | **∞ (undetectable) via the existing plant** — power = 0 | `N_LOW` magnitude; eps-carrier has no signed anti-form; firing is per-prime `z20` (§2) | z20 > +6 at eps=0.20 for p ≥ 577; chirp/tone extremes exact |

**Scoped power statement:** for the anti-coherent question, this probe has **zero power on
all four pipelines** — it cannot reject "detection unchanged" because `S_flip ≡ S_coh` by
algebra. The coherent baseline (PC1) has the power quoted in the right column, which is why
PC1 fires; that power is about *coherent* plants and says nothing about anti-coherent ones.

**What a properly-powered anti-coherence test would require (named, not run here):** a
statistic that pools across primes **with a sign** (a phase-coherent pool such as
`|Σ_p V̂(χ)(p)|²` across primes, or the signed Stouffer `Z` of row-budget used *as the
firing statistic*), against which a coherent plant adds and an anti-coherent plant cancels.
That is a different statistic from the four registered here and needs its own prereg.

---

## 6. SCOPE (inherited by every number this run emits)

Every detection rate, INV value, and grade below is scoped to:

- **spectrum / magnitude / monodromy:** stratum S = 12 primes `p ∈ [823, 2731]`, `p ≡ 7
  mod 12`, `n = #E(F_p)` prime, curve `y² = x³ + 7` (j = 0, μ₆ CM); calibration primes
  {127, 163, 211} (+ reference {349, 397, 433, 547}); `χ₂(y)` channel; `R = 3000` perm
  reps; freeze `twist_orbit_spectrum_FREEZE_v2.json`, SHA `7cde99fe…`.
- **row-budget:** 10 model primes {163, 211, 349, 433, 577, 991, 2089, 4159, 9319, 19231},
  generic μ₆×conj stratum, `N_LOW` at `ρ < 0.01`, nulls MN-μ6 / MN-neg / MN-free, frozen
  frequency list SHA `9695989b…`, `R = 64`.
- **alignments:** `s_p` by `p mod 4`; by `p mod 3`; random-per-prime (seeded, the floor).
- **NOT in scope:** real-data leakage, key recovery, ECDLP, secp scale (`p ≈ 2²⁵⁶`), any
  statistic other than the four named plant statistics, and any coherent-vs-anti-coherent
  claim that would require the signed cross-prime pool of §5.

No number produced by this run may be quoted without this scope line.

---

## 7. FALSIFICATION (written before the run)

Per (pipeline × alignment) cell, the outcome is decided by INV first, then by R_flip:

- **VACUOUS** (pre-committed prediction for all 12 cells): `INV_cell ≤ τ_INV = 1e-9`. The
  statistic is invariant to the flip. The cell **strengthens nothing and scope-corrects
  nothing**. Reporting it as Outcome A is forbidden by this prereg (it would be a
  null-mismatch artifact). What it *does* license, once PC2 has fired: the scoped, graded
  statement *"pipeline X's firing statistic is sign-blind at the per-prime level; the
  anti-coherent alternative is out of scope of that statistic — neither in nor out of the
  original null."*
- **Outcome A (strengthens)** — admissible **only if** `INV_cell > τ_INV` **and**
  `R_flip ≥ R_coh − δ_R` (`δ_R = 1/#scoped primes`, i.e. within one prime of the coherent
  rate): the null holds against both coherent and anti-coherent alternatives; state the
  number.
- **Outcome B (goes blind → re-analysis mandatory)** — `INV_cell > τ_INV` **and**
  `R_flip < R_coh − δ_R`: the pipeline detects coherent but not anti-coherent plants; its
  nulls are scoped to coherent alternatives only; a re-analysis of those nulls is required.
- **VOID:** PC1 fails for that pipeline, or PC2 fails globally (§4).

**What refutes the P0 spec's own thesis:** if every cell is VACUOUS (the pre-committed
prediction), the P0 test as written **cannot deliver its advertised A/B outcome** — it is
under-powered by construction. That is itself the finding, and it is reported as such, with
the §2 algebra as the witness. The remedy (a signed-pool statistic, §5) is named, not run.

---

## 8. EXACTNESS

- **Signal path stays exact and untouched.** The sign flip is injected **only** into the
  synthetic plant, never into the real signal path. The real path — Legendre `χ₂`
  (`twist_orbit_spectrum_run_v1.py:39-43`), the curve orbit `[d]G`
  (`row_budget_core_v1.py:28-65`), the multiplicative index `mult_index` (`:93-102`), the
  integer autocorrelation `R(j)` (`twist_orbit_monodromy_run_v1.py:36`), the exponent
  `(b·x_d + c·y_d) mod p` (`row_budget_run_v1.py:148`, `row_budget_v3_run.py:44`) — remains
  Python `int` / `Fraction` as in the source and is not modified by P0.
- **The sign `s_p` is exact integer.** `s_p = +1 if (p % 4 == 1) else −1` (and analogously
  `p % 3`); random-per-prime `s_p` drawn from a seeded PRNG mapped to `{+1,−1}` (integer).
  `p % 4`, `p % 3` are pure integer ops. `s_p` is an int; `s_p² = 1` is an exact integer
  identity, which is *why* `INV = 0` is machine-exact for the spectrum (§2), not merely
  small.
- **Injection points (named, so the flip stays exact and out of the key path):**
  spectrum `rho_plant → s_p * rho_plant` at `:206-207`; magnitude `tone`'s AC part
  (or whole `tone`) `→ s_p * (...)` at `:81-82`; monodromy — no injection point exists
  (the plant is a distribution, `:79-81`); row-budget — no signed injection point exists in
  the eps-carrier (`row_budget_v3_run.py:57-60`).
- **Float carve-out (unchanged from the source, sanctioned).** The plant tones
  (`exp(iπs/L)`, `cos(...)`) and the FFT/simulation statistics are already float
  *references ranked against the permutation/simulation null* per `CLAUDE.md`
  "NO FLOATING POINT" — analytic size only, no key in the path. Multiplying a float plant
  by the integer `s_p` preserves that status (IEEE negation is exact; `|−z|² = |z|²`
  exactly). The `INV` comparison is a float diagnostic used **only** as a monotone gate
  against `τ_INV` — and in the invariant cells it is exactly `0`, provable as the integer
  identity `s_p² = 1`, so no float decides the verdict there.
- `check_no_float.sh` (AST checker, `check_no_float.py`) must pass on any new P0 driver
  before the run, exactly as for the four source instruments.

---

## 9. PRE-COMMITMENT grade table (filled BEFORE the run)

Decidable rule: read `INV_cell` first (§2), then `R_flip` (§7). PC1/PC2 gate everything.

| cell (pipeline × alignment) | pre-committed **predicted** outcome | grade if it occurs | grade if it does NOT (the surprising branch) |
|---|---|---|---|
| spectrum × {p mod 4, p mod 3, random} | **VACUOUS** (`INV=0`, §2) | `[VERIFIED — exact invariance; sign out of scope of `\|V̂\|²`; null neither strengthened nor scope-corrected]` | if `INV>0`: instrument bug (linearity/`\|·\|²` broken) → investigate before any A/B |
| magnitude × {3 alignments} | **VACUOUS** (`INV=0`, §2) | `[VERIFIED — exact invariance; sign out of scope of `\|V\|²`-energy statistic]` | if `INV>0`: bug → investigate |
| monodromy × {3 alignments} | **VACUOUS** (`INV=0`; plant has no sign, §2) | `[VERIFIED — even moment + sign-free plant; P0 ill-posed for this pipeline]` | if `INV>0`: bug → investigate |
| row-budget × {3 alignments} | **VACUOUS** for the existing plant (`INV=0`, §2) | `[VERIFIED — N_LOW magnitude + per-prime firing; eps-plant has no signed anti-form]` | if a signed anti-plant were built and `INV>0`: escalate to a real A/B under a new prereg |

**Global pre-commitments:**
- If **PC2 fails** (anti-coherent `Z_sign` does not collapse): whole run **VOID**; the
  flip-injection is broken; no VACUOUS/A/B claim may be made. (Distinguishes sign-blindness
  from a bug.)
- If **PC1 fails** on a pipeline: that pipeline's cell **VOID**; not the one that produced
  the baseline.
- If the pre-committed **VACUOUS** prediction holds (all real-pipeline cells `INV=0`, PC2
  fired): the reported conclusion is *"P0 as written is zero-power on all four pipelines —
  it can neither strengthen nor scope-correct their nulls, because each firing statistic is
  sign-blind at the per-prime level. The anti-coherent question is real but requires a
  signed cross-prime pooling statistic (§5), which is a separate prereg."* This is graded
  `[VERIFIED — exact/near-exact; scoped]` and is the honest deliverable — **not** a
  strengthening of the four nulls, and **not** a leakage finding.
- The spec's claim *"P0 cannot manufacture a positive leakage finding"* is **CONFIRMED**
  and, moreover, sharpened: P0 cannot manufacture *any* finding about the four nulls'
  anti-coherent scope (it is zero-power), so it can only (a) reproduce baselines via PC1,
  or (b) report the sign-blindness scope fact above. It never touches real-data leakage.

---

## Provenance

- Instruments read (grounding every number/line above): `twist_orbit_spectrum_run_v1.py`,
  `twist_orbit_magnitude_run_v1.py`, `twist_orbit_monodromy_run_v1.py`,
  `row_budget_run_v1.py`, `row_budget_v3_run.py`, `row_budget_core_v1.py`.
- Baselines: `RESULT_twist_orbit_spectrum_v1.md`, `RESULT_twist_orbit_magnitude_v1.md`,
  `RESULT_twist_orbit_monodromy_v1.md`, `RESULT_row_budget_lowtail_v3.md`; preregs
  `PREREG_twist_orbit_spectrum_v2.md`, `PREREG_twist_orbit_magnitude_v1.md`,
  `PREREG_twist_orbit_monodromy_v1.md`, `PREREG_row_budget_lowtail_v3.md`.
- INV=0 verified numerically (spectrum + magnitude, machine-exact `0.000e+00`) and proven
  algebraically (§2) before freezing.
- Exactness rule: `btc_puzzle_investigation/CLAUDE.md` "NO FLOATING POINT IN THE SIGNAL
  PATH"; enforcement `check_no_float.sh` / `check_no_float.py`.

**FROZEN pre-registration. No data seen.**
