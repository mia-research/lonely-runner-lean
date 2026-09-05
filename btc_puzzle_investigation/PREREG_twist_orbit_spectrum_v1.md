# PREREG — Is the twist orbit `a ↦ V(a)` structured beyond its Sato–Tate marginal?

*(multiplicative-spectrum concentration of `V` on `Q = (ℤ/n)^×/μ₆`)*

*2026-07-26. **Written before any `V(a)` is computed.** Arms HELD pending `experiment-designer`
sign-off (CLAUDE.md §2b, mandatory). Sibling to the 120° ideal test (`PREREG_n1_120deg_exact_ideal_v1.md`,
separate session) but **orthogonal** to it — this tests the ARRANGEMENT of the free angle over the
twist orbit, not the ζ₃ lock, and does not use the 120° law as an input. No leakage or ECDLP claim;
pure curve arithmetic.*

> **Provenance.** Operationalizes two hypotheses supplied this session (curve-structure brainstorm,
> external): **Hyp I** — the φ(n)-"dampening" reading (the ζ₃ lock claims 2 of 4 dof; the residual
> free parameter must carry the arrangement); **Hyp II** — the "spectral-dilution / frame-coercivity"
> reading. §0.5 records what happened when Hyp II's object was pinned exactly.

---

## §0 — What is tested, and what a positive would name

Object (record's own cheap instrument): for `a ∈ (ℤ/n)^×`,
`V(a) = Σ_{P ∈ E(F_p)} χ₂(y_P) · ζ_n^{a·d(P)} ∈ ℤ[ζ_n]`, where `d(P)` = dlog of `P` base a fixed
generator `G` (free by walking `[k]G`). `V` is `μ₆`-invariant (`V(a)=V(aλ)`, `λ∈μ₆`) — a **forced**
factor-6 periodicity — so it descends to a function on the cyclic quotient `Q = (ℤ/n)^×/μ₆`,
`|Q| = (n−1)/6`.

The record has the **marginal** of `|V(a)|`: it is `≈` Sato–Tate (`mean|u| = 0.408` vs the SU(2)
value `4/(3π) = 0.4244`, `u := V/(2√p)`) `[EMPIRICAL, on file]`. **Untested: the ARRANGEMENT** — how
`V` is laid out as a function on the group `Q`. That is exactly Hyp I's claim ("the residual dof forms
a rigid progression across the twist orbit"), and it is the natural basis-free question for a
group-indexed sequence.

> **PRIMARY statistic.** `T(p) = max_{ψ ∈ Q̂, ψ ≠ 1} |V̂(ψ)|² / Σ_{a∈Q}|V(a)|²`, where
> `V̂(ψ) = Σ_{a∈Q} V(a) ψ(a)` is the multiplicative(-character) Fourier coefficient of `V` on `Q`.
> **Pre-committed prediction (the "structureless arrangement" null): `T(p)` lies within the
> value-permutation band at every tested prime** — no multiplicative character carries anomalous mass.

`T` large ⇒ a character `ψ*` with anomalous concentration ⇒ a **named** structural handle (its order,
conductor, whether it is common across primes). `T` in-band ⇒ a **scoped magnitude bound** on
multiplicative concentration of the arrangement (a bound, not "no structure" —
[[feedback_negative_bias_enlarge_nulls_2026_07_17]]).

---

## §0.5 — ⚠ FINDING made while pinning Hyp II's object: the literal frame-Gram is FORCED

Hyp II asks to "project the `V(a)` vectors onto the orthogonal complement of the `μ₃`-invariants and
measure the coercivity of the resulting Gram matrix." Pinning the natural vectors
`f_a(P) = χ₂(y_P) ζ_n^{a d(P)}` (so `V(a) = ⟨f_a, 𝟙⟩`) gives, **exactly**:

```
⟨f_a, f_b⟩ = Σ_{P affine} χ₂(y_P)² · ζ_n^{(a−b)d(P)}
           = Σ_{k=1}^{n−1} ζ_n^{(a−b)k}          (χ₂(y)²=1 for all affine P; no 2-torsion since n odd)
           = n·1_{a=b} − 1        ⇒   M = n·I − J.
```

**Verified exactly** (`scratchpad/gram_direct.py`, `p=67,n=79`, 400 random `(a,b)` pairs, integer
arithmetic): the frame Gram is `nI − J`, **curve-independent** — the χ₂ sign (the entire curve signal)
is annihilated because `|f_a(P)| = 1` pointwise. Independently, `V` is already `μ₆`-invariant, so its
projection onto the `μ₃`-complement is **0**. **⇒ Hyp II's literal statistic carries zero curve
information and is NOT run as a test** (it is an instrument identity, of the same kind as the forced
`e₃, e₄` in the 120° prereg). This is a **positive dissolution**: it locates the curve signal in the
**values** `V(a)`, not in the unit-modulus frame — which is precisely what the PRIMARY statistic reads.
Hyp II's surviving, non-forced content = the **shape** of the Arm-I spectrum `{|V̂(ψ)|²}` (its
flatness / participation ratio), reported as a secondary readout of the same computation (§6), never as
an independent arm.

---

## §1 — Assumption audit (run before the design; folded in)

| # | assumption | status | consequence |
|---|---|---|---|
| A1 | `E: y²=x³+7 /F_p`, `n=#E(F_p)` prime, `E(F_p)≅ℤ/n` | curve of record; stratum requires `n` prime | defines `d(P)` and `Q` |
| A2 | `μ₆ ⊂ (ℤ/n)^×`, so `Q` has order `(n−1)/6` | `6 \| n−1`: `3\|n−1` (`n≡1 mod 3` FORCED, record L3) and `2\|n−1` (`n` odd prime) | `Q` cyclic, well-defined |
| A3 | `χ₂(y_P) ≠ 0` at every affine `P` | no affine 2-torsion (`n` odd) — **verified 8/8 primes** (`gram_check.py`) | needed for §0.5 and for `V` well-defined |
| A4 | `V(a) ∈ ℤ[ζ_n]` is EXACT, `O(n)` to compute | one group walk; record's 193-prime instrument | no float in the signal path |
| A5 | `V` is `μ₆`-invariant | record `[PROVED]` (class action `a↦aλ`) | the factor-6 is FORCED and must be quotiented BEFORE the test (else a spurious 6-fold spike) |
| A6 | the marginal `\|V\|/2√p ≈` Sato–Tate | `[EMPIRICAL, on file]` (`mean\|u\|=0.408`) | the null must PRESERVE this marginal — hence the value-permutation null (§2), which reuses the exact empirical values |
| A7 | **the 120° law is NOT assumed here** | we compute `V(a)` directly; arm I never invokes `α₂/α₁=ζ₃` | ⇒ genuine orthogonality to the sibling session |

**A5/A6 are the design's spine:** quotient by `μ₆` first (kill the forced periodicity), then test the
residual arrangement against a null that holds the Sato–Tate marginal fixed by construction.

---

## §2 — Instrument (no floating point in the signal path — folder OVERRIDE)

1. **`V(a)`** for all `a ∈ Q`: exact element of `ℤ[ζ_n]`, stored as the integer coefficient vector
   `(m_0,…,m_{n−1})`, `m_j = Σ_{k: ak≡j} χ₂(y_{[k]G})`. One `O(n)` walk builds every `V(a)` at once.
2. **`V̂(ψ) = Σ_{a∈Q} V(a) ψ(a)`** — `ψ` a character of `Q` (order `\| (n−1)/6`). Element of a cyclotomic
   compositum; **exact**.
3. **Ranking statistic** `|V̂(ψ)|²` and `Σ|V(a)|²`: taken in **high precision (mpmath, monotone
   only)**. Permitted by the folder rule *only* as a monotone statistic ranked against a matched
   permutation null — **the verdict comes from an exact integer rank count, never from a float
   threshold.** Exact-`Norm` fallback available if the rank is ever within float tolerance of a tie.
4. **Value-permutation null (matched control + p-value engine):** draw `π ∈ Sym(Q)`, set
   `V_π(a)=V(π(a))`, recompute `T`. This **preserves the exact value multiset `{V(a)}` (hence the
   Sato–Tate marginal) and destroys only the arrangement** — the precise null for "is the arrangement
   structured." `p = (#{π : T(V_π) ≥ T(V)} + 1)/(R+1)`, `R` permutations, an exact integer ratio.

**No factorization, no ideal arithmetic, no splitting field** — the base field never exceeds `ℚ(ζ_n)`
extended by one small `ψ`-order, so cost is `O(n)` per prime for `V` and `O(|Q|²)` for the spectrum.

---

## §3 — Sample, frozen before any `V` is computed

**Selection rule (deterministic, reproducible):**

- **STRATUM S (primary):** primes `p ≡ 7 mod 12` (secp's class) with `n=#E(F_p)` prime, the first
  **12** with `p > 547`. *(`p > 547` makes S entirely OUT-OF-SAMPLE: every N1/120° measurement on file
  is at `p ≤ 547`.)*
- **STRATUM J (mechanism control):** for each `p ∈ S`, one **`j ≠ 0`** curve `y²=x³+b'` over the same
  `p` with prime order — where the `μ₃`/ζ₃ CM lock is ABSENT. Hyp I predicts any Arm-I structure is a
  `j=0` (CM) property, so J must read as its own null.
- **IN-SAMPLE reference I:** the nine primes `{13,43,127,163,211,349,397,433,547}`, reported in their
  own row, never pooled with S.

**Cells:** the `(n−1)/6` **μ₆ classes** per prime (one `V`-value per class). **Every count in the
report names μ₆ classes and primes separately** (the record's recurring defect: reading `30/30` where
the truth is `5/5`).

**Freeze:** the prime list, the class-representative rule, the generator choice per prime, and `R` are
written to `twist_orbit_spectrum_FREEZE_v1.json` and **SHA-256'd before the first `V` call**; the hash
goes in the RESULT.

**Budget / ABSTAIN:** `O(n)` per prime. If the frozen stratum cannot be completed in the declared
wall-clock, **report the completed primes and ABSTAIN on the rest** — do not substitute easier primes
(the record's B1 blocker). **Abstention is not a closure** ([[feedback_prereg_abstention_is_the_finding_2026_07_19]]).

*(The "both real + constructed sets" rule is N/A here: the object is the curve+prime, no keys are
involved. The matched control is across curve families, `j=0` stratum S vs `j≠0` stratum J.)*

---

## §4 — Controls (each must fire; each declared AS a control)

| id | control | must produce |
|---|---|---|
| **PLANT-POS** *(planted positive)* | inject a synthetic `V'(a)=ψ₀(a)·r_a`, `ψ₀∈Q̂` a fixed nontrivial character, `r_a` drawn from the empirical `\|V\|`-multiset (Sato–Tate magnitude) | **`T` flags `ψ₀`** at `p < permutation floor` — the pipeline can see a planted character |
| **PLANT-NEG** *(planted negative — specificity)* | a synthetic sequence = the empirical value multiset placed on `Q` **at random** (no character) | **`T` within the null band** — a spike is not manufactured by the marginal alone |
| **C-PERM** | the value-permutation null itself (§2.4) | supplies the exact p-value; its own distribution is checked (mean rank ≈ ½) |
| **C-JZERO** | run the full statistic on stratum **J** (`j≠0`) | reads as null if the structure is `j=0`-specific; a positive here re-types the finding as generic |
| **C-CROSS** | `V(a)` from this pipeline vs the record's independent cheap `V₁` instrument | exact agreement at every cell |
| **C-NOFLOAT** | `check_no_float.sh` over the signal-path files | passes **before** any cell is run |
| **C-FORCED** | reconfirm `M = nI − J` at one small prime (§0.5) | agreement. ⚠ **FORCED, so it is an INSTRUMENT CHECK and is NOT evidence for anything** |

⚠ **NOT a control, and must not be reported as one:** any claim that a fired `ψ*` "leaks the scalar."
`V(a)` is a **complete sum over the whole group** indexed by the frequency `a`; it contains no single
secret. A bit-leak is a **downstream, disjoint-construction** test (feature from a public point `[d]G`,
target `= d`) and is reported **nowhere** in this experiment.

---

## §5 — Pre-committed readings (written before any data)

| outcome | pre-committed conclusion |
|---|---|
| `T(p)` within the value-permutation band at **every** prime of S | the arrangement `a↦V(a)` is **structureless beyond `μ₆` at this scale** — report the concentration bound WITH its power and scope; **not** "no structure." Next probe named: the additive/short-scalar arrangement, or the 2-point angle statistic `(θ_a,θ_{ab})` |
| a character `ψ*` fires on S | **NAME it** — order, conductor, whether `ord(ψ*) \| ` a small `ℓ`. Report as a **characterized structural handle**, graded `[EMPIRICAL — SEEN-DATA]`, NOT as leakage. Follow-up: is `ψ*` the **same across primes** (a law) or per-prime (noise)? **Reproduce the count** before naming |
| fires on S but **not** on J | `j=0`-specific structure (a CM property of `y²=x³+7`). Fires on **both** ⇒ generic, re-type |
| any PLANT fails | **halt.** No cell result is reported; the instrument is broken |
| budget exhausted | ABSTAIN on the remainder with the completed count stated |

**Falsification, stated once:** `T(p)` within the value-permutation band at every prime of S refutes
"the arrangement is multiplicatively structured" at this scale and power. **The output is a
characterization or a bounded magnitude — never a verdict on the avenue** (Anomaly-Drill protocol,
[[feedback_anomaly_drill_protocol_2026_07_17]]).

---

## §6 — Secondary (reported, never promoted)

- **Hyp II readout (the surviving content):** the **shape** of the spectrum `{|V̂(ψ)|²}` — participation
  ratio / flatness / residual mass outside the lowest-order characters ("coercivity"). A **derived
  readout of the Arm-I computation**, not a separate object (§0.5).
- **Multiplicativity** `V(a)V(b)/V(ab)` exact residue pattern in `ℤ[ζ_n]` — a second structural probe,
  reported if cheap; a clean multiplicative relation would be a stronger statement than `T`.
- `S_y = max_a|V(a)|/√p` per prime, recomputed exactly, as a cross-check against the record's cap.

---

## §7 — Scope, and what this cannot do

- **Scale banner.** Every cell is at `p ≈ 10³`; secp is `2²⁵⁶`. A null is a scoped magnitude bound; a
  positive is a characterized handle — **neither transfers to secp without a proof.** Reach comes from
  a law, not these numbers.
- Does **not** test the 120° law, the cap `S_y≤2`, Stickelberger, or leakage. It tests one thing: is
  the twist-orbit arrangement multiplicatively concentrated.
- Inherits **no** unverified citation (no Stickelberger, no all-embeddings purity).

---

## §8 — Status

**Arms HELD.** Not runnable until `experiment-designer` signs off (statistic / matched control / power
/ scope / falsifier, and an independent check that §0.5's `nI−J` is genuinely forced). Deviations to be
filed in `PREREG_twist_orbit_spectrum_v1_DEVIATIONS.md` as they occur, not retrospectively.
