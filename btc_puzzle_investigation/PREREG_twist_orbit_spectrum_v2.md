# PREREG — Is the twist orbit `a ↦ V(a)` structured beyond its Sato–Tate marginal? (v2)

*(multiplicative-spectrum concentration of the SIGNED, `μ₃`-invariant, `−a`-ODD sum `V`)*

*2026-07-26. **Written before any signal `V(a)` is examined for structure.** Arms HELD pending
`experiment-designer` re-sign-off (CLAUDE.md §2b). Sibling to `PREREG_n1_120deg_exact_ideal_v1.md`
(separate session) but **orthogonal** — tests the ARRANGEMENT of the free angle over the twist orbit,
not the ζ₃ lock, and does not use the 120° law as an input. No leakage or ECDLP claim.*

> **Operationalizes** two curve-structure hypotheses supplied this session (external brainstorm):
> **Hyp I** (φ(n)-"dampening" → the residual free dof carries the arrangement) and **Hyp II**
> (spectral-dilution / frame-coercivity). §0.5 records what pinning Hyp II's object produced.

---

## §0.0 — ⚠ Correction lineage: what v1 got wrong, and the gate that caught it

`PREREG_twist_orbit_spectrum_v1.md` asserted `V` is **`μ₆`-invariant** and placed it on
`Q=(ℤ/n)^×/μ₆`. **That is false**, and the `experiment-designer` sign-off (fresh prime `p=43,n=31`;
reproduced here `verify_symmetry.py` at `p=67,79,127`) caught it:

- **`V(−a) = −V(a)` — FORCED and curve-independent.** For `p≡7 mod 12 ⟹ p≡3 mod 4`, `χ₂(−1)=−1`;
  reindexing by `P↦−P` (`d(−P)=−d(P)`, `y_{−P}=−y_P`) gives `V(−a)=χ₂(−1)V(a)=−V(a)`.
- **`V` is `μ₃`-invariant, NOT `μ₆`-invariant**, and **purely imaginary**. (The record's "(n−1)/6 μ₆
  classes" is correct for the *magnitude*/`v=u²` object, which IS `μ₆`-invariant; v1's error was
  applying it to the *signed* `V`.)

Consequence v1 got wrong on two counts: (i) a value of `V` on `Q=(ℤ/n)^×/μ₆` is **ill-defined** (sign
flips with the representative — the gate showed `T: 1.408→1.047` under one rep flip); (ii) the free
value-permutation null would have **destroyed the forced anti-symmetry `V(−a)=−V(a)`**, i.e. broken a
by-definition symmetry like real signal — the invalid-null trap already logged on this project
([[feedback_residue_vs_component_tautology_2026_07_14]]). **v2 fixes both** (§0, §2). v1 is superseded
and retained only as the audit trail.

---

## §0 — What is tested, and what a positive would name

Object: `V(a) = Σ_{P∈E(F_p)} χ₂(y_P)·ζ_n^{a·d(P)} ∈ ℤ[ζ_n]`, `a∈(ℤ/n)^×`, `d(P)`=dlog base a fixed
generator (free by walking `[k]G`). **Forced structure (verified, exact):** `V(a)=i√p·ρ(a)` with
`ρ(a)∈ℝ`, `ρ(ωa)=ρ(a)` (`ω` order 3), `ρ(−a)=−ρ(a)`. So the **free data is the signed real sequence
`ρ` on the `L=(n−1)/6` `μ₆`-magnitude-classes** — magnitude `μ₆`-invariant, sign a free bit per class.

The record has the **magnitude marginal**: `|ρ|/2=|u|≈` Sato–Tate (`mean|u|=0.408` vs SU(2) `0.4244`)
`[EMPIRICAL, on file]`. **Untested: the ARRANGEMENT of the signed `ρ` over the group** — Hyp I's claim.
The multiplicative spectrum of `V` is supported **exactly** on the `L=(n−1)/6` characters `χ` of
`(ℤ/n)^×` that are **trivial on `μ₃` AND odd** (`χ(−1)=−1`); operationally this is the DFT of the
length-`L` signed sequence `ρ` on the cyclic group `ℤ/L`.

> **PRIMARY statistic.** `T(p)=max_{χ admissible, χ≠—}|V̂(χ)|² / (n(n−1))`, where
> `V̂(χ)=Σ_{a∈(ℤ/n)^×}V(a)χ(a)`, and the denominator is the **forced** Parseval constant
> `Σ_{a∈(ℤ/n)^×}|V(a)|²=n(n−1)` (§0.5, disclosed as an instrument constant).
> **Pre-committed prediction (structureless-arrangement null): `T(p)` within the signed-value
> permutation band at every tested prime.**

`T` large ⇒ an admissible odd character `χ*` with anomalous concentration ⇒ a **named** handle (order,
conductor, cross-prime persistence). `T` in-band ⇒ a **scoped magnitude bound** on the arrangement's
concentration — a bound, not "no structure" ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]).

---

## §0.5 — Forced objects, disclosed (each an instrument check, none evidence)

Pinning Hyp II's frame `f_a(P)=χ₂(y_P)ζ_n^{a d(P)}` (`V(a)=⟨f_a,𝟙⟩`) gives **exactly**, and
**curve-independently** (verified `gram_direct.py`, `p=67`, 400 pairs; agent reconfirmed `p=43`):

```
⟨f_a,f_b⟩ = Σ_{k=1}^{n−1} ζ_n^{(a−b)k} = n·1_{a=b} − 1 = (nI − J)[a,b].
```

`χ₂(y)²=1` at every affine `P` (no 2-torsion, `n` odd — verified 8/8) annihilates the χ₂ sign, so the
frame Gram is a fixed `nI−J`. **⇒ Hyp II's literal statistic carries zero curve information and is NOT
a test.** Its surviving content = the **shape** of Arm I's spectrum (§6). Independently, `V` is
`μ₃`-invariant, so its projection on the `μ₃`-complement is `0` — the second reason the literal Hyp II
object is empty. **Two further forced, curve-independent quantities, disclosed:** the denominator
`Σ|V(a)|²=n(n−1)` (Parseval; verified 6 primes) and the symmetries `V(−a)=−V(a)`, `V μ₃`-invariant, `V`
purely imaginary. **None of these tautologizes `T`** — its numerator (which arrangement, which `χ`)
stays curve-dependent — but each is used only as an instrument check (§4), never as evidence.

---

## §1 — Assumption audit (folded in; the ones that flipped from v1 are marked ⚑)

| # | assumption | status | consequence |
|---|---|---|---|
| A1 | `E:y²=x³+7/F_p`, `n=#E` prime, `E(F_p)≅ℤ/n` | curve of record | defines `d(P)` |
| A2 ⚑ | `V` is `μ₃`-invariant **and** `V(−a)=−V(a)` (odd), purely imaginary | **verified exact** (`verify_symmetry.py`, 3 primes; agent `p=43`) — **v1's `μ₆`-invariance is WRONG** | free object = signed `ρ` on `L=(n−1)/6` classes; spectrum on odd-`μ₃`-trivial `χ` |
| A3 | `χ₂(y_P)≠0` at every affine `P` | no affine 2-torsion (`n` odd) — verified 8/8 | `V`, §0.5 well-defined |
| A4 | `V(a)∈ℤ[ζ_n]` EXACT, `O(n)` | one group walk | no float in signal path |
| A5 ⚑ | the marginal preserved by the null must be the `μ₆`-invariant **magnitude** distribution AND the forced sign structure | ⇒ **permute SIGNED class-values** (§2.4), not a free shuffle | fixes v1's invalid null |
| A6 | `\|ρ\|/2≈` Sato–Tate | `[EMPIRICAL, on file]` | reused verbatim by the null (not modelled) |
| A7 | Parseval denominator `Σ\|V\|²=n(n−1)` FORCED | verified 6 primes | a constant normalization; instrument check, not evidence |
| A8 | the 120° law is **not** assumed | `V(a)` computed directly | genuine orthogonality to the sibling session |

---

## §2 — Instrument (no floating point in the signal path — folder OVERRIDE)

1. **`V(a)`** exact in `ℤ[ζ_n]` (integer coeff vector), all `a` from one `O(n)` walk. Reduce to the
   signed class-sequence `ρ∈ℝ^L` via `ρ(a)=V(a)/(i√p)` — **but the EXACT carrier stays `V(a)∈ℤ[ζ_n]`;**
   `√p` enters only the monotone ranking (below), never a stored signal value.
2. **`V̂(χ)`** over the `L=(n−1)/6` admissible odd characters: exact cyclotomic sum.
3. **Ranking statistic** `|V̂(χ)|²` in **high precision (monotone only)** — permitted by the folder
   rule *solely* as a monotone statistic; the **verdict is an exact integer rank** against:
4. **Signed-value permutation null (matched control + p-value engine):** draw `π∈Sym(L)`, permute the
   **signed** class-values `{ρ_c}` (equivalently `{V(a_c)}`), rebuild `V_π` respecting `μ₃`-invariance +
   `V(−a)=−V(a)`, recompute `T`. This **preserves the exact signed-value multiset** (⇒ magnitude
   marginal + sign balance + forced anti-symmetry) and **destroys only the arrangement**.
   `p=(#{π:T(V_π)≥T(V)}+1)/(R+1)`. *(Robustness variant, secondary: permute magnitudes with iid signs —
   forces sign-balance 50/50; reported only if it disagrees with the primary.)*

No factorization, no ideals, no splitting field: base field `≤ ℚ(ζ_n)·ℚ(χ)`, cost `O(n)+O(L²)`/prime.

---

## §3 — Sample, frozen before any structure is examined

- **STRATUM S (primary):** `p≡7 mod 12`, `n=#E` prime, first **12** with `p>547` — entirely
  OUT-OF-SAMPLE (all N1/120° data is `p≤547`).
- **STRATUM J (mechanism control):** one `j≠0` prime-order curve per `p∈S` (ζ₃/CM lock ABSENT). Hyp I
  predicts any structure is a `j=0` property ⇒ J reads as its own null.
- **IN-SAMPLE reference I:** `{13,43,127,163,211,349,397,433,547}`, own row, never pooled.
- **Cells:** the `L=(n−1)/6` classes per prime; **counts name classes and primes separately.**
- **Freeze:** prime list, generator per prime, class-rep rule, `R` → `twist_orbit_spectrum_FREEZE_v2.json`,
  **SHA-256'd before the first structural read**; hash in the RESULT.
- **Budget/ABSTAIN:** `O(n)`/prime; if S can't complete, report completed + **ABSTAIN**, no
  substitution. Abstention ≠ closure ([[feedback_prereg_abstention_is_the_finding_2026_07_19]]).

*(“Both real + constructed sets” rule N/A — object is the curve, no keys; the matched cross-condition
is `j=0` (S) vs `j≠0` (J).)*

---

## §4 — Controls (each must fire; each declared AS a control)

| id | control | must produce |
|---|---|---|
| **PLANT-POS** | inject `ρ'(c)=` an admissible odd character pattern × empirical magnitudes | `T` flags `χ₀` below the permutation floor (energy ≈72% ≫ ≈6% detectable ⇒ >10× margin) |
| **PLANT-NEG** | empirical signed values placed on the classes at random (no character) | `T` within band — the marginal alone manufactures no spike |
| **C-PERM** | the signed-value permutation null (§2.4) | exact p-value; own mean rank ≈ ½ |
| **C-JZERO** | full statistic on stratum **J** (`j≠0`) | null if structure is `j=0`-specific; positive ⇒ re-type as generic |
| **C-ODD** | verify `V(−a)=−V(a)` at every cell | holds (forced) — if it fails, the enumeration is wrong. Instrument check |
| **C-CROSS** | `V(a)` vs the record's independent `V₁` instrument | exact agreement |
| **C-NOFLOAT** | `check_no_float.sh` over signal-path files | passes before any cell |
| **C-FORCED** | reconfirm `M=nI−J` and `Σ\|V\|²=n(n−1)` at one prime | agreement. ⚠ FORCED ⇒ instrument checks, NOT evidence |

⚠ **NOT a control:** any claim a fired `χ*` "leaks the scalar." `V(a)` is a complete sum over the whole
group indexed by the frequency `a`; it holds no single secret. A bit-leak is a **downstream
disjoint-construction** test (feature from a public `[d]G`, target `=d`), reported nowhere here.

---

## §5 — Pre-committed readings (before any structural read)

| outcome | pre-committed conclusion |
|---|---|
| `T(p)` within the permutation band at **every** S prime | the signed arrangement is **structureless beyond the forced `μ₃`+odd symmetries at this scale** — report the concentration bound WITH power + scope; **not** "no structure." Next probe: the additive/short-scalar arrangement, or the 2-pt statistic `(ρ_a,ρ_{ab})` |
| an admissible `χ*` fires on S | **NAME it** (order, conductor, `ord(χ*)\|`small `ℓ`?). Characterized handle, `[EMPIRICAL — SEEN-DATA]`, **not** leakage. Follow-up: same `χ*` across primes (a law) or per-prime (noise)? **Reproduce the count** before naming |
| fires on S but not J | `j=0`/CM-specific structure. Fires on both ⇒ generic, re-type |
| any PLANT fails, or C-ODD/C-CROSS/C-NOFLOAT fails | **halt.** Instrument broken; no cell reported |
| budget exhausted | ABSTAIN on remainder, completed count stated |

**Falsification (once):** `T(p)` within the signed-value permutation band at every S prime refutes "the
arrangement is multiplicatively structured" at this scale/power. **Output = a characterization or a
bounded magnitude, never a verdict on the avenue** ([[feedback_anomaly_drill_protocol_2026_07_17]]).

---

## §6 — Secondary (reported, never promoted)

- **Hyp II readout:** spectrum **shape** `{|V̂(χ)|²}` — participation ratio / flatness / residual mass
  outside the lowest-order admissible characters ("coercivity"). A derived readout of the same
  computation (§0.5).
- **Multiplicativity** `V(a)V(b)/V(ab)` exact residue pattern in `ℤ[ζ_n]`.
- `S_y=max_a|V(a)|/√p` per prime, exact, as a cap cross-check.

---

## §7 — Scope

- **Scale banner.** Cells at `p≈10³`; secp `2²⁵⁶`. A null is a scoped magnitude bound; a positive is a
  characterized handle — **neither transfers to secp without a proof.**
- Does **not** test the 120° law, the cap, Stickelberger, or leakage. Inherits **no** unverified citation.

---

## §8 — Status

**Arms HELD.** Re-issued for `experiment-designer` re-sign-off of the two fixes (object on the signed
odd-`μ₃`-trivial support; signed-value permutation null). Deviations →
`PREREG_twist_orbit_spectrum_v2_DEVIATIONS.md` as they occur.
