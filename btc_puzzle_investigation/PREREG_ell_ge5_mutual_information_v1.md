# PREREG — ℓ≥5: does ANY dependence link `χ_ℓ(p mod n)` and `χ_ℓ(n mod p)`? (mutual-information probe)

**Date:** 2026-07-25 · **Frozen BEFORE any data.** Exact integers; every verdict from an exact
permutation count (no float threshold). Attacks the **pre-committed blind spot** of
`RESULT_bridge_dichotomy_v1.md` §3/§6 and `RESULT_cubic_sextic_bridge_v1` §6.

## 0. The blind spot this is designed to defeat

D3 tested `A := [p is an ℓ-th power residue mod n]` vs `B := [n is an ℓ-th power residue mod p]` — a
**2×2** table — and found `A ⊥ B` for ℓ=5,7,11,13. Its own pre-committed caveat: *"No bridge with a
non-uniform correction is detectable by a generator-free 2×2 association at this N."* The 2×2 collapses
the ℓ-valued exponents `j,k` (`χ_ℓ(p mod n)=ζ_n^j`, `χ_ℓ(n mod p)=ζ_p^k`) to `[j=0],[k=0]` and reads
only the `(0,0)` cell. A dependence living in the **off-diagonal** cells — e.g. `j = k+c` with `c`
uniform in the margin but **correlated with `k`** — leaves `P(j=0∧k=0)=P(j=0)P(k=0)` yet is a real
relation. **The 2×2 is blind to it; mutual information is not.**

## 1. The statistic, and why it is choice-free (the load-bearing claim)

**Primary:** `Î(j;k)` — plug-in mutual information of the joint `(j,k)` over `(ℤ/ℓ)²`.

`j` needs a chosen primitive ℓ-th root `ζ_n∈F_n` (`ζ_n := g_n^{(n−1)/ℓ}`, `g_n` least primitive root);
relabeling `ζ_n→ζ_n^a` (`a∈(ℤ/ℓ)*`) sends `j→a·j (mod ℓ)`, a **bijection** of the alphabet. **MI is
invariant under any bijection of either variable's alphabet**, so `Î(j;k)` does **not** depend on the
choice of `ζ_n` or `ζ_p`. This is what lets it beat the 2×2 while staying choice-free.

**This claim is MACHINERY and will be VERIFIED in-script (control M0):** compute `Î` under `(ζ_n,ζ_p)`
and under `(ζ_n²,ζ_p³)`; **they must be bit-identical**, else the statistic is not choice-free and
**everything is void.**

**Null:** permutation. Shuffle `{k_i}` against `{j_i}`, recompute `Î`, `10^4` times; exact
`p = (#{Î_perm ≥ Î_obs} + 1)/(shuffles + 1)`. Plug-in MI has a positive finite-sample bias
`≈ (ℓ−1)²/(2N)`; the permutation null carries the **same** bias, so it cancels — the null is the
correct reference, not `Î=0`.

## 2. Controls (each pre-committed; failure of a starred one voids the run)

| # | control | required |
|---|---|---|
| **M0★** | `Î` invariant under `ζ→ζ^a` relabeling | **bit-identical**, else statistic not choice-free ⇒ VOID |
| **M1★ synthetic-positive** | inject a **uniform-marginal but dependent** coupling on `(ℤ/ℓ)²` (a cyclic Latin-square shift with noise) whose 2×2 `(0,0)` cell is exactly `P(j=0)P(k=0)` | the pipeline **must** flag `Î>null` here — this **proves the method sees what the 2×2 cannot**; if it fails, the probe has no power against its target and is VOID |
| **C+ positive** | ℓ=3, D=−3 (bridge known, `P(c₃=0)=5/9`) | `Î ≫ null` |
| **C− negative** | ℓ=3, D=−11 (w=2, no bridge) | `Î ≈ null` |
| **C−r random base** | replace `p` by seeded random base, every arm | `Î ≈ null` |

## 3. Arms (frozen)

- **Main:** ℓ ∈ {5,7,11,13}, D=−3, `N` as large as `p<2^30` sampling gives (target ≥ 8000).
- **Splitting axis** (recorded, secondary): ℓ=5,11 are **inert** in ℤ[ω] (`ℓ≡2 mod 3`); ℓ=7,13 are
  **split** (`ℓ≡1 mod 3`). If a signal appears, is it keyed to this? Pre-committed as *observational*,
  not a verdict.
- **Cross-D:** ℓ=5 at D ∈ {−11,−19,−43} — does any ℓ≥5 dependence depend on the discriminant?

## 4. Pre-committed interpretation (frozen BEFORE data)

- **`Î_arm > null` (NEG clean, M0/M1 pass):** a dependence exists that the 2×2 missed ⇒ the blind spot
  was hiding structure. Output = **characterize** it (which cells carry it; is `j−k` or `j·k^{−1}`
  concentrated under some alignment), **never** a "bridge proved" verdict. Follow-up under EXPLORATORY.
- **`Î_arm ≈ null`:** report as a **BOUND**, with these exact words: *"`j` and `k` are independent to
  the resolution `ΔÎ` at this N — stronger than the 2×2 null (which only bounded the `(0,0)` cell), but
  it does NOT establish that no ℓ-th power reciprocity exists in `ℚ(ζ_ℓ)`."* Reason, stated now: the
  **general power-reciprocity law (Artin/Hilbert)** operates on symbols in `ℚ(ζ_ℓ)` with a **choice of
  prime ideals** over `p,n`; projecting to the *rational* exponents `(j,k)` via a fixed rational root
  can wash an ideal-level relation into rational independence. A rational-MI null is scoped to the
  rational exponents, not to `ℚ(ζ_ℓ)`.

## 5. Falsification

- M0 or M1★ fails ⇒ **VOID** (statistic not choice-free, or has no power against its target).
- C+ does not exceed null ⇒ the statistic can't see the *known* bridge ⇒ **VOID**.
- An arm's `Î` exceeds null at the C+-calibrated scale with NEG controls clean ⇒ H-"ℓ≥5 fully null" is
  **FALSE**; the blind spot hid structure.

## 6. Reach limit, stated before the run

Full `Î` needs `~ℓ²` populated cells ⇒ `N ≫ ℓ²`. **secp's own factors `149, 631, …` are out of reach**
for MI (`149² ≈ 22000` cells); only the boolean 2×2 (already D3) or a 1-dim contrast is testable there.
This probe covers small ℓ; the large-ℓ secp factors remain a **separate, harder** question.

## 7. Prior art / scope

This is **exploration** (mapping dependence), not a novelty claim, so it does not trip the
novelty gate — **but** any positive, structured finding would require the literature sweep
(`AUDIT_citation_verification_v1` §5.3: Lemmermeyer *Reciprocity Laws* Ch. 7 covers exactly the general
power-reciprocity law) before being called new. The general power-reciprocity law is **classical**;
nothing here is claimed original. Public data only (`p,n,t`); no leakage/ECDLP content.
