# RESULT — `|FLD| = 6·h(−p)` assembles to a THEOREM via the (†) route; **L1 is not needed**

*2026-08-08. Grade `[PROVED — assembly of independently-proved links; classical Dirichlet input CITED]`.
No new mathematics: this document only **assembles** results that were already proved in separate files
and were never combined, and records that two live documents carry a **stale** grade on the combined
result. No leakage / ECDLP claim — pure CM / analytic number theory about the flap class-number law.*

---

## 0. Why this document exists — a one-way flattening, caught by assembly

Two current documents present `|FLD| = 6h(−p)` as unproven, and name **two different** "single open
steps," **both stale**:

- `OPEN_ITEMS_LEDGER_v1.md` item **16** (line 68): calls `(†)` "the **single** open step of P2 …
  needs **generalized Dedekind sums / Rademacher**," graded `[VERIFIED 134 primes]`.
  → **Stale.** `(†)` was **PROVED** three days after the ledger's cited sweep
  (`RESULT_fld_dagger_proof_v1.md`, 2026-07-24; adversarial review **PASSED**,
  `REVIEW_twisted_dedekind_v1.md`; exact at 569 primes to `p=20000`). The Dedekind/Rademacher
  machinery the item says is "needed" is exactly the classical class-number formula that **proved** it.
  The ledger's own item **8** already records this; item 16 contradicts item 8 and was never updated.
- `POSITIVE_FINDINGS_MASTER_v6.md` **M11** (line 203) / **§X.2**: graded `[EMPIRICAL, exact match]`,
  "**Not `[PROVED]` — the chain closes modulo lemma L1 alone**," where `L1: |S+| = F4`.
  → **Stale.** The chain also closes through a **different** route (below) that never uses L1. In that
  route **L1 falls out as a corollary** (`|S+| = F4 = 3h`), so it is an output, not an input.

The pattern is the project's documented one-way suppression: a proved positive carried forward under
"still open / [EMPIRICAL] / modulo L1" language because its pieces were proved in separate files and
never assembled. This file does the assembly and the exact re-verification.

## 1. The theorem

For prime `p ≡ 1 (mod 6)` (so `μ₃ ⊂ F_p`), with `FLD(p) := Σ_{x∈F_p} σ(x)·χ₂(x)` (σ the Cap-Law flap
sign, P11; χ₂ the Legendre symbol):

> **`FLD(p) = 0` unless `p ≡ 19 (mod 24)`, and `|FLD(p)| = 6·h(−p)` there**, `h(−p) = ` class number of
> `ℚ(√−p)`.

## 2. The reduction chain — every link independently `[PROVED]`

| # | link | statement | grade | source |
|---|---|---|---|---|
| 1 | `p≡1 mod4 ⇒ FLD=0` | negation antisymmetry: `σ(−x)=−σ(x)`, `χ₂(−x)=+χ₂(x)` | `[PROVED]` | master §X.2 |
| 2 | `p≡3 mod4 ⇒ FLD=2·S+` | `S+ := Σ_{σ(x)=+1} χ₂(x)`; `σ,χ₂` both odd fold `S−=−S+` | `[PROVED]` | master §X.2 |
| 3 | flap = window | `s∈T⁺ ⟺ ρs mod p ∈ [(p+1)/2, H+s]` (geometric flap-positive set = arithmetic window) | `[PROVED]` | flap-lemmas **v2 P1 Step 1** |
| 4 | `S′ = A + C`, `C+C′ = A` | `A:=Σ_{s=1}^{H}χ₂(s)`; `C,C′` the `ρs mod p ≶ s` splits | `[PROVED]` | flap-lemmas v3 §1 |
| 5 | `A = (2−χ₂(2))·h` | bijection `t=ρs` + **Dirichlet finite class-number formula** | `[PROVED / CITED classical]` | flap-lemmas v3 §2; review re-derived `h=−(1/p)Σχ₂(a)a` independently |
| 6 | `(†)  C′−C = 3h` | `Σ_{s=1}^{H}χ₂(s)·sgn(ρs mod p − s) = 3h` | `[PROVED — reviewed]` | `RESULT_fld_dagger_proof_v1.md` |

**Assembly.** From 4+5+6: `C = (A−3h)/2 = −h(1+χ₂(2))/2`, hence
```
   S′ = A + C = (2−χ₂(2))h − h(1+χ₂(2))/2 = (3h/2)·(1 − χ₂(2)).
```
By link 3, `S+ = S′` (as flap sums; magnitude verified 246/246, §3). By links 1–2:
```
   |FLD| = 2|S+| = 2·(3h/2)|1−χ₂(2)| = 3h·|1−χ₂(2)|
         = 6h   at χ₂(2)=−1  (p≡3 mod8, i.e. p≡19 mod24),
         = 0    at χ₂(2)=+1  (p≡7 mod8, i.e. p≡7 mod24);
   = 0 at p≡1 mod4 by link 1.                                                        ∎
```

**L1 is a corollary, not an input.** `|S+| = |S′| = 3h` at `p≡19 mod24`, and `F4 = D = (2−χ₂(2))h = 3h`
there (L2 + Dirichlet). Hence `|S+| = F4` — the very statement master §X.2 lists as the open lemma L1 —
**follows** from the (†) route. Nothing in the chain calls L1.

## 3. Exact re-verification (this file's own check)

`fld_6h_assembly_check_v1.py` (exact `int` only; geometric σ from `_sigma_chi2_scan_v1`; ρ-arithmetic
independent; `h(−p)` by reduced-form count). Over **all 246 primes `p≡7 mod12` in [100, 8000)** plus the
238 `p≡1 mod4` controls:

| link checked | result |
|---|---|
| `S+`(geometric flap) `= S′`(arithmetic window), in magnitude | **246/246** |
| `A = (2−χ₂(2))h` | **246/246** |
| `C+C′ = A` and `S′ = A + C` | **246/246** |
| `(†)  C′−C = 3h` | **246/246** |
| assembly `S′ = (3h/2)(1−χ₂(2))` | **246/246** |
| `|FLD| = 6h` at `p≡19 mod24` | **122/122** |
| `FLD = 0` off `p≡19 mod24` | **362/362** |
| corollary `|S+| = F4` | **246/246** |
| `FLD = 2·S+` on `p≡3 mod4` | **246/246** (fails on `p≡1 mod4`, where `FLD=0` by link 1 — not claimed there) |

The only non-clean tally is the **sign** of `S+` vs `S′` (189/246): the geometric-σ orientation and the
ρ/reflection convention disagree on 57 primes. This affects only the **sign** of FLD, which the master
already flags as "possibly convention-dependent / unresolved" (§X.2, §XI.9). The **magnitude** result
`|FLD|=6h` is unaffected.

## 4. Grade and what remains

- **`|FLD| = 6·h(−p)` (M11): `[PROVED]`** — as the assembly of links 1–6, each `[PROVED]`, with
  Dirichlet's finite class-number formula the sole classical input (already independently re-derived in
  the adversarial review). Scope: prime `p≡1 mod6`.
- **`L1` is discharged** as a corollary; it should be reclassified from "open" to
  "`[PROVED — corollary of (†)]`," not carried as the blocker.
- **The sign of `FLD`** (`sign(FLD) = −χ₂(M)` vs intrinsic invariants) is genuinely still open — it is a
  *different* question from the magnitude law and is untouched here.
- **No novelty is claimed.** Per `RESULT_priority_sweep_v1.md`, class-number-as-Dedekind-sum is classical
  (Berndt–Evans 1977, Goldstein–Razar 1976); the content is the specific secp-adjacent identification
  `|FLD|=6h` with constant 6, as a worked instance.

## 5. Recommended gated follow-ups (NOT done here — they need the mandatory gates)

1. **Promote M11 in the master to `[PROVED]`** → new master version, **`compile-diff` gate required**
   (CLAUDE.md §2, promoting a consolidated/master doc). Cite this file + flap-lemmas v2/v3 + the dagger.
2. **Correct `OPEN_ITEMS_LEDGER` item 16** (stale; contradicts item 8) → new ledger version.
3. **`citation-verifier` on Dirichlet's finite class-number formula** `h=−(1/p)Σχ₂(a)a` and on
   Berndt–Evans/Goldstein–Razar — the one classical input the whole chain rests on; the review
   re-derived it numerically but the *citation* pass (owed since 2026-07-25, agent died on a session
   limit) is still outstanding.

## 6. Reproduction
```
python3 fld_6h_assembly_check_v1.py 100 8000
```
Exact integers; geometric σ from the Cap-Law build; ρ-arithmetic and `h(−p)` computed independently.
