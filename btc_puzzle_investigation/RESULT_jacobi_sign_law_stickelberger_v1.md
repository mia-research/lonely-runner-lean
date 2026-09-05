# The `J(χ₃,χ₄)` sign law — CLOSED, both halves, by Stickelberger + two congruences

**Date:** 2026-07-25 · Spec: `VERIFY_SPEC_jacobi_stickelberger_v1.md` (frozen before any cell was
computed) · Script: `scripts_bridge_programme/jacobi_stickelberger_v1.py`, log `…_v1.log`.
Exact integer arithmetic throughout; `ℤ[ζ₁₂] = ℤ[x]/(x⁴−x²+1)` as 4-vectors of Python `int`.
No float anywhere in the signal path.

**No leakage, key-recovery or ECDLP claim.** See §6.

---

## 1. The result

> **Theorem.** Let `p ≡ 3 mod 4`, `q = p²`, and let `χ₃, χ₄` be *any* characters of `F_q^*` of order
> 3 and 4. Then
> ```
>   J(χ₃,χ₄) = −p   if p ≡ 1 mod 3   (p ≡ 7 mod 12 — secp's class)
>   J(χ₃,χ₄) = +p   if p ≡ 2 mod 3   (p ≡ 11 mod 12)
> ```
> **`[PROVED — modulo (D2); (D2)'s citation is UNVERIFIED, see §4]`**

This closes the gap `RESULT_jacobi_sign_law_semiprimitive_v1.md` §5 left open, **and re-proves its §4
by a different route.** The `p ≡ 7 mod 12` half was the one that mattered: it is secp's class.

## 2. The proof

Write `m = 12`, `M = (q−1)/12`, and take `χ₃ = ω^{−4M}`, `χ₄ = ω^{−3M}` for the Teichmüller character
`ω` attached to a prime `𝔭` of `ℤ[ζ₁₂]` over `p`. Since `p ≡ 7 mod 12` has order 2 in `(ℤ/12)^*`,
`p` has `f = 2`, `g = 2` in `ℚ(ζ₁₂)`; the decomposition group is `{1,7}`, so `t = 1,7` name one prime
and `t = 5,11` the other.

**(D1)** Each of the four conjugates `σ_t(J) = J(χ₃^t, χ₄^t)` is a Jacobi sum of nontrivial characters
with nontrivial product (order 12), so `|σ_t(J)| = √q = p` for all four.

**(D2)** *(the one external input)* Stickelberger's valuation formula for Jacobi sums:
`v_𝔭(J(ω^{−a},ω^{−b})) = [s(a)+s(b)−s(⟨a+b⟩)]/(p−1)`, `s` = base-`p` digit sum on `[0,q−1)`,
`v_𝔭(p) = 1`; conjugates via `v_{σ_t^{−1}𝔭}(J) = v_𝔭(J(χ^t,ψ^t))`.

**(D3) — the digit computation.** With `a = 4M`, `b = 3M`, `a+b = 7M`, put `d = (p−1)/3`,
`e = (p+1)/4`. For `p ≡ 7 mod 12`:

- `4M = (p²−1)/3 = d·(p+1) = d·p + d` ⇒ `s(4M) = 2d = 2(p−1)/3`.
- `3M = (p²−1)/4 = (p−1)e = (e−1)p + (p−e)` ⇒ `s(3M) = p−1`.
- `d − e = (p−7)/12 =: k ≥ 0`, so `4M + 3M` **carries**: `7M = (d+e)p + k` with
  `d+e = (7p−1)/12 < p` ⇒ `s(7M) = (7p−1)/12 + (p−7)/12 = 2(p−1)/3`.
- `s(M) = 2(p−1)/3` likewise.

Hence `v_{t=1} = [2(p−1)/3 + (p−1) − 2(p−1)/3]/(p−1) = 1`. The other three `t` follow from the same
four quantities via the complement identity `s(N) + s((q−1)−N) = 2(p−1)`:
`t=5 → (8M,3M,11M)`, `t=7 → (4M,9M,M)`, `t=11 → (8M,9M,5M)`, each giving **`v_t = 1`**.
*(`t=1` and `t=7` agree, as they must — same prime. That coincidence is a self-check, not an
independent datum.)*

> ⇒ **`(J) = 𝔭₁𝔭₂ = (p)` as ideals of `ℤ[ζ₁₂]`.**

**This is the step `π²` dies at**, and it is the step Frobenius could not reach: `(π²)` is
`𝔭^2` for a single prime, not `𝔭₁𝔭₂`. §5 of the predecessor was right that the forced facts were
insufficient — they were the *wrong kind* of fact. The ideal, not the field of definition, separates
`p` from `π²`.

**(D4)** `(J) = (p)` makes `J/p` a unit of `ℤ[ζ₁₂]`; by (D1) all four of its archimedean absolute
values are 1; by Kronecker it is a root of unity. So **`J = ζ·p` with `ζ ∈ μ₁₂`**. Write `ζ = i^α ω^β`.

**(D5) — mod the prime above 2 kills `β`.** In `ℤ[ζ₁₂]`, 2 has `e=2, f=2`, residue field `F₄`, and
`i ≡ 1` there (`i²=−1=1`, so `(i−1)²=0`). Therefore, reducing the defining sum termwise,
```
J ≡ Σ_{x≠0,1} χ₃(x)·1 = (Σ_{x≠0} χ₃(x)) − χ₃(1) = 0 − 1 = −1   (mod 𝔮₂).
```
`p` is odd so `p ≡ 1`, giving `i^α ω^β ≡ 1`, i.e. `ω^β ≡ 1` in `F₄^*`. As `ω` has order 3 there,
**`β = 0`** — so **`J = ±p` or `±ip`, and in particular `J` is fixed by the `μ₃`-part.**
Combined with (D6) below this is the **rationality** the predecessor named as the whole remaining gap.

**(D6) — mod the prime above 3 fixes `α`.** In `ℤ[ζ₁₂]`, 3 has `e=2, f=2`, residue field `F₉`, and
`ω ≡ 1` there. Reducing termwise the other way (`y = 1−x`):
```
J ≡ Σ_{y≠0,1} χ₄(y) = (Σ_{y≠0} χ₄(y)) − χ₄(1) = 0 − 1 = −1   (mod 𝔩₃).
```
`i` has order 4 in `F₉^*`, so `i² = −1`.
- `p ≡ 1 mod 3` ⇒ `i^α ≡ −1` ⇒ `α ≡ 2 mod 4` ⇒ `ζ = −1` ⇒ **`J = −p`**.
- `p ≡ 2 mod 3` ⇒ `−i^α ≡ −1` ⇒ `α ≡ 0 mod 4` ⇒ `ζ = +1` ⇒ **`J = +p`**. ∎

**Neither (S) nor Frobenius is used anywhere.** The proof is uniform in the two residue classes — the
`p mod 3` split enters only at the last line, through `p mod 𝔩₃`.

## 3. Verification — spec `VERIFY_SPEC_jacobi_stickelberger_v1.md`, all criteria frozen in advance

| id | check | result |
|---|---|---|
| **C1** | exact `J` over `F_{p²}`, **28 primes** `p ≡ 3 mod 4` below 260, all 4 character pairs | **PASS — 0 failures** |
| **C2** | `\|J\|² = q` exactly *(forced — instrument validation only)* | **PASS** |
| **C3** | Stickelberger predictor vs **directly computed** ideal factorization in `ℤ[ω]` | **PASS — `(1,1)` in every split cell** |
| **C4** | closed-form digit lemmas vs direct base-`p` digit sums, **4807 primes** below `10⁵` | **PASS — 0 mismatches** |
| **C5** | the (D5)/(D6) congruences `J ≡ −1` *(forced)* | **PASS** |

**★ Counting honestly (drill rule: count only unforced hits, and reproduce the count).**
The run performed **112 evaluations = 28 primes × 4 character pairs**. **The information unit is 28,
not 112**: the four pairs `(χ₃^u, χ₄^w)` are Galois conjugates of one another, so once `J` is rational
their agreement is forced. What their agreement *does* test — non-vacuously — is **rationality itself**,
which was the open question; so it is reported as a witness for (D5)+(D6), not as ×4 evidence for the
value. **14 primes in each residue class.** C4's 4807 primes check *my algebra in (D3)*, not anything
about curves; it is a proof-step check and carries no independent weight.

### Firing controls — all five fire

Recorded because the predecessor was correctly criticized for a `43/43` from an instrument never shown
able to reject.

| control | result |
|---|---|
| **FC1** discrimination: same code at `p ≡ 1 mod 4` (hypothesis fails there) | **FIRES** — `0/24` cells return `±p`; not a constant-output artifact |
| **FC2** corrupted non-multiplicative character | **FIRES** — `\|J\|²=q` fails `6/6` |
| **FC3** sign-flipped rule | **FIRES** — agrees `0/28`; a wrong sign would have been caught |
| **FC4** predictor is not a constant: classical cubic `J(χ₃,χ₃)/F_p` | **FIRES** — returns `(0,1)` not `(1,1)`, and matches the direct factorization at `p=7,13,31,43,61,67` |
| **FC5** planted `J := π²` (the §5 competitor, exhibited) | **FIRES** — factors as `(2,0)`, rejected by C3 at all 6 primes |

**FC4 is the load-bearing control**: it is what shows (D2)'s normalization is the right one, by making
the predictor reproduce a *known non-trivial* answer rather than the constant the theorem wants.
⚠ **Scope of C3/FC4:** the pairing of the abstract prime `𝔭_t` with the concrete `π` found by search
is not pinned down by the code, so C3 compares the **multiset** of valuations. That is exactly what
`(J) = (p)` requires, and nothing more is claimed.

### Scale

`p mod 12` and two base-`p` digits are the only inputs, and **neither grows with `p`**. At secp's own
`p = 2²⁵⁶ − 2³² − 977`, computed directly (not extrapolated):

```
p mod 4 = 3    p mod 3 = 1    p mod 12 = 7
closed-form digit lemmas match : True
Stickelberger profile (v_1,v_5,v_7,v_11) = (1, 1, 1, 1)   ⇒  (J) = (p)
⇒  J(χ₃,χ₄) = −p  at secp
```

## 4. ⚠ The one debt — and it is not discharged

**(D2) is `[UNVERIFIED CITATION]`.** The `citation-verifier` pass launched for Stickelberger's Jacobi
valuation formula **died on a session limit and produced no artifact** — the *third* citation-verifier
failure on this project (Lemmermeyer Ch. 7 twice, now this). No primary text has been opened.

What stands in for it: **FC4**, which settles the normalization *by arithmetic* — the predictor
reproduces the classical cubic case's `(0,1)` and matches an independent exact factorization. That is
real evidence about the formula I wrote down, and it is **not** a citation. Specifically unverified:
whether the standard sources state (D2) for `m = 12` (**not** a prime power) and `f = 2`, or only for
`m` an odd prime and/or `f = 1`. **If a source restricts to prime-power `m`, the proof needs a
different reference, not a different argument.**

⇒ The theorem's tag is **`[PROVED — modulo (D2), citation unverified]`** and stays there. Do not cite
it as `[PROVED]` unqualified. **The literature item on the ledger stays OPEN and now has a named,
scoped target**, which is an improvement over "Lemmermeyer Ch. 7, somewhere":
> *Stickelberger's factorization of Jacobi sums, in the form `v = [s(a)+s(b)−s(a+b)]/(p−1)`, for
> composite `m` and `f > 1`.* Candidates: Ireland–Rosen 2nd ed. Ch. 14; Lang *Cyclotomic Fields* Ch. 1;
> Washington Ch. 6; Berndt–Evans–Williams *Gauss and Jacobi Sums* Ch. 11.

## 5. Ledger effect

| item | before | after |
|---|---|---|
| `J` sign, `p ≡ 11 mod 12` | `[PROVED — modulo (S)]`, (S) citation unverified | **`[PROVED — modulo (D2)]`** — re-proved; **the (S) dependency is GONE** |
| `J` sign, `p ≡ 7 mod 12` | `[EMPIRICAL]`, open; re-typed to "prove `J` rational"; `π²` competitor live | **`[PROVED — modulo (D2)]`**; `π²` killed by the ideal, not by the field |
| **`m = 1` at secp** | **`[CONDITIONAL]`** | **`[PROVED — modulo (D2)]`** |
| (S), the semiprimitive Gauss-sum evaluation | load-bearing, citation unverified | **no longer load-bearing** for the `m`-law; keeps its own `[VERIFIED 43/43]` standing |
| literature debt | "Lemmermeyer Ch. 7", unscoped | **re-scoped to (D2)**, still OPEN, `citation-verifier` still owed |

**On `m = 1`:** `RESULT_jacobi_closed_form_m_law_v4.md` §2 names the `J` sign law as *"the single
remaining gap"*, and §4 records the secp branch as `[CONDITIONAL on §2]` with *"Proving §2 promotes it
to `[PROVED]`"*. §2 is now proved, so the promotion is the one that file pre-committed to — not a new
inference drawn here. The v4 ERRATUM stands untouched: `m = 1` denotes eigenvalues
`√p·{ω, ω², ζ₆, ζ₆⁵}` (primitive 3rd/6th roots, orders `[3,3,6,6]`), **not** `√p·{±ζ₁₂,±ζ₁₂⁵}`.
This result changes the grade of `m = 1`; it does not touch which root system `m = 1` names.

## 6. What this is NOT

- **No ECDLP, leakage, or key-recovery content.** `m` is a CM/quantum-number label on the Frobenius
  eigenvalues of a supersingular abelian surface. Pinning it extracts no bit of any scalar `d` and
  approaches no such extraction. Public data only.
- **No novelty claimed, and novelty is specifically DOUBTED.** Jacobi sums over `F_{p²}` for
  subfield-trivial quartic against norm-lifted cubic characters are the classical
  semiprimitive/uniform-cyclotomy regime, and evaluating them is exactly what Stickelberger is *for*.
  The predecessor recorded **four un-checked-prior-work misses in one session**; the base rate says
  this is the fifth. Treat §1 as a *re-derivation* until the sweep in §4 says otherwise.
- **Not a closure of anything empirical.** This is a statement about `J`, proved. It does not bear on
  any of the open frontiers, and no frontier status changes.
