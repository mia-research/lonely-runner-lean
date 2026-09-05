# RESULT — the m-law is a THEOREM at `p ≡ 7 mod 12` (secp's class): the last empirical link `m = Re(S)/p` is PROVED by Lefschetz point counting, and `b₁ = 0` falls out as a by-product

*2026-09-02. Discharges the open item raised the same morning in
`RESULT_jacobi_sign_law_proved_secp_class_v1.md`'s correction header — that `m = Re(S)/p` was a
**firing control** (`RESULT_mu4_eigenvalue_individual_v1.md`: 155/155 OOS + 30/30 in-sample), never
derived. Script `mlaw_lefschetz_bridge_v1.py` (+ `.log`), pure stdlib, exact integer; `S ∈ Z[i]` so
even `Re(S)` is exact. **No leakage / ECDLP / keyspace claim.***

---

## 0. The chain, now complete

At `p ≡ 7 mod 12` (`= p ≡ 3 mod 4` and `p ≡ 1 mod 3`) — **secp's class** — with `B ∈ F_p^*`:

| # | statement | status |
|---|---|---|
| 1 | `b₁ = 0` — the "μ₄ argument" | **`[PROVED]` §1, and *derived* here, not assumed** |
| 2 | `a_new(2) = −2·Re(S)`, `S = Σ_{x∈F_{p²}} χ₄(x³+B)` | **`[PROVED]` §2** |
| 3 | `b₂ = Re(S)`, hence **`m = b₂/p = Re(S)/p`** | **`[PROVED]` §3** — *this was the firing control* |
| 4 | `S = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)` | `[PROVED]` — `..._m_law_v4` §1, re-verified first-hand 2026-09-02 (`mlaw_s1_firsthand_check_v1.py`, 14 primes exact) |
| 5 | `J(χ₃,χ₄) = −p` at `p ≡ 1 mod 3` | `[PROVED]` 2026-09-01 (`RESULT_jacobi_sign_law_proved_secp_class_v1.md`) |

> ### ⇒ **`m = −2` if `B` is a cubic residue mod `p`, `m = +1` otherwise. THEOREM.**
> ### And `m` names all four Frobenius eigenvalues of `A_new` via `z⁴ + m z² + 1 = 0`.

This is law **H2** of `RESULT_mu4_eigenvalue_individual_v1.md`, previously `[EMPIRICAL]` on 26 OOS
primes. It is now proved, and the proof is an **identity in `p`** — **scale-immune**, so it covers
`p = 2²⁵⁶`. At secp, `B = 7` is a cubic residue iff `7^{(p−1)/3} ≡ 1`; the corpus records `m = 1` at
secp, i.e. `7` is a cubic non-residue there.

---

## 1. `b₁ = 0`, derived `[PROVED]`

`C : w⁴ = f(x)`, `f = x³+B`. Since `gcd(4,3) = 1`, `C` is smooth of genus `3` with **exactly one**
point at infinity. The map `(x,w) ↦ (x, w²)` sends `C → E : y² = x³+B`, so by Poincaré reducibility
`Jac(C) ~ E × A_new` with `dim A_new = 2`, and traces add: **`a_C(k) = a_E(k) + a_new(k)`** for all `k`.

Over `F_p` with `p ≡ 3 mod 4`: `gcd(4, p−1) = 2`, so `w ↦ w⁴` and `w ↦ w²` have **identical** image
and fibre sizes, giving `#C(F_p) = #E(F_p)`, hence `a_C(1) = a_E(1)` and **`a_new(1) = 0`**. By the
Weil functional equation the characteristic polynomial of Frobenius on `A_new` is
`t⁴ + b₁t³ + b₂t² + b₁p t + p²`, whose trace is `−b₁`. Therefore **`b₁ = 0`**. ∎

*This is the "μ₄ argument" that `RESULT_mu4_eigenvalue_individual_v1.md` §1 invokes without proof.
It is one line of point counting.*

## 2. `a_new(2) = −2·Re(S)` `[PROVED]`

For any finite field `F_Q` with `4 | Q−1`, and every `u ∈ F_Q` **including `u = 0`**:

> `#{w ∈ F_Q : w⁴ = u} = Σ_{χ⁴ = ε} χ(u) = 1 + χ₂(u) + χ₄(u) + χ̄₄(u)`

(at `u=0` both sides are `1`, since nontrivial `χ` vanish at `0`). Summing over `x ∈ F_Q`:

```
#C_aff(F_Q) = Q + Σ_x χ₂(f(x)) + S + S̄ = Q + Σ_x χ₂(f(x)) + 2·Re(S)
```

and `#C(F_Q) = #C_aff(F_Q) + 1` (one point at infinity). The same display for `E` gives
`#E_aff(F_Q) = Q + Σ_x χ₂(f(x))`, i.e. `Σ_x χ₂(f(x)) = −a_E`. Hence
`a_C = a_E − 2Re(S)`, and by the additivity of §1, **`a_new = −2·Re(S)`**. Taking `Q = p²`
(where `4 | p²−1` always, so `χ₄` exists — the reason the whole construction lives over `F_{p²}`):
**`a_new(2) = −2·Re(S)`**. ∎

## 3. `b₂ = Re(S)` `[PROVED]`

`a_new(2) = Σ_i α_i²` where `α_i` are the four Frobenius eigenvalues over `F_p`. Newton:
`Σα_i² = e₁² − 2e₂ = b₁² − 2b₂ = −2b₂` by §1. Comparing with §2:

> `−2b₂ = −2·Re(S)` ⟹ **`b₂ = Re(S)`** ⟹ **`m = b₂/p = Re(S)/p`**. ∎

---

## 4. Verification (exact integer, `mlaw_lefschetz_bridge_v1.py`, `p ≡ 3 mod 4`, `p < 140`, `B=7`)

| arm | check | result |
|---|---|---|
| **A1** | `#C(F_p) = #E(F_p)` (§1 ⇒ `b₁ = 0`) | **all primes** |
| **A2** | `#C_aff(F_{p²}) = p² + Σχ₂(f) + 2Re(S)` (§2's display, brute-force count vs formula) | **all primes** |
| **A3** | `#{w : w⁴=u} = 1+χ₂+χ₄+χ̄₄` for **every** `u ∈ F_{p²}`, `u=0` included | **all primes** |
| **A4** | `p ∣ Re(S)`, and `m = Re(S)/p` matches the measured law | **all primes** |
| **A5** | `Im(S) = 0` | **all primes** — *not needed by the proof; recorded because it is why writing `Re(S)` costs nothing* |

`S` is accumulated in `Z[i]` (χ₄ takes values in `μ₄`), so `Re(S)` is an exact integer and no float
enters any verdict.

## 5. Grades, citations, scope

| item | grade |
|---|---|
| §1 `b₁ = 0` | **`[PROVED — elementary point counting]`** |
| §2 `a_new(2) = −2Re(S)` | **`[PROVED]`**, modulo the three standard facts below |
| §3 `m = Re(S)/p` | **`[PROVED]`** |
| **H2 at `p ≡ 7 mod 12`: `m = −2` / `+1` by cubic class of `B`** | **`[PROVED]`** — was `[EMPIRICAL, 26 OOS primes]` |
| H1 at `p ≡ 11 mod 12`: `m = 2` | still **`[EMPIRICAL]`** — §1–§3 apply, but step 5 (`J = +p`) is unproved there |

> ### `[PROVISIONAL — citation-verifier unavailable]`
> Attempted 2026-09-02; the project agents are not loaded in this session. Three standard facts are
> load-bearing and are **named, not hidden**: (i) **Weil/Grothendieck–Lefschetz** for curves,
> `#C(F_Q) = Q + 1 − a_C`; (ii) `C : w⁴ = f`, `deg f = 3`, `gcd(4,3)=1` is **smooth of genus 3 with a
> single point at infinity**; (iii) **Poincaré reducibility** giving `Jac(C) ~ E × A_new` and hence
> additivity of traces. All three are textbook, and (i)+(ii) are *witnessed numerically* here (A2/A3
> would fail if the point-at-infinity count or the trace formula were wrong). Per CLAUDE.md §2a: tag
> in the grade slot, self-audit here, gate recorded owed, **no other claim promoted on this file.**

**What is NOT claimed.** Nothing about `p ≡ 11 mod 12` beyond what §1–§3 give (the sign of `J` there
is still empirical). Nothing about the *other* m-values `{−1, 0}` in the support — they do not occur
at `p ≡ 3 mod 4` for this family, which §1–§3 explain but which is not separately audited here.
**Nothing about leakage, keyspace, or ECDLP:** this is a statement about the Frobenius eigenvalues of
an abelian surface, and it neither is nor implies a statement about recovering `d`.
