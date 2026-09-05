# The bridge is CM-generated (bounded), and its correction collapses to `c₃ = s·(t−1)/3`

**Date:** 2026-07-24 · Pre-registered: `PREREG_bridge_mechanism_isolation_v1.md` (frozen before the run).
Scripts: `scratchpad/mechanism_isolation_v{1,2}.py`. Exact integers; verdicts from exact permutation
counts. Follow-on to `RESULT_bridge_dichotomy_v1.md` §6.

---

## 1. P1 — Mechanism isolation: CM, not shape

Every CM instance has `n − p = ±U` exactly. The **matched control** redraws an unrelated prime `p′` of
the same bit length and sets `n′ = p′ + Δ` using the **same `Δ` multiset**, keeping only prime
`n′ ≡ 1 mod 3` — breaking the CM tie and nothing else.

| | N | agree | E | ratio | perm p | power | control |
|---|---|---|---|---|---|---|---|
| **CM `D=−3, ℓ=3`** | 20000 | 3733 | 2269.3 | **1.645** | `1/20001` | `29.5σ` | clean |
| **matched `n−p=Δ`** | 17305 | 1950 | 1964.7 | **0.993** | `13949/20001` | `27.5σ` | clean |

> **(M1) The shape account is excluded as the dominant mechanism.** The elementary fact `n−p = ±U`
> does **not**, on its own, reproduce the association.

**Scoping of this null — stated as a bound, not an absence.** With `E = 1964.7`, the agreement count's
`sd ≈ 41.7`, so a 3σ excess is `≈ +125` agreements, i.e. **ratio `≈ 1.06`**. The control therefore
bounds any shape-generated association to **ratio `< ~1.06` at 3σ**, against the CM effect of `1.645`.
It does **not** establish that no shape effect exists, and it is scoped to: **30-bit primes, this `Δ`
multiset, this 2×2 statistic, `N = 17305`.** A residual shape contribution below ~6% of the
independence baseline is **not** excluded by this run.

## 2. P2 — the constant `5/9` survives; my derivation of it did **not**

The prereg required **all six** sub-claims, precisely to stop a right number rescuing a wrong model.

| sub-claim | result |
|---|---|
| (i) `s` uniform on `ℤ/3` | `6601/6704/6695` of 20000 — **see §4, do not treat as established** |
| (ii) `e(ν′)`, `e(π̄′)` each uniform | ✅ `6689/6639/6672`, `6639/6747/6614` |
| **(iii) `e(ν′) ⊥ e(π̄′)`** | ❌ **FALSE** — only **6 of 9** joint cells populated |
| (iv) `k ⊥ c₃` | ✅ `χ²(4df) = 3.45` |
| (v) `P(c₃=0) = 5/9` | ✅ `0.5524` (`z=−0.90`), `0.5488` (`z=−1.48`) |
| (vi) ratio `= 5/3` | ✅ `1.645`, `1.647` |

Per the pre-committed guard, **H-constant is NOT verified as stated.** The number is right; the reason
I gave for it was wrong. The forbidden cells were exactly `(0,2),(1,1),(2,0)` — those with
`e(ν′)+e(π̄′) ≡ 2` — and the `sum ≡ 1` count equalled the `s=0` count exactly. Chasing that gave the
true structure:

## 3. The replacement — three exact laws, `0` violations in `12000`

> **(E1)** `e(ν′) + e(π̄′) ≢ 2 (mod 3)` — one full coset is forbidden. **0/12000**
> **(E2)** `s = 0 ⟺ e(ν′) + e(π̄′) ≡ 1 (mod 3)` — biconditional. **0/12000**
> **(E3)** `e(π̄′) − e(ν′) ≡ (t−1)/3 (mod 3)` — **12000/12000**, and the primarizing unit's sign is
> `+1` in **all** 12000 instances (only `+ω^s`, never `−ω^s`, is ever needed).

**(E3) collapses the bridge's correction to arithmetic in `t` alone.** Since `c₃ = s·(e(π̄′)−e(ν′))`:

> ### `c₃ ≡ s · (t−1)/3 (mod 3)`
> No character evaluation, no primarized coefficients — just the primarization exponent `s` and
> `(t−1)/3 mod 3`. (`3 ∣ t−1` is forced, proved in `RESULT_cubic_sextic_bridge_v1` (B3).)

> **(E4)** `c₃ = 0 ⟺ (s = 0 **or** 9 ∣ t−1)` — **0/12000**.

Hence the **correct** derivation of the constant, by inclusion–exclusion on two events that test as
independent (`(T,T)` cell `1255` vs `1280.7` expected, `z=−0.76`):

```
P(c3=0) = P(s=0) + P(9 | t-1) - P(both) = 1/3 + 1/3 - 1/9 = 5/9,   ratio = (1/3 * 5/9)/(1/9) = 5/3
```

My original route (`1/3 + (2/3)(1/3)`) reaches `5/9` too — which is exactly why (v) and (vi) passed
while (iii) was false. **A passing number is not a passing model.**

## 4. A consistency flag I am not dismissing

`P(s=0)` and `P(9∣t−1)` both run **slightly below `1/3` in both independent samples**:
`s=0` at `6601/20000` and `3904/12000` → combined `10505/32000 = 0.3283`, **`z = −1.92`**.
This is not significant at any pre-set level and may be sampler-related (the four twists of one `p` are
not independent draws), but it is a **consistent-direction deficit across two samples**, and it is the
reason (v)/(vi) land `~1–1.5σ` low each time. **Uniformity of `s` is therefore NOT established**, and
`5/9` should be read as *"consistent with, to within `~1.5σ`, on two samples"* — not as verified exact.

## 5. P3 — the `h>1` gap, closed

`RESULT_bridge_dichotomy_v1` tested `w=2` only at `h=1`. All ten `h=2`, `D ≡ 5 mod 8` discriminants,
`ℓ=3`, `N ≈ 5000` each:

`D = −35, −51, −91, −115, −123, −187, −235, −267, −403, −427` → ratios **`0.96–1.02`**, every perm
`p ≥ 4005/20001`, **power `12.7–15.0σ`** against an Arm-1-sized effect, **all controls clean**.

> **(M2) H-dichotomy is keyed to `w`, not to class number** — bounded, at these `N`/power, to
> effects below ratio `≈ 1.08` (3σ) in each `h=2` family. Scoped to `h=2`; `h ≥ 3` untested.

## 6. Status of everything above

| item | grade |
|---|---|
| (M1) bridge is CM-generated, shape bounded `< ~1.06` | `[VERIFIED — bounded, scoped §1]` |
| (E1)(E2)(E3)(E4) | `[VERIFIED — 0 violations / 12000, 26-bit p]` |
| `c₃ = s·(t−1)/3 mod 3` | `[VERIFIED]`, implied by (E3) at `12000/12000` |
| `P(c₃=0) = 5/9`, ratio `5/3` | `[CONSISTENT, not verified]` — see §4 |
| (M2) `w`-keyed, not `h`-keyed | `[VERIFIED — bounded, `h=2` only]` |

**No originality claimed.** (E1)–(E4) are elementary consequences of the classical supplement
`χ_λ(ω) = ω^{(a+b+1)/3}` plus `3 ∣ t−1`; I derived them here because the first model was wrong, not
because they are believed new. `citation-verifier` **remains unrun** (ledger ★).

## 7. What stays open

- **§4's deficit.** Resolve by resampling **one twist per `p`** (independent draws) at `N ≥ 50000`; if
  `P(s=0)` stays low, `s` is not uniform and `5/9` needs restating.
- **(E1)–(E3) are verified, not proved.** They should follow from `μ(λ)=A+B`, `e=(μ+1)/3`, and
  `μ(π̄′)−μ(ν′) = μ(u(t−1))` with `3∣t−1`; that derivation is sketched but **not completed**.
- **Why the primarizing sign is always `+1`** (12000/12000) is unexplained.
- **The uniform-correction blind spot** (`RESULT_bridge_dichotomy_v1` §3) is untouched by this work.
- `h ≥ 3`, `ℓ ≥ 17` still untested.
