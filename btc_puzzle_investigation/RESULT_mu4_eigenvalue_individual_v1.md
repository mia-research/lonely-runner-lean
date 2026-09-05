# RESULT — the four Frobenius eigenvalues of `A_new`, individually: `m` is the quantum number, and an arithmetic condition names it

**Date 2026-07-20.** Executes `PREREG_mu4_eigenvalue_individual_v1.md` (frozen before the run).
Artifacts: `mu4_eigenvalue_individual_v1.py` / `.log`; deviations in
`PREREG_mu4_eigenvalue_individual_v1_DEVIATIONS.md`.
Object: `A_new` = new part of `Jac(C)`, `C : w⁴ = f(x)`, `dim A_new = 2` — the same surface as
`RESULT_mu6_cohomology_supersingular_v2.md`.

**What changed in the treatment.** The supersingularity result reports the four eigenvalues as a
*set property* ("all roots are `√p·ζ`", `m ∈ {−2,−1,0,1,2}`). This run treats each eigenvalue as an
individual: it names the exact rational angle of each of the four, and asks what arithmetic
condition on `(B, p)` selects it.

---

## 1. The individual eigenvalues, and what `m` is

At `p ≡ 3 mod 4` the μ₄ argument forces `b₁ = 0`, so `char(t) = t⁴ + m·p·t² + p²`. Substituting
`t = √p·z` gives `z⁴ + m z² + 1 = 0`: **the integer `m` names all four eigenvalues individually.**

| `m` | the four eigenvalues | angles `θ` (units of `π`) | order of `ζ` | minimal `k` with `π^k` scalar |
|---|---|---|---|---|
| `−2` | `√p·{1, 1, −1, −1}` | `0, 0, 1, 1` | 1, 2 | `k = 2`, `π² = +p·id` |
| `−1` | `√p·`primitive 12th | `±1/6, ±5/6` | 12 | `k = 6`, `π⁶ = −p³·id` |
| `0` | `√p·`primitive 8th | `±1/4, ±3/4` | 8 | `k = 4`, `π⁴ = −p²·id` |
| `1` | `√p·{ω, ω², −ω, −ω²}` | `±1/3, ±2/3` | 3, 6 | `k = 6`, `π⁶ = +p³·id` |
| `2` | `√p·{i, i, −i, −i}` | `±1/2` (doubled) | 4 | `k = 2`, `π² = −p·id` |

The last column is the individual-level content: `k(m)` is the smallest extension `F_{p^k}` over
which Frobenius becomes a scalar, i.e. over which `A_new`'s supersingular endomorphism structure is
fully defined. `k = 2` for `m = ±2`, `k = 4` for `m = 0`, `k = 6` for `m = ±1`. The angles are taken
by **table lookup on the integer `m`** — the v1 script's `QQbar` + `1e-9` root-finding path is banned
from this verdict path (prereg §8).

---

## 2. The measured law `[EMPIRICAL]`

Out-of-sample window, **strictly disjoint** from the `13 ≤ p ≤ 199` rows that generated the
hypothesis: `p ≡ 3 mod 4`, `200 < p < 500` (26 primes), `f = x³ + B`, `B ∈ {7, 2, 11}`.

> **H1 — `p ≡ 11 mod 12` ⇒ `m = 2`.** Eigenvalues `√p·{i,i,−i,−i}`.
> **42/42 rows, `K1 = 26` distinct configurations, zero violations.**
>
> **H2 — `p ≡ 7 mod 12` ⇒ `m = −2` if `B^((p−1)/3) ≡ 1` (cubic residue), else `m = 1`.**
> Eigenvalues `√p·{1,1,−1,−1}` versus `√p·{ω,ω²,−ω,−ω²}`.
> **36/36 rows, `K2 = 22` (pre-committed; script computed 26), zero violations.**

Null model (frozen in the prereg): `m` uniform on the in-sample CM support `{−2, 1, 2}`, independent
across **distinct configurations**, not rows. `3^−26 = 3.9e−13` (H1), `3^−22 = 3.2e−11` (H2). Both
clear the pre-committed adequacy bar `K ≥ 10`.

**The B-dependence fires within a fixed prime — this is what carries H2.** At 10 of the 12 primes in
the `p ≡ 7 mod 12` arm the three cubics do **not** share an `m`, and the cubic-residue symbol picks
the split correctly every time: `p=211 → (7,2,11) = (1,1,−2)`, `p=223 → (−2,−2,1)`,
`p=283 → (1,−2,1)`, `p=307 → (1,−2,1)`, `p=331 → (−2,1,1)`, `p=439 → (−2,−2,1)`, `p=499 → (1,−2,1)`.
No rule keyed to `p` alone can produce this. Mandated per-`B` breakdown of the `m = −2` cell:
12 rows, `{B=7: 6, B=2: 5, B=11: 1}` — the `B=11` corner rests on a single row.

**H2b (rider): does `m` depend on `B` only through the cubic character?** Only **3** configurations in
this window can test it (prereg expected 7). No violations. Reported as *consistent, K = 3*,
**below its own prereg's expectation and far below the `K ≥ 10` bar — not a confirmed independence.**

---

## 3. Controls (all fired before any verdict was read)

| control | what it does | outcome |
|---|---|---|
| **Firing control** — the `χ₄` identity `m = Re(S)/p`, `S = Σ_{x∈F_{p²}} χ₄(f(x))`, computed by a **separate function with its own enumeration** of `F_{p²}`, forbidden from reading `b₂`, `P₂`, `a_C`, `a_E`, `L_new` | independent route to the same integer | **PASS: 155/155 out-of-sample rows and 30/30 in-sample readout re-checks agree exactly** |
| **Plant 1** — deliberately false `H1' : p ≡ 11 mod 12 ⇒ m = 1` | can the comparator report a failure at all? | **FIRED**, 42 violations |
| **Plant 2** — `χ₄` route on `f+1` against the `b₂` route on `f`, three named rows | can the control disagree at all? | **FIRED**, 1/3 disagree (`B=7, p=211`) |
| **Plant 3** — four `p ≡ 1 mod 4` rows | is the `b₁ = 0` column measured, or hard-coded? | **FIRED**, `b₁ ≠ 0` at `p = 229, 241` |

Forced columns, reported and **not counted as evidence**: `b₁ = 0` on every `p ≡ 3 mod 4` row
(forced by the μ₄ argument), `p | b₂` on every such row, `|m| ≤ 2` everywhere.

---

## 4. Scope, and what this does **not** establish

Every number above inherits: *6 cubics; `p ≡ 3 mod 4`, `200 < p < 500`; `m = b₂/p` from exact integer
point counts over `F_p` and `F_{p²}`.*

- Tagged **`[EMPIRICAL]`**, not `[PROVED]`. It is a law measured on 26 primes.
- **It does not transfer to `p = 2²⁵⁶ − 2³² − 977`, and no statement about that prime's `m`, its
  eigenvalue angles, or its `k` is made here.** The scale-free μ₄ argument covers `b₁ = 0` only; the
  *value* of `m` is exactly what that argument leaves open, and this run does not close it.
- **Zero power** against any rule agreeing with H1/H2 on this window — e.g. one keyed to `p mod 24`,
  or to the sextic rather than cubic character. That indistinguishability holds regardless of outcome.
- No ECDLP, key-recovery, or security statement is made or implied.

**Observation recorded, not a hypothesis:** `b₁ = 0` also occurs at `p = 233, 257` (`p ≡ 1 mod 4`,
`B = 7`). The μ₄ argument gives `p ≡ 3 mod 4 ⇒ b₁ = 0`; the converse is false.

**Exploratory arm (non-CM cubics `x³+2x+5`, `x³+x+1`, `x³−x+3`):** `m` values recorded in the log
under `EXPLORATORY — no prediction`. All five values `{−2,0,1,2}` and `−1`-free behaviour appear.
**No rule is stated and no significance is computed for them**; a rule there needs its own prereg and
the reserved `500 < p < 700` window, untouched by this run.

---

## 5. The next probe (named now, so it cannot be chosen post hoc)

The firing control is also the analytic handle. Because `b₁ = 0`,
`m = Re(S)/p` with `S = Σ_{x ∈ F_{p²}} χ₄(x³ + B)` — a **quartic-character sum over `F_{p²}` of a
`j = 0` cubic**, i.e. a Jacobi-sum object. Evaluating `S` in closed form for `f = x³ + B` would
derive H1/H2 rather than measure them, and — unlike this run — such a derivation takes only `p mod 12`
and a character value as input, so it would be scale-free in the same sense the μ₄ argument is.

That derivation, not more primes, is what would move this off `[EMPIRICAL]`. Until it exists, the
`m`-value at any specific large prime is **not** determined by anything in this file.

Related: the `k(m)` column is the first place the 2+2 splitting produces a *field*, not just a
magnitude — `A_new`'s endomorphisms become scalar over `F_{p^k}` with `k ∈ {2,4,6}` selected by the
same arithmetic condition. Whether that field is visible in the `V_i ⊕ V_{−i}` decomposition that
N1's ½-saturation also sees (`RESULT_mu6_cohomology_supersingular_v2.md` §2, Fact 1) is untested
here and is a separate prereg.
