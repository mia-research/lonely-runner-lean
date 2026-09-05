> ## ⚠ CORRECTION 2026-09-02, then DISCHARGED the same day. Read both boxes.
>
> **DISCHARGE (later 2026-09-02):** the bridge below is now **PROVED** —
> `RESULT_mlaw_theorem_secp_class_v1.md` derives `m = Re(S)/p` by Lefschetz point counting on
> `C : w⁴ = x³+B` (and derives `b₁ = 0` as a by-product). **The m-law IS a theorem at
> `p ≡ 7 mod 12`.** The correction below is kept as the trail — it was right when written, and the
> reasoning that found it is the reason the bridge got proved.
>
> ## ⚠ CORRECTION 2026-09-02 (superseded above) — "the m-law is a theorem" was TOO STRONG.
>
> Flag F2 of `AUDIT_session_2026_09_01_honesty_flags_v1.md` was discharged today
> (`mlaw_s1_firsthand_check_v1.py`) and it found **more than it was looking for**.
>
> **What checked out.** `RESULT_jacobi_closed_form_m_law_v4.md` §1 — the reduction
> `S = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)` — is **correct, verified first-hand and exactly** at 14
> primes, together with all three structural facts it rests on (`χ₄` trivial on `F_p^*`; `χ₃(−1)=1`;
> `#{x : x³=u} = 3` on cubes and `0` off them). Combined with §2 (proved below), the **closed form of
> the character sum `S` is a theorem** at `p ≡ 7 mod 12`: `S = −2p` if `B` is a cubic residue,
> `S = +p` otherwise.
>
> **What did NOT check out.** The step from `S` to the eigenvalue invariant — **`m = Re(S)/p`** — is
> **not derived anywhere in the corpus.** `RESULT_mu4_eigenvalue_individual_v1.md` §"controls"
> introduces it explicitly as a **"Firing control — an independent route to the same integer"**,
> graded by agreement: **PASS 155/155 out-of-sample rows + 30/30 in-sample re-checks.** That is
> `[EMPIRICAL]`, at high weight, but it is a *cross-check between two computations*, not a proof that
> the quartic-character sum computes `b₂`.
>
> **Corrected claim.** *The closed form of `S` is proved. The m-law proper — `m = b₂/p` naming
> `A_new`'s four Frobenius eigenvalues via `z⁴+mz²+1=0`, laws H1/H2 — is proved **modulo one
> empirical bridge**, `m = Re(S)/p`.* Anywhere this file, `ROADMAP_REDIRECT_v4.md`, `RESEARCH.md (e)`
> or the handoff log says "the m-law is a theorem", read it with that bridge named.
>
> **New open item (well-posed, and probably not hard).** Prove `m = Re(S)/p` by Weil/Lefschetz point
> counting on `C : w⁴ = x³+B` over `F_{p²}` — `#C(F_{p²})` expands into character sums, and the
> `χ₄`-terms are exactly the `A_new` block. Nothing in it needs GKR, sheaves, or new machinery. Until
> it is done, the theorem is about a character sum, not about an abelian variety.

# RESULT — Brick D2 CLOSED at `p ≡ 7 mod 12` (secp's class): `J(χ₃,χ₄) = −p` is PROVED. Rationality by Hasse–Davenport; the sign falls out mod a prime above 3, in both regimes.

*2026-09-01. Closes the single remaining gap of `RESULT_jacobi_closed_form_m_law_v4.md` §2 (graded
there `[EMPIRICAL 12/12] … NOT proved here`) at secp's residue class, and thereby the residual (C2)
of `RESULT_jacobi_rationality_reduction_v1.md` (same session). Script `jacobi_hd_closure_v1.py`;
prior exact witnesses `jacobi_rationality_gate_v1.py` (31/31 primes, `Z[ζ₁₂]`),
`jacobi_rationality_reduction_v1.py`.*

**No leakage / ECDLP / keyspace claim.** Pure character-sum arithmetic. Not a leakage test, sweep,
scan or anomaly drill — no statistic, no null, no target involving `d`; the `experiment-designer`
gate does not apply.

> ### `[PROVISIONAL — citation-verifier unavailable]`
> The proof invokes **two standard Hasse–Davenport relations** (lifting and product). CLAUDE.md §2
> makes `citation-verifier` mandatory before a grade moves on a citation's strength; it was attempted
> 2026-09-01 and is **UNAVAILABLE** (`Agent type 'citation-verifier' not found` — the project agents
> are not loaded in this session's harness). Per §2a all four conditions are met: this tag is in the
> grade slot, the self-audit is §5, the gate is owed, and **the grade below does not move any other
> claim up until the gate clears.** Both relations are textbook (Berndt–Evans–Williams, *Gauss and
> Jacobi Sums*, ch. 11; Ireland–Rosen §11.4) and each is **numerically witnessed here independently**
> (§3 columns D/E/F), so the exposure is the citation's exact statement and hypotheses, not its truth.

---

## 0. Statement

`p ≡ 3 mod 4`, `q = p²`, `F_q = F_p[i]`, `χ₃`/`χ₄` cubic/quartic characters of `F_q^*`.

> **`J(χ₃,χ₄) = −p` for `p ≡ 1 mod 3`;  `J(χ₃,χ₄) = +p` for `p ≡ 2 mod 3`.**

**Proved here for `p ≡ 7 mod 12`** (`= p ≡ 3 mod 4` and `p ≡ 1 mod 3`) — **secp's class**
(`p_secp ≡ 7 mod 12`). The `p ≡ 11 mod 12` half is *not* closed; see §4.

The proof splits cleanly: **rationality** (`J = ±p`) is the hard half and is where the regimes differ;
the **sign** is then free, by one congruence, in *both* regimes at once.

---

## 1. Rationality: `J = ±p` at `p ≡ 7 mod 12` `[PROVED]`

Write `θ := χ₃|_{F_p^*}`; at `p ≡ 1 mod 3`, `χ₃ = χ₃'∘N` is a norm-lift and `θ = χ̄₃'`.
Recall `J(χ₃,χ₄) = g(χ₃)g(χ₄)/g(χ₃χ₄)` and, from
`RESULT_jacobi_rationality_reduction_v1.md`, `g(χ₄) = (2|p)·p` `[PROVED — derived]`.

**P1 (Frobenius).** `x ↦ x^p` is a bijection of `F_q` with `Tr(x^p) = Tr(x)`, so `g(χ) = g(χ^p)` for
every `χ`. With `p ≡ 3 mod 4`, `χ₄^p = χ̄₄`, hence **`g(χ₃χ̄₄) = g(χ₃χ₄)`**.

**P2 (Hasse–Davenport product, `m=2`, `ρ = χ₂`).**
`g(χ)·g(χχ₂) = χ^{-2}(2)·g(χ²)·g(χ₂)`. At `χ = χ₃χ₄`: `χχ₂ = χ₃χ̄₄`, `χ² = χ̄₃χ₂`, and
`χ^{-2}(2) = θ(2)` (as `χ₄(2)=1` and `θ(2)³=1`). Applying **P1** to collapse the left side:

> **`g(χ₃χ₄)² = θ(2) · g(χ̄₃χ₂) · g(χ₂)`.**

**P3 (Hasse–Davenport lifting, `s=2`).** `g_q(χ'∘N) = −g_p(χ')²`. Hence
`g(χ₂) = −g_p(χ₂')² = p` — note this needs only the **square** of the quadratic Gauss sum, which is
elementary (`g(χ)g(χ̄) = χ(−1)p` at `χ = χ̄ = χ₂'` gives `g_p(χ₂')² = χ₂'(−1)p = −p`); **Gauss's sign
theorem `g_p(χ₂') = i√p` is NOT used**, which keeps the citation exposure to the two HD relations
alone; `g(χ₃) = −g_p(χ₃')²`; and, since `χ̄₃χ₂ = (χ̄₃'χ₂')∘N`
(both factors are norm-lifts — this is exactly where `p ≡ 1 mod 3` is used),
`g(χ̄₃χ₂) = −g_p(χ̄₃'χ₂')²`.

**P4 (an `F_p`-side identity).** From the `m=2` product relation over `F_p`,
`g_p(χ̄₃')g_p(χ̄₃'χ₂') = χ̄₃'(2)·g_p(χ₃')·g_p(χ₂')`, together with `g_p(χ₃')g_p(χ̄₃') = χ₃'(−1)p = p`
and `g_p(χ₂')² = χ₂'(−1)p = −p`:

> **`g_p(χ̄₃'χ₂')² = −χ₃'(2)·g_p(χ₃')⁴ / p`,**  and `χ₃'(2) = \overline{θ(2)}`.

**Assembly.** Substituting P3 and P4 into P2:

```
g(χ₃χ₄)² = θ(2)·(−g_p(χ̄₃'χ₂')²)·p = θ(2)·χ₃'(2)·g_p(χ₃')⁴ = |θ(2)|²·g_p(χ₃')⁴ = g_p(χ₃')⁴ = g(χ₃)²
```

> **`[g(χ₃χ₄)/g(χ₃)]² = 1`, so `g(χ₃χ₄) = ± g(χ₃)`, and therefore `J = g(χ₄)·g(χ₃)/g(χ₃χ₄) = ±p`.**
> **`J` is rational.** ∎

*This is the statement the m-law file named as its gap ("prove `J` rational"). The mechanism is the
one flagged in `RESULT_jacobi_rationality_reduction_v1.md` §1: `χ₄` is subfield-trivial, so `χ₃` and
`χ₃χ₄` share `θ` and the irrational `F_p`-side Gauss factors cancel — here that cancellation is
executed exactly rather than observed.*

## 2. The sign: free, and in BOTH regimes `[PROVED]`

Let `λ` be a prime of `Z[ζ₁₂]` above `3`. Since `ζ₃ ≡ 1 mod λ`, we have `χ₃(t) ≡ 1 mod λ` for every
`t ≠ 0`. Hence, reducing `J = Σ_{t≠0,1} χ₃(t)χ₄(1−t)` and substituting `u = 1−t`:

> `J ≡ Σ_{u≠0,1} χ₄(u) = (Σ_{u≠0} χ₄(u)) − χ₄(1) = 0 − 1 = **−1**  (mod λ).`

An integer `n` satisfies `n ≡ 0 mod λ` iff `3 | n`. Writing `J = ε·p`, `ε = ±1` (§1):

| | `p mod 3` | `ε·p ≡ −1 mod λ` forces | conclusion |
|---|---|---|---|
| `p ≡ 1 mod 3` | `p ≡ 1` | `ε ≡ −1`; `ε=+1` would give `1 ≡ −1`, i.e. `λ \| 2` — false | **`J = −p`** |
| `p ≡ 2 mod 3` | `p ≡ −1` | `−ε ≡ −1` ⇒ `ε = +1` | **`J = +p`** |

∎ — **exactly the measured law.** Note the sign argument is **regime-independent**: it needs only
`J = ±p`. All the regime-dependence of the theorem sits in §1.

---

## 3. Verification (`jacobi_hd_closure_v1.py`, `p ≡ 3 mod 4`, `p < 100`)

Float columns corroborate the Gauss-sum steps only (Gauss sums over `F_q` live in `Z[ζ₁₂ₚ]`); **no
verdict rests on a float** — the endpoint `J = ∓p` is verified *exactly* in `Z[ζ₁₂]` at **31/31**
primes and all four character pairs by `jacobi_rationality_gate_v1.py`.

| step | check | `p ≡ 7 mod 12` | `p ≡ 11 mod 12` |
|---|---|---|---|
| **A** P3 | `g(χ₂) = p` | `≤ 2.9e−14` | `≤ 5.7e−14` |
| **B** P3 | `g(χ₃) = −g_p(χ₃')²` | `≤ 2.1e−12` | **fails, as it must** — `χ₃` is not a norm-lift (`3 ∤ p−1`) |
| **C** | `g(χ₃χ₄) = ε·g(χ₃)`, `ε = −(2\|p)(−3\|p)` | `≤ 2.1e−12` | `≤ 2.5e−12` (holds, though §1 does not prove it there) |
| **D** P1 | `g(χ₃χ̄₄) = g(χ₃χ₄)` | `≤ 6.7e−14` | `≤ 9.7e−14` |
| **E** P2 | `g(χ₃χ₄)² = θ(2)g(χ̄₃χ₂)g(χ₂)` | `≤ 2.1e−11` | `≤ 1.1e−11` |
| **F** P4 | `g_p(χ̄₃'χ₂')² = −χ₃'(2)g_p(χ₃')⁴/p` | `≤ 1.8e−13` | **fails, as it must** (same reason as B) |
| **G** §2 | `3 \| (J+1)` — the sign congruence | **holds** | **holds** |

The B/F failures at `p ≡ 11 mod 12` are the *expected* regime split, not defects: there `3 | p+1`,
`χ₃|_{F_p^*}` is trivial, and P3 has no norm-lift to apply to.

---

## 4. Grades and scope

| item | grade |
|---|---|
| **P1** Frobenius invariance of `g` | `[PROVED — elementary]` |
| **P4** the `F_p`-side identity | `[PROVED]` (from the `m=2` product relation + two standard evaluations) |
| **§1 rationality `J = ±p` at `p ≡ 7 mod 12`** | **`[PROVED — modulo two standard Hasse–Davenport citations; citation-verifier owed]`** |
| **§2 sign, both regimes, given rationality** | **`[PROVED — elementary]`** |
| **`J = −p` at `p ≡ 7 mod 12` (secp's class)** | **`[PROVED]`**, provisional on the citation gate only |
| `J = +p` at `p ≡ 11 mod 12` | **still `[EMPIRICAL — 31/31 exact]`** — §2 supplies the sign, §1 does not supply rationality there |

**Consequence — stated with its dependency, not compressed.** What is proved here is
`RESULT_jacobi_closed_form_m_law_v4.md` **§2**, that file's named "single remaining gap." The step
from §2 to the m-law itself is that file's **§1 reduction**, graded `[PROVED]` *there* and **not
re-verified here**. So: at `p ≡ 7 mod 12` the m-law `m = Re(S)/p ∈ {−2,+1}` (by the cubic-residue
symbol of `B`) is a **theorem given that §1 reduction**.
> ⚠ **This dependency is load-bearing and is flagged in `AUDIT_session_2026_09_01_honesty_flags_v1.md`
> §F2.** `RESULT_jacobi_closed_form_m_law_v4.md` opens with a self-audit confessing v1–v3 defects —
> an inflated tally (`34/34` → 15 distinct, 19 algebraically forced) and configurations in which the
> hypothesis confirmed itself. A first-hand check of its §1 is **OWED** before the m-law is called a
> theorem elsewhere. The sign law below does not depend on §1 and is unaffected. Per `ROADMAP_REDIRECT_v4.md` §1 Brick D, D2 "protects A/C/E (the
m-law)" — that protection is now proved at secp's class. **This is a statement about the Frobenius
eigenvalues of `A_new`; it is not a leak, a bit, or a keyspace statement, and nothing here is
conditional on ECDLP.**

**Scale.** Unlike every empirical row in the programme, §1–§2 are **scale-immune**: they are
identities in `p`, so `p = 2²⁵⁶` is covered by the same argument. That was the point of the Brick D
track (`ROADMAP_REDIRECT_v4.md` §1: *exact identities that reach `2²⁵⁶`*).

## 5. Self-audit and owed

- **`citation-verifier` — owed**, attempted 2026-09-01, unavailable (agent not loaded). Exposure: the
  exact statement/hypotheses of the HD **lifting** relation (`s=2` form and its sign convention) and
  the HD **product** relation (`m=2`, and whether `χ^{-m}(m)` is the right normalisation for a
  character of `F_{p²}^*`). Both are independently witnessed numerically here (columns A/B, E, F), so
  a citation error would show as a numerical failure; it does not.
- **Uncovered (frame).** Whether `p ≡ 11 mod 12` admits an analogous route at all — §1's method
  provably does not extend, and I did not look for a substitute. Not secp's class, so not chased.
- **Not owed:** `experiment-designer` (no statistic), `compile-diff` (this is a RESULT, not a
  consolidated document — it applies when this is folded into a master).
