# RESULT — Brick D2 at `p ≡ 7 mod 12` (secp's class): the "prove `J` is rational" gap is REDUCED to one explicit sign identity, and the barred `g(χ₄)` sign rule is DERIVED

*2026-09-01. Advances the single remaining gap of `RESULT_jacobi_closed_form_m_law_v4.md` §2
(`J(χ₃,χ₄) = ∓p`, graded there `[EMPIRICAL 12/12] … NOT proved here`). Scripts:
`jacobi_rationality_gate_v1.py`, `jacobi_rationality_reduction_v1.py`; logs alongside. Exact
integer / `Z[ζ₁₂]` arithmetic in every verdict path; floats appear only in two clearly-marked
cross-checks that decide nothing.*

**No leakage / ECDLP / keyspace claim.** Pure character-sum arithmetic over `F_{p²}`. Not a leakage
test, sweep, scan or anomaly drill — no statistic, no null, no target involving `d` — so the
CLAUDE.md §2 `experiment-designer` gate does not apply.

---

## 0. Setup

`p ≡ 3 mod 4`, `q = p²`, `F_q = F_p[i]` (`i² = −1`, legitimate since `p ≡ 3 mod 4`), so
`Tr(a+bi) = 2a` and `N(a+bi) = a²+b²`. `χ₃`, `χ₄` are cubic and quartic characters of `F_q^*`.
v4's (F1): **`χ₄` is trivial on `F_p^*`**. v4's (F2): `χ₃|_{F_p^*}` is **nontrivial** exactly when
`p ≡ 1 mod 3`, i.e. `p ≡ 7 mod 12` — **secp's class** (`p_secp ≡ 7 mod 12`, `≡ 7 mod 24`).

---

## 1. Three steps, two of them now proved

**L1 — the coset identity `[PROVED — elementary]`.** Let `χ` be any character of `F_q^*` whose
restriction `θ := χ|_{F_p^*}` is **nontrivial**. Splitting `g(χ) = Σ_{x∈F_q^*} χ(x)ψ_p(Tr x)` over
the cosets of `F_p^*` and using `Σ_{c∈F_p^*} θ(c)ψ_p(cT) = θ̄(T)g_p(θ)` for `T ≠ 0`, `= 0` for
`T = 0`:

> **`g(χ) = g_p(θ) · S(χ)`,  where `S(χ) := Σ_{x : Tr(x)=1} χ(x)`**  (a sum of length `p`).

Each `Tr ≠ 0` coset has a unique `Tr = 1` representative, and `θ̄(1) = 1`; the `Tr = 0` coset
contributes `0`. **Load-bearing consequence:** because `χ₄` is subfield-trivial (F1), `χ₃` and
`χ₃χ₄` have the **same** `θ`, so the irrational prefactor `g_p(θ)` **cancels identically** in the
ratio. This is the structural reason `J` can be rational at all.

**L2 — bookkeeping `[PROVED]`.** `J(χ₃,χ₄) = g(χ₃)g(χ₄)/g(χ₃χ₄) = g(χ₄)·S(χ₃)/S(χ₃χ₄)`.

**L3 — the subfield-trivial quartic Gauss sum `[PROVED — derived]`.** For `χ₄` (trivial on `F_p^*`)
the same coset split gives `Σ_{cosets} χ₄ = 0` and leaves only the trace-zero coset:

> **`g(χ₄) = p · χ₄(x₀)`, `x₀` any nonzero trace-zero element.**

`x₀^{p−1} = −1`, so `x₀ = g^{(p+1)/2}` up to `F_p^*`; `4 | p+1` makes `dlog(x₀) mod 4` well defined
and equal to `(p+1)/2`, whence `χ₄(x₀) = ζ₄^{(p+1)/2} = +1 ⟺ 8 | p+1`. Therefore

> **`g(χ₄) = (2|p) · p`**  (`+p` at `p ≡ 7 mod 8`, `−p` at `p ≡ 3 mod 8`).

> **This discharges a v4 drill-rule bar.** v4 §2 recorded this sign rule as *"fitted to **three
> primes** and **not** retested out of sample; by drill rule it may not be named or used in a proof
> until it is."* It is now (a) **derived**, not fitted, and (b) witnessed exactly at **31/31**
> primes `p ≡ 3 mod 4`, `p < 300` (`B1`: the nonzero trace-zero elements form exactly one coset of
> `F_p^*`; `B2`: `dlog(x₀) ≡ (p+1)/2 mod 4`), with a float cross-check
> `|g(χ₄) − p·χ₄(x₀)| ≤ 2.3e−13` at every prime. The bar lifts; the rule may now be named and used.

---

## 2. The gap, restated

Substituting L1–L3 into the target `J = −p` (`p ≡ 1 mod 3`) / `+p` (`p ≡ 2 mod 3`) turns the whole
claim into a single identity between two **length-`p`** character sums:

> **(C2)  `S(χ₃χ₄) = −(2|p)(−3|p) · S(χ₃)`**

This is the entire residual content of v4 §2 at `p ≡ 7 mod 12`. Explicitly, with `x = ½ + bi`
running over the trace-1 line, `S(χ₃) = Σ_{b∈F_p} χ₃(½+bi)` and `S(χ₃χ₄) = Σ_{b∈F_p} χ₃χ₄(½+bi)`.

**A classical foothold `(C3)`.** At `p ≡ 7 mod 12`, `χ₃ = χ₃'∘N` is a norm-lift, so
`χ₃(½+bi) = χ₃'(¼+b²)`; expanding `#{b : b² = u} = 1+χ₂'(u)` and substituting `u = −t/4`:

> **(C3)  `S(χ₃) = −χ₃'(2) · J_p(χ₂', χ₃')`**

— the **classical Jacobi sum over `F_p`** of the quadratic against the cubic character, `|·| = √p`,
the Eisenstein prime above `p`. So (C2) says the quartic twist multiplies that classical object by
an explicit sign.

---

## 3. Exact verification

`jacobi_rationality_gate_v1.py` (31 primes `p ≡ 3 mod 4`, `p < 300`), `J` accumulated as an exact
vector in `Z[ζ₁₂] = Z[x]/(x⁴−x²+1)`:

| check | result |
|---|---|
| `J(χ₃^a, χ₄^b) = −p` (`p≡1 mod3`) / `+p` (`p≡2 mod3`), **all four** pairs `a∈{1,2}, b∈{1,3}` | **31/31 primes × 4 pairs — exact** |
| `B1` one trace-zero coset · `B2` `dlog(x₀) ≡ (p+1)/2 mod 4` · `χ₄(x₀) = (2\|p)` | **31/31 — exact** |

`jacobi_rationality_reduction_v1.py` (same primes):

| check | `p ≡ 7 mod 12` (secp's class) | `p ≡ 11 mod 12` |
|---|---|---|
| **C0** `χ₃ = χ₃'∘N` (norm-lift) | **16/16 exact** | n/a — `χ₃\|_{F_p^*}` trivial |
| **C1** `g(χ) = g_p(θ)S(χ)`, `χ∈{χ₃,χ₃χ₄}` *(float, not a verdict)* | `≤ 4.3e−11` | fails, **as it must** (`θ` trivial ⇒ L1's hypothesis absent) |
| **C2** the reduced gap | **16/16 exact** | 15/15 exact |
| **C3** tie to `J_p(χ₂',χ₃')` | **16/16 exact** | n/a |
| **C4** `J = ∓p` recomputed independently | 16/16 | 15/15 |

**Two independent gains over v4's base.** (a) The empirical base moves `12 → 31` primes. (b) v4
computed one character pair; here **all four** `(χ₃^a, χ₄^b)` agree, so the value is not an artifact
of a conjugate choice — a control v4 did not have.

---

## 4. Grades

| item | grade |
|---|---|
| **L1** `g(χ) = g_p(θ)S(χ)` for `θ` nontrivial | **`[PROVED — elementary]`** |
| **L3** `g(χ₄) = (2\|p)·p` (subfield-trivial quartic Gauss sum) | **`[PROVED — derived]`**, witnessed 31/31 |
| **L2 + reduction:** v4 §2 `⟺` **(C2)** at `p ≡ 7 mod 12` | **`[PROVED — reduction]`** |
| **(C3)** `S(χ₃) = −χ₃'(2)J_p(χ₂',χ₃')` | **`[EMPIRICAL — 16/16 exact]`**; derivation sketched §2, not written out |
| **(C2)** itself | **`[EMPIRICAL — 31/31 exact]` — THE remaining gap** |
| v4 §2 `J = ∓p` | **`[EMPIRICAL 31/31, all 4 character pairs]`** (was `[EMPIRICAL 12/12]`) |

---

## 5. What is owed

1. **Prove (C2).** The residual. Under the Cayley parametrization `1+bi ↦ u = (1−bi)/(1+bi)`,
   `F_q^*/F_p^* ≅ U` (norm-1, cyclic of order `p+1`) and `χ₄(1+bi) = λ(u)` with `λ` of order 4 on
   `U`; (C2) becomes a statement about twisting `Σ_b χ₃'(1+b²)` by a quartic character of `U`. The
   natural tool is the Hasse–Davenport product relation with `m = 2`, `ρ = χ₄² = χ₂`. Not attempted.
2. **Write out (C3).** The substitution chain is elementary; only the write-up is owed.
3. **The `p ≡ 11 mod 12` half needs a different route.** There `θ` is trivial, so L1 does not apply
   and the `g_p(θ)` cancellation argument is unavailable — the coset split degenerates exactly as C1
   records. That half is **not** secp's class and is untouched here.
4. **`citation-verifier`** if the Hasse–Davenport product relation is used in a written proof.
   **`compile-diff`** if this is folded into a master.

---

## 6. Scope

Model primes `p < 300`. `p_secp = 2²⁵⁶−2³²−977 ≡ 7 mod 24` lies in the class where L1/L3/C0/C3 hold,
so the reduction — not the numbers — is what would transfer. (C2) is scale-immune in form: proving
it proves v4 §2 for **all** `p ≡ 7 mod 12`, which is the whole point of the D2 track (`Brick D`,
`ROADMAP_REDIRECT_v3.md`: *exact identities that reach `2²⁵⁶`*). Nothing here is a leak, a bit, or a
keyspace statement.
