# Where the structure is — and the next five places to look

*2026-07-23. Not a promotion; nothing here is folded into a master. No leakage, key-recovery, or
ECDLP claim.*

> ⚠ **PROVENANCE — what was actually read, and what was not.** This synthesis was built from:
> `memory/btc_puzzle_INDEX.md` (all 454 lines), `POSITIVE_FINDINGS_MASTER_v4.md` **§XI only** plus its
> heading list, `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` **§A1, §A5, §A6** plus its heading list and the
> §A4 item lines. **NOT read: master Parts I–X, Addendum §A2/§A3 bodies, and every `RESULT_*`
> artifact.** For those, §1 and §2 below rest on the **index's own summaries** — i.e. one compression
> away from the object. Treat every row not sourced to §A1/§XI as a pointer to check, not as a
> restatement of a verified claim. The §2 originality list in particular is **unaudited against the
> literature and unaudited against the full record.**

---

## 1. The frame the whole record actually fits

Every original result in this project has the same shape: **a curve quantity is shown to equal a
lattice or class-field quantity.**

| curve-side object | equals | arithmetic object |
|---|---|---|
| Cap Law: `ε ≠ 0` | ⟺ | `|u ∓ v| > ½` — a region of the hexagonal lattice `ℤ[ω]` |
| `H1`: `(−1)^{flap/6}` | = | `χ₂(2) = (−1)^{(p²−1)/8}` — a Gauss-sum sign |
| `|FLD|` | = | `6·h(−p)` — the class number of `ℚ(√−p)` |
| `m = b₂/p` (Frobenius of `A_new`) | = | a Jacobi sum `J(χ₃, χ₄)` |
| `#E(F_p) = N` **and** `#E(F_N) = p` | ⟸ | `(π_n) = (π_p − 1)` in `ℤ[ω]` + the sextic-twist class of `b=7` |
| `T = 1` stratum of `(n,k,D)` | = | `{⌊lo/q⌋}` — the Dirichlet hyperbola |
| Claim F: FIELD/CURVE split | — | the excess `ℤ/2` **is** the sextic twist |

The unifying object is not the curve. It is **`ℤ[ω]` together with its two adjacent ideals
`(π_p)` and `(π_n) = (π_p − 1)`**: coordinates live in `ℤ[ω]/(π_p) ≅ F_p`, scalars live in
`ℤ[ω]/(π_n) ≅ ℤ/n`. Every law above is a statement about one of those quotients; every *open* frontier
of consequence sits in the **slippage between them** — the `−1`.

That also locates the leakage frontier. Part VI closes the single-index,
bounded-degree readouts analytically (KS/Weil), and Boneh–Shparlinski makes the residual door *be*
the ECDLP. What is **not** closed is anything that reads the two quotients *jointly*.

## 2. What appears to be undocumented elsewhere

Stated as a claim about *this record's* originality, not about the literature — an actual priority
search has never been run and is itself a task worth doing.

1. **The Cap Law** and the `flap` as an exact lattice region of the Eisenstein lift `[PROVED]`.
2. **`H1`: `(−1)^{flap/6} = χ₂(2)`** `[VERIFIED 61/61 incl. 38 OOS]`, reduced to `ORB = |T⁺|/3`
   `[PROVED]` and thence to one classical Dedekind-type lattice-count lemma.
3. **`|FLD| = 6h(−p)`** — P1 a theorem, P2 down to the single identity `(†)`.
4. **Claim S** (isotypic selection rule: one rule absorbs five separately-discovered zeros) and
   **Claim F** (every `j=0` pairing splits exactly into FIELD + CURVE) `[PROVED + 336/336, 180/180]`.
   Claim F's operative content: reporting the total attributes a pure lattice fact to curve
   arithmetic, so the split is mandatory.
5. **`A_new` supersingular at every `p ≡ 3 mod 4`, for every separable cubic** — mechanism is the μ₄
   cover, **not** CM `[PROVED, scale-free, holds at secp]`; plus its corrected isogeny type
   (`RESULT_anew_isogeny_type_correction_v1.md`).
6. **secp256k1 is an amicable pair** `[PROVED by verification at the real 256-bit primes]` — the
   Silverman–Stange framework is published; that secp *is* one, with the twist-selection named as the
   unforced part, is this record's.
7. **`m` as the quantum number** naming all four Frobenius eigenvalues, reduced to one Jacobi sign.
8. **Three exact conservations of `U(a,b,c)`**, including `Σ_a |U|² = n(n−1)` — the one constraint no
   random-target null satisfies.
9. **The bilinear closure theorem** (two-point Fourier factorization ⇒ `O(p^{−1/2})`).
10. **`k_den` level sets = the primitive Farey comb** `[VERIFIED exactly + derivable]` — d-side only,
    no curve enters it (scope correction already recorded).

**Tie-ins to what is known** (all already `[CITED]` in the record): Kohel–Shparlinski `max|U| ≤ 4√p+1`;
Boneh–Shparlinski (no concentration ⟺ ECDLP hard); Semaev/Diem first-fall and the BFS isobaric
argument; Galbraith–Ruprai negation-on-intervals `√2`; Silverman–Stange aliquot cycles Conj. 40;
Waterhouse/Honda–Tate supersingular Weil numbers; Dirichlet's class-number formula; Hasse–Davenport +
BEW semi-primitive Gauss sums; Katz–Sarnak / Porter–Thomas.

---

## 3. Ranked next moves

Ordering is my proposal, not a computation — none of "structure gained", "decidability" or "cost"
has a measured value here. Read it as a suggested order, and reorder freely. It is **not** ordered by
proximity to a break.

### #1 — Measure the four *twisted* eigenvalues. `[the object; every N1 run so far measured a proxy]`

N1 (the `2√p` cap on `χ₂(y)`; v4 §XI.10, Addendum §A5) has been attacked three times and every attempt
measured **`max_a |V(a)|` — a magnitude**. The record's own restated question is eigenvalue-level:

> "`#R = 4` is right as a `dim H¹`; what's unproved is that all 4 Frobenius eigenvalues can align…
> whether the TWISTED `H¹(a)` inherits [the `±` pairing] is the thing to settle."

**The eigenvalues are directly computable and never have been.** The twisted sheaf
`L_{χ₂(y)} ⊗ L_{χ_a}` on `E` is the Kohel–Shparlinski object; the character `χ_a` extends to
`E(F_{p^k})` through the norm, so
`V_k(a) = Σ_{P ∈ E(F_{p^k})} χ₂(y_P) · χ_a(N_{k/1} P)` for `k = 1,2,3,4` determines the four
eigenvalues via Newton's identities. Cost `O(p⁴)` — comfortable at `p ≤ 43`, reachable at `p ≤ 79`.

What it settles, either way:
- If the twisted eigenvalues are `√p ·` (roots of unity) in a configuration whose maximum attainable
  `|Σ|` is `2√p`, **N1 is explained** and the answer is a symmetry type, not a bound.
- If they are not all of weight `√p`, or the configuration permits `> 2√p`, then the cap is *not* an
  eigenvalue fact and every prior N1 framing is mis-typed.
- Ramification check first: `y` has odd order at the three 2-torsion points and at `O` ⇒ four tame
  points ⇒ `dim H¹ = 2g−2+4 = 4`. Confirm this numerically before interpreting anything.

**Requires a pre-registration** (drill protocol; a fired control = a planted eigenvalue configuration
recovered from synthetic `V_k`). ⚠ The derivation already on file — `[−1]` maps `H¹(a) → H¹(−a)`, so it
**swaps** two cohomologies and cannot split one — means the splitting mechanism, if any, is **not**
`[−1]`. Do not re-propose it.

⚠ `ζ₄` **may not be** a fresh candidate either, but this is **my own unreviewed derivation, not an
established result** — treat it as a check to run, not a closed door: `E = C/⟨ζ₄²⟩` has `y = w²`, and
`ζ₄ : w ↦ iw` gives `y ↦ −y`, so `ζ₄` would induce `[−1]` on `E` and land on the same refuted
mechanism. `[DERIVED — UNVERIFIED, mine]`. **Verify it before letting it suppress the candidate** —
an in-head derivation that closes an avenue is the exact shape of
[[feedback_negative_bias_enlarge_nulls_2026_07_17]].

### #2 — The parity-matched amicable lift channel. `[a null that was forced to be zero]`

Frontier §XI.3 / §X.3 (the non-homomorphic amicable correspondence) is open, and its ambient object is
now a **verified fact at full scale** (secp is an amicable pair, §A1.2). The one test run against it —
"field-lift(`X`) vs scalar-lift(`d`)", `lift_amicable_slippage_v1.py` — returned null at a ~2% floor.

**That null is uninformative by the record's own theorem.** Part 4 of the same work proves
`eis_p(X_d)` is **even** in `d` and `eis_n(d)` is **odd** in `d`, with energies exactly `0` — the linear
channel between them is `0` **by parity, before any data**. Measuring it measures nothing. This is the
same class as the several broken instruments already caught here (the μ₆-blind shuffle null, the
`D_int` uncentred primary, the `W1` non-primitive plant).

**The parity-legal rebuild:** use an **odd-in-`d`** curve-side lift. Two are already proved available —
`y` (odd in `d`), and `xy = X·Y` (proved **odd in `d` and μ₃-covariant**, and independently identified
as the structural why behind the known `(X·Y) mod 64 → D mod 64` shadow). Reduce the *same* Eisenstein
lift `z ∈ ℤ[ω]` mod `π_n` instead of `π_p` — the two quotients differ by the `−1`, which is the whole
content — and test against `eis_n(d)`.

Controls that must fire: a plant at a known injection level; the μ₆-carrying null (never a plain
shuffle); and the parity ledger printed for **both** sides so a second forced zero cannot masquerade as
a result. Pre-registration mandatory; `experiment-designer` before any run.

### #3 — Frontier #17: is the low tail the shadow of the row budget? `[named, decidable, cheap]`

`Σ_{a mod n} |U(a,b,c)|² = n(n−1)` exactly, at every fixed `(b,c)` — **the one exact conservation a
random target does not satisfy**, and therefore the one place where the character is structurally
distinguishable from every null used so far. The sub-Rayleigh deficit is real (`Z = −13.99`, survives
the exact value-multiset control) and its locus is the **`+8%` excess of near-zero harmonics** at row
`a₀`. The decidable question: is that near-zero excess **compensated by large `|U|` at other `a` for the
same `(b,c)`**? A joint statistic over `(a,b,c)`, not a marginal at fixed `a`.

Two prior method notes bind it: a fourth moment is blind to the low tail (`r⁴ ≈ 0` for `r < 0.1`), so
do **not** re-run `M4`; and no unitary basis change can create concentration (§A1.7-2), so the statistic
must not be a re-basing.

### #4 — Frontier #16, `(†)`: name the machinery. `[pure structure; zero ECDLP content]`

`(†) C′ − C = Σ_{s=1}^{H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`, `[VERIFIED 134 primes]`, is the single
open step of P2 and would promote `|FLD| = 6h(−p)` to a theorem. Elementary manipulation is *provably*
circular at source.

**One route is now closed off:** the `3` is **not** a compositum class number — `h(−12p)/h(−p)` is not
constant (`0.49 … 20.0`, `p < 2000`, both classes mod 12); see
`RESULT_anew_isogeny_type_correction_v1.md` §6. The remaining candidate machinery is
**generalized Dedekind sums / the Rademacher function**: `sgn(ρs mod p − s)` is a sawtooth in `s`
against multiplication by a primitive 6th root, and `x ↦ (u−v) mod 1` is already known here to be an
additive isomorphism `ℤ[ω]/(π_p) ≅ (1/p)ℤ/ℤ`. The same machinery is what `H1`'s remaining lemma needs
(`|T⁺| ≡ 0 mod 6 ⟺ χ₂(2) = 1` — the classical origin of `χ₂(2) = (−1)^{(p²−1)/8)}`). **Two open items,
one tool.** Source-first: read the Dedekind-sum reciprocity literature before inventing.

### #5 — Frontier #15's sub-items, and a priority search. `[cheap, closes bookkeeping]`

The Jacobi sign law is down to **one square-root sign** `s` in `g(χ₃χ₄) = s·g_p(χ')²`, with empirics
forcing `s = (−1)^{(p+1)/4}` over 27 primes (15 out-of-sample). Its named sub-items are unfinished: the
`G(χ₄)` sign rule is **fitted to three primes and barred from use until retested out-of-sample**. Retest
it. (The `σ₅`-invariance and norm-lift sub-items are now discharged by `RESULT_jacobi_sign_law_v1.md`.)

Separately and overdue: **§2's originality has never been checked against the literature.** A
citation-verifier / literature pass on the Cap Law, `H1`, `|FLD| = 6h(−p)`, and the amicability of secp
would either establish priority or find the theorem already written — and this project's own record is
that reading the source dissolved the obstacle **four** times.

---

## 4. Two things not to do

- **No PRNG / generation-side work.** Standing, repeated: the object is curve arithmetic structure.
- **Do not re-propose `[−1]` or `ζ₄` as the N1 splitting mechanism.** Both are the same map on `E` and
  both are refuted on file. A new candidate must be a symmetry that acts *within* fixed-`a`
  cohomology.
