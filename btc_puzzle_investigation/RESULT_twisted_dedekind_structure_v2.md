# RESULT v2 — the twisted sign/sawtooth family: two clean general laws, PROVED

*2026-07-24. **Supersedes `RESULT_twisted_dedekind_structure_v1.md`**, whose higher-character (d=3,6)
claims — "χ₆ nonlinear / p-dependent," "no clean universal form" — were **artefacts of a buggy
character function** (§5). With correct characters the whole family collapses to two clean laws, both
PROVED and now verified. `p ≡ 7 mod 12`, `n=#E(F_p)` prime, `h=h(−p)`. Exact arithmetic.*

**No leakage / ECDLP claim. Character-twisted lattice sums.**

---

## 0. Objects

For a Dirichlet character `χ` mod `p` (`χ ≠ χ₀`) and `c ∈ (ℤ/p)*`, `c≠1`:
```
sawsum_χ(c) = Σ_{s=1}^{p−1} χ(s)·((cs/p))            ((x)) = {x} − ½
sgnsum_χ(c) = Σ_{s=1}^{p−1} χ(s)·sgn(cs mod p − s)
B_{1,χ}     = (1/p) Σ_{t=1}^{p−1} χ(t)·t             (generalized Bernoulli)
```

## 1. The two laws `[PROVED — every NON-PRINCIPAL χ, any prime p]`

> **SAWTOOTH:  `sawsum_χ(c) = χ̄(c)·B_{1,χ}`.**
> **SIGN:      `sgnsum_χ(c) = 2·B_{1,χ}·( χ̄(c) − χ̄(c−1) − 1 )`.**

Both are **linear in the conjugate characters at the two endpoints `c` and `c−1`**, with coefficient
`B_{1,χ}`.

**⚠ Scope, tested precisely (not "all χ"):**
- **The principal character `χ₀` is EXCLUDED** — the proof (§2) uses `Σ_s χ(s)=0`, false for `χ₀`.
  Directly: at `p=127` the formula misses `χ₀` by residual `126`. Non-principal only.
- **Every non-principal order verified, not just `d=2,3,6`:** all divisor-orders `d ≤ 40` at
  `p = 79, 127, 199, 211, 337, 421`, all `c` — residual `≤ 2.9×10⁻¹²`.
- **Any prime `p`, not only `p≡7 mod12`:** verified at `p=337, 421` (`≡1 mod4`) as well. The
  `p≡7 mod12` restriction belongs to the **`(†)` application**, not to these two laws.

**Parity.** `B_{1,χ}=0` for even `χ` (standard; `Σ_{t<p/2}χ(t)=0`), so **both sums vanish for even
`χ`** — consistent with the antisymmetry of the summand under `s↦p−s`. Nonzero requires **odd** `χ`.

## 2. Proof (floor telescoping — elementary, character-agnostic)

**(a) Sawtooth.** `sawsum_χ(c) = (1/p)Σχ(s)(cs mod p) − ½Σχ(s)`. Second term 0; substitute `t=cs mod p`:
`(1/p)Σ_t χ(c⁻¹t)t = χ̄(c)B_{1,χ}`. ∎

**(b) The intermediate `D_χ(c) := Σ_s χ(s)⌊cs/p⌋ = B_{1,χ}·(c − χ̄(c))`.**
From `cs mod p = cs − p⌊cs/p⌋`: `Σχ(s)(cs mod p) = c·Σχ(s)s − p·D_χ(c) = c·pB_{1,χ} − p D_χ(c)`. But
`Σχ(s)(cs mod p) = p·sawsum_χ(c) = p·χ̄(c)B_{1,χ}` (by (a)). Equate and divide by `p`:
`χ̄(c)B_{1,χ} = cB_{1,χ} − D_χ(c)`, i.e. `D_χ(c) = B_{1,χ}(c − χ̄(c))`. ✓ (verified `≤1.4×10⁻¹²`)

**(c) The floor identity `[cs mod p > s] = 1 − (⌊cs/p⌋ − ⌊(c−1)s/p⌋)`.**
`(cs − (c−1)s)/p = s/p < 1`, so `⌊cs/p⌋ − ⌊(c−1)s/p⌋ ∈ {0,1}`; it is `0` **iff** no integer lies in
`((c−1)s/p, cs/p]` **iff** `cs mod p > s`. Elementary. ✓ (verified exactly)

**(d) Telescope.** `M_χ(c) := Σχ(s)[cs mod p>s] = Σχ(s) − D_χ(c) + D_χ(c−1) = D_χ(c−1) − D_χ(c)
= B_{1,χ}(χ̄(c) − χ̄(c−1) − 1)`. Since `sgn = 2[·]−1` and `Σχ(s)=0`, `sgnsum_χ = 2M_χ`. ∎

## 3. Corollaries

- **LAW1 (χ₂):** `B_{1,χ₂} = −h`, so `sgnsum_χ₂(c) = 2h·(1 − χ₂(c) + χ₂(c−1))`. `[PROVED]`
- **`(†)`:** `c = ρ` (primitive 6th root): `χ₂(ρ)=−1`, `χ₂(ρ−1)=χ₂(ρ²)=1` ⇒ `sgnsum_χ₂(ρ)=6h`, i.e.
  `T = 3h`. **`[PROVED]` — now by TWO independent routes:** the floor-telescoping above, and the
  orbit-collapse of `RESULT_fld_dagger_proof_v1.md`. Promotes `|FLD|=6h(−p)` to a theorem.
- **Reciprocity:** `M(c) = −χ₂(c)·M(c⁻¹)` (substitution `t=cs`), consistent with LAW1. `[PROVED]`
- **`sawsum_χ₂(c) = −χ₂(c)h`** — the anchor of the original `(†)` proof. `[PROVED]`

## 4. What the family actually is
The endpoint-linearity (§1) is the Dedekind–Rademacher **cocycle** structure: both sums are
coboundaries `Φ(c) − Φ(c−1)` of `Φ_χ = −D_χ` (sign) resp. a sawtooth potential, evaluated at the two
"cusps." There is **no** `p`-dependent or nonlinear behaviour for any `χ` — v1's contrary claim was
the bug. The only `χ`-dependence is the scalar `B_{1,χ}`, which for odd `χ` is (a period times) the
`L(1,χ)` / class-number of the associated field.

## 5. ⚠ The v1 error — a buggy character function, caught by out-of-sample testing

v1 reported `sgnsum_χ₆` as "nonlinear, `p`-dependent, no clean form" and a `d=3` residual of `198`.
**Both were artefacts.** The exploratory `make_chi(p,d)` had a spurious `(p−1)/d` factor in the
exponent (`χ(a) = ζ_d^{dl(a)·(p−1)/d mod (p−1)}` instead of `ζ_d^{dl(a)}`); it is **accidentally
correct only for `d=2`**, and returned e.g. the **principal** character at `p=127` (`B=63=(p−1)/2`).
The χ₂ results were never affected (they used the independent `pow`-based `chi2`, and every χ₂ proof
step was verified). Re-running d=3,6 with `χ(a)=ζ_d^{dl(a)}` gives the clean law at `≤5×10⁻¹²`.

**Lesson (recorded):** the bug surfaced only because a *derived* general formula was tested against a
character order it had not been fit on (`d=3`), and produced an impossible residual. Fitting and
"verifying" with the same buggy instrument (v1's d=6 basis fit) is self-confirming; the cross-order
prediction is what exposed it. Test derived structure on cases outside the one it was read from.

## 6. Grades

| statement | grade |
|---|---|
| `sawsum_χ(c) = χ̄(c)B_{1,χ}` (non-principal χ, any p) | **`[PROVED]`** |
| `D_χ(c) = B_{1,χ}(c−χ̄(c))` | **`[PROVED]`** |
| **`sgnsum_χ(c) = 2B_{1,χ}(χ̄(c)−χ̄(c−1)−1)` (non-principal χ, any p)** | **`[PROVED]`** (floor telescoping) |
| LAW1 (`χ₂`) and `(†)` (`c=ρ`) | **`[PROVED]`** (two routes) |
| reciprocity `M(c)=−χ₂(c)M(c⁻¹)` | **`[PROVED]`** |
| v1's "χ₆ nonlinear / p-dependent" | **RETRACTED — character-function bug** |

## 7. Verification (large, exact) and review — done

- **Independent adversarial review PASSED** (`REVIEW_twisted_dedekind_v1.md`): every proof step
  re-derived on fresh instruments; the two factor/parity attacks (missing `(2−χ₂(2))`/`w/2`; even-χ
  vanishing) came back clean; the class-number input re-derived by reduced-form counting.
- **EXACT cyclotomic test** (integer-exact, not float): the SIGN law at **every non-principal
  character order, ALL `c`, 43 primes `11…219`** covering all residues `p mod12 ∈ {1,5,7,11}` —
  **0 failures**. (Higher orders also float-checked to `d≤40`, 6 primes to `p=421`, residual `≤3e-12`.)
- **χ₂ core, exact:** LAW1 at **all `c`, 217 primes `p≡3 mod4 <3000`** (0 fail); `(†)` at **569 primes
  `p≡7 mod12` up to `p=20000`** (0 fail). Firing controls: principal `χ₀` fails (residual 126);
  wrong constant rejected.

**Remaining:** the end-to-end `|FLD|=6h` re-grade (a P1/P2 assembly on `p≡19 mod24`, separate from the
identities proved here); stating `B_{1,χ}` as an explicit `L(1,χ)`/class number per odd `χ`.
