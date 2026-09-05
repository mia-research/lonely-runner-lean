# REVIEW — twisted sawtooth/sign family + (†): adversarial pass

*2026-07-24. Independent adversarial review of `RESULT_twisted_dedekind_structure_v2.md`
(laws S, D, SIGN) and `RESULT_fld_dagger_proof_v1.md` (the (†) proof, both routes), with the
v38 setup (`masked_structure_findings_v38.md §1–2`) as context. Every load-bearing step was
re-derived by hand and re-verified by exact/high-precision numerics on a fresh instrument
(independent character construction; class number by reduced-form counting, not by the cited
formula). Reviewer was not shown the session narrative — only the claims + criteria.*

## Verdict

**The proofs are correct.** Claims S, D, SIGN, the χ₂ corollary `B_{1,χ₂}=−h`, and (†)
(`T=3h`) all hold, by both the floor-telescoping route and the orbit-collapse route. No gap,
no unjustified step, no false claim was found in the reasoning. Two immaterial documentation
points are noted at the end (neither affects a proof).

This is a clean result, not an "issues manufactured to fill the report" result. The numbers
below are the object-level checks, each naming what it counts.

---

## What was checked, step by step

### Load-bearing classical inputs (the proofs stand on these)
1. **`Σ_{s} χ(s)=0` for non-principal χ** (orthogonality). Used in S, D, SIGN. Correctly
   restricted: the principal character is excluded, and the SIGN law genuinely fails for χ₀
   (residual `−126` at p=127; see note 1). ✓
2. **`χ(c⁻¹)=χ̄(c)`** on `(ℤ/p)*` (values on the unit circle ⇒ inverse = conjugate). ✓
3. **Bijection `t=cs mod p`** on `(ℤ/p)*` (gcd(c,p)=1). ✓
4. **Finite class-number formula `h(−p)=−(1/p)Σ_{a}χ₂(a)a`**, `p≡3 mod4`, `p>3`, `w=2`.
   *Independently confirmed* — see the explicit factor check below. ✓ `[CITED — classical]`
5. **Φ₆ relations `ρ²=ρ−1`, `ρ³=−1`, `ρ⁶=1`** for a primitive 6th root, + Euler's criterion
   `χ₂(a)=a^{(p−1)/2}`. ✓

### Step 1 — Floor identity `[cs mod p > s] = 1 − (⌊cs/p⌋ − ⌊(c−1)s/p⌋)`
Re-derived from `s = p·d + (cs mod p) − ((c−1)s mod p)`, where `d` is the floor difference.
With `A=cs mod p, B=(c−1)s mod p` both in `{1,…,p−1}` (B≠0 uses `c≠1`), `p·d = s−A+B ∈ {0,p}`
forces `d=0 ⟺ A>s` and `d=1 ⟺ A<s`. **The boundary case `A=s` cannot occur** (`A=s ⇒
(c−1)s≡0 ⇒ c=1`, excluded), so the "iff" is complete and there is no third case. **CORRECT.**
Exact check: 0 mismatches over all `p<200`, all `c∈{2,…,p−1}`, all `s`; `cs mod p = s` occurred
**0** times (diagonal empty).

### Step 2 — Sawtooth law S  `Σχ(s)((cs/p)) = χ̄(c)B_{1,χ}`
`{cs/p}=(cs mod p)/p` genuinely (`cs mod p∈{1,…,p−1}`, never integer). Split off `−½Σχ(s)=0`;
substitute `t=cs mod p`, `χ(s)=χ(c⁻¹t)=χ̄(c)χ(t)`. **CORRECT.** Exact check: 0 fails.

### Step 3 — Claim D  `Σχ(s)⌊cs/p⌋ = B_{1,χ}(c−χ̄(c))`
Algebra from `cs mod p = cs − p⌊cs/p⌋`, using `Σχ(s)s=pB_{1,χ}` (definitional) and Step 2.
`c` is used consistently as the integer representative in `{2,…,p−1}`. **CORRECT.** 0 fails.

### Step 4 — Telescope / SIGN  `sgnsum = 2B_{1,χ}(χ̄(c)−χ̄(c−1)−1)`
`M_χ(c)=Σχ(s)−D_χ(c)+D_χ(c−1)=D_χ(c−1)−D_χ(c)`. **The one subtlety worth stating:** the
constant `−1` in the answer is `(c−1)_{int} − c_{int}`, and this equals `−1` **only because
`c∈{2,…,p−1}` makes `c` and `c−1` consecutive integer representatives** — which is exactly what
`c≠1` guarantees (and `c−1≢0` makes `χ̄(c−1)` well-defined). If `c=1` were admitted the
telescope would break; it is correctly excluded. Then `sgn=2[·]−1` is *exact* (never applied at
0, since the diagonal is empty). **CORRECT.** Exact check: 0 fails over 250 (χ,c) triples
including complex χ of orders 3,4,6 across 9 primes.

### Step 5 — (†) as corollary
- `χ₂(ρ)=ρ^{(p−1)/2}=ρ³=−1`: needs `(p−1)/2 ≡ 3 (mod 6)`, which is exactly `p≡7 mod12`. ✓
- `χ₂(ρ−1)=χ₂(ρ²)=χ₂(ρ)²=1` via `ρ²=ρ−1` (Φ₆). ✓
- ⇒ `sgnsum_χ₂(ρ)=2(−h)(−1−1−1)=6h`. ✓
- **Reflection halving `Σ_{1}^{p−1}=2Σ_{1}^{(p−1)/2}`**: `s↦p−s` is a fixed-point-free
  involution (odd p); `χ₂(p−s)=−χ₂(s)` and `sgn(ρ(p−s) mod p−(p−s))=−sgn(ρs mod p−s)` — the
  two flips cancel, summand invariant, so `T=3h`. **CORRECT.** Exact check on the invariance:
  0 non-invariances.

### Orbit-collapse route (Step B of the (†) file), the one genuinely new step
`sgnsum(ρ)=6·sawsum(ρ)` via size-6 `⟨ρ⟩`-orbits. Re-derived all six terms: with
`χ₂(a_i)=(−1)^iχ₂(s)` and `a_{i+3}=p−a_i` (from `ρ³=−1`), each sign term `=χ₂(s)sgn(ρs mod p−s)`
and each sawtooth orbit-sum `=χ₂(s)sgn(ρs mod p−s)`, the case split driven by `ρ²=ρ−1 ⇒
a₂=a₁−a₀` (no wrap) vs `a₂=a₁−a₀+p` (wrap). Consistent with the floor-telescoping value.
**CORRECT.** Exact check: **580 orbits** over all `p≡7 mod12, p<400` — sawtooth collapse,
sign collapse, and "every one of the 6 terms equal" all pass, 0 fails.

---

## The specific attacks requested

- **Missing `(2−χ₂(2))` or `w/2` factor in `B_{1,χ₂}=−h`?** No. Computed `h(−p)` independently
  by counting reduced primitive forms of discriminant `−p` (matches known `h(−7)=1, h(−23)=3,
  h(−47)=5, h(−71)=7, h(−167)=11`, …), then checked `−(1/p)Σχ₂(a)a` against it for **all
  `p≡3 mod4` in [7,500): 0 mismatches**. The weighted-sum form is exact as cited; the
  `(2−χ₂(2))` factor belongs to the *different* half-interval form `h=Σ_{0<a<p/2}χ₂(a)/(2−χ₂(2))`,
  not to this one. `p≡7 mod12 ⇒ p≥7 ⇒ w=2`, so no root-of-unity factor. ✓
- **Even χ ⇒ `sgnsum=0`?** Yes. `B_{1,χ}=Σ_{t≤(p−1)/2}χ(t)=0` for even non-principal χ (full
  sum 0 + even symmetry), matching the `s↦p−s` antisymmetry of the summand. Exact check: 29 even
  non-principal characters, `B_{1,χ}=0` and `sgnsum=0`, 0 fails. ✓
- **Reflection halving genuinely valid?** Yes — verified the two sign flips cancel term-by-term
  (0 non-invariances), and the involution is fixed-point-free. ✓
- **Hidden assumptions `c−1≢0`, `χ(c−1)` defined?** Present and discharged by `c≠1`; `c=ρ` gives
  `ρ−1=ρ²≠0`. ✓

## Full-result numeric (belt-and-suspenders)
`T_full=sgnsum_χ₂(ρ)=6h`, `T=3h`, `sawsum_χ₂(ρ)=h`, `χ₂(ρ)=−1`, `χ₂(ρ−1)=1`, and both
primitive 6th roots give `6h`: **78/78 primes `p≡7 mod12`, `p<2000`**, 0 fails.

---

## Two immaterial notes (no proof impact)

1. **v2 §1 "misses χ₀ by residual 126."** Accurate, but for the **SIGN** law (LHS 0, RHS −126 at
   p=127). The **SAWTOOTH** law residual for χ₀ is 63, not 126. The sentence sits under the "two
   laws" heading, so quoting one of the two residuals is fine; just noting the 126 is the sign
   law's, not the sawtooth's. Does not affect the exclusion argument, which is correct.
2. **Claim D is stated for non-principal χ, but actually holds for χ₀ too** (checked: LHS=RHS at
   p=127 for c=2,3,5), by a coincidental cancellation — its S-based derivation doesn't apply to
   χ₀, but the identity is true there anyway. The stated "non-principal" scope is merely
   conservative for D; not an error.

## Out of scope (flagged by the authors themselves, not a gap here)
The `p≡7 mod12` vs `p≡19 mod24` reconciliation for the *downstream* `|FLD|=6h` promotion lives
in `RESULT_fld_classnumber`, not in the proofs reviewed here. The (†) statement and its proof are
self-contained on `p≡7 mod12`; whether that set matches the `|FLD|` document's regime is a
cross-reference to check when promoting `|FLD|`, and is correctly listed as pending in both files.

## Bottom line
Load-bearing classical inputs: (i) the sawtooth/character substitution `t=cs mod p` +
`Σχ(s)=0`, and (ii) the finite class-number formula `h(−p)=−(1/p)Σχ₂(a)a` (independently
re-derived here). Everything else is elementary and exact. **Both routes to (†) are valid; laws
S, D, SIGN are proved as stated for non-principal χ, any prime p.** Recommend promoting
`RESULT_fld_dagger_proof_v1.md` from `[PROVED — pending independent adversarial review]` to
`[PROVED]` on the strength of this pass.
