# Ultrathink: implications of the secp256k1 arithmetic study, and the threads it exposes

**2026-07-11.** Stepping back from the accumulated results (exact CM arithmetic +
the spectral audit) to ask what they collectively *imply* and where genuinely new,
pullable structure lives. Grounded by `thread_mu2_mu3_probe.py`. Written as a map,
not a to-do — the point is to see the shape.

---

## Part 1 — Three structural implications

### I1. μ₆ = μ₂ × μ₃ splits by ROLE, not just by factorization

The order-6 Grössencharacter `χ = −(28/π)₆⁻¹` decomposes canonically:
`χ³ = χ₋₃` (quadratic, the CM discriminant), `χ² = ` the cubic character. These two
factors play *completely different* roles:

- **μ₂ = χ₋₃ is the SUPPORT / geometry.** `a_ℓ = 0` exactly on inert primes
  (`χ₋₃(ℓ) = −1`). This vanishing is the *only* thing that ever produces a real
  spectral correlation (the rank-1 conductor shadow). It is a *support* fact —
  where the Hecke data lives.
- **μ₃ (cubic) and the full sextic phase are DECORATION.** On split primes the
  Frobenius phase `u = χ(ℓ) ∈ μ₆` is Hecke-equidistributed; it is a pure phase
  with no vanishing, hence no support effect.

This is why every "sextic/rank-3 spectral common mode" claim failed: the sextic is
a phase, and **real second moments cannot see an equidistributed phase.** The `2`
does all the spectral work; the `3` is invisible to correlations.

> **⚠ DOWNGRADED 2026-07-11 (`INTEGRITY_AUDIT_v1.md`):** I2 below is a
> **conjecture, not an established result.** It rests on Gram/spectral tests that
> proved highly confound-prone (the `1/√p` envelope and sample-set differences
> flip the verdict; my Finding-3 analysis flip-flopped twice before a clean
> same-sample envelope-preserving null settled it). The *dilution* χ₋₃ finding
> survives because it has an envelope-independent mechanism (exact shared zero
> `a_ℓ=0` on inert primes; split-only kills it; χ₋₃-alignment 0.997). But "the
> axis is *exhausted* / *no* other structure" is not proven — it is a plausible
> conjecture pending same-sample + matched-char-null re-tests of the residual
> split-only modes.

### I2. The "shadow meta-theorem" (CONJECTURE) — these constructions may only refract ONE datum

`thread_mu2_mu3_probe.py` sharpens this into a general statement about the whole
family of character/Gram constructions used in the RH-programme line:

> A feature Gram matrix indexed by primes `q` develops a common mode **iff** its
> features are residues/characters of a *shared per-ℓ quantity* — and then the mode
> is exactly the **shadow of that one shared quantity**, refracted across the q's.
> It is never independent higher-rank structure.

Evidence *(from the split-prime probe; not yet re-run under the matched-null
discipline — treat as suggestive, `RESULTS_LEDGER_v1.md` C1)*: pure `(ℓ/q)₃` →
flat; features built from the shared `a_ℓ` → a weak mode consistent with an
a_ℓ-shadow; `a_ℓ=0`-on-inert → the strong χ₋₃ shadow. **Conjectured consequence:**
the spectral/Gram direction may have essentially one degree of freedom to show (the
Hecke datum a_ℓ, support χ₋₃). *This is a conjecture, not established* — the Gram
tests are confound-prone (Finding-3 flipped twice), and the residual split-prime
modes have not been re-tested under same-sample + matched-character null. If it
holds, further structure is sought off this axis; either way the p-adic / dynamical
threads below are independent of it.

### I3. One ideal + one character generate the entire first ledger

`(π_p − 1)` gives the amicable pair, the GLV lattice, the unique prime-order twist,
the shared-M norm form. `χ = −(28/π)₆⁻¹` gives the L-function, the trace law, the
amicable closure constant. Everything exact about the curve is downstream of these
two objects. The open question is whether they descend from a single motivic object
(a CM motive with its Grössencharacter) in a way that makes the amicable relation
`π_n = π_p − 1` a *morphism*, not a coincidence.

---

## Part 2 — Where the genuine further structure is (prioritised threads)

The spectral axis is closed (I2). The live structure is in the p-adic, dynamical,
and motivic directions.

### ★ Thread α (deepest) — the formal group is the p-adic L-function gateway

Everything we found about the formal group points at Katz's p-adic L-function of ψ,
the one classical direction we have only touched (Iwasawa thread G):

- The **ASD congruence** `7^k C(3k,k) ≡ a_ℓ (mod ℓ)` and its **three-term** lift
  `b_{ℓ²} − a_ℓ b_ℓ + ℓ ≡ 0 (mod ℓ²)` are the *definition* of the formal group's
  connection to the eigenvalues — and Katz builds his p-adic L from exactly this
  moment/formal-group data.
- The **mod-ℓ³ upgrade locus `{a_ℓ = ±1}`** (= the anomalous primes 61,127,397,547
  plus 37) is unexplained combinatorially — but `a_ℓ = 1` is precisely where the
  **unit root ≡ 1** and the p-adic L / p-adic height *degenerate* (trivial-zero /
  exceptional-zero phenomena). Strong candidate: the ℓ³-locus is the p-adic special
  locus.
- **δ_ℓ = (b_ℓ − a_ℓ)/ℓ is non-elementary Gauss-sum content** — exactly what the
  **Gross–Koblitz formula** expresses via the p-adic Γ-function. Candidate: δ_ℓ is a
  p-adic Γ (Diamond log-Γ) value. This would upgrade "non-elementary" to a *closed
  p-adic form*.
- **256-bit showcase:** compute the unit root `α_p` of E at p to high p-adic
  precision *from the explicit formal group* (Honda/Artin–Hasse), the concrete
  large instance of the p-adic theory. Rubin's `μ = 0` (CM) is known; the λ-invariant
  and the p-adic L-value at the 256-bit p are the uncomputed showcase.

**First concrete step:** compute the p-adic unit root via the formal-group log
(Fuss–Catalan recursion), check `{a_ℓ=±1}` against unit-root ≡ ±1 mod ℓ² and against
Rubin/Katz trivial-zero criteria on the small anomalous primes; test the
Gross–Koblitz identification of δ_ℓ against p-adic Γ on ℓ < 500.

### ★ Thread β — the amicable/aliquot map as a dynamical system

`T : q ↦ #E(F_q)` on CM primes is a genuine dynamical system we have only sampled.
`π_n = π_p − 1` is a *shift* in ℤ[ω]; the amicable pair is a 2-cycle; we found the
closure constant (13/50 = S–S Conj 40) and **no 3-cycles**.

- **Is the absence of 3-cycles structural or just rare?** Closure = a chain of Hecke
  unit alignments (the 13/50 mechanism). A 3-cycle needs two consecutive alignments;
  the expected density is computable exactly from the mod-84 class census squared —
  derive it and state whether 3-cycles are *forbidden* for j=0 or merely `O(X/log³X)`.
- **The prime-producing quadratic** `Q(c) = N(π_p − c) = c² − tc + p` (disc −27M²)
  packages the c-neighbors: `Q(0)=p, Q(1)=n, Q(−1)=n_t`. Its aliquot graph and the
  Hardy–Littlewood constant 2.277 are a self-contained object; the amicable pair is
  the `{0,1}` edge. **A "CM aliquot dynamical zeta"** `ζ_T(s)` packaging the periodic
  orbits (fixed points = anomalous primes, 2-cycles = amicable pairs) would encode
  13/50 as a residue — a new object, cleanly defined.

**First concrete step:** derive the exact expected 3-cycle density from the mod-84
class census (product of two alignment probabilities over twin-triple norms); compare
to the empirical zero-count bound; if it is positive, predict the height of the first
j=0 3-cycle.

### Thread γ — the "shadow meta-theorem" as an actual theorem

I2 is currently an empirical pattern. Prove it: for a self-dual CM Hecke L-function
of ∞-type (1,0), the second moment of the normalized coefficients across any prime-
indexed residue family depends only on the **quadratic** part χ₋₃ (via the
supersingular support), and the cubic/sextic parts contribute zero to all real
second moments (equidistribution of the Grössencharacter phase). This would convert
the entire cluster of failed "sextic common mode" claims into a *theorem* — and it
sharply predicts where the cubic *does* appear: the **Sym² L-function**
`L(Sym²E,s) = L(ψ²,s)L(χ₋₃,s−1)`, whose `L(ψ²)` carries the cubic character `χ²`.
The honest test of "where μ₃ lives" is the third moment / Sym² zero statistics, not
first-moment Grams.

### Thread δ — the motivic unification (π_p−1) ⊕ χ

Make I3 precise: is there a single object (the CM motive `h¹(E)` with its
Grössencharacter, or the Hecke character ψ itself as a motive over K) from which
both `(π_p−1)` and `χ` are readings, so that `π_n = π_p − 1` is the image of a
canonical map (a Hecke correspondence / the "−1 translation" on the CM abelian
variety)? This is the most speculative but would explain the amicable relation as
structure rather than arithmetic accident.

---

## Part 3 — What this pause settles

- The **spectral/Gram axis is closed** (I2): it refracts exactly one datum (a_ℓ,
  support χ₋₃); no further CM structure is hiding there. This retires a whole class
  of "common mode / spectral gap" probes as answered.
- The **μ₆ = μ₂ × μ₃ role split** (I1) explains *why*: the 2 is support (visible),
  the 3 is phase (invisible to first/second real moments; lives in Sym²).
- The **live frontier is p-adic (α), dynamical (β), and the theorem (γ)** — all
  concrete, all off the exhausted spectral axis. Thread α (formal group → Katz
  p-adic L, with δ_ℓ = Gross–Koblitz and `{a_ℓ=±1}` = the p-adic special locus) is
  the single richest pull: it reconnects the formal group (§2), the Hecke character
  (§3), the anomalous primes, and Iwasawa μ=0 into one object, with a 256-bit
  showcase.
