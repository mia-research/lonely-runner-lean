# AUDIT — the four cross-domain "ports" (RH/LRC methodology → curve), premises checked against the record

*2026-07-24. Object-level audit of an externally-supplied synthesis, run BEFORE any of its
proposals were tested. Script: `xdomain_derivation_checks_v1.py` (DC1–DC4, all pre-data).
No leakage, key-recovery or ECDLP claim.*

> **Why this document exists.** The prior external critique on this project
> ([[feedback_verify_external_critiques_2026_07_17]]) was **wrong in every particular and right in
> thesis**. The rule that came out of it is to check the two separately, **thesis first**, and to
> trace *items*, not tags. This audit checks each proposal's stated premise against the object it
> names — not against my summary of it.

---

## 0. Verdict in one table

| # | Proposal | Its stated premise | Premise status | What survives |
|---|---|---|---|---|
| 1 | RH spectral-ceiling projection → the `½`-saturation | `χ₂(y)` saturates ½ its ceiling; same-dim `bx+cy` reaches 0.876; N1 unexplained | **ACCURATE** (M3, §VII.5, §XI.10) | The *thesis* — test it at eigenvalue level. Its named **mechanism (μ₃ projection) is REFUTED by DC1.** |
| 2 | LRC boundary-set exactness → the `C_T` carry-leak | "you concluded [the 2–3%] is a deterministic arithmetic seam … not statistical noise" | **INVERTED** — the record concluded the opposite | The **method** (event-complete ≫ sampled) is a real power gain. Arm A. |
| 3 | `φ(n)` grid law → forced isolation of `[k]P` | perfect isolation at coprime `r/n`, `φ(n)` instants, Fourier modes vanish | **VACUOUS AT SECP** (DC3: `n` prime ⇒ `φ(n)=n−1`) | Its curve question is already answered and proved (Cap Law Thm B). |
| 4 | `φ(n)`-averaging / log coordinate → amicable transfer | "`t_n = 2 − t_p` acts as the arithmetic boundary condition" | **FORCED IDENTITY** (DC2), zero information | The underlying frontier is real and open — but the record's **parity theorem** already voids the naive channel. |

**Thesis-level:** the synthesis's closing instruction — *"stop treating the curve statistically; apply
boundary-set exactness"* — is **worth acting on**, and is the one thing here that changes what gets
run. It is aimed at a conclusion the record does not hold (see §2), but the method it names is a
genuine 6–30× power gain over the instrument actually used. That is Arm A.

---

## 1. Play 1 — premise accurate, mechanism refuted

**Premise, checked.** `POSITIVE_FINDINGS_MASTER_v4.md:166` (M3) records saturation as
*measured max ÷ its own ceiling `dim·√p`*: `bx+cy` (dim 4) **0.876**; `bx` (dim 3) 0.909;
`χ₂(x)` (dim 2) 0.947; **`χ₂(y)` (dim 4) 0.470**, converging to ½. `:189` (N1) calls it
*"the one measured anomaly in the set with no account."* The synthesis states this correctly,
including the same-dimension control. ✔

**One citation-strength correction.** The synthesis says the ceiling mechanism is one *"you proved
for Dirichlet families."* The preprint's own abstract says: *"Assuming a moment-pumping hypothesis
for horizontal zero displacement, the resulting spectral ceiling produces a zero-free region"* —
unconditional **only in the certified finite regime** (`Q₀={3,5,7,11,13}`, `X∈[100,5000]`).
So the transferable object is a **conditional mechanism**, `[CITED-CONDITIONAL]`, not a theorem.

**Name collision, flagged.** The synthesis writes *"bounding `λ_max(C_T)`"* of the RH side. The RH
preprint has **no `C_T`**: its operators are the residue Gram operator `κ` and the projected
obstruction operator `κ_{+,r}^⊥`; its ceiling constant is `C(X,k,r)`. The curve's `C_T` is the 9×9
addition-carry transition operator. **Two unrelated objects, joined only by a symbol.** This is the
shape of a spurious bridge and is why the arms below are built on the *mechanism*, never the symbol.

**DC1 — the proposed mechanism is refuted, by the same argument that already killed two others.**
The GLV endomorphism `β(x,y) = (ζ₃x, y)` **fixes `y`** and acts on the group as `[λ]`. Hence in
`V(a) = Σ_P χ₂(y_P)·e(a·d_P/n)`, substituting `P = βQ` gives

> **`V(a) = V(aλ)` exactly** — verified to machine epsilon at **11 primes** (`p = 13…397`, `n` prime).

So `β` is an **isomorphism `H¹(a) → H¹(aλ)` between different twisted cohomologies**. It does not act
within fixed-`a` cohomology and therefore **cannot split `H¹(a)`** — precisely the defect that
`NEXT_DIRECTIONS_v1.md §4` records for `[−1]` and `ζ₄`. A μ₃-residue projector is not available.

⚠ **`V(a) = V(aλ)` is FORCED by the substitution.** The 11/11 agreement is an **instrument check on
my own code and carries zero information as evidence.** What it settles is the *availability of the
mechanism*, by derivation.

⚠ **Refuting the mechanism does not refute the thesis.** That `½` is a rank-drop remains open and is
exactly what Arm B measures.

## 2. Play 2 — the premise is inverted; the method is the yield

**What the synthesis asserts we concluded:** *"a 2-3% inter-coordinate coupling in the transition
operator `C_T`, which you concluded is a deterministic arithmetic seam (a carry-leak in the lattice
rounding process), not statistical noise."*

**What the record actually says — three sources, all the other way:**

- `ANOMALY_DRILL_01_CT_SPLIT_v1.md` (2026-07-17): against a coupling-free surrogate with the same
  marginals and length, `δ=|λ₂−λ₃|` gave **z = +0.13**; the pooled `G²` factorization test gave
  **`G² = 16.80`, 16 df, p = 0.40**, **z = −0.19**; swap-even/odd channels z = −0.55 / +0.34. Real and
  surrogate deviations scale with the **same exponent** (`n^−0.596` vs `n^−0.584`).
- `masked_structure_findings_v35.md §10`: the proposed **"flap-translation shear" mechanism is
  refuted — it predicts zero coupling, not the 2–3%.**
- `POSITIVE_FINDINGS_MASTER_v4.md:170` (M7): *coupling `< ~1.6%` at `n ≈ 1.3×10⁵`*, control fired
  (plant at ε̂=1.6% → z=8.1), **no power below ~1.6%, zero power at 2²⁵⁶**.

⚠ **The nuance that must survive this correction.** `AUDIT_negative_bias_session2to4_v1.md §2`
records that the *further* claim **"the observed 2–3% is finite-n" was asserted beyond what the v35
data showed.** So the accurate state is **neither** the synthesis's "deterministic seam" **nor**
"it's noise": the coupling is **bounded below ≈1.6–2% with fired controls, and undetermined below
that.** A magnitude with power and scope — not a verdict either way.

**What survives, and it is the best item here.** The instrument that produced the bound used a
**single generator's orbit** — `n` transitions, scope *"this orbit, this generator, this prime."*
The state map `s(P,Q)` is defined for **all** pairs. Enumerating **all `n` step sizes × all `n`
positions** gives `n²` transitions: the complete population, generator scope removed, floor
`√30/n` instead of `√(30/n)`. **That is the boundary-set port, and it is a 6–30× power gain.**
→ **Arm A**, `ct_event_complete_v1.py`.

## 3. Play 3 — vacuous at secp, and its curve question is already proved

**DC3.** The `φ(n)` law selects times `{δt} = r/n` with `gcd(r,n)=1`, giving `φ(n)` instants per
period. **secp's `n` is prime ⇒ `φ(n) = n−1` ⇒ every `r ≢ 0` qualifies.** The selection — the entire
discriminating content of the law — is **vacuous**. Its power comes from *composite* `n`.

**Second, structural, obstruction.** The law's hypothesis is that positions are `{v_j t}` with `v_j`
in **exact arithmetic progression**. The map `d ↦ eis([d]G)` is not an AP in the fundamental domain;
that it is not *is* the ECDLP scramble. The port has no hypothesis to apply.

**And the curve question it poses is already answered.** *"Are there specific multiples `[k]P` where
the point is structurally forced into perfect isolation?"* — **yes, `k = λ`**, and it is on file
**`[PROVED]`**: `cap_law_proofs_v1.md` Thm B, `σ(βx) = σ(x)` — the sextant index is invariant under
the GLV multiple. Not a new lever; a restatement of a proved law.

⚠ Scope: this retires **the port as stated**. It says nothing about the `φ(n)`-residue line's value
in its own domain, where `n` ranges over composites.

## 4. Play 4 — the "boundary condition" is an identity

**DC2.** For an amicable pair, `#E(F_p) = n` and `#Ẽ(F_n) = p`, so `t_p = p+1−n` and `t_n = n+1−p`,
hence

> **`t_p + t_n = 2` identically** — confirmed at the real 256-bit values
> (`t_p = 432420386565659656852420866390673177327`).

This is an identity **in the definition of amicability**. It cannot function as an informative
"arithmetic boundary condition"; it constrains nothing that amicability did not already fix.

**The frontier underneath is real, and the record is ahead of the proposal.** The non-homomorphic
amicable correspondence is open (§XI.3 / §X.3), and `NEXT_DIRECTIONS_v1.md #2` already specifies why
the one test run against it was uninformative: **`eis_p(X_d)` is even in `d` and `eis_n(d)` is odd in
`d`, so the linear channel between them is exactly `0` by parity, before any data.** The proposal as
stated adds a coordinate change but not an odd-in-`d` lift, so it would **re-run a forced zero**.
The parity-legal rebuild (`y` or `xy`, both proved odd in `d`, reduced mod `π_n`) is the live version
and needs its own pre-registration.

---

## 5. What this audit does NOT say

- It does not say the synthesis is wrong in thesis. Its closing instruction is acted on, in Arm A.
- It does not close `C_T`, N1, the amicable correspondence, or any frontier. Play 2's premise
  being inverted **restores** the item to "bounded with power, undetermined below the bound".
- DC1–DC4 are **forced** results. They settle *availability of mechanisms*, by derivation. None of
  them is evidence about the curve, and none may be counted as a confirmation.
