# RESULT — the Stickelberger citation is VERIFIED (Katre), with two named caveats

*2026-07-27. Output of a `citation-verifier` run (isolated context, verbatim primary text in hand).
Discharges the `[UNVERIFIED CITATION]` debt on Stickelberger that failed three prior runs. No leakage
or ECDLP claim.*

---

## 1. Verdict

> **Classical Stickelberger SUPPORTS the intended use** — the prime-ideal factorization of Gauss/Jacobi
> sums over `ℚ(ζ_m)` for **`m = 12` (composite, not a prime power)** and **residue degree `f = 2`**
> (`q = p²`, forced when `p ≡ 3 mod4`). The `[UNVERIFIED CITATION]` on (D2) can move to
> **`[CITED — verified]`.**

**Reference (verbatim text read):** S. A. Katre, *"Gauss-Jacobi Sums and Stickelberger's Theorem"*
(bprim.org/…/jacn.pdf): Prop 1(f) p.76; Prop 2 + digit-sum summary p.81; the ramification descent
`P = P̄^{p−1}` p.80; explicit Jacobi factorization Prop 4(ii) p.83–84. Corroborated (arbitrary-`m`
point) against Michigan lecture notes L9 and Wikipedia *Stickelberger's theorem*.

| sub-claim | verdict | why |
|---|---|---|
| (1) `m = 12` composite | **CLEAN** | Stickelberger is stated for **arbitrary `m`** coprime to `p` (Katre: "Let `m` be a fixed positive integer, `(p,m)=1`"); no prime/prime-power hypothesis exists to violate |
| (2) residue degree `f = 2` | **CLEAN** | stated over `F_q = F_{p^f}` for **general `f`** via the base-`p` digit sum `s(α)` (Katre §3, Prop 2); `f = ord_{12}(p) = 2` is exactly this case |
| (3) Jacobi ideal-equality | **SUPPORTS-WITH-CAVEAT** | `(J₁)=(J₂) ⟺` equal Stickelberger exponent vectors `θ_{j,k}`; holds for our `(j,k,m)=(4,3,12)` — see caveat 1 |

---

## 2. The three caveats to carry with the promotion (load-bearing)

1. **Composite-`m` hypothesis subtlety.** Katre's Prop 4(ii) is *printed* with hypothesis
   `jk(j+k) ≢ 0 (mod m)`, which our exponents `(j,k)=(4,3)`, `m=12` **violate** (`4·3·7 = 84 ≡ 0
   mod 12`, precisely because `12` is composite). But the **proof** uses the weaker, correct hypothesis
   `j, k, j+k ≢ 0 (mod m)` (`4,3,7` all `≢ 0 mod 12`) ✓. **Cite the proof's hypothesis** (or route
   through Prop 3′ + Prop 1(f)), not the printed one.
2. **Use the `F_q` digit-sum form, not the `ℓ ≡ 1 mod m` form.** The "`χ` a character of the prime
   field `F_ℓ`" packaging (Washington/Lang/Michigan) is the **`f = 1`** regime and does **not** cover
   `f = 2`. The correct lineage is Katre §3 / Ireland–Rosen Ch. 14 / Gross–Koblitz.
3. **Stickelberger gives the IDEAL, not the value.** It yields `(J₁)=(J₂)` (equivalently `J₁/J₂` a
   unit), **not** `J₁ = J₂`. The residual root of unity is pinned separately by Kronecker + reductions
   mod the primes over 2 and 3 — not by Stickelberger. (The Jacobi-sign-law document already does this
   in its (D4)–(D6); no overclaim.)

**Honesty note from the verifier:** verified against Katre (verbatim) + Michigan L9 + Wikipedia; did
**not** open Ireland–Rosen Ch. 14, Washington §6, or Lang Ch. 1. The scoped debt ("does a standard
source state it for composite `m`, `f=2`") is discharged by Katre; Ireland–Rosen Ch. 14 is the natural
textbook to open next if a canonical citation is wanted.

---

## 3. What this moves, and what it does NOT

**Moves (recommended):**
- **`RESULT_jacobi_sign_law_stickelberger_v1.md` (D2): `[UNVERIFIED CITATION]` → `[CITED — verified]`**
  (Katre, with the three caveats). This is a grade move on that separate result; applying it there is a
  new version of that file — **offered, not yet done.**

**Does NOT move — the 120° route's remaining gap is now sharp:**
- The verifier confirmed the **TOOL** (Stickelberger applies for `m=12`, `f=2`, and reduces
  `(α₁)=(α₂)` to an exponent-vector equality). It did **not** confirm the **PREMISE** that the
  **`a ≠ 0` twisted** eigenvalues of `H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` **are** Jacobi sums Stickelberger
  governs.
  - **`a = 0`:** the `A_new` eigenvalues **are** those Jacobi sums (supersingular, `√p·μ₁₂`) — tool
    directly applies.
  - **`a ≠ 0`:** `L_{χ_a}` is a Lang-torsor character of the group `E(F_p)`, **not** manifestly a
    multiplicative character of `F_q^×`, so the eigenvalues are not *obviously* Jacobi sums. **This is
    the one open premise** for using L-Stick to prove uniform `u = ζ₃` (`ANALYSIS_..._v3.md §4`).

> **Net:** the Stickelberger citation is verified and the ideal-equality machinery is unblocked for the
> `a=0` anchor. **The sole remaining question for uniformity is whether the `a≠0` twisted eigenvalues
> are Stickelberger-governed sums** — the next analytic target (or, failing it, the L-mono monodromy
> route).
