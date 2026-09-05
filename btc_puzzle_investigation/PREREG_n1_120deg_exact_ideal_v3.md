# PREREG — Is the 120° law EXACT? (`deg gcd(L*(T), L*(ζ₃T)) = 2`)

*2026-07-26. **Written before any `L*` is computed.** Arms HELD pending `experiment-designer`
sign-off (CLAUDE.md §2, mandatory). No leakage or ECDLP claim; this is pure curve arithmetic.*

> **v3 supersedes v2**, applying the five findings of the `experiment-designer` gate run on v2
> (all pre-data; no `V₁`/`V₂`/`L*` has been computed). Changes, each tagged ⟪GATE-n⟫ below:
> **(1, HIGH)** the `V₂→e₂` sign was unspecified and verdict-flipping — now pinned to `P₂ = −V₂`,
> `e₂ = (V₁² + V₂)/2`, and a new control **C-COEFF** validates `e₁, e₂` convention-independently
> (independently reproduced: correct `e₂` → `g=2`, sign-flipped `e₂` → `g=0` at `p=13`);
> **(2)** `g ∈ {1,3}` (odd) is a reachable *distinct* structure, not a law failure — given its own
> reading; the impossible `g=4` row is removed; **(3)** a concrete wall-clock budget is frozen;
> **(4)** the `V(a)=0` census is declared a **discrimination** safeguard and gets a planted control
> **PLANT-Z**; **(5)** plant angles are pinned generic. The gate confirmed the core sound: exhaustively,
> among census survivors, **`g=2 ⟺ 120° law`**.

---

## 0. What is being tested, and what it would buy

`RESULT_n1_v_sign_mechanism_v1.md` established, **numerically**, that the two Frobenius half-angles of
`H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` differ by 120° (357/357 classes, max deviation `9.5×10⁻⁴⁰`).
Equivalently: **`α₂/α₁` is a primitive cube root of unity.**

`ANALYSIS_n1_cap_anew_channel_kronecker_route_v2.md` argues that IF that ratio is exactly a root of
unity, the open cap `S_y ≤ 2` follows, via: purity (all embeddings) ⇒ every pairwise ratio has
modulus 1 everywhere ⇒ if the ratio is a **unit**, Kronecker forces it to be a root of unity ⇒ the
trace is `−2i√p·sin(θ−60°)` because `|1+ζ₃| = 1`.

**This prereg tests only the premise, exactly.** It does not test the cap and does not test
Stickelberger.

> **PRIMARY: `g(p,a) := deg gcd( L*(T), L*(ζ₃·T) )` computed exactly over `ℚ(ζ_n, ζ₃)`.
> Pre-committed prediction: `g = 2` at every census-surviving cell.**

`g = 2` at a census-surviving cell is an **exact proof** that two of the four eigenvalues differ by
exactly `ζ₃` at that cell — upgrading the 120° law there from `[VERIFIED — numeric, 9.5e−40]` to
`[PROVED — exact]`.

⟪GATE-2⟫ **The statistic's exact range is `g ∈ {0,1,2}`** on distinct-root closure configurations
(established exhaustively by the gate, and by orbit-counting: a `ζ₃`-stable set of nonzero roots has
orbit sizes divisible by 3, so `g=4` is impossible and `g=3` cannot fill a 4-set either — an odd `g`
can only be `1`). Each reachable value has a pre-committed reading in §5.

---

## 1. ⚠ Assumption audit — run BEFORE the design, results folded in

| # | assumption | status | consequence |
|---|---|---|---|
| A1 | `H¹_c(E, L_{χ₂(y)}) = H¹(A_new)`, dim 4 | derived: `H¹(C)=H¹(E)⊕H¹(E,L_{χ₂(y)})`, `6=2+4`; `F^{I_x}=0` at all 4 punctures gives `H¹_c=H¹`. ⟪REV⟫ reviewer reconfirmed `dim H¹_c=4` by Euler characteristic (`χ_c=−4`) | framing only; not load-bearing for the statistic |
| A2 | `V(a) = −tr(Frob | H¹_c)` | Lefschetz; `H⁰_c=H²_c=0`; the 3 two-torsion points contribute `χ₂(0)=0`, `O` excluded. ⟪REV⟫ leading sign is `−`; `V` purely imaginary (`≤7e−15`) | **sets the `V_m ↔ P_m` sign — see A2′** |
| A2′ | ⟪GATE-1⟫ **`V_m(a) = −P_m`** where `P_m = Σαᵢ^m` (same Lefschetz `−` as A2, over `F_{p^m}`) | ⇒ `e₁ = P₁ = −V₁`; `e₂ = (P₁²−P₂)/2 = (V₁² + V₂)/2`. **Verified this session:** the correct `e₂` gives `g=2`, the sign-flipped `e₂=(V₁²−V₂)/2` gives `g=0` at `p=13` (PLANT-A geometry) | **verdict-determining.** The `e₁` sign does **not** affect `g` (overall `T↦−T`); the `e₂` sign **does** |
| A3 | **purity holds at EVERY embedding** | `[PROVED — CITED]` (Deligne Weil II 3.2.3(2); KS Prop 2). ⚠ every numerical check on file is ONE archimedean place; all-places rests on the citation. ⟪REV⟫ this per-embedding form is the load-bearing step (S6) | load-bearing for Kronecker; not tested here; flagged |
| A4 | splitting field is CM (so `αᾱ=p` algebraically) | ⟪REV⟫ **derived from purity** (a Weil number forces `ℚ(α)` CM-or-totally-real); `ℚ(ζ_n,ζ₃)` abelian hence CM ✓ | needed for `α·(−ᾱ)=−p` |
| A5 | `α_i` are algebraic integers | `L*` monic degree 4, coefficients in `ℤ[ζ_n]` ✓. ⟪REV⟫ does **not** follow from purity — a genuine named input | Kronecker (integral ideals); S5–S7 survive with fractional ideals |
| A6 | **`e₃=−p·e₁`, `e₄=p²` FORCED by closure+purity alone** | verified by derivation + numerically. ⟪GATE-3⟫ gate reconfirmed they hold across the *entire* closure family (PLANT-B carries the same `e₃,e₄` yet gives `g=0`) | ⇒ **zero information; never evidence.** Instrument checks only |
| A7 | ⚠ existing 120°-law evidence is NUMERICAL not exact | `9.5e−40` is precision, not identity. Folder OVERRIDE. ⟪REV⟫ reviewer added an independent numeric check via `V₂` (`(S²+Q)/2=0.750000000`, 18 cells) — still numeric | **the reason for this experiment**; no float in the statistic |
| A8 | `L_{χ_a}` totally unramified ⇒ `dim H¹_c` stays 4 | record's weight-1 proof | degree-4 model |
| A9 | ⟪REV⟫ statistic must be **label-free** | the 120° *statement* is representative-dependent; `g` reads the whole multiset, so it is invariant | design already avoids the e.1 ambiguity |

**A6 + A2′ are the design's foundation:** `e₃,e₄` forced ⇒ the free parameters are exactly `(θ₁,θ₂)`
(equivalently the free `(e₁,e₂)`), so the 120° law is a genuine one-constraint reduction and the test
discriminates — confirmed exhaustively by the gate (§4 PLANT-B, and the grid).

---

## 2. Instrument

**No floating point anywhere in the signal path** (folder OVERRIDE). All arithmetic in `ℤ`, `ℤ[ζ_n]`,
`ℚ(ζ_n, ζ₃)`.

1. **`V₁(a) = Σ_{P∈E(F_p)} χ₂(y_P)·ζ_n^{a·d(P)}`** — exact element of `ℤ[ζ_n]`, cost `O(p)` after one
   `O(p)` group enumeration. **`e₁ := −V₁(a)`** ⟪GATE-1 / A2′⟫ (the record's cheap instrument).
2. **`V₂(a) = Σ_{P∈E(F_{p²})} χ₂(y_P)·ζ_n^{a·N(P)}`** — cost `O(p²)`, exact (the record's `O(p²)`
   route, `AUDIT_prereg_n1_v_sign_sweep_v2_v1.md`, replacing the `O(p⁴)` solve). Then ⟪GATE-1⟫
   **`P₂ = −V₂(a)`** and **`e₂ := (e₁² − P₂)/2 = (V₁² + V₂)/2`** — division by 2 is exact in `ℤ[ζ_n]`.
   *The `−V₂` sign is not optional: `+V₂` computes `(V₁²−V₂)/2` and turns a true law-cell into `g=0`.*
3. **`e₃ := −p·e₁`, `e₄ := p²`** — *definitions* (forced, A6), independently verified where the
   `O(p⁴)` route is affordable (C-FORCED, an instrument check only).
4. `L*(T) = T⁴ − e₁T³ + e₂T² − e₃T + e₄ ∈ ℤ[ζ_n][T]`.
5. **`g(p,a) = deg gcd(L*(T), L*(ζ₃T))` in `ℚ(ζ_n, ζ₃)[T]`** — a Euclidean GCD of two quartics. **No
   factorization, no splitting field, no ideal arithmetic**; the degree-`2(n−1)` base field is not a
   cost problem.

**Why this statistic and not the ideal test:** the ideal formulation of
`ANALYSIS_..._kronecker_route_v2.md §7` needs the splitting field of a quartic over `ℚ(ζ_n)` — degree
up to `4(n−1)`, infeasible past tiny `p`. **`g` is label-free, Galois-safe, exact, and cheap**, and
tests the same statement. *(If `g=2`, the between-pair ratio is exactly `ζ₃`, hence a unit, hence the
ideal equality of that route follows — no separate computation.)*

---

## 3. Sample — frozen before any `L*` is computed

**Selection rule (deterministic):** primes `p` with `p ≡ 7 mod 12` (secp's class), `#E(F_p)=n` prime,
increasing order.

- **STRATUM S (primary), `p ≡ 7 mod 12`:** the first **10** such primes with `p > 547`.
  *(`p>547` makes the whole stratum OUT-OF-SAMPLE: the law was measured at
  `p ∈ {13,43,127,163,211,349,397,433,547}` — all `≤547`. Those nine are IN-SAMPLE, reported
  separately, never pooled.)*
- **STRATUM C (cross-stratum control), `p ≡ 1 mod 12`:** the first **5** with `n` prime, `p>547`. The
  `e₂` dictionary is stratum-dependent and inverts (F2), so this is a genuine second condition.
- **IN-SAMPLE set I:** the nine primes above, in their own row.

**Cells:** all `(n−1)/6` **μ₆ classes** per prime — never raw `a`. **Every count names μ₆ classes and
primes separately.** (The record's repeated defect: `30/30` where the truth is `5/5`.)

**Freeze:** the prime list, the class-representative rule, the cell count per prime, ⟪GATE-3⟫ **and the
wall-clock budget below** are written to `n1_120deg_FREEZE_v1.json` and **SHA-256'd before the first
`V₁` call.** The hash goes in the RESULT.

⟪GATE-3⟫ **Budget (frozen, concrete):** per-prime cap **900 s** wall-clock for the full `V₂` sweep of
that prime; total cap **7200 s**. **ABSTAIN rule:** if a prime's `V₂` sweep exceeds its 900 s cap, or
the total exceeds 7200 s, **ABSTAIN on that prime and all larger primes in the frozen list, report the
completed primes, and never substitute easier ones.** (The record's B1 blocker: a sweep that dies at
prime 8 of 50 and gets silently re-scoped.) **Abstention is not a closure**
([[feedback_prereg_abstention_is_the_finding_2026_07_19]]).

---

## 4. Controls — every one must fire, and each is declared AS a control

| id | control | must produce |
|---|---|---|
| **PLANT-A** *(planted positive)* | synthetic quartet `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}`, `α` an exact Weil number at a **generic** angle (⟪GATE-5⟫ `θ ∉ {30,90,150,210,270,330}°`, `−ᾱ/α` not a root of unity) | **`g=2`** — the pipeline sees the thing |
| **PLANT-B** *(planted negative — discrimination)* | `{α, β, −ᾱ, −β̄}`, `α, β` exact Weil numbers at **generic** angles (⟪GATE-5⟫ as PLANT-A, for both), `β/α` not a cube root of unity (`β=−α` is admissible and generic) | **`g=0`** — a `g=2` reading is not an artifact of closure/purity |
| **PLANT-U1** *(equal-pairs degeneracy, ⟪REV e.2⟫)* | `{α, −ᾱ, α, −ᾱ}` (the `u=1` case; true bound `4√p`), `α` generic | **`g=0` AND flagged repeated-root** |
| **PLANT-Z** ⟪GATE-4⟫ *(the non-law `g=2` corner)* | the primitive-12th-root multiset with `L*(T)=T⁴−pT²+p²` (`e₁=0`, so `V(a)=0`) | **`g=2` AND removed by the `V(a)=0` census** — proves the census is what discriminates this corner, so a later census-narrowing cannot silently break `g=2⟺law` |
| **PLANT-C** *(degeneracy)* | quartet with a repeated root | **flagged degenerate**, not silently `g≥2` |
| **C-COEFF** ⟪GATE-1⟫ *(the sign catcher)* | `e₁` **and `e₂`** from the `V₁,V₂` instrument vs the `O(p⁴)` eigenvalue solve at `p=13,43` — a convention-independent method | **exact agreement.** This is the only control that exercises the `V₂→e₂` sign; a `+V₂` bug fails here |
| **C-FORCED** | `e₃=−p·e₁`, `e₄=p²` vs the `O(p⁴)` eigenvalues at `p=13,43` | agreement. ⚠ **A6: FORCED, so this is an INSTRUMENT CHECK, NOT evidence** |
| **C-CROSS** | `e₁` (and the derived `e₂`) from this pipeline vs the record's independent `V₁`/`V₂` computation | exact agreement at every cell |
| **C-NOFLOAT** | `check_no_float.sh` over the signal-path files | passes before any cell |
| **C-DEGEN/DISCRIM-CENSUS** ⟪GATE-4⟫ | count cells with `V(a)=0` (`e₁=0`) or repeated roots. **This census is BOTH a degeneracy filter AND a discrimination safeguard** — the only non-law `g=2` configs are the `e₁=0` corner (PLANT-Z) | separate row; excluded from the primary with the exclusion count printed; **the `V(a)=0` cut may not be narrowed without re-running PLANT-Z** |

⚠ **NOT a control:** the prediction that `ζ₃` lies in the splitting field (`ANALYSIS §6`) — a
consequence of the hypothesis, reported in §6 only.

---

## 5. Pre-committed readings — written before any data

| outcome | pre-committed conclusion |
|---|---|
| `g=2` at **every** census-surviving cell of stratum S | the 120° law is **`[PROVED — exact]` at the tested cells**; the Kronecker premise holds there. ⇒ proceed to Stickelberger — **only** after re-verifying that citation (three failed runs). ⟪REV⟫ per-cell only; **uniformity in `(a,p)` is NOT established by any finite sweep** |
| `g=0` (distinct roots, `e₁≠0`) at **any** cell of S | **the 120° law is NOT exact** there. A `9.5e−40` agreement that is not an identity is itself a major finding; the Kronecker route is **dead**. Report the failing cell verbatim; do not re-scope |
| ⟪GATE-2⟫ `g=1` (odd; `e₁≠0`) at a cell | a **distinct second-order structure**: a Frobenius CM pair internally spans `ζ₃` (`−ᾱ/α = ζ₃`), **not** the between-pair 120° law. Report as its own object (cf. the project's second-object lesson); it neither confirms nor refutes the between-pair law and is **not** counted as a refutation |
| `g=0` **with a repeated root** | the `u=1`/equal-pairs degeneracy (⟪REV e.2⟫): that cell's cap is `4√p`. Report in the census, not as a law failure |
| `g=2` on S but `g=0` on stratum C | the law is **stratum-specific** (`p≡7 mod12`). Re-type; secp's stratum unaffected but the mechanism is not generic `j=0` |
| any PLANT fails (incl. PLANT-Z not caught by the census) | **halt.** No cell result reported. The instrument is broken |
| budget exhausted | ABSTAIN on the remainder with the completed count. **Abstention is not a closure** |

**Falsification condition, stated once:** a single **census-surviving** cell of stratum S with
distinct roots, `e₁≠0`, and `g=0` refutes exactness. ⟪GATE-2⟫ `g=1` is **not** a refutation — it is a
distinct structure, reported under its own row. `g∈{3,4}` cannot occur (§0) and if observed indicates
an instrument fault, not a result.

---

## 6. Secondary (reported, never promoted)

- `ζ₃ ∈` splitting field of `L*` — forced by the hypothesis, informative only if it **fails** (then
  the eigenvalue computation is wrong, not the theory). ⟪REV e.3⟫ rules out `μ_n`-only but does **not**
  determine `μ(L)`, which the order-pinning step still needs.
- The order of the between-pair ratio when `g=2`: pre-committed to exactly 3. A different order ⇒ "ratio
  is a root of unity of varying order" — a different statement.
- ⟪REV §4b lead⟫ whether `L*` descends to `ℚ(ζ_n)^{⟨σ_λ⟩}` (the Galois home of the `ζ₃`, from the
  order-3 `ω:(x,y)↦(ζ₃x,y)`). Logged as an observation, **not** a pre-committed prediction.
- `S_y = max|V|/√p` per prime, exact, vs the record's `[VERIFIED, 120 primes]` cap.

---

## 7. Scope, and what this cannot do

- **Scale banner #5.** Every cell is at `p ≈ 10³`. secp is `2²⁵⁶`. `g=2` at 15 primes says nothing
  directly about secp; it establishes an exact identity at tested cells — the input the *analytic*
  route needs. The reach comes from a proof, not these numbers.
- **This does NOT prove the cap.** It tests the premise. The cap additionally needs A3 (cited, untested
  here), the order-pinning step incl. `μ(L)` (§5 row 1, ⟪REV e.3⟫), and **uniformity in `(a,p)`**
  (⟪REV e.5⟫) — none of which Kronecker or any finite sweep supplies.
- **Does not test Stickelberger** and inherits none of its unverified citation.
- ⚠ **`e₃, e₄` are forced (A6).** No count involving them may appear in any headline.

---

## 8. Status

**Arms HELD.** The v2 gate run returned five findings (one HIGH: the `V₂→e₂` sign); all are folded into
this v3. **A confirmatory `experiment-designer` re-gate of v3 is the last step before the freeze hash is
computed.** Deviations to `PREREG_n1_120deg_exact_ideal_v3_DEVIATIONS.md` as they occur, not
retrospectively.
