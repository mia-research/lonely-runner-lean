# RESULT — the `m`-law route to a 120° cell at secp scale: the anchor cell holds exactly, the propagation to `a≠0` does not follow

*2026-07-30. Tests a four-step chain proposed in session (`m=1` ⇒ eigenvalues ⇒ 120° ⇒ "the empirical
nulls are bypassed at `2²⁵⁶`"). Script `test_120deg_anchor_from_mlaw_v1.py`, log `…_v1.log`. Exact
integer arithmetic only: roots of unity carried as exponents in `ℤ/24`, membership **derived** from the
defining polynomial by exact reduction in `ℤ[x]/Φ₂₄ = ℤ[x]/(x⁸−x⁴+1)`, never asserted. No float in the
signal path. No leakage, key-recovery or ECDLP claim.*

**Grades used.** `[PROVED-exact]` = exact identity, all `p` in the stated class. `[CITED — verified,
caveated]` = `citation-verifier` discharged with load-bearing caveats. `[MEASURED — does not survive]` =
the project has an existing measurement that the property fails at the stated object.

---

## 1. Headline — steps 2–3 hold, step 4 does not follow, step 1 is not load-bearing *for `g`*

> **`[PROVED-exact]` Steps 2 and 3 hold** (with one misstatement corrected, §3). At `m=1` the normalized
> characteristic polynomial `z⁴+z²+1` factors as `(z²+z+1)(z²−z+1)` and its root multiset is
> `√p·{ω, ω², −ω, −ω²} = √p·{ζ₂₄⁴, ζ₂₄⁸, ζ₂₄¹⁶, ζ₂₄²⁰}`, orders `[6,3,3,6]` — **identical to the
> `RESULT_jacobi_closed_form_m_law_v4.md` ERRATUM set** `√p·{ω,ω²,ζ₆,ζ₆⁵}`, and **not** `√p·{±ζ₁₂,±ζ₁₂⁵}`.
> Applying the N1 route's own statistic to it gives **`g = 2`**: the 120° law holds at the anchor,
> for every `p` in the class, hence at secp's own `p`.

> **Step 1 IS load-bearing for the `g=2` conclusion — §4 CORRECTED 2026-07-30, see §4a.** `g = 2` holds
> for `m ∈ {−1, +1}` and fails (`g = 0`) for `m ∈ {−2, 0, +2}`. The *abstract* implication is therefore
> `g=2 ⟸ k(m) ∈ {6,12}`, weaker than `m=1` — **but the alternative branch the `m`-law actually realizes
> at `p ≡ 7 mod 12` is `m = −2`, not `m = −1`** (A2.1 H2), and `m = −2` gives `g = 0`. So the
> cubic-residue symbol decides whether the 120° lock exists at all in this class. The control fires, so
> `g=2` is not vacuous.

> **✗ Step 4 does not follow, for three independent reasons (§5).** The object `m=1` governs is the
> **`a=0` untwisted-supersingular anchor**; the 120° law's open gap is **uniformity over `a≠0`**, and
> `a=0` is outside the census by construction. Worse, the specific property step 4 leans on —
> *each `αᵢ` is `√p` × a root of unity* — is the one property the project has **already measured as NOT
> surviving the twist**.

---

## 2. What was run

| id | check | method | result |
|---|---|---|---|
| **T1** | root system of `z⁴+mz²+1`, `m ∈ {−2,−1,0,1,2}` | exact reduction in `ℤ[x]/Φ₂₄`, brute-force over all 24 exponents; `m=±2` multiplicity from `disc = m²−4 = 0` | derived, table §3 |
| **T2** | every ordered ratio in the `m=1` multiset | exponent subtraction in `ℤ/24` | table §3 |
| **T3** | `g` = #ordered pairs with ratio `ζ₃` (= `deg gcd(L*(T), L*(ζ₃T))`), all five `m` | integer | **`g=2` iff `m=±1`**; `g=0` for `m ∈ {−2,0,2}` |
| **T4** | secp inputs | Python `int`, `pow` | `p mod 4=3`, `p mod 3=1`, `p mod 12=7`, `7^((p−1)/3) ≢ 1` ⇒ **7 a cubic non-residue** |
| **T5** | normalization `char(t)=t⁴+m·p·t²+p²` under `t=√p·z` | symbolic | `p²(z⁴+mz²+1)` — consistent |

**Counting honestly (drill rule).** T1–T3 are **derivations, not evidence**: five `m`-values, all
algebraically forced, zero statistical content. The information here is the *implication structure*, not
a tally. T4 reproduces `m_branch_secp_v1.py` independently; it is a **consistency re-check of a recorded
number, not a new datum**. **No out-of-sample content, no sample, no null.**

---

## 3. The root systems, derived

| `m` | roots (× `√p`), as `ζ₂₄` exponents | orders | `g` |
|---|---|---|---|
| `−2` | `0, 0, 12, 12` | `[1,1,2,2]` | 0 |
| `−1` | `2, 10, 14, 22` | `[12,12,12,12]` | **2** |
| `0` | `3, 9, 15, 21` | `[8,8,8,8]` | 0 |
| **`+1`** | `4, 8, 16, 20` | `[6,3,3,6]` | **2** |
| `+2` | `6, 6, 18, 18` | `[4,4,4,4]` | 0 |

**Correction to step 3 as written.** The claim *"the ratio of the ± eigenvalue pairs is exactly `ζ₃`"* is
**false as stated**. The `±` pairs are `(ω, −ω)` and `(ω², −ω²)`, and both ratios are `−1` (`ζ₂₄¹²`,
order 2), not `ζ₃`. The `ζ₃` ratios in the `m=1` multiset are:

```
  ω²  / ω    = ζ₃        -ω  / -ω²  = ζ₃          (the two 120° pairs, g = 2)
  ω   / ω²   = ζ₃²       -ω² / -ω   = ζ₃²         (their inverses)
  -ω  / ω    = -1        -ω² / ω²   = -1          (the ± pairs — NOT ζ₃)
```

So the `ζ₃` sits **within** each same-order pair (`{ω,ω²}` order 3, `{−ω,−ω²}` order 6), **across** the
`±` pairing, not along it. The conclusion `g=2` is unaffected — the count is right, the pairing named for
it is not. This matches the N1 shape `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` with `α = √p·ω`, which reproduces the multiset
exactly.

---

## 4. What `g=2` needs from `m` — and why the cubic-residue symbol is load-bearing after all

`g=2` for both `m=−1` and `m=+1`; the two differ in root order (`12` vs `6`), i.e. in `k(m)`, but not in
the presence of the `ζ₃` ratio. So the *abstract* implication is `g=2 ⟸ k(m) ∈ {6,12}`, strictly weaker
than `m=1`.

### §4a — CORRECTION (2026-07-30). The alternative branch is `m=−2`, and it has no lock.

An earlier draft of this section read the weaker abstract implication as making the cubic-residue step
**not** load-bearing, on the reasoning that `m=−1` also gives `g=2`. **That is withdrawn: it compares
`m=1` against a branch the `m`-law does not realize in this class.** A2.1 H2 states the actual dichotomy:

> **H2 — `p ≡ 7 mod 12` ⇒ `m = −2` if `B^{(p−1)/3} ≡ 1` (cubic residue), else `m = 1`.** (36/36 rows,
> `K2 = 22` pre-committed distinct configurations.)

`m = −2` is `√p·{1,1,−1,−1}`, orders `[1,1,2,2]`, and T3 gives **`g = 0`** there. The two branches
reachable at `p ≡ 7 mod 12` therefore differ in `g`:

| branch | condition | `m` | eigenvalues | orders | `g` | 120° lock |
|---|---|---|---|---|---|---|
| cubic **residue** | `B^{(p−1)/3} ≡ 1` | `−2` | `√p·{1,1,−1,−1}` | `[1,1,2,2]` | **0** | **no** |
| cubic **non-residue** (secp, `B=7`) | `B^{(p−1)/3} ≢ 1` | `+1` | `√p·{ω,ω²,−ω,−ω²}` | `[6,3,3,6]` | **2** | **yes** |

⇒ **the cubic-residue symbol decides whether the 120° lock exists at all**, and the `J`-sign law and the
Stickelberger citation (`[CITED — verified]`, **caveat 1**: Katre's *printed* hypothesis
`jk(j+k) ≢ 0 mod m` is violated by `(j,k,m)=(4,3,12)`; only the proof's weaker `j,k,j+k ≢ 0 mod m`
applies) are load-bearing for it, not merely for the root orders.

`m = −1` and `m = 0` do not appear in the measured law at `p ≡ 3 mod 4` at all — H1 gives `m=2` at
`p ≡ 11 mod 12`, H2 gives `m ∈ {−2,1}` at `p ≡ 7 mod 12`. The realized support is `{−2,1,2}`, which is
also the frozen null's support. **Error class:** an implication evaluated over the abstract range of `m`
rather than the range the law realizes — the same object/quantifier slip logged in §7.

---

## 5. Why step 4 does not follow

**(i) Object mismatch — the anchor is outside the census.** The `m`-law governs the **untwisted
supersingular `A_new`**, which is *precisely the `a=0` fibre* (`RESULT_cap_reducibility_analysis_v1.md`
§, `ANALYSIS_…_kronecker_route_v3.md` §4: *"anchored at `a=0` — there `A_new` is supersingular and the
eigenvalues are `√p × μ₁₂`"*). The 120° law's cells are the `(n−1)/6` cosets of `μ₆` in **`(ℤ/n)*`**
(`freeze_n1_120deg_v1.py`); `0 ∉ (ℤ/n)*`, and at `a=0` the sheaf `L_{χ_a}` is trivial so the twisted
object degenerates to the untwisted one. **The open uniformity gap is exactly `α₂/α₁ = ζ₃` for all
`a ∈ (ℤ/n)*`, all `p`** (`ANALYSIS_…_v3.md` §4: *"the ONLY remaining gap is uniformity"*). An exact value
at the one excluded fibre is not an instance of the quantifier that is open.

**(ii) The property does not survive the twist — already measured.** `ANALYSIS_…_kronecker_route_v1.md`
§2 (the rigidity budget) records, for the transition `a=0 → a≠0`:

| property at `a=0` | survives the twist? |
|---|---|
| purity `\|αᵢ\|=√p` at every embedding | **YES** `[PROVED — all p]` |
| multiset closed under `α ↦ −ᾱ` | **YES** `[PROVED — FORCED]` |
| **each `αᵢ` IS `√p` × a root of unity** | **NO** — angle becomes free and equidistributes (Sato–Tate) |
| trace `= 0` | **NO** |
| the RATIO of the two pairs is a root of unity | **YES** — the 120° law |

Step 4's engine is row 3 — the **absolute** rigidity. That is the row measured as destroyed. The row that
survives is row 5, the **relative** rigidity, and it survives as an *independent* finding
(`RESULT_n1_120deg_exact_v1.md`, `g=2` at 22 primes × all cells), **not** as a consequence of the anchor
value. Deriving row 5 at `a≠0` from row 3 at `a=0` runs the implication in the direction the measurement
forbids. *(`ANALYSIS_…_v3.md` §2 logs the same category error twice already — "a group action relating
cells, mistaken for a within-cell forcing" — with a note to prevent a third instance.)*

**(iii) The nulls are about a readout; an eigenvalue label is not one.** "Bypassing the
Kohel–Shparlinski noise floor and the `μ₆` exact zero cancellations" is a category shift. Those nulls
bound **extraction** — whether a statistic on curve data recovers scalar information. `m` is a CM/quantum
number on the Frobenius eigenvalues of a supersingular abelian surface; pinning it extracts no bit of any
scalar `d` (`RESULT_jacobi_sign_law_stickelberger_v1.md` §6, and the recorded `D1` non-additivity
`0/48` raw, `0/22` affine — a lift target's eigenvalues say nothing about whether the lift transports a
discrete log). The nulls are not bypassed; they are **not addressed**, which is a different thing and
carries no discredit to either side.

---

## 6. What this route DOES deliver, stated at its true scope

> **`[PROVED-exact]`** For every prime `p ≡ 7 mod 12` with `B` a cubic non-residue — **including
> `p = 2²⁵⁶−2³²−977`, computed directly, not extrapolated** — the untwisted supersingular `A_new`
> (the `a=0` fibre) has Frobenius eigenvalue multiset `√p·{ω,ω²,−ω,−ω²}` and therefore satisfies the
> 120° identity `α₂/α₁ = ζ₃` **exactly**, conditional on the `J`-sign law
> (`[PROVED — modulo (D2)]`, `(D2)` now `[CITED — verified]` with caveat 1 above). Weakened but
> citation-independent form: `g=2` needs only `m ∈ {±1}`.

**Power and scope.** One fibre (`a=0`), all `p` in the class, exact. **Zero power** over any `a≠0` cell —
the quantifier the uniformity gap ranges over. It does not touch banner #5 as banner #5 is stated (*"every
cell is `p≈10³`"*), because it produces no cell; it produces the excluded fibre. It is a **necessary
consistency condition** on any uniform mechanism: a proof of uniform `u=ζ₃` must specialize correctly
here, and it does.

**Delta against the prior record — narrower than a first write-up of this claimed.** `ANALYSIS_…_v3.md`
§85–86 already had the `a=0` end **"anchored"** and graded **`[CITED; record L3, ℚ(ζ₁₂)]`**: *"there
`A_new` is supersingular and the eigenvalues are `√p × μ₁₂` roots of unity, the Jacobi/Gauss-sum values
Stickelberger factorizes."* So this result does **not** strengthen a weak end, and the earlier phrasing
("the `a=0` end is no longer the weak end") is **withdrawn as narrative overreach** — the weak end was
always `a≠0` and still is. What is added over that line is only:
1. **which** element of `√p·μ₁₂` — the multiset `{ζ₂₄⁴,ζ₂₄⁸,ζ₂₄¹⁶,ζ₂₄²⁰}`, orders `[6,3,3,6]`, derived not
   repeated;
2. that the N1 statistic evaluated on it gives **`g=2`**, i.e. the anchor satisfies the same identity the
   census cells do;
3. the **`m=±1` degeneracy** of `g` (§4), which relocates what the citation debt buys.

The open question is unchanged and unmoved by any of the three: *"for `a≠0` the twist by the Lang torsor
`L_{χ_a}` deforms these; whether the deformed eigenvalues remain Jacobi-sum-shaped (so Stickelberger still
applies) is the premise that must be verified before the citation is used."* Rows 1, 2 and 5 of the
rigidity budget survive the twist; row 3 does not. A mechanism accounting for *why 5 survives while 3
dies* is the lever; neither the `m`-law nor the ω-descent (`ANALYSIS_…_v3.md` §2, confirmed but
insufficient) is that mechanism. (L-mono) — a `μ₃` in the sheaf's geometric monodromy — remains untried
and is the only candidate on the ledger that is within-cell by construction.

---

## 7. Process status — read before citing

- **No `experiment-designer` pre-registration, and I judge none was owed.** T1–T3 are deterministic
  algebraic derivations from a defining polynomial (no sample, no statistic, no null, no free parameter);
  T4 is two modular exponentiations on public constants reproducing a recorded value. **This
  justification does not extend** to any sweep over primes or cells — `RESULT_jacobi_sign_law_semiprimitive_v1.md`
  §0a records a self-authorized prereg-shaped run on exactly that reasoning and flags it as a defect.
  If this route is extended to `a≠0` cells or to a multi-prime `m` census, prereg first.
- **`compile-diff` owed** before any of this reaches `POSITIVE_FINDINGS_MASTER_*`.
- **Root system derived, not repeated.** Per the standing rule that a `m=1` root-system claim from an
  external paste was previously wrong in the same slot, the multiset here is produced by exact reduction
  in `ℤ[x]/Φ₂₄` and cross-checked against the v4 ERRATUM. It agrees.
- **Verdict words.** The proposal's *"m=1 is confirmed"* and *"you have just proven"* are not the grades
  on the ledger. `m=1` is `[PROVED — modulo (D2)]` with `(D2)` `[CITED — verified, 3 caveats]`; step 4 is
  **not** proved and §5 gives the reasons.
- **★ Self-cert word fired an audit on this write-up, and the audit found three defects — all inflating
  this result's contribution, none touching T1–T5.** Trigger: a self-certifying word in the covering
  summary. Per the passage-scope rule the whole passage was audited, not the clause. Findings, all
  corrected above:
  1. **Mis-scoped rule.** The BTC-folder analytical-closure line was called "the exact shape of the
     step-4 gap." It is not: that line governs reading a fact as **closing** an avenue, and its
     burden-of-proof is explicitly asymmetric (raises the bar on closures, *not* on finds). Step 4 is a
     false **propagation** of a positive from one fibre to the ensemble — an analogous quantifier error
     pointed the other way, which that rule does not govern. Applying a rule outside the object it is
     about is the error the rule itself warns against.
  2. **Over-attributed the counterweight to measurement.** Of the three reasons in §5, only (ii) is a
     project measurement; (i) is definitional (`0 ∉ (ℤ/n)*`) and (iii) is a category distinction. The
     summary credited "your own measurement" with the whole of it, and appended *"not a training prior"* —
     a self-certification of the reasoning as prior-free, which is the move that taints the rest.
  3. **Narrative overreach in §6** — "strengthens the anchor end", "no longer the weak end", against a
     source that already had that end anchored and `[CITED]`. Withdrawn in §6, with the three-item delta
     substituted. Generator: a result owes a payoff, so the contribution inflated to supply one.
  Also corrected: ranking the project rules by which one "bites" hardest (§5 no-editorializing bans
  difficulty/importance ranking); the prereg rule constrains the next step more concretely than the
  closure rule does.
