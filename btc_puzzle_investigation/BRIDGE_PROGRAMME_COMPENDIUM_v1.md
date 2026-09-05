# The reciprocity-bridge programme — compendium (2026-07-24)

> **THIS PROMOTES NOTHING AND SUPERSEDES NOTHING.** It consolidates four `RESULT_*`, two `AUDIT_*` and
> four `*_DEVIATIONS` files from one day's work. **Every open item, caveat, retraction and deviation
> from all ten is carried below; none is merged into a closure or dropped.** `compile-diff` was run
> against the sources before this file was promoted.
>
> **Why the paranoia:** `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` records live frontiers going **5 → 0**
> across one consolidation, invisible to tag-count auditing. Consolidation is the failure mode.

**Sources compiled:** `RESULT_ord_n_residue_structure_v1`, `RESULT_cubic_sextic_bridge_v1`,
`RESULT_bridge_dichotomy_v1`, `RESULT_bridge_mechanism_and_constant_v1`,
`AUDIT_bridge_laws_independent_retest_v1`, `AUDIT_citation_verification_v1`, and the DEVIATIONS files
for all four preregistrations.

---

## 0. The one-paragraph account

The ledger item *"`ord_n(p) = (n−1)/6`, `ord_n(2) = (n−1)/64`, `[VERIFIED]` and never explained"*
dissolved in both halves — but pulling it apart produced an exact reciprocity law connecting the two
primes that define the curve. `n = p+1−t` gives `p ≡ t−1 (mod n)` and `n ≡ 1−t (mod p)`; with
`ν = 1−π` in `ℤ[ω]` (`N(ν) = n`), Eisenstein reciprocity turns this into a **bridge**:
`χ₃(p mod n) = ω^{c₃}·χ₃(n mod p)` with `c₃ ≡ s·(t−1)/3 (mod 3)`. Combined with quadratic reciprocity,
**`c_p = 6 ⟺ n` is a sextic residue mod `p`**. The bridge exists at `ℓ=3` **only** for `D = −3` among
prime-order CM curves — and secp is on that discriminant. Unlike every density in this record, an
**exact identity does not decay**, so it holds at `2²⁵⁶` and was verified there.

## 1. Results, with grades as corrected by the audits

| # | statement | grade |
|---|---|---|
| **L3** | `3 ∣ n−1` forced for prime-order `j=0` curves (`p ≡ 1 mod 3`, `t = ±(a±3b)`, `n ≡ 2−a mod 3`, `3∤a`) — the reason GLV applies | **`[PROVED]`** + `4977/4977` |
| **L1** | `n ≡ 1 mod 24` ⇒ `sf(\|t−1\|) ∣ 6 ⇒ (p/n) = +1` forced | **`[PROVED]`** + `1546/1546`, 0 violations |
| **L2** | forced density `≈ 2.69/√(2√p) ∝ p^{−1/4}` ⇒ `≈10^{−19}` at secp | **`[PROVED asymptotic]`** + `[VERIFIED 20–48 bits]` |
| **B1** | **cubic bridge** `χ₃(p mod n) = ω^{c₃}·χ₃(n mod p)` | `[PROVED\|classical inputs]` + `12050/12050`, 8→256 bits |
| **B2** | `χ_λ(ω) = ω^{(a+b+1)/3)}` for primary `λ` | **`[PROVED — identity]`** ⬆ *(upgraded by audit §1)* |
| **B3** | `t ≡ 1 mod 3` ⇒ `ν`, `π̄` share a primarizing unit | **`[CITED — Silverman–Stange Thm 19(a)]`** ⬇ *(regraded: prior art, not ours)* |
| **B4** | **sextic law**: `c_p = 6 ⟺ n` sextic residue mod `p` | `[VERIFIED]` `3000/3000`, `300/300`, `200/200`, **`150/150` at 256 bits**, + secp |
| **B5** | `\|t−1\|` a perfect cube ⇒ `χ₃ = 1` forced; density `∝ p^{−1/3}` | `[VERIFIED]` rate `1.0000`, `0/64`; **density under-powered** |
| **D1** | odd (hence prime, `N>5`) order ⇒ `D ≡ 5 mod 8`, i.e. 2 inert in the **order `O_D`** | **`[CITED — Bröker–Stevenhagen §2]`**; converse (existence ∀ such `D`) **empirical, `0/67477`, not cited** |
| **D2** | `w=4` branch empty (only `D=−4`, ramified) | `[VERIFIED]` `35907` twists, `0` odd |
| **D3** | bridge present at `ℓ=3` **only** for `D=−3`; absent `ℓ=5,7,11,13` | `[VERIFIED — bounded, §3]` |
| **M1** | bridge is **CM-generated**, not shape-generated | `[VERIFIED — bounded, §3]` |
| **M2** | dichotomy keyed to `w`, not class number | `[VERIFIED — bounded, `h=2` only]` |
| **E1–E5** | the exact congruence laws ⇒ **`c₃ ≡ s·(t−1)/3 (mod 3)`** | `[VERIFIED — 0/52000, two independent samples]` |
| **—** | `P(c₃=0) = 5/9`, association ratio `5/3` | `[VERIFIED]` pooled `z=+0.08` — **with the `s`-uniformity caveat, §3** |

**Dissolutions (both scoped, neither a closure of anything else):**
`ord_n(2) = (n−1)/64` is a **selection effect** (5 of 168 primes `q<1000` have odd order mod `n`;
expected 2.62). `ord_n(p) = (n−1)/6` is a **`1/6` draw** — H-sextic (CM *forces* it) **falsified**,
cube rate `0.3349`, `z=+0.27`, control `0.3325`. The bridge **determines** where the draw is made; it
does **not** force it.

## 2. secp256k1

`s₁=s₂=0` ⇒ `c₃=0`; `n ≡ 1 mod 4` ⇒ quadratic sign `+1`. The law degenerates to
**`p` sextic residue mod `n` ⟺ `n` sextic residue mod `p`**. `n` is both a cube and a QR mod `p`
⇒ `c_p = 6`, matching direct computation. `|t−1|` (129 bits) is not a perfect cube, so secp is **not**
in L1/B5's forced populations — the value is carried by the bridge, not by a forcing. `D = −3` is the
unique prime-order CM discriminant with a bridge past `ℓ=2`; **this is a restatement of `j=0`/CM by
`ℤ[ω]`, not an independent property, and carries no leakage or ECDLP content** — every quantity on both
sides is public (`p`, `n`, `t`).

## 3. EVERY open item, carried verbatim in substance

**From the citation audit (§5 of that file) — the highest-priority item:**
- **No novelty claim of any kind is supportable** until: citation-graph sweep of the ~40 papers citing
  Silverman–Stange; **Lemmermeyer, *Reciprocity Laws* Ch. 7**; **Cox, *Primes of the Form x²+ny²* §4**;
  MathSciNet/zbMATH. **Not done.** B1 sits inside a known `p↔q` sextic-reciprocity family
  (Silverman–Stange Prop 23(b), Thm 7.1(d); Babinkostova et al. Thm 2.7 "Law of Elliptic
  Reciprocity"); the published identities are at base `2`/`4k`, the **base-`p`/base-`n`** instance was
  **not found** — *not found ≠ novel*.
- `KNOWN_FACTS_*`'s "exactly one prime-order sextic class" framing should be **deflated**: over
  `p ≡ 1 mod 6`, `p<600`, the count is `{0:6, 1:31, 2:12, 3:1}` — secp's "exactly one" is typical
  (~62%), not distinctive.
- Three files carry edits from the audit and have **not** been rewritten (CLAUDE.md §1 versioning):
  `RESULT_cubic_sextic_bridge_v1` (B2/B3/§5), `RESULT_bridge_dichotomy_v1` (D1), `KNOWN_FACTS_*`.

**Mathematical gaps:**
- **E1–E5 are verified, not proved.** The derivation from `μ(λ)=A+B`, `e=(μ+1)/3`,
  `μ(π̄′)−μ(ν′)=μ(u(t−1))` with `3∣t−1` is **sketched but not completed**.
- **Why the primarizing unit's sign is always `+1`** (`0` exceptions in `52000`) is **unexplained**.
- **`s`-uniformity is not established**: audit sample `13539/13097/13364`, `χ²=7.43` (2 df, `p≈0.024`),
  unexplained. `5/9` follows from E4 **only if** `s` and `9∣t−1` are equidistributed; the *structure*
  (E4 + their independence) is what is verified.
- **`P(s=0)` systematic: WITHDRAWN** as unsupported (reversed sign, `z=−1.92` → `+2.18`). Whether the
  discovery deficit was correlated twists or fluctuation is **not determined**.

**Bounds that are bounds, not absences:**
- **M1's null is a bound:** shape-generated association `< ~1.06` ratio at 3σ vs CM's `1.645`. Scoped to
  30-bit `p`, this `Δ` multiset, this 2×2 statistic, `N=17305`. A residual below ~6% of the
  independence baseline is **not excluded**.
- **The uniform-correction blind spot (pre-committed wording, unchanged):** *"No bridge with a
  non-uniform correction is detectable by a generator-free 2×2 association at this N."* **Not** "no
  bridge exists." A hypothetical `ℓ≥5` bridge with exactly uniform correction would read as absent —
  wrongly. **Untouched by all subsequent work.**
- **L1's free cell is bounded at `0.5`, not proved** (`±0.015` at 16–28 bits, `±0.04` at 256 bits).
- **B5's density prediction is under-powered**, not confirmed: predicted `+0.015/+0.008/+0.003` vs
  observed `−0.015/+0.018/−0.004`; only `64` forced instances. Rate law exact; density order-of-magnitude.
- **M2 scoped to `h=2`**; `h ≥ 3` untested. **`ℓ ≥ 17` untested**; `ℓ=11,13` weakly bounded
  (`4.5σ`, `3.6σ`).
- **`w=4` unreachable** by D2, so H-dichotomy's "iff" is verified only at `w ∈ {2,6}`.
- **`ord_n(2)`'s dissolution is about `2`, not about `n`** — the cofactor distribution over `q<1000`
  was not tested for structure beyond the two frozen counts.

**Deviations carried from all four preregistrations:**
- `ord_n`: family experiment was **unregistered** (extension, new data); H-sextic's reciprocity
  confirmation **not run** (moot after falsification); hypothesis (i) falsified and **repaired
  post-hoc** — protected only by predicting `1.0000` exactly.
- `cubic_sextic`: **train/freeze/test protocol NOT executed** (correction proved derivable — safe
  direction, but the protocol did not do the protecting); Arm B's first run **void** (resampling,
  ~40 distinct instances behind 6000 draws); a **float cube root** was written and removed before the
  reported run (project rule); `c₃`'s distribution not pre-registered.
- `dichotomy`: **D1 generalized post-hoc** after arms came back empty; pre-registered secondary
  statistic **not run** (labelling obstruction); power column **added** post-hoc, superseding v1's
  `ℓ=11,13` rows; sampling method changed v1→v2; **no multiple-comparison correction** over 10 tests.
- `mechanism`: anti-fit guard **fired** — `e(ν′)⊥e(π̄′)` FALSE; replacement laws **post-hoc on the
  discovery sample** *(debt since discharged by the independent retest)*; a null was **mis-scoped as
  an absence and corrected to a bound**; matched control reached `N=17305` not `20000`; K0/K1/K3 not
  re-run in that arm *(since discharged: 1500/1500, 400/400, 1500/1500 at 32-bit `p`)*.

**Recorded so they are NOT re-run:**
- `D ≢ 5 (mod 8)` **cannot** yield prime `n` — do not re-attempt association tests at `D = −4, −7, −8,
  −15, −20, −24, −40`.
- `4p = L²+27M²` is **always** solvable for `p ≡ 1 mod 3` — the "2 is a cubic residue" worry was
  unfounded; two independent parametrizations reproduced the family instance-for-instance.
- The `29/5125` quadratic-identity anomalies were `t = 1` (anomalous `n = p`, Legendre `0`); `0/3000`
  once excluded.
- "3 is a cubic residue mod `p` ⟺ `p = a²+243b²`" is **FALSE** — it is `4p` (`2001` mismatches/`8988`
  for the `p`-form). Never in a file; recorded so it is not repeated.

## 4. Reproduction

`scratchpad/`: `ord_n_structure_v1.py`, `ord_n_family_v{1,2}.py`, `ord_n_quad_oos_v1.py`,
`ord_n_secp_scale_v1.py`, `ord_n_mechanism_v{1,2}.py`, `cubic_bridge_v{1,2,3}.py`,
`bridge_dichotomy_v{1,2}.py`, `mechanism_isolation_v{1,2}.py`, `audit_retest_v1.py`.
Exact integers throughout; no float in any signal path; all verdicts from exact permutation counts.
