# The reciprocity-bridge programme — compendium v2 (2026-07-24)

> **SUPERSEDES `BRIDGE_PROGRAMME_COMPENDIUM_v1.md`, WHICH WAS DEFECTIVE.** v1 asserted in its own
> header that "every open item, caveat, retraction and deviation is carried; none dropped" **and** that
> "`compile-diff` was run before this file was promoted." **Both statements were false when written** —
> compile-diff had not yet been run, and when it was, it found **11 DROPPED and 10 WEAKENED items**.
> v1 is retained unaltered as the audit trail. This file restores the losses v1's audit named — the
> 22-item restoration is grep-verified in `AUDIT_compendium_v2_restoration_check_v1.md` (which states
> its own limits: it checks the *named* items, and is not a fresh full re-audit — see this file's footer).
>
> **This document promotes nothing and supersedes nothing except v1.** `compile-diff` findings
> #1–#23 are each addressed below.

**Sources compiled (10):** `RESULT_ord_n_residue_structure_v1`, `RESULT_cubic_sextic_bridge_v1`,
`RESULT_bridge_dichotomy_v1`, `RESULT_bridge_mechanism_and_constant_v1`,
`AUDIT_bridge_laws_independent_retest_v1`, `AUDIT_citation_verification_v1`, and the DEVIATIONS files
for all four preregistrations.

✅ **Reproducibility (was a compile-diff gap, now closed):** all 15 scripts are copied into the repo at
`scripts_bridge_programme/` and verified to run from there — `ord_n_structure_v1.py` reproduces
`c_2=64`/`c_p=6`, and every `exec(open('…'))` cross-reference resolves within the copied set. They are
in the working tree (not yet committed).

---

## 0. The account, with its mechanism

The ledger item *"`ord_n(p)=(n−1)/6`, `ord_n(2)=(n−1)/64`, `[VERIFIED]` and never explained"* dissolved
in both halves; pulling it apart produced an exact reciprocity law.

**The reduction — elementary, and it is the whole question.** `n = p+1−t ⇒ n−p = 1−t`, so with
`U := |t−1|`: **`n ≡ p (mod U)`**, and for odd `ℓ`, `χ_ℓ(p mod n) = χ_ℓ(U mod n)` and
`χ_ℓ(n mod p) = χ_ℓ(U mod p)`. So: *for two primes `p ≡ n (mod U)`, are the `ℓ`-th power characters of
`U` related?*
- **`ℓ=2`:** yes — `ℚ(√U)/ℚ` is **abelian**, so the symbol is a congruence condition.
- **`ℓ≥3`:** `ℚ(ζ_ℓ, U^{1/ℓ})/ℚ` is **non-abelian**, so **no congruence can do it** — a bridge then
  requires `ζ_ℓ` to lie **in the CM field**. This is the mechanism behind the entire dichotomy in §3.

With `ν = 1−π` in `ℤ[ω]` (`N(ν)=n`), `π ≡ 1 (mod ν)` and `ν ≡ 1−t (mod π̄)`, Eisenstein reciprocity
gives the **bridge** `χ₃(p mod n) = ω^{c₃}·χ₃(n mod p)`, `c₃ ≡ s·(t−1)/3 (mod 3)`. With quadratic
reciprocity: **`c_p = 6 ⟺ n` is a sextic residue mod `p`, up to the two explicit corrections.**
An **exact identity does not decay** — unlike every density here — so it holds at `2²⁵⁶`.

## 1. CONTROLS — restored in full (the Anomaly-Drill protocol requires the control to fire)

| control | result | note |
|---|---|---|
| **K0** Eisenstein reciprocity `χ_ν(π̄′)=χ_π̄(ν′)` | **4000/4000** (8–18 bit) + **1500/1500** (32-bit) | pre-committed **void-everything** control |
| **K1** Gauss: `2` cubic residue mod `n` ⟺ `n=a²+27b²` | **1200/1200** + **400/400** (32-bit) | pre-committed **void-everything** control |
| **K2** base rate `χ₃^{(n)}(p)=1` vs random base | `0.3395` vs control `0.3250` (chance `1/3`) | |
| **K3** `ω²+ω+1≡0` both fields | all pass + **1500/1500** (32-bit) | |
| **dichotomy positive control** | predicted `agree/N ≈ 0.194` vs independence `0.111`; **observed `0.1920` vs `0.1185`** (`N=3000`), ratio **`1.69`** (`N=6000`) | reproduced its **pre-committed** effect size |
| **negative controls** | **every** random-base control clean, in **every** arm | |
| `ord_n` arms | **"Controls fire in every table reported here."** | |

## 2. Results, with grades as corrected by the audits

| # | statement | grade |
|---|---|---|
| **L3** | `3∣n−1` forced for prime-order `j=0` (the reason GLV applies) | **`[PROVED]`** + `4977/4977` |
| **L1** | `n≡1 mod 24` ⇒ `sf(\|t−1\|)∣6 ⇒ (p/n)=+1` forced | **`[PROVED]`** + `1546/1546`, 0 violations |
| **L2** | density `≈2.69/√(2√p) ∝ p^{−1/4}` ⇒ `≈10^{−19}` at secp | `[PROVED asymptotic]` + `[VERIFIED 20–48 bits]` |
| **B1** | **cubic bridge** `χ₃(p mod n)=ω^{c₃}·χ₃(n mod p)` | `[PROVED\|classical inputs]` + `12050/12050`, 8→256 bits |
| **B2** | `χ_λ(ω)=ω^{(a+b+1)/3}`, primary `λ` | **`[PROVED — identity `(N(λ)−1)/3 ≡ (a+b+1)/3 mod 3`, verified `3659/3659`]`** ⬆ *(upgraded by AUDIT §1)*. **Citation: Ireland–Rosen 2nd ed. Ch. 9 Exercises, p. 135; stated as eq. (1.1) in Z.-H. Sun, *Acta Arith.* 84 (1998) 291. NOT IR Prop 9.3.3** — that is the solvability/multiplicativity proposition and says nothing about `ω`. |
| **B3** | `t≡1 mod 3` ⇒ `ν`, `π̄` share a primarizing unit | **`[CITED — Silverman–Stange arXiv:0912.1831 Thm 19(a)]`** ⬇ *(regraded by AUDIT §5: **prior art, not ours**)* |
| **B4** | `c_p=6 ⟺ n` sextic residue mod `p`, **up to the two explicit corrections** | `[VERIFIED]` `3000/3000`, `300/300`, `200/200`, **`150/150` at 256 bits**, + secp |
| **B5** | `\|t−1\|` a perfect cube ⇒ `χ₃=1` forced; density `∝p^{−1/3}` | `[VERIFIED]` rate `1.0000`, `0/64`; **density under-powered** |
| **D1** | odd (hence prime, `N>5`) order ⇒ `D≡5 mod 8`, i.e. 2 inert in the **order `O_D`** | **`[CITED — Bröker–Stevenhagen §2]`**; converse (existence ∀ such `D`) **empirical `0/67477`, NOT cited** |
| **D2** | `w=4` branch empty (only `D=−4`, ramified) | `[VERIFIED]` `35907` twists, `0` odd |
| **D3** | bridge at `ℓ=3` **only** for `D=−3`; absent `ℓ=5,7,11,13` | `[VERIFIED — bounded, §4]` |
| **M1** | bridge is **CM-generated**, not shape-generated | `[VERIFIED — bounded, §4]` |
| **M2** | dichotomy keyed to `w`, **not** class number | `[VERIFIED — bounded, `h=2` only]` |
| **E1–E5** | exact congruence laws ⇒ **`c₃ ≡ s·(t−1)/3 (mod 3)`** | `[VERIFIED — 0/52000, two independent samples, 26- and 32-bit `p`]` |
| **—** | `P(c₃=0)=5/9`, ratio `5/3` | `[CONSISTENT, not verified]` ⬆ **→ `[VERIFIED]`** *(moved by AUDIT §3: pooled `z=+0.08`, independent sample `z=+1.55`)* — **with the `s`-uniformity caveat, §4** |

**Dissolutions — each with its full scope clause:**
- **`ord_n(2)=(n−1)/64` is a selection effect**: `ν₂(n−1)=6`, and **5** of 168 primes `q<1000` have odd
  order mod `n` (**`2, 79, 137, 199, 367`**) against `2.62` expected. *Scoped:* this is about **`2`**,
  not about `n`; the cofactor distribution was not tested for structure beyond the two frozen counts.
- **`ord_n(p)=(n−1)/6` is a `1/6` draw** `[VERIFIED]`. H-sextic (*CM forces it*) **falsified**:
  cube rate `0.3349`, `z=+0.27`, control `0.3325`, `N=6790`. *Scoped, verbatim:* **this says the two
  mechanisms examined (small-residue quadratic forcing; the cubic character) do not force it. It is
  not a claim that no mechanism does.** The bridge **determines** where the draw is made; it does
  **not** force it.
- Decay of the `(p/n)` finite-size effect at secp scale: `z` runs `+10.48` (16 bit) → `+3.25` (24) →
  `+0.58` (32) → `+0.15` (**256 bit**, `N=700`), controls clean throughout.

## 3. The dichotomy measurement (the file's own declared contribution)

`N=6000` each; `E` = agreements expected under independence; power vs an Arm-1-sized effect (`1.62`).

| family | `w` | ratio | perm `p` | power | control |
|---|---|---|---|---|---|
| **`D=−3, ℓ=3`** (POS CTL) | 6 | **1.69** | `1/20001` | **`16.1σ`** | clean |
| `D=−3, ℓ=5` | 6 | 0.96 | `15324/20001` | **`9.7σ`** | clean |
| `D=−3, ℓ=7` | 6 | 0.96 | `14529/20001` | **`7.0σ`** | clean |
| `D=−3, ℓ=11` | 6 | 1.03 | `8671/20001` | `4.5σ` | clean |
| `D=−3, ℓ=13` | 6 | 1.03 | `9161/20001` | `3.6σ` | clean |
| `D=−11 / −19 / −43 / −67 / −163`, `ℓ=3` | 2 | `1.04 / 1.01 / 1.00 / 0.96 / 0.94` | all `≥1521/20001` | **`15.7–16.0σ`** | clean |
| `h=2`: `D=−35,−51,−91,−115,−123,−187,−235,−267,−403,−427`, `ℓ=3` | 2 | `0.96–1.02` | all `≥4005/20001` | **`12.7–15.0σ`** | clean |
| **CM `D=−3, ℓ=3`** (M1) | | **1.645** | `1/20001` | **`29.5σ`** | clean |
| **matched control `n−p=Δ`** (M1) | | **0.993** | `13949/20001` | **`27.5σ`** | clean |

## 4. EVERY open item, caveat and bound — carried

**Prior art / novelty — highest priority:**
- **No novelty claim of any kind is supportable** until: citation-graph sweep of the ~40 papers citing
  **Silverman–Stange (arXiv:0912.1831)**; **Lemmermeyer, *Reciprocity Laws* Ch. 7**; **Cox, *Primes of
  the Form x²+ny²* §4**; MathSciNet/zbMATH. **Not done.**
- **B1 sits inside a known `p↔q` sextic-reciprocity family**: Silverman–Stange Prop 23(b)
  (`(2/p)₆(2/q)₆ = (2/p)_Q(2/q)_Q`, proved by *our exact manoeuvre*), Thm 7.1(d); **Babinkostova et al.,
  *Elliptic Reciprocity* (arXiv:1212.1983) Thm 2.7 "Law of Elliptic Reciprocity"**. Published identities
  are at base `2`/`4k`; the **base-`p`/base-`n`** instance was **NOT FOUND** in sources reached.
  **Not found ≠ novel.**
- **`KNOWN_FACTS_*` deflation:** "exactly one prime-order sextic class" is **not** a general law — over
  `p≡1 mod 6`, `p<600`, the count is `{0:6, 1:31, 2:12, 3:1}`. secp's "exactly one" is **typical
  (~62%), not distinctive.**
- **Three files carry unapplied audit edits** (CLAUDE.md §1 forbids overwriting):
  `RESULT_cubic_sextic_bridge_v1` (B2/B3/§5), `RESULT_bridge_dichotomy_v1` (D1), `KNOWN_FACTS_*` (§6).

**Corrections of record — kept so the errors stay inoculated:**
- **B2's citation was wrong** (IR Prop 9.3.3 → Ch. 9 Exercises p. 135 / Sun eq. (1.1)). See §2.
- **"2 inert in the CM *field*" is wrong**: `D=−12` (conductor 2) has 2 **inert in `K=ℚ(√−3)`** yet
  **`6028/6028` even orders**. The condition is on the **order `O_D`**.
- **`D≡5 mod 8 ⇒ odd order` is FALSE pointwise**: `p=7`, `D=−3` gives orders **`{3,4,7,9,12,13}`** —
  four even; `F₁₃`: `{7,9,12,16,19,21}`. Only the converse is a theorem.
- **Attributions:** Gauss's `2`-criterion is **Euler's conjecture, first proved by Gauss** (Werke VIII,
  posth.). "Rajwade" replaced by **IR Ch. 18 §3 Thm 4** + **arXiv:1212.1983 Thm 2.4** +
  **Silverman–Stange Remark 25**. Eisenstein reciprocity's textbook hypothesis `N(π₁)≠N(π₂)` **is
  satisfied** in our use (`N(ν)=n ≠ p=N(π̄)`).
- **"3 cubic residue mod `p` ⟺ `p=a²+243b²`" is FALSE — it is `4p`** (`2001` mismatches / `8988` for
  the `p`-form; `4p`-form `8988/8988`). Never in a file; recorded so it is not repeated.
- **H-constant was REJECTED, not merely flagged.** `e(ν′)⊥e(π̄′)` is FALSE ⇒ *"H-constant is NOT
  verified as stated"*; **"A passing number is not a passing model."** `5/9` was **not** graded on
  (v)/(vi) passing — which the raw p-values would have permitted. Its later `[VERIFIED]` rests on the
  independent retest, not on the rejected model.
- **`P(s=0)` systematic: WITHDRAWN** as unsupported (`z=−1.92` → `+2.18`). Whether the discovery
  deficit was correlated twists or fluctuation is **not determined**.

**Mathematical gaps:**
- **E1–E5 verified, not proved** — derivation from `μ(λ)=A+B`, `e=(μ+1)/3`, `μ(π̄′)−μ(ν′)=μ(u(t−1))`
  with `3∣t−1` is **sketched, not completed**.
- **Primarizing sign always `+1`** (`0` exceptions in `52000`) — **unexplained**.
- **`s`-uniformity not established**: `13539/13097/13364`, `χ²=7.43` (2 df, `p≈0.024`), unexplained.
  `5/9` follows from E4 **only if** `s` and `9∣t−1` are equidistributed; the verified object is the
  **structure** (E4 + their independence), not the value.
- **secp's other `n−1` factors — `149, 631, 107361793816595537, …` — have no reciprocity law in hand.**
- **`w=4`** would need a different framework (e.g. working **modulo the odd part of `#E`**, a different
  object).

**Bounds that are bounds, not absences:**
- **M1:** shape-generated association **`< ~1.06` ratio at 3σ** vs CM's `1.645`. Scoped to 30-bit `p`,
  this `Δ` multiset, this 2×2 statistic, `N=17305`. **A residual below ~6% of the independence baseline
  is not excluded.**
- **Uniform-correction blind spot, pre-committed wording verbatim:** *"No bridge with a non-uniform
  correction is detectable by a generator-free 2×2 association at this N."* **Not** "no bridge exists."
  A hypothetical `ℓ≥5` bridge with exactly uniform correction would read as absent — **wrongly.**
  **Untouched by all subsequent work.**
- **M2 bounded to ratio `≈1.08` (3σ)** in each `h=2` family; `h≥3` untested.
- **L1's free cell bounded at `0.5`, not proved**: `±0.015` (16–28 bits), `±0.04` (256 bits, `N=700`).
- **B5's density under-powered**: predicted `+0.015/+0.008/+0.003` vs observed `−0.015/+0.018/−0.004`,
  excess's own `sd = 0.016` at `N=877`; only `64` forced instances. **Rate law exact; density
  order-of-magnitude only.**
- **`ℓ≥17` untested**; `ℓ=11,13` weakly bounded (`4.5σ`, `3.6σ`).
- **`ℓ=5,7` (`9.7σ`, `7.0σ`) and all `ℓ=3` rows (`≈16σ`) are strongly tested** — those nulls have teeth.

**Deviations from all four preregistrations:**
- `ord_n`: family experiment **unregistered**; H-sextic reciprocity half **not run**; hypothesis (i)
  falsified and **repaired post-hoc** (protected only by predicting `1.0000` exactly); **cell counts not
  pre-committed** — at 40–64 bits the forced population falls to `5, 1, 0` instances, so **those rows
  confirm the density law but carry no independent weight on the rate law.**
- `cubic_sextic`: **train/freeze/test protocol NOT executed**; **`e_λ(ω)` supplement was tested, not
  assumed — the prereg did not name it** (relevant now that B2 is `[PROVED]`: it entered the programme
  unregistered); Arm B's first run **void** (resampling, ~40 distinct instances behind 6000 draws); a
  **float cube root** written and removed before the reported run; `c₃` distribution not pre-registered.
- `dichotomy`: **D1 generalized post-hoc** after arms came back empty; pre-registered secondary
  statistic **not run** (labelling obstruction); power column **added post-hoc**, superseding v1's
  `ℓ=11,13` rows; sampling changed v1→v2; **no multiple-comparison correction** over 10 tests — two
  nominally small p-values (`389/10001`, `366/10001`) **vanished at higher power.**
- `mechanism`: anti-fit guard **fired**; replacement laws **post-hoc on the discovery sample**
  *(discharged by the independent retest)*; a null **mis-scoped as an absence, corrected to a bound**;
  matched control `N=17305` not `20000`; K0/K1/K3 not re-run in that arm *(discharged: `1500/1500`,
  `400/400`, `1500/1500` at 32-bit `p`)*.

**Recorded so they are NOT re-run:** `D ≢ 5 mod 8` cannot yield prime `n` (`−4,−7,−8,−15,−20,−24,−40`);
`4p=L²+27M²` is always solvable for `p≡1 mod 3`; the `29/5125` anomalies were `t=1`; the `243`-form
error above.

## 5. Reproduction

`scratchpad/` (⚠ session-local, unversioned): `ord_n_structure_v1.py`, `ord_n_family_v{1,2}.py`,
`ord_n_quad_oos_v1.py`, `ord_n_secp_scale_v1.py`, `ord_n_mechanism_v{1,2}.py`,
`cubic_bridge_v{1,2,3}.py`, `bridge_dichotomy_v{1,2}.py`, `mechanism_isolation_v{1,2}.py`,
`audit_retest_v1.py`. Exact integers throughout; no float in any signal path; all verdicts from exact
permutation counts.

**Audit status of this file:** `compile-diff` was run against the ten sources **on v1**, producing 23
findings; this v2 addresses each, and the 22-item restoration is grep-verified in
`AUDIT_compendium_v2_restoration_check_v1.md`. **A fresh full re-audit of v2 was attempted but HUNG
(~9h, killed) and was NOT completed** — so a *new* loss introduced by v2 (beyond the named-item and
self-cert scans) would not have been caught. That gap is open.
