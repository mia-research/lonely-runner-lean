# n = 8 Branch Coverage Inventory — `lrc_proof_v10_21.md`

**Target file:** `/Users/trentpalelei/Desktop/Math Ex/lrc_proof_v10_21.md` (1641 lines).
**Scope:** rational (integer) speed tuples only; `n` fixed at 8. `E` = 7 distinct positive
integers, `gcd(E) = 1`. Irrational speeds (Theorem 3.1, §3) are out of scope by task
definition.
**Method:** grep + targeted section reads. Every row carries `file:line`. Quotations are
verbatim from the file. Items marked *[derived]* are arithmetic performed here from the
manuscript's own definitions, not manuscript statements.

---

## 1. The top-level split, as verified against the file

The task summary is correct in outline and needs three corrections. Verified text:

| Node | Defining condition (manuscript vocabulary) | Location |
|---|---|---|
| Case 1 | "**Case 1:** $E_{\rm div} = \emptyset$. Section 4." | `lrc_proof_v10_21.md:83` |
| Case 2 | "**Case 2:** $E_{\rm div} \neq \emptyset$. Sections 5–12." | `lrc_proof_v10_21.md:84` |

with `$E_{\rm div} = \{e \in E : n \mid e\}$` (`lrc_proof_v10_21.md:80`).

**Correction 1 — the Case-2 sub-split is on `R_non`, not on a fixed count of two dropped
classes.** The operative condition is Theorem 9.3: *"If all $\varphi(n)$ units of
$\{1,\ldots,n-1\}$ are in $E_{\rm non}$ (Unit-Complete case)"* (`lrc_proof_v10_21.md:661`).
Lemma 9.4 gives only a sufficient condition for it: *"If both dropped elements from
$\{1,\ldots,n-1\}$ are non-units, then all $\varphi(n)$ units are in $E_{\rm non}$"*
(`lrc_proof_v10_21.md:737`). At `|E_div| = 1` a tuple may drop exactly **one** residue class;
if that class is a non-unit the tuple is Unit-Complete without "both dropped" applying
literally. The split is therefore: (A) some unit class `d ∉ R_non`; (B) no unit class is
missing.

**Correction 2 — Sub-case B2a is unreachable inside Case 2.** It is stated as
*"**Sub-case B2a ($E_{\rm div} = \varnothing$, no divisible runners).**"*
(`lrc_proof_v10_21.md:942`), and Case 2 is by definition `E_div ≠ ∅`
(`lrc_proof_v10_21.md:84`). The Tier-1 table row *"Case 2, any composite $n$, both
non-units, $E_{\rm div}=\varnothing$"* (`lrc_proof_v10_21.md:1440`) is a vacuous row: that
configuration is Case 1, closed by Theorem 4.1. No n = 8 leaf reaches B2a.

**Correction 3 — the arithmetic-type branch used for n = 8 is `n` even (B1), not `n = p^k`.**
Sub-case B3 is headed *"**Sub-case B3 ($n = p^k$, odd prime power, $k \geq 2$).**"*
(`lrc_proof_v10_21.md:1167`) — n = 8 is a prime power but not an *odd* one, so B3 and its
contents (G-PRES for n=9, Theorem 11.5) are outside its own stated scope at n = 8. The
routing sentence at `lrc_proof_v10_21.md:291` and `:936` sends n = 2^k to B1.

### Vacuity of the small-`L` base cases at n = 8 *[derived]*

Proposition 5.1 (`lrc_proof_v10_21.md:283`) handles `L ∈ {n, 2n}`. Its own note reasons by
divisor count: *"The case $\mathrm{lcm}(E) = n$ requires $n-1$ distinct positive divisors of
$n$"* (`lrc_proof_v10_21.md:285`). Applying the same criterion at n = 8: `L = 8` needs 7
distinct divisors of 8 and `d(8) = 4`; `L = 16` needs 7 distinct divisors of 16 and
`d(16) = 5`. Both are impossible, so **every** n = 8 Case-2 tuple has `L > 2n`, which is the
hypothesis Proposition 11.3-FINAL requires. The `L = 2n` Case-B routing at
`lrc_proof_v10_21.md:291` (which forwards even `n` to Sub-case B1) is therefore vacuous at
n = 8 and carries no n = 8 obligation.

---

## 2. The exhaustive n = 8 case tree

Non-units of `Z/8Z` in `{1,…,7}` are `{2,4,6}`; units are `{1,3,5,7}`, `φ(8) = 4`.

```
n = 8, integer tuple E (7 distinct, gcd 1)
├─ L1  E_div = ∅                                    → Case 1
└─      E_div ≠ ∅  (Case 2; L > 2n automatically, §1 above)
   ├─ L2  some unit d ∈ {1,3,5,7} missing from R_non ("dropped unit", Case A)
   │      ├─ L2a  |E_div| = 1
   │      └─ L2b  |E_div| ≥ 2
   └─      no unit missing from R_non ("Unit-Complete", Case B)
          → all of {1,3,5,7} ⊆ R_non; missing classes ⊆ {2,4,6}
          n = 8 is even  → Sub-case B1
          ├─ L3a  retained non-unit residue has gcd(ρ,8) = 2  (ρ ∈ {2,6})
          └─ L3b  retained non-unit residue has gcd(ρ,8) = 4  (ρ = 4)
```

L3a/L3b are the two `Z/8Z`-distinct shapes of the Unit-Complete leaf; the manuscript does
not itself split them, but the split is forced by Lemma FLOOR0 (`lrc_proof_v10_21.md:461`),
whose output depends on `g = gcd(e,n)`, and it is where B1's argument separates (§4 below).

Both Unit-Complete leaves are non-empty *[derived]*: `E = {1,3,4,5,7,8,9}` has residues
`1,3,4,5,7,0,1`, so `R_non = {1,3,4,5,7}`, `E_div = {8}`, gcd 1, 7 distinct — a valid n = 8
Case-2 Unit-Complete tuple of shape L3b. `E = {1,2,3,5,7,8,9}` gives `R_non = {1,2,3,5,7}` —
shape L3a.

---

## 3. Leaf table

| Leaf | (a) Defining condition | (b) Closing result, file:line | (c) Hypotheses satisfied at n = 8? | (d) Depends on a retracted/FALSE result? |
|---|---|---|---|---|
| **L1** | `E_div = ∅` | **Theorem 4.1**, `lrc_proof_v10_21.md:252` — *"If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$."* | **Yes.** No arithmetic-type hypothesis on `n`; proof is a 3-line direct witness argument (`:254`). | No. |
| **L2a** | Case 2, `|E_div| = 1`, some unit `d ∉ R_non` | **Proposition 11.3-FINAL**, `lrc_proof_v10_21.md:848` — *"For composite $n \geq 4$ with one dropped unit residue class $d \notin R_{\rm non}$ and $L > 2n$ (with $n \mid L$)"* — via **Lemma 11.3a'**, `:866` — *"Let $n \geq 4$ be composite, $\|E_{\rm div}\| \geq 1$…"* | **Yes.** n = 8 is composite and ≥ 4; `L > 2n` holds automatically (§1); `n \| L` holds since `E_div ≠ ∅`. n = 8 is worked explicitly at `:862` (`L = 120`, Tier 2) and used as an example at `:864`. | No. The dependency line states *"**No Lemma 5.2 dependency for composite $n$.**"* (`:1421`), and Lemma 11.3a' is the ERR-C-01 repair of the withdrawn Lemma 11.3a (`:870`). |
| **L2b** | Case 2, `|E_div| ≥ 2`, some unit `d ∉ R_non` | Two routes are given. (i) **Lemma 11.3a'**, `:866`, hypothesis `\|E_{\rm div}\| \geq 1` — covers this leaf; table row *"Case 2, composite $n$, dropped unit \| **PROVED** (v10.13) \| Proposition 11.3-FINAL + Lemma 11.3a'"* (`:1438`) carries no `\|E_div\|` restriction. (ii) **Theorem 12.1 Case A**, `:1189`. | (i) **Yes**, as L2a. (ii) **Scope mismatch, non-fatal.** Case A reads *"Lemma 5.2 (proved, v10.11) supplies a safe fibre"* (`:1189`), but Lemma 5.2 is headed *"**Lemma 5.2 (Dropped-unit bridge; proved for prime $n$).**"* (`:427`) and n = 8 is not prime. Route (i) is independent of Lemma 5.2 and closes the leaf. | No. |
| **L3a** | Case 2, Unit-Complete, retained non-unit residue `ρ ∈ {2,6}` (`g = 2`) | **Sub-case B1**, `lrc_proof_v10_21.md:934–936`; table row *"Case 2, composite $n$, even, both non-units \| **PROVED** \| Sub-case B1"* (`:1439`) | **No — see §4.** The displayed inequality's own side condition and the §11 parity argument it invokes both fail at n = 8. | Not directly. B1's own text says *"(The former reference to Theorem 9.2c'' here was unnecessary and is removed since 9.2c'' is FALSE.)"* (`:936`), so the FALSE dependency was cut — but nothing valid at n = 8 replaced it. |
| **L3b** | Case 2, Unit-Complete, retained non-unit residue `ρ = 4` (`g = 4`) | **Sub-case B1**, same as L3a | **No — see §4.** In addition, the specific floor-0 mechanism B1 names is refuted at n = 8 in this shape *[derived, §4.5]*. | Same as L3a. |

### Named results checked and found **out of scope at n = 8** (so not usable as fallbacks)

| Result | Quoted hypothesis | Line | Why n = 8 fails it |
|---|---|---|---|
| Theorem 11.5 (Late Bottleneck Window) | *"Let $n=p^k$ with $p \geq 3$, $k \geq 3$"* | `:1173` | n = 8 = 2³ has p = 2 < 3. |
| Sub-case B3 heading | *"$n = p^k$, odd prime power, $k \geq 2$"* | `:1167` | 8 is not an odd prime power. |
| Sub-case PP(i) / G-PRES route | *"**Sub-case PP(i) ($n=9$, $p=3$, $k=2$):**"* | `:1169` | n = 9 only. |
| Theorem N-PSQ-REP | *"For $n = p^2$ ($p \geq 5$ prime)"* | `:1270` | 8 is not `p²`. |
| Lemmas 12.2/12.3 (Silence Fibre) | *"We treat squarefree $n = pq$ ($p < q$ primes)."* | `:1191` | 8 is not squarefree. |
| Sub-case B2 heading | *"**Sub-case B2 ($n$ odd, $\geq 2$ distinct prime factors).**"* | `:938` | 8 is even and has one prime factor. |
| Sub-case B2a | *"$E_{\rm div} = \varnothing$, no divisible runners"* | `:942` | Contradicts Case 2. |
| Lemma 5.2 | *"**Lemma 5.2 (Dropped-unit bridge; proved for prime $n$).**"* | `:427` | 8 is not prime. |
| Lemma 11.3c | *"$d \in \{1,\ldots,n-1\}$ a dropped unit residue class"* | `:906` | In leaves L3a/L3b every dropped class is a non-unit, so `d^{-1}` — on which the whole proof runs, via `$r_d := -d^{-1} \pmod{n}$` (`:906`) — does not exist. |

---

## 4. Why Sub-case B1 does not close L3a/L3b at n = 8

Sub-case B1 is two lines long. Full text, `lrc_proof_v10_21.md:934–936`:

> **Sub-case B1 ($n$ even).**
> $$\frac{2\varphi(n)}{n} = \prod_{p \mid m}\!\left(1-\frac{1}{p}\right) \leq \frac{2}{3} < 1$$
> (where $n = 2^a m$, $m$ odd $\geq 3$), giving $|U_{\rm unit}| \leq 2\varphi(n) < n$ so some
> residue is uncovered by unit runners. For $n = 2^k$ ($k \geq 3$): $n$ is even, so Sub-case
> B1 (parity argument, §11) applies directly: the parity of $d_1$ (an odd non-unit in
> $\mathbb{Z}_{2^k}$) gives an uncovered residue at floor 0, giving $B_{\rm safe} \geq 1$.

Five separate facts about this passage at n = 8:

**4.1 The displayed inequality excludes n = 8 by its own side condition, and is false there.**
The parenthetical is *"(where $n = 2^a m$, $m$ odd $\geq 3$)"*. n = 8 = 2³·1 has m = 1, not
odd ≥ 3. *[derived]* With m = 1 the product over `p | m` is empty and equals 1, and
`2φ(8)/8 = 2·4/8 = 1`, so the asserted `≤ 2/3 < 1` fails and the conclusion
`|U_unit| ≤ 2φ(n) < n` collapses to `≤ 8 < 8`.

**4.2 The n = 2^k sentence is self-referential.** *"$n$ is even, so Sub-case B1 (parity
argument, §11) applies directly"* — B1 is the sub-case being proved. The pointer to §11's
parity argument resolves to Lemma 11.3c, *"**Lemma 11.3c (Even-$n$ early-fibre lemma;
proved).** Let $n \geq 4$ be even and composite, $d \in \{1,\ldots,n-1\}$ a dropped unit
residue class…"* (`:906`), whose proof turns entirely on *"Since $n$ is even and $d$ is a
unit ($\gcd(d,n)=1$), $d$ must be odd"* (`:916`). In Sub-case B every dropped class is a
non-unit, so Lemma 11.3c's hypothesis is not satisfied on this leaf.

**4.3 "an odd non-unit in $\mathbb{Z}_{2^k}$" names an element that does not exist**, by the
manuscript's own next sentence: *"the units of $\mathbb{Z}_{2^k}$ are precisely the odd
elements"* (`:936`). At n = 8 the non-units of `{1,…,7}` are `{2,4,6}`, all even. The parity
that the argument invokes is therefore the parity of an object the same paragraph rules out.

**4.4 No fibre is named.** Every other closing result on this branch exhibits an explicit
fibre — `b^early = 2L/n` (`:907`), `b^* = (n-1)L/n` (`:866`), `b_0 = L/q` (`:1193`),
`r^* = p^2 + j^*` (`:1270`). B1 asserts "at floor 0" without producing a `b ∈ B_div` at which
the runners simultaneously occupy the floor states it assumes. Corollary 11.0, the statement
B1 is said to instantiate (*"The sub-cases below instantiate this corollary with
branch-specific inputs."*, `:932`), explicitly disclaims the floor-0 route: *"The floor-0
observation is therefore a floor-0 statement only and is not used in the proof below."*
(`:926`). Corollary 11.0's actual proof-by-branch list (`:928`) does not contain an even-`n`
or `2^k` entry at all — it lists `E_div = ∅`, squarefree `pq`, and `p²` only.

**4.5 In leaf L3b the floor-0 mechanism is refuted at n = 8** *[derived, from Lemma FLOOR0,
`lrc_proof_v10_21.md:461`: "if $\gcd(e,n)=1$ then $\mathrm{bad}(e,0,n) = \{0, -e^{-1}\}$; if
$\gcd(e,n)=g>1$ then $\mathrm{bad}(e,0,n) = H_g$"].*
In `Z/8Z` every unit is self-inverse, so the four unit runners contribute
`{0,-1} ∪ {0,-3} ∪ {0,-5} ∪ {0,-7} = {0,1,3,5,7}` at floor 0. A retained runner of residue 4
has `g = gcd(4,8) = 4` and `H_4 = (8/4)(Z/8Z) = {0,2,4,6}`. The union is all of `Z/8Z`: at
floor 0 nothing is uncovered, contradicting B1's conclusion for this leaf. Separately, any
divisible runner (`8 | e`, so `g = 8`, `H_8 = Z/8Z`) covers everything at floor 0 on its own,
and Case 2 guarantees at least one such runner exists. In leaf L3a (`ρ ∈ {2,6}`, `H_2 =
{0,4}`) the unit-plus-non-unit union misses `{2,6}`, so B1's *conclusion* is plausible there —
but it is still not established, because no fibre is exhibited at which the divisible runner
is off floor 0.

**Net:** for both L3a and L3b the manuscript's closing result is graded PROVED at `:1439`
while its stated argument has no hypothesis n = 8 satisfies, and in L3b its named mechanism
is contradicted at n = 8.

---

## 5. Occurrence ledger: FALSE / RETRACTED / REFUTED / OPEN / abandoned

Complete grep of the file. "n=8 relevance" says whether the item sits on any n = 8 leaf path.

| Line | Word | Applies to | n = 8 relevance |
|---|---|---|---|
| 7 | REFUTED | N-PSQ-T02 (saturation counterexample) | No — `n = p²` only |
| 7 | RETRACTED | Corollary N-PSQ-MOD-C (U2 audit 2026-05-08) | No — `n = p²` only |
| 7 | RETRACTED | LARGE-Q-SAFE candidate (2026-05-08) | No — `n = p²` only |
| 11 | FALSE | ERR-C-02, Theorem 9.2c'' (counterexample n = 15); *"The floor-reset targeting approach is **abandoned** for the Unit-Complete composite branch."* | **Yes, indirectly** — n = 8 lies in the Unit-Complete composite branch; the replacement named there is the Silence Fibre construction, *"✓ (for squarefree $n$)"*, which excludes n = 8 |
| 13 | OPEN | squarefree `pq` n > 15 actual speeds; `n = p²` p ≥ 17 | No |
| 130 | open item | Proposition 10.5 (Tier 2, prime n) | No |
| 221 | open items | §2.7 companion Baton-Pass certificate | No — *"carry no proof obligation for Theorem A"* |
| 291 | OPEN | `n = p²`, p ≥ 5, `\|E_div\| ≥ 1` in Proposition 5.1 Case B | No |
| 663 | FALSE | Theorem 9.2c'', in the proof of Theorem 9.3 | **Yes** — Theorem 9.3 is the Unit-Complete safe-fibre bound; its replacement branch list at `:663` includes *"Sub-case B1 ($n$ even)"*, i.e. it re-routes n = 8 into the defective B1 |
| 928 | FALSE / OPEN | Theorem 9.2c'' in Corollary 11.0's proof; `n = p²` marked OPEN | **Yes** — Corollary 11.0 is the statement B1 instantiates, and its branch list omits even `n` entirely |
| 936 | FALSE | Theorem 9.2c'' reference removed from Sub-case B1 | **Yes** — this is the L3a/L3b closing text |
| 940 | FALSE | Theorem 9.2c'' (Sub-case B2 status note) | No — B2 is odd `n` |
| 950 | OPEN | Sub-case B2b actual speeds, `pq` n > 15 | No |
| 1040 | PARTIAL | Theorem B2b-ACTUAL (n = 15) | No |
| 1056 | REFUTED | PS-7 (bijection impossibility, n = 21) | No |
| 1132 | RETRACTED | LARGE-Q-SAFE | No |
| 1150 | FALSE / REFUTED | PS-7 FALSE; PS-SAFE REFUTED for all `n = pq` | No |
| 1179 | FALSE / OPEN | Theorem 9.2c''; `k = 2, p ≥ 5` OPEN | No |
| 1197 | OPEN | Theorem 12.1 Case B actual speeds, n > 15 | No |
| 1256 | RETRACTED | Corollary N-PSQ-MOD-C | No |
| 1274 | refuted | N-PSQ-T02 | No |
| 1276 | FALSE | N-PSQ-T02 as originally stated | No |
| 1293 | OPEN | ingredient (3) of N-PSQ-T02-RESTRICTED | No |
| 1329 | false | UNIV-JBB single-band (`k = 1`) version | No |
| 1403 | FALSE | original N-PSQ-T02 | No |
| 1443 | OPEN / refuted | `n = p²`, k = 2, p ≥ 29 actual speeds | No |
| 1448 | OPEN / REFUTED | squarefree `pq` n > 15, PS-7 | No |
| 1452 | OPEN | `n = pq` n > 15, `\|E_div\| ≥ 2` | No |
| 1467 | refuted | N-PSQ-T02, in the two-open-families summary | No |
| 1468 | REFUTED | PS-7 | No |
| 1474 | — | *"**Theorem A ($x_0 \geq 1$ for all $n \geq 3$) requires closure of both open items above.**"* | Neither of the two named open families is n = 8 |
| 1526 | FALSE | Theorem 9.2c'' (Appendix A.2 status) | No — appendix *"is not used in Theorem A"* |
| 1596 | archival | Appendix A.5 (superseded enumeration) | No |

**No n = 8 leaf depends, directly or transitively, on Theorem 9.2c'', N-PSQ-T02,
LARGE-Q-SAFE, Corollary N-PSQ-MOD-C or PS-7 as a load-bearing input.** The three
9.2c''-adjacent lines that touch n = 8 (`:11`, `:663`, `:928`, `:936`) all *remove* the FALSE
dependency; the defect is that on the n = 8 path nothing valid was substituted.

---

## 6. Answer to the direct question

> **Is every n = 8 tuple covered by a result whose hypotheses n = 8 actually satisfies, and
> which does not depend on a retracted result?**

**No.** Three of five leaves are covered; two are not.

**Covered, hypotheses literally satisfied, no retracted dependency:**

- **L1** (`E_div = ∅`) — Theorem 4.1, `lrc_proof_v10_21.md:252`. Hypothesis is `n ∤ e_i`; no
  condition on the arithmetic type of `n`.
- **L2a** (`|E_div| = 1`, dropped unit) — Proposition 11.3-FINAL, `:848`, via Lemma 11.3a',
  `:866`. Hypotheses "composite `n ≥ 4`", "`L > 2n`", "`n | L`", "`|E_div| ≥ 1`" all hold at
  n = 8; §1 above shows `L > 2n` is automatic.
- **L2b** (`|E_div| ≥ 2`, dropped unit) — same pair, whose `|E_div| ≥ 1` hypothesis covers it,
  consistent with the unrestricted table row at `:1438`. *Caveat, not fatal:* the alternative
  route offered for this leaf, Theorem 12.1 Case A (`:1189`), cites Lemma 5.2, which is scoped
  *"proved for prime $n$"* (`:427`) and does not apply at n = 8. A second, narrower note: the
  proof of Lemma 11.3a' is organised as a trichotomy on a single divisible runner — Case I
  reads *"$e_{\rm div} = kn$ having $k \not\equiv 1 \pmod n$"* (`:868`, proof heading `:876`), Cases II and III
  likewise treat one `kn` (`:886`, `:896`) — while the lemma's hypothesis is `|E_div| ≥ 1`.
  Simultaneity across two or more divisible runners of different `k`-classes at the single
  witness `b̂` is not written out. This is a proof-completeness note on L2b, not a hypothesis
  mismatch.

**Not covered:**

- **L3a** — Case 2, Unit-Complete, retained non-unit residue `ρ ∈ {2,6}`.
- **L3b** — Case 2, Unit-Complete, retained non-unit residue `ρ = 4`.

Both are assigned to Sub-case B1 (`:934–936`), graded **PROVED** at `:1439` and again in the
header's *"Current Tier 1 status: Proved for: … composite $n$ even (Sub-case B1)"* (`:13`).
At n = 8 that argument has (i) a stated side condition n = 8 fails — *"(where $n = 2^a m$,
$m$ odd $\geq 3$)"* (`:936`), with `2φ(8)/8 = 1` so the strict inequality is false; (ii) a
pointer to a §11 parity argument, Lemma 11.3c, whose hypothesis is *"$d \in \{1,\ldots,n-1\}$
a dropped unit residue class"* (`:906`) — the leaf's dropped classes are non-units by
definition; (iii) an appeal to *"the parity of $d_1$ (an odd non-unit in $\mathbb{Z}_{2^k}$)"*
(`:936`), an element the same sentence's own remark excludes; and (iv) no exhibited fibre. In
L3b the named floor-0 mechanism is additionally contradicted at n = 8 by Lemma FLOOR0 (§4.5).

Neither leaf appears in the manuscript's own open-item ledger — the two families listed at
`:1467–1468` are `n = p²` and squarefree `n = pq`, `n > 15`. n = 8 is carried as closed at
`:13`, `:663`, `:1422` and `:1439`.

---

*Compiled 2026-09-07 by targeted grep/section read of `lrc_proof_v10_21.md`. No other file
was modified.*
