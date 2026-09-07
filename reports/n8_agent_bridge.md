# Audit of the safe-fibre → loneliness-time bridge, n = 8

**Target.** `lrc_proof_v10_21.md` (1641 lines), the implication

> "there exists a safe fibre `b ∈ B_div`"  ⟹  `x_0(E) ≥ 1`.

**Scripts.** `experiments/n8/bridge_*.py` (five files, all exact integer arithmetic,
no floating point in any decision). Log: `experiments/n8/bridge_run_v1_L1200.log`.

---

## 0. Verdict

| Question | Answer | Grade |
|---|---|---|
| Is the implication stated as a lemma anywhere in the file? | **No.** It is used as an unstated inference rule in at least six places. | `[VERIFIED-scope]` — grep + read of §§1–13 |
| Is a map `(b, r) ↦ k ∈ {1,…,N−1}` given anywhere? | **No.** The manuscript never writes one down. | `[VERIFIED-scope]` |
| Is the implication *established*? | **No** — it is asserted, not proved. | `[VERIFIED-scope]` |
| Is it *true* at n = 8? | Not refuted, and it cannot be refuted at n = 8 (LRC holds there, so the consequent is always true). No tuple was found where the antecedent held and `x_0 = 0`. | `[EMPIRICAL]`, 1928 tuples |
| Does the framework's **own** safety notion (`E_non`-only, §2/§2.4) suffice for the reconstructed map? | **No.** 899 204 of 2 406 197 `(b,r)` pairs produce a `k` that is not a safe point; 17.7 % of `E_non`-safe fibres produce **no** valid `k` at all. | `[EMPIRICAL]`, exact |
| Does the **all-runner** safety notion suffice? | **Yes**, exactly. 1 353 447 / 1 353 447 pairs valid; 0 failures. | `[EMPIRICAL]` + `[PROVED]` identity, §3 |
| Are there named "proved" lemmas that fail at n = 8? | **Yes, two.** Lemma 11.3c is false; Lemma 11.3a′ Case III is incomplete at its own witness fibre. Both hand-verified. | `[PROVED]` (explicit counterexamples) |

The headline is not "the bridge is false". It is: **the bridge is a gap, not a step.**
The manuscript's stated safety notion is *not* sufficient for it, the sufficient
notion is a different one that the manuscript uses only intermittently, and two
lemmas that instantiate the bridge for even `n` and for `e_div = n²` are wrong at
`n = 8` for exactly the reason the missing step would have exposed.

---

## 1. Where the implication appears (located, quoted verbatim, file:line)

The implication is never given a name, a statement, or a proof. It appears as an
unannounced final clause. Every instance below is a place where a residue-level
conclusion is converted into `x_0 ≥ 1` with no intervening construction.

`lrc_proof_v10_21.md:150`
> The goal in Case 2 is to prove that there exist $b \in B_{\rm div}$ and $r \in \mathbb{Z}/n\mathbb{Z}$ with $C(r,b)=0$. Equivalently, full obstruction cannot persist on the divisible-fibre interval.

That is the antecedent, and the word "Equivalently" is doing no work toward `x_0`.
The coverage multiplicity it refers to is defined one line earlier, over `E_non` only:

`lrc_proof_v10_21.md:149`
> $$C(r,b)=\#\{e \in E_{\rm non} : r \in \mathrm{bad}(e,\lfloor eb/L \rfloor,n)\}.$$

`lrc_proof_v10_21.md:279` (the formal definition, §5.1 — index set left unspecified)
> Fibre $b$ is **safe** if $\bigcup_i \mathrm{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

`lrc_proof_v10_21.md:379` (Lemma 5.2a)
> …*then $r_d = -d^{-1} \bmod n$ is uncovered at $b_0 = L/n$, giving $x_0(E) \geq 1$ directly.*

`lrc_proof_v10_21.md:429` (Lemma 5.2, the "Dropped-unit bridge")
> *Then $x_0(E) \geq 1$.*

`lrc_proof_v10_21.md:854` (Proposition 11.3-FINAL, Tier 1 — the clearest instance)
> **Proof (Tier 1).** By Lemma 11.3a' (proved above), there exists a fibre $\hat{b} \in J \cap \mathbb{Z}$ at which $s_d$ is uncovered. … In all cases $\hat{b} \in B_{\rm div}$. Hence $x_0 \geq 1$. $\square$

`lrc_proof_v10_21.md:866` (Lemma 11.3a′)
> …*Then there exists a fibre $\hat{b} \in J \cap \mathbb{Z}$ at which $s_d$ is uncovered by every retained runner, giving $x_0(E) \geq 1$.*

`lrc_proof_v10_21.md:981`
> Hence $M^* \not\subseteq \bigcup_e \mathrm{bad}(e, T_e(b^*), n)$, and some residue in $M^*$ is uncovered at $b^*$. Therefore $b^*$ is safe and $x_0 \geq 1$. $\square$

`lrc_proof_v10_21.md:755` (Corollary 9.6 — the two quantities are silently identified)
> …so both $B_{\rm safe} \geq \varphi(n)$ and $x_0 \geq \varphi(n)$ hold in every composite quantitative branch treated in §9.

`B_safe` is never defined in the file. The pattern "`b` is safe, hence `x_0 ≥ 1`" is
the entire content of the bridge, and the sentence at `lrc_proof_v10_21.md:946` shows
the type confusion that follows from never writing the map down:

> Since this holds for all $v \in E$, runner 0 is lonely at $t^* = 1/n$. Hence $x_0 \leq 1/n$, and since $x_0 \geq 1/n$ is the definition of loneliness, $x_0 \geq 1/n$ gives $B_{\rm safe} \geq 1$.

`x_0` is a cardinality (§1.2, line 62); `1/n` is a real number. The three clauses are
not comparable quantities and the sentence does not parse as mathematics.

### 1.1 Finding F0 — no map is given

**There is no map from `(b, r)` to `k` anywhere in `lrc_proof_v10_21.md`.** Confirmed by
grep over the whole file for `nL`, `N-1`, `\bmod N`, `k =`, `b +`, `rL`. `N = nL` and the
definition of `x_0` occur only at lines 61–66 (§1.2) and in §4 (line 254, Case 1, which
uses its own witnesses `k_j = jL` and never touches `B_div`). From line 258 onwards the
variable `k` is re-used for the divisible-runner multiplier `e_div = kn` and for band
indices, and never again denotes a time. **`B_div` and `{1,…,N−1}` are never connected.**

This is itself the primary finding. Everything below is what happens when the missing
map is reconstructed in the only way the coordinates allow.

---

## 2. What the pair `(b, r)` must be converted into

`B_div ⊂ [L/n, (n−1)L/n]` has about `L` elements; `{1,…,N−1}` has `nL − 1`. A fibre
alone cannot be a time. The unique reconstruction consistent with the manuscript's own
coordinates (`b` a fibre, `r ∈ Z/nZ` an uncovered residue) is

```
    k(b, r) := b + r·L .
```

### 2.1 Why this is the right map (exact, proved)

For `b ∈ [0, L)` write `e·b = t_e·L + s_e` with `t_e = ⌊e b / L⌋`, `s_e = (e b) mod L ∈ [0,L)`.
Then `e·k = t_e L + s_e + e r L`, and since `s_e < L`,

```
    (e·k) mod nL = L · ((t_e + e·r) mod n) + s_e .
```

Write `u_e := (t_e + e r) mod n`. Membership `(e k mod N) ∈ [L, (n−1)L]` therefore holds
iff `u_e ∈ {1,…,n−2}`, or `u_e = n−1` and `s_e = 0`. And by definition
`r ∈ bad(e, t_e, n) ⟺ e r ≡ −t_e or −(t_e+1) (mod n) ⟺ u_e ∈ {0, n−1}`. Hence:

> **The correct bridge.** If `r ∉ ⋃_{e ∈ E} bad(e, t_e(b), n)` — the union over **all**
> speeds, divisible ones included — then `k = b + rL` satisfies `1 ≤ k ≤ N−1` and
> `(e_i k mod N) ∈ [L,(n−1)L]` for every `i`. So `x_0(E) ≥ 1`.
> The converse fails only in the boundary case `u_e = n−1, s_e = 0`, where the bad-set
> definition is conservative.

Verified on 221 654 `(b,r)` pairs over 739 tuples: **0 mismatches** of the characterisation,
**0 failures** of the implication on the 36 804 pairs where `r` was uncovered by all of `E`,
and 6 758 safe `k` sitting on the conservative boundary (`bridge_map_identity_v1.py`).

### 2.2 The gap this exposes

`B_div` is defined (§5.1, line 264) purely as an interval, and §2/§2.4 take the union over
`E_non` only. Membership `b ∈ B_div` is therefore doing the work of the divisible runners
implicitly. It succeeds **only for `e_div = n` exactly**:

- For `e = n`: `u_e = ⌊n b / L⌋ mod n ∈ {1,…,n−1}` on `B_div`, and `u_e = n−1` forces
  `b = (n−1)L/n`, where `s_e = 0`. Safe throughout `B_div`, including the endpoint.
- For `e = cn` with `c ≥ 2`: the condition is `(c·b mod L) ∈ [L/n, (n−1)L/n]`, which
  `b ∈ B_div` does **not** imply.

So the framework's own safety notion is sufficient exactly when `E_div = {n}` — and the
manuscript's §11–§12 branches are all stated for `|E_div| ≥ 1` with `e_div = kn`, `k` arbitrary.

---

## 3. The test

**n = 8. All arithmetic exact.**

Tuples: 7 distinct positive integers, `gcd = 1`, at least one multiple of 8 (Case 2).
To make direct enumeration of `k ∈ {1,…,N−1}` feasible I restricted to `L = lcm(E) ≤ 1200`,
so `N = 8L ≤ 9600`. **This restriction is stated as a scope limit, not a result.** Two
generators were used, so the sample is not an artefact of one construction:

1. **Divisor families** — all 7-subsets of the divisors of `L` with `lcm` exactly `L`,
   `gcd 1`, at least one multiple of 8; capped per `L`, shuffled.
2. **Random small speeds** — random 7-subsets of `[1,90]` with the same filters.

Each generator was run twice: once unrestricted, once forcing `8 ∉ E` (so `E_div` contains
only proper multiples `16, 24, 32, …`) — the stress case identified in §2.2.

Per tuple: `x_0(E)` by direct enumeration over all `k`; the set of `E_non`-safe fibres and
the set of all-`E`-safe fibres over `B_div`; and, for every `(b, r)` with `r` uncovered,
a direct membership check of `k = b + rL`.

---

## 4. Results

### 4.1 Both directions of the implication

`bridge_safe_fibre_to_k_v1.py 1200` — 1928 tuples over four families:

```
  x_0 = 0                                     : 0
  E_non-safe fibre exists but x_0 = 0         : 0        <- implication never falsified
  x_0 >= 1 but NO E_non-safe fibre            : 0
  x_0 >= 1 but NO all-E-safe fibre            : 0
  map k=b+rL on E_non-safe pairs   : 1506993/2406197 valid,  899204 FAIL   (37.4%)
  map k=b+rL on all-E-safe pairs   : 1353447/1353447 valid,       0 FAIL
  tuples where EVERY E_non-safe fibre fails   : 0
  true safe points k, total                   : 1860130
  ... whose fibre b = k mod L is NOT in B_div :  287274  (15.4%)
```

Reading:

- **The implication itself was never falsified**, and at `n = 8` it cannot be: LRC holds
  for `n = 8`, so `x_0 ≥ 1` for every tuple and the consequent is vacuously available.
  This is a limitation of testing at `n = 8`, and it is why the map, not the implication,
  is the object worth testing.
- **The reverse direction is tight in the sample**: no tuple had `x_0 ≥ 1` with no safe
  fibre, under either reading. The framework does not miss tuples; it misses *witnesses*.
- **The framework's own `E_non`-only reading does not support the map**: 37.4 % of the
  `(b,r)` pairs it certifies produce a `k` that is not a safe point.
- **The all-`E` reading supports it exactly**: 0 failures in 1 353 447 pairs.
- `B_div` is lossy in the other direction too: 15.4 % of the true safe points have
  `b = k mod L` outside `B_div`, so they are invisible to the framework.

### 4.2 Does every safe fibre yield a `k`?

`bridge_fibre_yield_v1.py` — 1389 divisor-family tuples, `L ≤ 1200`:

```
  E_non-safe fibres b in B_div                 : 616216
  ... of which yield NO safe k at all          : 108839   (17.7%)
  tuples having at least one such barren fibre :   1114   (80.2%)
```

**No.** Nearly one in five `E_non`-safe fibres is barren: every residue it leaves uncovered
maps to a `k` that fails the membership condition. Smallest example, fully hand-checkable:
`E = (1,2,3,4,6,8,24)`, `L = 24`, `b = 8` — uncovered by `E_non` is `{3,6}`, uncovered by all
of `E` is `∅`, and both `k = 8+3·24 = 80` and `k = 8+6·24 = 152` fail.

### 4.3 Exactly when the `E_non`-only reading is sound

`bridge_ediv_scope_v1.py`, partitioning the same tuples by `E_div`:

| `E_div` | tuples | `E_non`-safe fibres | barren | `(b,r)` pairs | failing |
|---|---:|---:|---:|---:|---:|
| `= {8}` exactly | 275 | 123 422 | **0 (0.00 %)** | 224 786 | **0 (0.00 %)** |
| `\|E_div\| = 1`, `e_div ≠ 8` | 282 | 125 273 | 21 760 (17.37 %) | 196 016 | 32 455 (16.56 %) |
| `\|E_div\| ≥ 2` | 832 | 367 521 | 87 079 (23.69 %) | 1 044 766 | 271 131 (25.95 %) |

This is the sharp form of the gap, and it matches the analysis of §2.2 exactly: the
`E_non`-only notion of safety is sound **iff** the only divisible speed is `n` itself.
Every other Case-2 configuration needs the divisible runners in the union, and the
manuscript's §2 and §2.4 leave them out.

---

## 5. Two named "proved" lemmas that fail at n = 8

Both are instances of the bridge — each produces a specific `(b, r)` pair and concludes
`x_0 ≥ 1`. Both are hand-verified below from the definitions.

### 5.1 Lemma 11.3c is FALSE

`lrc_proof_v10_21.md:906` states:

> **Lemma 11.3c (Even-$n$ early-fibre lemma; proved).** *Let $n \geq 4$ be even and composite, $d \in \{1,\ldots,n-1\}$ a dropped unit residue class, and set $r_d := -d^{-1} \pmod{n}$. Then the fibre $b^{\rm early} := \frac{2L}{n} \in B_{\rm div}$ is safe: no retained runner covers $r_d$ at $b^{\rm early}$.*

**Counterexample.** `n = 8`, `E = (1,2,3,4,6,8,24)`. `gcd(E) = 1`, `L = lcm(E) = 24`, `8 ∈ E`
so Case 2 holds. `R_non = {1,2,3,4,6}`; the units mod 8 are `{1,3,5,7}`; retained units are
`{1,3}`; so `d = 7` is a dropped unit class. `d⁻¹ = 7`, `r_d = −7 ≡ 1 (mod 8)`.
`b_early = 2L/n = 6 ∈ B_div = [3,21]`.

The **retained** runner `e = 6` (non-divisible, `gcd(6,8) = 2`) has floor
`t = ⌊6·6/24⌋ = 1` and, by the §5.1 definition,
`bad(6,1,8) = Sol(6,−1,8) ∪ Sol(6,−2,8) = ∅ ∪ {1,5} = {1,5} ∋ 1 = r_d`.

So a retained runner covers `r_d` at `b_early`. The lemma is false as stated. The induced
witness `k = b_early + r_d·L = 30` is not a safe point: `6·30 mod 192 = 180 ∉ [24,168]`.

**Where the proof goes wrong.** `lrc_proof_v10_21.md:911`:
> $$r(e,\, b^{\rm early}) = \left\lfloor \frac{n \cdot e \cdot (2L/n)}{L} \right\rfloor \bmod n = \lfloor 2e \rfloor \bmod n = 2e \bmod n = 2\rho_e \bmod n,$$

The proof assigns each runner the *single* residue `2ρ_e mod n` and then argues by parity
that it is even while `r_d` is odd. But `2ρ_e mod n` is not `bad(e, t_e(b), n)`. For a
non-unit `e` at a floor `t` with `g | t`, the bad set is a whole coset of `H_g`, and such a
coset contains odd residues. Here `{1,5} = 1 + H_2` is entirely odd. **The parity argument
never engages the actual bad-set definition.**

The manuscript already knows this phenomenon and states it two pages earlier — at
`lrc_proof_v10_21.md:864`, Remark 11.4:
> For composite $n$, non-unit runners can cover $r_d$ on $I_d$ (e.g.\ $n=8$, $d=7$, runner $e=4$ with $\rho=4$ is non-unit and can block $r_d$ on $I_d$), so the $I_d$-based safe-fibre count used in earlier drafts does not apply. Proposition 11.3-FINAL bypasses $I_d$ entirely, using the $J$-window and (for even $n$) the early fibre $b = 2L/n$ instead.

The escape route chosen in that remark — `b = 2L/n` — is precisely Lemma 11.3c, and it
fails to the same mechanism, at the same `n = 8, d = 7`.

**Frequency.** Over 2856 `(E, d)` cases with `L ≤ 1200` (`bridge_named_lemma_instances_v2.py`):
`r_d` is covered at `b_early` by a **retained** `e ∈ E_non` in **1105** cases (38.7 %);
`b_early` is not safe even under the all-`E` reading in 768 cases;
`k = b_early + r_d·L` is not a safe point in 1461 cases.

**Load-bearing?** `lrc_proof_v10_21.md:1421` lists 11.3c in the Tier-1 dependency map:
> - *Case 2, composite $n$, $|E_{\rm div}|=1$, dropped unit:* **Lemma 11.3a'** (actual-speed late-window, proved v10.13; replaces Lemma 11.3a) + Lemma 11.3c $\Rightarrow$ Proposition 11.3-FINAL.

Its only explicit *use* in a proof body is Tier 2 (`:862`). Whether Tier 1 genuinely needs
it is a question for the manuscript's authors; the dependency map says it does.

### 5.2 Lemma 11.3a′ Case III does not check the divisible runner at its own witness fibre

`lrc_proof_v10_21.md:896`, Case III in full:

> **Proof (Case III: $k \equiv 0 \pmod n$, i.e.\ $e_{\rm div} = n^2, 2n^2, \ldots$).** Then $k(n-1) \equiv 0 \pmod n$ and $k(n-1)+1 \equiv 1 \pmod n$, so $n \nmid k(n-1)+1$. The LOW Sol is non-empty: $\mathrm{bad}(kn, k(n-1), n) = \mathbb{Z}/n\mathbb{Z}$ only if $n \mid k(n-1)$; here $k(n-1) \equiv -k(1) \equiv 0$, so $n \mid k(n-1)$ and bad $= \mathbb{Z}/n\mathbb{Z}$. Use $\hat{b} = b^* - 1$ as in Case II. Since $L \geq n^2 > n(n-1)$: unit runner floors at $\hat{b}$ are $\rho - 1$, same argument. ✓

The last sentence checks the **unit** runners at `b̂` and stops. The divisible runner is
never recomputed at `b̂`. Case II *does* recompute it, and its conclusion there
(`bad = ∅`) rests on `k ≡ 1 (mod n)` — which is exactly what Case III negates.

**Counterexample.** `n = 8`, `E = (1,2,3,4,5,6,64)`. `gcd(E) = 1`, `L = 960`,
`E_div = {64} = {8·8}` so `k = 8 ≡ 0 (mod 8)`: Case III, `|E_div| = 1`. Every non-divisible
speed is `< 8`, so `q_e = 0` for all of them — the proof's clean branch, no shift invoked.
`R_non = {1,…,6}`, so `d = 7` is the dropped unit class and `s_d = d⁻¹ − 1 = 6`.
`b* = 7·960/8 = 840`, witness `b̂ = 839`.

At `b̂ = 839` the divisible runner has `t = ⌊64·839/960⌋ = 55`, and
`−(t+1) = −56 ≡ 0 (mod 8)`, so `Sol(64, −56, 8) = Z/8Z` and
`bad(64, 55, 8) = Z/8Z ∋ 6 = s_d`.

So `s_d` **is** covered at `b̂`, contradicting the lemma's "uncovered by every retained
runner". The full computation, every runner printed, is in
`bridge_ediv_scope_v1.py` section (A). The induced witness `k = 839 + 6·960 = 6599` is not
a safe point: `64·6599 mod 7680 = 7616 ∉ [960, 6720]`.

Note the mechanism: the six non-divisible runners **do** leave `s_d = 6` uncovered — the
`E_non`-only reading calls `b̂ = 839` safe. It is the divisible runner, dropped from the
union by §2.4, that closes the gap. This is finding F0 and §2.2 firing on a named lemma.

**Frequency, respecting the case hypotheses** (`bridge_fibre_yield_v1.py`, `|E_div| = 1`,
split by case and by whether all non-divisible speeds are `< n`):

```
  Case I   q_e=0    cases=  37   s_d covered by all E =   0   k unsafe =   0   [clean]
  Case II  q_e=0    cases=   7   s_d covered by all E =   0   k unsafe =   0   [clean]
  Case III q_e=0    cases=   4   s_d covered by all E =   4   k unsafe =   3   [FAILS]
```

Cases I and II are clean in their own hypotheses in this sample. **Case III fails in
4 of 4.** The `q_e ≥ 1` rows are reported separately in the script output and are **not**
counted as refutations: the proof at `lrc_proof_v10_21.md:898` prescribes a leftward shift
there rather than claiming `b*` works, and that shift procedure was not tested.

### 5.3 The manuscript's one explicit n = 8 numeric claim

`lrc_proof_v10_21.md:862`:
> *Case $n=8$, $L=120$:* $J = [720/7,\, 105]$, so $J \cap \mathbb{Z} = \{103,104,105\}$ (3 fibres, all safe by Lemma 11.3a). Since $n=8$ is even and $d$ is a dropped unit of $\mathbb{Z}/8\mathbb{Z}$, Lemma 11.3c gives the additional safe fibre $b^{\rm early} = 2L/n = 30 \in B_{\rm div}$. The sets $\{103,104,105\}$ and $\{30\}$ are disjoint, giving $x_0 \geq 4 = \varphi(8)$.

Exhaustive check over all **9668** tuples with `lcm` exactly 120, `gcd 1`, at least one
multiple of 8, and at least one dropped unit class:

```
  fibre b=103 not safe (all-E union = Z/8Z)      : 4474
  fibre b=104 not safe                           : 4695
  fibre b=105 not safe                           : 4695
  fibre b= 30 not safe                           : 2020
  at least one of 103,104,105 not safe           : 7337   (75.9%)
  r_d covered at b_early = 30 (11.3c fails here) : 6781   (70.1%)
  k = 30 + r_d*120 not a safe point              : 4340   (44.9%)
```

**The route fails for most tuples; the conclusion happens to hold.** `min x_0 = 60` over
all 9668 tuples, comfortably above `φ(8) = 4`. Reported this way deliberately: the
paragraph's arithmetic does not survive, but nothing here shows `x_0 ≥ φ(8)` to be false.
Separately, the paragraph cites **Lemma 11.3a**, which `lrc_proof_v10_21.md:9` records as
carrying defect ERR-C-01 and as superseded by 11.3a′.

---

## 6. What this audit does NOT claim

- It does **not** refute the implication "safe fibre ⟹ `x_0 ≥ 1`". At `n = 8` that is
  untestable, because the consequent always holds. Testing at a modulus where LRC is open
  would be needed, and no such modulus admits exhaustive `x_0` enumeration.
- It does **not** touch the prime-`n` chain-transfer argument (§5.3, CT.1-FINAL), the
  `n = p²` material (§13), or the squarefree `n = pq` branch (§12). Only the bridge and
  the two even-/prime-power lemmas that instantiate it at `n = 8` were examined.
- It does **not** claim Lemma 11.3a′ Cases I and II are correct — only that no failure was
  found within their own hypotheses in this sample (37 and 7 cases respectively, which is
  a small sample and reflects how rarely `L ≤ 1200` admits all non-divisible speeds `< 8`).
- The `q_e ≥ 1` shift procedure of `lrc_proof_v10_21.md:898` was **not** tested.
- Scope of every empirical number above: `n = 8`, `L ≤ 1200`, the four generators of §3.

## 7. What would repair the bridge

Adding one lemma, with the argument of §2.1, would close F0 and simultaneously fix §5.2:

> **Lemma (Fibre-to-time).** Let `b ∈ Z ∩ [0, L)` and `r ∈ Z/nZ` satisfy
> `r ∉ ⋃_{e ∈ E} bad(e, ⌊eb/L⌋, n)` — the union over **all** `n−1` speeds. Then
> `k := b + rL ∈ {1,…,N−1}` and `(e_i k mod N) ∈ [L,(n−1)L]` for all `i`; hence `x_0(E) ≥ 1`.

Consequences for the manuscript: `C(r,b)` at `:149` must range over `E`, not `E_non`; the
index `i` at `:279` must be said to range over all of `E`; and `b ∈ B_div` becomes
unnecessary rather than load-bearing (any `b ∈ [0,L)` works once the divisible runners are
in the union). Every branch that currently discharges the divisible runners by appeal to
`b ∈ B_div` alone would then need to discharge them explicitly, as Lemma 11.3a′ Cases I
and II already do and Case III does not.

---

## Appendix — scripts

| File | Purpose |
|---|---|
| `experiments/n8/bridge_safe_fibre_to_k_v1.py` | Main sweep: true `x_0`, both safety readings, map test, both directions. `python3 bridge_safe_fibre_to_k_v1.py 1200` |
| `experiments/n8/bridge_fibre_yield_v1.py` | Per-fibre yield (barren fibres); Lemma 11.3a′ split by its own cases |
| `experiments/n8/bridge_ediv_scope_v1.py` | Hand-checkable recomputation of both counterexamples; `E_div` scope table |
| `experiments/n8/bridge_named_lemma_instances_v1.py` | First pass at the named lemmas (superseded by v2) |
| `experiments/n8/bridge_named_lemma_instances_v2.py` | Case-respecting test of 11.3c, 11.3a′, and the `L = 120` claim |
| `experiments/n8/bridge_map_identity_v1.py` | Verifies the exact `(e·k) mod nL` characterisation underpinning §2.1 |
| `experiments/n8/bridge_run_v1_L1200.log` | Full output of the main sweep |
