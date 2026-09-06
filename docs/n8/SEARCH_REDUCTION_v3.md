# Two reductions of Rosenfeld's Lemma 7 search (v3)

2026-09-07. Supersedes v1 (wrong prime set) and v2 (§1 wrongly accused
`WHY_13_AND_19_v2.md` of inverting the p=41 exception; it did not). Scripts: `experiments/n8/normalised_search_v1.py`
(plain), `normalised_search_v2.py` (with the paper's own optimisations).

Notation as in `COLLAPSE_Z163_v1.md`: `n = k+1`, `N = np`, `H = N/2`, targets
`j ∈ {1,…,H}`, speeds `v ∈ {1,…,H}` with `p ∤ v`; `v` covers `j` iff
`jv mod N < p` or `> N−p`.

---

## 1. The prime list: what was wrong, and what was not  [PROVED + CITED, source read]

**Retraction of a claim made in `SEARCH_REDUCTION_v2.md` §1.** That version said
the `k = 7` exception at 41 had been recorded "with the sense inverted" in
`WHY_13_AND_19_v2.md`. **That is false.** §3 of that document states the exception
correctly and derives it: it lists the four lonely windows of
`T₇ = {1,4,12,13,14,16,20}`, tabulates which primes' grids hit them, marks `p = 41`
as the sole miss, and quotes Rosenfeld's sentence verbatim. It was right. The
check that settles it is reading §3, which v2 did not do before writing.

What *was* wrong is narrower: `run_k7_primes_v1.py`, written earlier today,
enumerated all 28 primes in `[31,163]`. The source gives

> `S = {31, 37, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
> 109, 113, 127, 131, 137, 139, 149, 151, 157, 163}`

— 27 primes, **41 omitted** — and §7 states that for `k = 7` any prime at least 31
*other than 41* works. The script is corrected and now asserts `len(PRIMES) == 27`.
`ROSENFELD_REVIEW_v1.md` said "27 primes" and elided the list; it was not wrong.

**The independent confirmation stands.** The bad-cover search found the witness at
`p = 41` before the source sentence was read:

    T = {1, 4, 12, 13, 14, 16, 20},   N = 328,  H = 164

covers all 164 targets (zero uncovered, checked directly), satisfies
`gcd(R ∪ {328}) = 1` for all 21 six-subsets `R`, and has the LR property as real
speeds (`max_t min_i ‖t v_i‖ = 0.14284 > 1/8`). Its value is that a structurally
different method — exhaustive search over covers, under the normalisation of §2 —
returns the same tuple and the same exception as the window/grid mechanism of
`WHY_13_AND_19_v2.md` §3. Two methods, one answer, agreeing with the source.

## 2. Unit scaling — WLOG `1 ∈ T`  [PROVED]

For a unit `c` mod `N`, the map `v ↦ cv`, `j ↦ c^{-1}j` permutes `ℤ/N` and fixes
`‖jv/N‖`, so it preserves "T covers every target"; it fixes the `q`-adic valuation
of every speed for each prime `q | N`, so it preserves the gcd side condition.
With the `v ↔ N−v` folding already used to halve the speed range, the group acting
is `(ℤ/N)^*/{±1}`, of order `φ(N)/2`.

The gcd condition says: for every prime `q | N`, at least two speeds of `T` avoid
`q` (a `(k−1)`-subset omits one element, so a subset inside `qℤ` exists iff at most
one speed escapes). When `n` is a prime power — `n = 7`, `n = 8` — the only prime
of `N` besides `p` is that one, and `p ∤ v` always, so some speed is coprime to `N`.
Scaling by its inverse gives **WLOG `1 ∈ T`**: a factor `φ(N)/2 = 324` at `N = 1304`.
The speed `1` covers exactly `{1,…,p−1}`, so the search restarts at target `p` with
`k−1` speeds.

The paper does not use this symmetry; §6 explicitly lists the one symmetry it
leaves unexploited (`i` covers `j` ⟺ `j` covers `i`) and unit scaling is not among
its optimisations. *Scope*: the step "some speed is coprime to `N`" needs `n` a
prime power — do not transcribe to general `n` unchecked.

## 3. A coarse speed is forced  [PROVED]

`p·v mod N = p·(v mod n)`, which is `< p` only when `n | v`, and never exceeds
`N − p = p(n−1)`. So **`j = p` is covered only by speeds divisible by `n`**, and
every bad cover contains one; likewise at `j = tp` for `t` coprime to `n`,
`tp ≤ H`. In the notation of `COLLAPSE_Z163_v1` §3 this is `x ≥ 1`, so with §5
there and the `x = 4` result, the sectors still open at `p = 163` are `x ∈ {1,2,3}`.

## 4. Validation  [VERIFIED against every published data point]

`normalised_search_v2.py` reproduces the paper's §7 statements exactly:

| `k` | our result | paper §7 |
|---|---|---|
| 3 | fails at 5, applies at 7, 11 | "true for all prime `p` larger than 7" |
| 6 | applies 13, 19, 31, 37; fails 17, 23, 29 | "larger than 31 and for 13 and 19 (not 17, 23, 29)" |
| 7 | applies 31, 37; **fails 41** | "any prime `p` at least 31 other than 41" |

Both our implementations (`lemma7_criterion_v1.py`, unnormalised; `normalised_*`)
agree on every case where both were run.

## 5. What is NOT claimed

The 32-hour search is **not** replaced. Our timings are `k=7`: 38 s at `p = 31`,
162 s at `p = 37` — roughly a fourfold rise per prime step in a pure-Python
implementation, against the author's C++ bitset code. Nothing here supports a
wall-clock claim at `p = 163`. What is established is a proved factor-`φ(N)/2`
reduction of the space, a proved forced first speed, and an implementation that
has matched every published data point.
