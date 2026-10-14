# Review — Rosenfeld, *The lonely runner conjecture holds for eight runners*

arXiv:2509.14111v2 (16 Oct 2025). Read from the PDF, 2026-09-07.
Integrity: `docs/n8/source_integrity.md`.

## 0. Two corrections to the automated summary that fetched it

A first pass used a summarizer, and two of its claims are **wrong**. Recorded so
neither propagates:

- It said the speeds must be "pairwise coprime". They need not be. The only
  normalisation is `gcd(v₁,…,v_k) = 1`, and that is WLOG (divide through).
- It attributed the minimal-counterexample bound to **Cusick (1973)**. It is
  **Malikiosis–Santos–Schymura**, cited as [13, Theorem A], and the abstract's
  "recent results" refers to that. Rosenfeld notes the weaker Giri–Kravitz bound
  [12] would probably also suffice.

## 1. What is proved, and in which convention

Rosenfeld indexes by `k` = number of **moving** speeds, with separation
`1/(k+1)`, so `k+1` runners counting the stationary one. He settles `k = 7`.

> **Theorem 1.** For all sets of integers `{v₁,…,v₇}` of size 7 there exists a
> real `t` such that for all `i`, `‖t vᵢ‖ ≥ 1/8`.

**This is exactly `intLRC 8` in our Lean tree** (`Fin 7` speeds, bound `1/8`) —
the direct successor to the `intLRC 7` we just closed. The runner-count
convention matches Barajas–Serra's "seven runners" and our `intLRC 7`.

## 2. The architecture

1. **Theorem 2** = [13, Thm A] (Malikiosis–Santos–Schymura). If LRC holds for
   `k`, it holds for `k+1` for every `k`-tuple with `gcd = 1` and
   `∑_{S ⊆ {1..k}} gcd({vᵢ : i ∈ S}) > ((k+1 choose 2))^{k−1}`.
2. **Corollary 3** (AM–GM on Theorem 2). A counterexample must have *bounded
   product*: for `k = 7`, `𝒫 = ∏vᵢ < 7.4 × 10⁵⁴`.
3. **Lemma 4.** `lcm(2,…,k+1)` divides `∏vᵢ` for any set without the LR
   property. Elementary.
4. **Lemma 5.** If LRC holds for `k−1`, `gcd(v₁..v_k) = 1` but
   `gcd(v₁..v_{k−1}) ≠ 1`, then `{v₁..v_k}` has the LR property.
5. **Lemma 6 / Lemma 7** (the engine). For a given `p`, if a **finite** condition
   over tuples in `{1,…,⌊(k+1)p/2⌋} \ pℕ` holds, then `p` divides `∏vᵢ` for every
   non-LR set. Lemma 7 is the set-cover reformulation actually computed.
6. **The contradiction.** Verify Lemma 7 for 27 primes
   `S = {31,37,…,163}`; then `𝒫` is divisible by
   `lcm({2..8} ∪ S) ≈ 1.82 × 10⁵⁵`, exceeding the `7.4 × 10⁵⁴` bound. No
   counterexample exists.

**Lemmas 5 and 6 both assume LRC for `k−1`.** For `k = 7` that hypothesis is
LRC for 6 moving speeds — i.e. **`intLRC 7`, which we now have machine-verified
and axiom-clean**. Rosenfeld's n=8 proof is conditional on precisely the result
this project just finished.

## 3. The computation, and what it costs

Lemma 7 is a set-cover search: find a `7`-tuple from `{1,…,⌊8p/2⌋} \ pℕ` that
covers `{1,…,⌊8p/2⌋}` under a divisibility-derived covering relation, subject to
a `gcd` side condition. If **no** such "bad cover" exists, Lemma 7 applies to
that `p`. The implementation is C++ with bitsets plus four backtracking
optimisations (§6).

> "verifying the condition of Lemma 7 for `k = 7` and `p = 163` takes roughly
> **32 hours** with our implementation on a single processor core"

— for **one** prime, the largest of 27.

**Consequence for mechanisation, stated now rather than discovered later:**
this is not reachable by the kernel-`rfl` technique that carried BS §7. That
technique ran ≈2×10⁶ kernel operations in ~21 s (≈10⁵ ops/s) and was already at
the edge of `lake build`'s elaboration stack. Rosenfeld's search is many orders
of magnitude larger *and* is a pruned backtracking search — kernel reduction
cannot exploit the pruning, so the naive cost is far worse than his 32 hours,
not better. **Formalising the computation as-is is not on the table by our
current method.** The analytic scaffolding (§2 items 1–5) is ordinary
mathematics and is formalisable.

## 4. The analytic target — named by the author

§7, "Possible further improvement":

> "There might even be a good provable reason for which Lemma 6 holds for all
> `k`, for any large enough integer `p`. That could lead to a proof of the
> lonely runner conjecture."

He also reports the empirical pattern: for `k = 3,4,5` every prime `p` larger
than 7, 17, 23 respectively appears to work; for `k = 6`, every `p > 31` and also
13, 19 (but not 17, 23, 29); for `k = 7`, every `p ≥ 31` other than 41.

**This is the well-posed analytic goal.** Proving "Lemma 6 holds for all
sufficiently large `p`" would (a) make `k = 7` computer-free, hence
mechanisable, and (b) attack all `k` by the same argument. It is the author's
own stated open direction, and it is the natural point of contact with this
project's general-`n` programme (`lrc_proof_allN_v11_8.md`, currently
**conditional**).

Note the exceptions are the interesting data: `k = 6` fails at 17, 23, 29 but
works at 13 and 19; `k = 7` fails at 41. Any proposed proof must predict those,
and they are cheap to reproduce — that is the first thing to check, and it is a
falsification test the moment a candidate mechanism exists.

## 5. What we have that bears on this

- `intLRC 7` — machine-verified, axiom-clean. Exactly Lemma 5/6's hypothesis.
- Kernel finite-search machinery (`Section7_M1*`) — proven to work axiom-free,
  with measured throughput and known stack limits. Useful for *small* `p`, and
  useful for reproducing the exception pattern above.
- `lrc_proof_allN_v11_8.md` — the conditional general-`n` manuscript, and the
  n=11 lineage. Whether its machinery says anything about Lemma 6 for large `p`
  is an open question, and the first thing worth checking.

## 6. Not yet done

- The implementation repository [17] has not been fetched or reviewed.
- §8 ("Improving the lacunary case", Theorems 8–10, Corollary 10) is read but
  not assessed; it is independent of the `k = 7` proof.
- [13] Malikiosis–Santos–Schymura and [12] Giri–Kravitz have not been obtained;
  Theorem 2 is currently `[CITED]`, not verified. It is load-bearing for the
  whole argument, so it needs `citation-verifier` before any grade rests on it.
