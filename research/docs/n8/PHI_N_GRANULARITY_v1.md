# The φ(n) permutation law is the n=8 block structure

2026-09-07. Follows the pointer to the extended AP work. The `8|v` block
structure found in `COLLAPSE_Z163_v1.md` is not specific to `p = 163`, and it is
not new to this project: it is the φ(n) permutation law of
`lrc_ap_phi_n_law_v1.md`, evaluated at a composite `n`.
Script: `experiments/n8/phi_n_granularity_v2.py`.

---

## 1. The shared mechanism

Two existing results in this corpus turn on one group fact.

**`lrc_ap_phi_n_law_v1.md`, Theorem 3.1** (φ(n) Isolation Law for APs). Perfect
isolation occurs at times with `{δt} = r/n`, `gcd(r,n) = 1`, and there are exactly
`φ(n)` such instants per phase period. *Mechanism, quoted from the record:*
`j ↦ jr (mod n)` is a permutation of `{0,…,n−1}` iff `gcd(r,n) = 1`. Here `j`
indexes **runners**.

**`lrc_n11_ap_paper_v26.md`, Step 3** (equally-spaced preimages). For
`p ≢ 0 (mod 11)`, `r = p mod 11`, `{p·t_j} = {α + rj/11}`; since `gcd(r,11) = 1`
the values `rj mod 11` permute `{0,…,10}`, giving eleven equally-spaced points.
Here `j` indexes **preimage times**.

Same fact, two index sets. §2 applies it to a third: the members of a residue
class of targets.

## 2. The granularity law  [PROVED; VERIFIED EXHAUSTIVELY]

Setup as in Rosenfeld's Lemma 7: `N = np`, targets `j ∈ {1,…,N−1}`, and `v`
covers `j` iff `jv mod N < p` or `> N−p`. Partition the targets into the `p`
classes mod `p`; class `r` is `{ r + pt : t ∈ ℤ/n }`. Write `rv mod N = ap + b`
with `0 ≤ b < p` — `a` the **block index**, `b` the **offset**. Then

    (r + pt)·v mod N  =  ((a + tv) mod n)·p + b,

so the block index runs over the coset `a + gℤ/n`, each value hit `g` times,
where `g = gcd(v,n)`. The covering window is block `0` in full together with
block `n−1` minus its first point (that inequality is strict). Hence

> **`coverage(v, class r) = g · | ( {0} ∪ {n−1 : b ≠ 0} ) ∩ (a + gℤ/n) |`,**
> and `b = 0` exactly when `p | r`.

**Coverage of a class is always a multiple of `g = gcd(v,n)`.** Speeds coprime to
`n` cover at the finest granularity; speeds sharing a factor with `n` cover in
lumps of size `g`; at `g = n` it is all-or-nothing.

Verified: 253 084 `(n,p,v,class)` instances at `n ∈ {7,8,9,11}`,
`p ∈ {13,17,23,31,47,163}` — **0 mismatches** against the closed form.

| `n` | `g = gcd(v,n)` | per-class coverage values |
|---|---|---|
| 7 (prime) | 1 | 1 or 2 |
| 8 | 1 | 1 or 2 |
| 8 | 2 | 2 |
| 8 | 4 | 0 or 4 |
| 8 | 8 | 0 or 8 |
| 9 | 1 / 3 / 9 | 1 or 2 / 0 or 3 / 0 or 9 |
| 11 (prime) | 1 | 1 or 2 |

The `g = 1` value is 2 except in the single class `r ≡ 0 (mod p)`, where `b = 0`
removes the strict-inequality block and leaves 1.

## 3. What this says about n = 8 versus n = 11

**For prime `n`, every admissible speed has `g = 1`.** The only other divisor is
`n` itself, and `n | v` is excluded. So at `n = 11` there is no lumping at all:
every speed permutes the blocks, every speed covers 2 of the 11 members of a
class, and the coupling/complementary-pair architecture of the n=11 paper works
on a uniform population of speeds.

**At `n = 8` there are four granularity levels.** Half the admissible speeds are
non-units. `8 = 2³` gives the longest divisor chain of any `n ≤ 11`
(`n = 9` gives three levels, every prime `n` gives one).

This is the same split that `COLLAPSE_Z163_v1.md` §2 found from the covering side
and recorded as "adjacent versus opposite pairs": **adjacent pairs are the units,
opposite pairs are the non-units.** The half-range `{1,…,N/2}` used in Lemma 7
halves each class, which is why the caps there read 2/1/2/4 rather than the
full-range 2/2/4/8.

It also identifies, in one line, why the n=11 architecture is not expected to
transfer unchanged: **`11` is prime and `8` is not**, and the mechanism both
architectures rest on is exactly the one that degenerates on non-units. That is a
derived expectation about transferability, not a claim that the transfer fails —
the n=11 machinery has not been run against the four-level population.

## 4. Grades

- §2 closed form: **PROVED** (three lines of arithmetic) and **VERIFIED
  EXHAUSTIVELY** on 253 084 instances across four `n` and six primes.
- §1 identification: the φ(n) AP law, the n=11 Step 3 lemma and §2 use the **same
  group fact on three different index sets** (runners; preimage times; members of
  a target class). That is stated as a shared mechanism, **not** as one theorem
  subsuming the others — the index sets are genuinely different objects.
- §3 last paragraph: **DERIVED** expectation. Untested.

## 5. What this does not do

It does not prove `n = 8`. It explains the structure that decided sectors `x = 5`
and `x = 4` at `p = 163`, shows that structure is a general-`n` law rather than an
artefact of one prime, and connects it to work already in the corpus. Whether the
granularity law constrains a bad cover enough to close the remaining sectors —
or, in the general-`n` framework, whether it bears on Conjecture 5.2-H at `n = 8` —
is open.
