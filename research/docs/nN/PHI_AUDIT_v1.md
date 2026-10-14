# The φ(n) audit — every site checked

2026-09-22. Asked to review the Lean and the framework for φ(n) influence missed elsewhere.
Every site below was checked, with the verdict and the artefact. Sites are listed whether or not
φ turned up, so absence is recorded rather than inferred.

## Found, and previously mislabelled

| site | was recorded as | is | artefact |
|---|---|---|---|
| the criterion's flank hypothesis | `n.Prime` | `gcd(e,n) = 1`; usable flanks number φ(n) | `flankWorks_of_coprime`, `card_nonresonant_eq_totient` |
| `exists_goodK`'s pigeonhole budget | `L.length + 1 < n` | `L.length < φ(n)`; the two agree only at primes | `shifted_budget_is_totient` |
| the shifted family's primality | Euclid's lemma | `n − 2 < φ(n) ↔ n.Prime`, since `φ(n) ≤ n−1` with equality only at primes | `shifted_budget_is_totient` |
| §13E's "Klein structure" | order-8 without a reason | `(ℤ/8)ˣ` has exponent 2, which holds for **exactly the divisors of 24** | `klein_at_eight`, `not_klein_at_five/seven/nine/ten` |
| §11's binding constraint `s₇·R = 89` | an empirical `89` | `s·R ≡ 1 (mod 8)` — the unit relation, same as `e·s ≡ 1 (mod n)` | manuscript §11.2 read against `flankWorks_of_coprime` |

## Found, and already correct but unremarked

| site | the φ structure |
|---|---|
| every opening index `a = n·j + 1` | `gcd(a,n) = 1` unconditionally — the framework only ever exhibits units (`witness_is_unit`) |
| `ratWorks n L a q` | φ(q) choices of `a` at each `q`; the divisibility corollaries use only `a = 1` |
| the ρ-construction | needs `gcd(m', e) = 1` — a φ(e) condition at the flank's modulus, not at `n` |
| §5, the AP instants | φ(n) of them — `isolation_iff_coprime`, `card_coprime_eq_totient`. **This is where it started** |

## Checked, no φ structure

| site | what it runs on instead |
|---|---|
| `Cascade/` (4,759 theorems) | 10 mentions of gcd/Coprime/ZMod across `Iteration`, `Reading`, `Flanks`. The cascade is essentially φ-free — it is an order/interval argument |
| §13 `ReachRule_v1` | interval folding over ℚ; a covering certificate, no arithmetic of units |
| §13 `GapRule_v1` | gap width as an integer inequality; no units |
| §13 `ArithForm_v1` | clearing denominators; `\|A − nks\| < s`, no units |
| §11 `RBand_v1` | `R mod n ∈ [1, n−1]`, i.e. *not* divisible by `n` — a divisibility condition, not a unit one |
| §13 `NoFinitePoints_v1` | a single near-`n` reading blocking a finite set; analytic, no units |
| `Cascade/FourDifferences` growth factors | `(nQ+1)/(nQ−1)` products; no residue structure |

## The consequence worth acting on

§13.11–13.12 cannot be ported to order 5, 7, 9 or 10, and the reason is now a theorem rather than
a grading note: `(ℤ/n)ˣ` has exponent 2 only for `n ∣ 24`. Any attempt to generalise the guard
machinery is wasted outside `{1,2,3,4,6,8,12,24}`.

And the converse: §11's `89` is not an empirical constant. It is `8·11 + 1`, i.e. `s·R ≡ 1`, the
same inverse the coprime-flank rule constructs. §11, §13E and `flankWorks_of_coprime` are three
readings of one relation.
