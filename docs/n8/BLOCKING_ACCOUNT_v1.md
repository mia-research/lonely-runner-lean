# What blocks the rest, and why

Answering: *the minimum speed blocks 21.94% of candidates — what blocks the other 78.06%?*
The complement is not "safe"; most of it is blocked by something else.

## The accounting

4,219,279 candidates over 8,000 unit-free (rational-frontier) speed sets:

| | share |
|---|---|
| blocked by other speeds, **not** the minimum | 58.22% |
| **clear — a witness** | **18.09%** |
| blocked by the minimum **and** others | 17.93% |
| **blocked by the minimum alone** | **5.76%** |

So of the 78.06% the minimum leaves alone, roughly three quarters are killed by other speeds and
about a fifth survive as witnesses.

**This corrects the cost of losing `unit_never_blocks`.** The relevant figure is not 21.94% but
**5.76%** — the candidates where the minimum is the *sole* blocker. Everywhere else the candidate was
already dead, or survives regardless. A unit speed would rescue 5.76% of candidates, not 22%.

## The mechanism

By `Rescale.gcd_covariant`, blocking depends only on the coprime parts: with `g = gcd(a₀, a)`,
`α = a₀/g`, `β = a/g`. Rate as a function of `β`:

| `β` | 1 | 2 | 3 | 4 | 5 | 6 | ≥20 |
|---|---|---|---|---|---|---|---|
| blocked | **0.00%** | **50.01%** | 33.14% | 25.03% | 21.56% | 18.42% | 24.69% |

- **`β = 1` is exactly `0%`, and that is `self_never_blocks`.** `β = 1` means `a ∣ a₀`; since `a₀` is
  the *minimum* speed this forces `a = a₀`, so `α = 1` and `8 ∤ 1`. A speed never blocks its own
  candidates.
- **`β = 2` is the worst case at exactly `50%`**, double the generic rate, and the reason is the
  inversion structure. Candidates give `8k+1 mod 16 ∈ {1,9}`, so the residues are `{α, 9α} mod 16`
  and blocking needs one of them in `{1,15}`. Working through odd `α`:

  > **at `β = 2`, the minimum blocks iff `α ≡ ±1 (mod 8)`.**

  **Verified exactly:** `α ≡ 1` → 50.00%, `α ≡ 3` → 0.00%, `α ≡ 5` → 0.00%, `α ≡ 7` → 50.00%, over
  265,500 candidates. `{1,7} = {±1}` is the order-2 subgroup of the Klein group `(ℤ/8)*`.
- **`α` matters only at `β = 2`.** Across all other `β`, every class of `α mod 8` blocks at ~24.5%
  (measured: 24.10, 24.37, 24.35, 24.60 for the odd classes; 25.15, 24.93, 25.06, 24.97 for even).
  The inversion structure governs one case, not the general one — worth stating, since the recurrence
  of reflections elsewhere makes it tempting to assume it governs everywhere.
- Rates converge to `≈ 1/4` for large `β`, the generic density.

## A clarification owed

Earlier this reduction was described as "an algebraic identity and can't fail". Stated precisely:

- **The identity cannot fail.** `sᵢ·t = (aᵢ/Q)·t = aᵢ·(t/Q) = aᵢ·τ` is substitution and
  associativity — the same real number on both sides of the same norm. A test of it tests the test
  harness, which is exactly what the 2,248 "mismatches" turned out to be.
- **The reduction around it can fail, and was tested.** That `Q = lcm` of denominators makes each
  `aᵢ` an integer; that `sᵢ ≥ 1` makes `a₁ = Q` minimal; that the candidate ranges correspond; and
  the characterisation **integer readings ⟺ `1` in the reduced speed set**, which is a real claim and
  was verified on 200,000 speed sets with 0 mismatches.

"The reduction can't fail" was too broad. The identity cannot; the bookkeeping can, and is checkable.
