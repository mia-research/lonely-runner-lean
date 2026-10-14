# The Lemma 7 exception pattern, explained — and where it already sits in our corpus

2026-09-07. Supersedes `WHY_13_AND_19_v1.md` (which lacked the `k=7` validation
and the corpus synthesis). Artifacts: `experiments/n8/lemma7_criterion_v1.py`,
`experiments/n8/enumerate_bad_covers_v1.py`.

## 1. The mechanism

Rosenfeld's Lemma 7 criterion is a question about **a fixed real interval being
hit or missed by an arithmetic grid**.

A candidate obstruction is a `k`-tuple `T`. Its **lonely set** is
`{x ∈ (0,1/2) : ‖xv‖ ≥ 1/(k+1) for all v ∈ T}` — a finite union of intervals
with rational endpoints, nonempty by LRC for `k`. Lemma 7 evaluates candidate
times on the grid `{j/N : 1 ≤ j ≤ N/2}`, `N = (k+1)p`. `T` covers everything —
i.e. Lemma 7 **fails** — exactly when the grid **misses every lonely interval**.

An interval `[a,b]` is missed iff no integer lies in `[Na, Nb]`, which has length
`N(b−a)`. So each fixed tuple dies once `N(b−a) ≥ 1`.

## 2. `k = 6`: one tuple, one interval, exact

The obstruction is `T₆ = {1, 6, 7, 8, 9, 15}`, which appears among the bad covers
at every failing prime. Its lonely set at bound `1/7` is a **single** interval:

    [15/49, 13/42]        length 1/294

With `N = 7p` the window in `j`-space is `[15p/7, 13p/6]`, length `p/42`:

| `p` | window | integer inside | Lemma 7 |
|---|---|---|---|
| 11 | 23.57 – 23.83 | no | fails |
| **13** | 27.86 – 28.17 | **28** | applies |
| 17 | 36.43 – 36.83 | no | fails |
| **19** | 40.71 – 41.17 | **41** | applies |
| 23 | 49.29 – 49.83 | no | fails |
| 29 | 62.14 – 62.83 | no | fails |
| 31 | 66.43 – 67.17 | **67** | applies |
| 37 | 79.29 – 80.17 | **80** | applies |

The integers 28, 41, 67, 80 are exactly the uncovered times the exhaustive search
reports. **13 and 19 work because `28/91` and `41/133` land inside
`[15/49, 13/42]`; 17, 23, 29 fail because no grid point does.** The exceptions
stop because the window has length `p/42`, so it must contain an integer once
`p ≥ 42`.

Exhaustive search independently confirms `p = 31` and `37` clean (300 s, 909 s).

## 3. `k = 7`: the mechanism predicts the lone exception at 41

Searching at `k = 7, p = 41` returns the obstruction
`T₇ = {1, 4, 12, 13, 14, 16, 20}`. Its lonely set at bound `1/8` is **four**
narrow intervals:

    [17/128, 15/112]  length 1/896
    [17/96,  23/128]  length 1/384
    [41/128, 31/96]   length 1/384
    [41/112, 47/128]  length 1/896

Testing whether the grid `{j/8p}` hits any of them:

| `p` | 31 | 37 | **41** | 43 | 47 | 53 | 59 | 61 |
|---|---|---|---|---|---|---|---|---|
| hits | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ |

At `p = 41` the grid threads between all four windows. This reproduces
Rosenfeld's *"for `k = 7`, it seems that any prime `p` at least 31 other than 41
works"* — **derived, not assumed**. Both of his stated exception patterns now
follow from one mechanism.

## 4. The same object is already in this corpus — twice

### 4.1 The n=11 paper defines exactly this count

`lrc_n11_paper_v4.tex` §"Discrete Formulation", verbatim:

> Let `E = (e₁,…,e₁₀)` … Set `L = lcm(E)`, `N = 11L`. Define the safe-point count
> `x₀(E) = #{ k ∈ {1,…,N−1} : eᵢ k mod N ∈ [L, 10L] ∀ i }`.
> Then `x₀(E) > 0` is equivalent to the Lonely Runner Conjecture for the tuple `E`.

That is Rosenfeld's uncovered-time count with `k+1 = 11` and `p = L`: safe means
`eᵢk mod N ∈ [L, N−L]`, i.e. `‖eᵢk/N‖ ≥ 1/11`. **Identical object, arrived at
independently.**

### 4.2 The same obstruction already stalled the general-`n` programme

`lrc_v11_9_srh_analysis_session_2026_05_28b.md`, "Closing the prime-`n` case",
verbatim:

> Bad-k for `w` at unit `c`: pair `{k₁, k₁ + (n − w⁻¹)}` — 2 elements. So
> `|⋃_w bad_k(w,c)| ≤ 2|W₁| ≤ 2(n−2)` — but this can exceed `n` for `n ≥ 5`.
> … average `|K(c)| ≤ 2(n−2) < n` if `n ≥ 4` — wait, `2(n−2) < n` requires
> `n < 4`, not `≥ 4`. **So averaging fails.**

`Conjecture 5.2-SR-H` (`lrc_v11_9_theorem_5_2_sr_draft_v2.md`) is precisely
"the union of blocked sets is not everything" — verified on 34/34 cases,
**analytically open**. The same shape appears as `Conjecture 5.2-H` in
`lrc_proof_allN_v11_8.md`, and the n=11 lineage carries the same tightness
("8 runners, 8 intervals … exactly tight").

So this is not a new obstruction. **It is the one that already blocked our
general-`n` work, met again in Rosenfeld's setting.**

## 5. The lead — and the asymmetry that limits it

The stalled attempts were **counting** arguments: bound the union of blocked
residues and hope it misses something. They fail because `2(n−2) > n`.

The window/grid view is **geometric**: the lonely set has positive measure, and
the grid has spacing `1/N`. That is a different handle on the same obstruction,
and it is the one that resolves individual tuples exactly, as §2 and §3 show.

**But note the asymmetry, which is why this is a lead and not a transfer.** In
Rosenfeld's setting `p` is a *free parameter* — he chooses which primes to
verify, and may take `p` large to make the grid fine. In the n=11 / general-`n`
setting `N = 11·lcm(E)` is *determined by the tuple*; there is no free parameter
to turn. Whether the geometric reframing survives that loss is exactly the
question, and it is untested.

## 6. Status — what is and is not established

**Established (computationally, exact rational arithmetic):**
- The `k = 6` and `k = 7` exception patterns both follow from the window/grid
  mechanism, with the obstructing tuples exhibited and their lonely sets computed
  exactly.
- The n=11 paper's `x₀(E)` is the same object as Rosenfeld's uncovered-time count.
- The general-`n` programme's Conjecture 5.2-SR-H is the same obstruction, and is
  open there.

**Not established:**
- No bound on lonely-window width is proved anywhere here.
- The reformulation in §1 is a restatement, not a theorem.
- Whether the geometric view helps where `p` is not free (§5) is untested.
- One discrepancy stands: for `k = 4` this implementation finds `p = 13` works,
  where the paper's §7 implies `p > 17`. Unresolved; check against the author's
  repository.

**The target remains:** a *uniform* lower bound on the widest lonely interval
over all admissible `k`-tuples — a quantitative strengthening of LRC ("a lonely
time exists **with room around it**"). Giri–Kravitz's spectrum work
(arXiv:2304.01462**v4**, MPCPS) is the nearest known machinery.
