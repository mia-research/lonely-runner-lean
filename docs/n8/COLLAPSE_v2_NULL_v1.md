# Joining the collapse to the block lemma — a null, and a correction to this session's reach figures

2026-09-10. Scripts `experiments/n8/ok_collapse_v2.py`, `ok_collapse_control_v1.py`.
Exact `Fraction`. This document reports a **negative result** and retracts two numbers.

---

## 1. What was tried

`ODD_RUNNER_COLLAPSE_v1` found the near-zero window where the odd runners provably leave an
odd residue free, then tested **one midpoint** per cell cut by the odd speeds. Inside such a
window the `v₂ ≥ 1` runners move, and the block lemma says exactly how, so the natural fix
is to subdivide the window by **all** breakpoints `m/(8e)` — exact and complete, no
sampling. Measured gain, Case-2 sample from `[1..18]`:

| | `a ≥ 4` | all Case 2 |
|---|---|---|
| one midpoint per window | 95% | 93% |
| window subdivided | **100%** | **99%** |

All witnesses verified exactly. On the face of it, `a ≥ 4` closed.

## 2. Two things wrong with it

**(a) A bug in my own check.** The first run reported hundreds of `FALSIFIED` lines. The
criterion returns the base point `t`, but the witness is `t + j/8` for the unblocked `j`;
I verified `t` itself. The mathematics was fine, the verification was not. Fixed.

**(b) The widened version is circular `[RETRACTED]`.** Extending the search to
`t < 1/8` gives **1520/1520**. It is worthless: `t ∈ (0,1/8)` together with the eight shifts
`j/8` covers `(0,1)` *exactly once*, so subdividing that range by all breakpoints and testing
every cell **is** an exhaustive search of the whole circle — i.e. it is `|G| > 0` itself.
Forced, and retracted.

## 3. The control, which fires  `[the decisive test]`

The near-zero window is a genuine restriction — it fails on 22 tuples, so it is not
equivalent to the full problem. But after the eight shifts it searches a set of measure
`4/e₁` (`e₁` = largest odd speed): **mean `0.2997`, median `0.2353`**. A 98% hit rate on 30%
of the circle proves nothing unless the *placement* matters. Same window length `L =
1/(2e₁)`, different offsets, 912 tuples:

| offset | hit rate |
|---|---|
| `0` — the collapse window | 901 (98%) |
| `L` | 908 (99%) |
| `2L` | 903 (99%) |
| `1/16 − L/2` | 886 (97%) |
| `1/8 − L` | 901 (98%) |

> **Every offset performs the same.** The near-zero placement carries **no information**.
> The 98–99% is a property of the window's *length*, not of the collapse mechanism.

## 4. What is retracted, and what stands

**Retracted:** the "`a ≥ 4` reaches 100%" and "Case 2 reaches 99%" figures of §1, and the
1520/1520 of §2b. Neither is evidence for the collapse.

**A correction to `ODD_RUNNER_COLLAPSE_v1` §4.** Its reported "82% converted to a witness"
has the same defect: the conversion step is an exhaustive search over the window, and §3
shows such a search succeeds at that rate wherever the window is placed. **The 82% and 90%
should not be read as evidence for the mechanism.** The document's *structural* claim — that
the odd runners provably collapse on an explicit window (98%) — is unaffected and stands.

**Unaffected by this control**, because they are structural certificates or closed-form
inequalities rather than searches:

- the tiling and block lemma, and the block criterion `a < 2·max(u_O,u_E)` — a positive is a
  structural certificate, not "some `j` happened to be free";
- the cluster criterion `Σ(⌊|W|v⌋+1)/(4v) < |W|` — a closed-form inequality, no search;
- the parity law, the passage law, the `α` closed form and its `O(N/x)` decay, and the exact
  rational values of all height-1 families.

## 5. The lesson, stated as a rule

Any result of the form "search a window and find a witness" must be controlled **against
window size at other offsets** before it counts. Otherwise it measures `|G|` and the
window's measure, not the idea that chose the window. This is the second forced statistic
this session — after the circular `Σα_v < 1` — and both were caught only by asking whether
the number *could* have come out differently.

## 6. Ledger

`[PROVED]` §2a the bug and its fix; §3 the control table.
`[RETRACTED]` §1 reach figures; §2b the widened search; and, per §4, the witness-conversion
percentages in `ODD_RUNNER_COLLAPSE_v1` §4.
`[STANDS]` everything listed at the end of §4.

`n = 8` is **not proved**, and this attempt did not advance it.
