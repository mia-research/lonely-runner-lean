# Is BS worthwhile for witnesses? — the direct answer

Supersedes `WITNESS_COMPLEXITY_v1.md` (retained). v1 gave measurements and no verdict. Here is the
verdict, with the decisive case being the parallel session's own 23-move example.

---

## The answer in one line

**Worthwhile as a tool, not as a theory.** It is strictly the better way to *exhibit* a witness. It
is not a route to Existence, and it does not improve the cascade.

Three questions that were being answered as one:

| question | answer |
|---|---|
| exhibit a witness for a given arrangement? | **yes — strictly better, never worse** |
| prove Existence at order 8? | **no** — `M` is unbounded |
| improve the cascade? | **no** — different procedure, nothing transfers |

---

## 1. Exhibiting a witness: yes, and by a margin

The parallel session's trace for subject `1` of `(1,31,75,97,128,160,176,225)` **verifies exactly** —
23 moves, `D_final = 32/11`, `t* = 11/256`, `R = 165/16`, 7 of 23 colliding setters, `224` setting
4× and `96` setting 3× (`trace_check_v1.py`). Nothing to correct. On that same subject:

```
  cascade    : t = 11/256   denominator 256   after 23 moves   margin exactly 1/8
  multiplier : t = 9/40     denominator  40   scanning M = 1..5  margin 9/40 = 0.225
```

**6.4× simpler, 1.8× the margin, and no 23-step recursion.** Generally (3200 subjects, v1 §2): the
multiplier denominator is strictly lower in 90.0%, equal in 10.0%, **higher in none**.

### 1.1 The margin difference is structural, not luck

The cascade's final move sets `t = (k + 1/8)/d`, which places the setter at circle-distance
**exactly** `1/8`. So it lands on the threshold with zero slack, always. Measured over 4000
subjects (`witness_margin_v1.py`):

```
  cascade witness margin     min 0.1250  median 0.1250  mean 0.1250  max 0.1250
  multiplier witness margin  min 0.1250  median 0.1667  mean 0.1878  max 0.5000

  cascade lands EXACTLY on the threshold : 4000/4000   (1.0000)
  multiplier margin strictly greater     : 2484/4000
```

**A cascade witness is tight by construction and cannot survive any perturbation or rounding.** For
exact rational arithmetic (Lean, `Fraction`) that is harmless. For anything numeric, or for a
witness meant to be checked independently or to remain valid under a small change, it is a
liability — and the multiplier witness has slack for free.

## 2. Proving Existence: no

`M` is unbounded as far as these searches go. A weak hill-climb reached `M = 13`, a harder one
`M = 20`, still climbing with no plateau (v1 §3). The `M ≤ 7` seen on random samples was a sampling
artifact, and the obvious driver — a thin witness margin — is dead: mean margin is flat at ~0.29
across `M = 1..7`, and the AP is tight at the threshold with `M = 1`. So this is not a bounded
finite search, and BS's counting, which is what would certify a bounded one, fails at order 8 in
23.5% of cases (`BS_TRANSFER_v1` §3) with the filtration route worse still at 41.2%
(`FILTER_ASSESSMENT_AND_CROSSCHECK_v1` A.5).

## 3. Improving the cascade: no

The two are different procedures on different objects. The cascade's structural role — Construction
and Localisation, both `[PROVED]` — is untouched by any of this, and nothing here transfers a bound
from one route to the other.

---

## 4. Where this is actually usable

If the project needs **certificates** — a Lean witness for a specific arrangement, a check on a hard
case, a data-availability artifact, a reviewer-checkable instant — search `λ/(8M)` rather than run
the cascade. It is cheaper to state, cheaper to verify, and carries slack. That is a real if modest
payoff, and it is firewall-independent: comparing two instant-producing procedures involves no
covering argument.

It changes nothing about the open problem.

```bash
python3 experiments/n8/trace_check_v1.py      # verifies their 23-step trace, then the comparison
python3 experiments/n8/witness_margin_v1.py   # cascade is tight 4000/4000
```
