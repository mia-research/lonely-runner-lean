# AP-Core Extremality Survey (v1)

**Conjecture (Lemma E):** x_0(E) >= phi(n) = x_0(A_n) for all gcd-1 tuples E.

Uses integer arithmetic: k safe iff L <= (e*k mod N) <= (n-1)*L for all e.

## Per-n Results

| n | phi(n) | max_e | gcd-1 tuples | min x_0 | min==phi(n) | A_n minimizer | violations (x_0<phi) | distinct min-tuples |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 12 | 91 | 2 | YES | YES | 0 | 3 |
| 4 | 2 | 9 | 637 | 2 | YES | YES | 0 | 1 |
| 5 | 4 | 7 | 2303 | 4 | YES | YES | 0 | 3 |
| 6 | 2 | 5 | 3091 | 2 | YES | YES | 0 | 1 |
| 7 | 6 | 4 | 4031 | 6 | YES | NO | 0 | 1 |
| 8 | 4 | 4 | 16255 | 7 | NO | NO | 0 | 1 |

## Global Verdict

- All tuples satisfy x_0 >= phi(n): **YES — Lemma E holds on this grid**
- min x_0 == phi(n) for all n:      **NO**
- A_n is always a minimizer:        **NO**

## Minimizing Tuples

(All tuples achieving the minimum safe count for each n)

| n | phi(n) | min x_0 | sorted tuple | is A_n |
|---:|---:|---:|:---|:---:|
| 3 | 2 | 2 | `1 1` | no |
| 3 | 2 | 2 | `1 2` | **YES** |
| 3 | 2 | 2 | `1 3` | no |
| 4 | 2 | 2 | `1 2 3` | **YES** |
| 5 | 4 | 4 | `1 1 1 1` | no |
| 5 | 4 | 4 | `1 2 3 4` | **YES** |
| 5 | 4 | 4 | `1 3 4 7` | no |
| 6 | 2 | 2 | `1 2 3 4 5` | **YES** |
| 7 | 6 | 6 | `1 1 1 1 1 1` | no |
| 8 | 4 | 7 | `1 1 1 1 1 1 1` | no |

## Interpretation

If violations==0 and min x_0==phi(n) for all n=3..8:

- O_mass = |union D_e|/N is maximized at A_n for all tested n and speeds.
- x_0(A_n) = phi(n) is the global minimum safe count within the tested grid.
- This computationally confirms Lemma E for n=3..8.
- Combined with the analytic proof that x_0(A_n)=phi(n) (Lemma P),
  an analytic generalization of Lemma E would close Lemma 8.1 and
  the rational SINGLE theorem for all n.
