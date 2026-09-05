# Normalization §4.1 — Draft (Qwen output, Step 1b)

## Raw Qwen Output

We now establish the canonical normalization for families with exactly one speed divisible by $p=11$. In this branch, we rescale the unique multiple of 11 to unity, leaving nine speeds coprime to 11. These remaining speeds decompose into a set $F \subset \{1, \dots, 10\}$ of size 8 and a single free parameter $M$, where $M$ is coprime to $11 \cdot \operatorname{lcm}(F)$. We define the family as $E_{F,M} = F \cup \{M\} \cup \{11\}$, with associated norms $|F|=8$, $L_0 = \operatorname{lcm}(F)$, and $L = L_0 M$. The condition $\gcd(M, 11 L_0) = 1$ ensures that the greatest common divisor of all elements in $E_{F,M}$ remains 1. There are exactly $\binom{10}{8} = 45$ such templates determined by the choice of $F$.

## Auditor Checkpoint

Qwen says: Self-contained normalization paragraph defining E_{F,M}, L_0, L, coprimality condition, 45 templates.
Decision: **Modifying** — "rescale to unity" needs clarification. Replacement wording for v3:

"We normalize the exactly-one-divisible branch as follows. Since the problem is invariant under scaling the tuple by a positive integer, we may assume without loss of generality that the unique speed divisible by $11$ is exactly $11$ itself. The remaining $9$ speeds, all coprime to $11$, are partitioned into a fixed set $F \subset \{1,\ldots,10\}$ with $|F|=8$ and a single free parameter $M$, subject to $\gcd(M, 11 L_0) = 1$ where $L_0 = \operatorname{lcm}(F)$. We write $L = L_0 M$. The condition $\gcd(M, 11 L_0)=1$ ensures $\gcd(E_{F,M})=1$. The normalized branch is indexed by the $\binom{10}{8}=45$ choices of $F$."
