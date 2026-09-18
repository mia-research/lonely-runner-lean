"""Item 1 of the proposed route -- "lambda_j < (8M+1)/(8M-1) contracts towards 1+, so the scale
cannot dilate indefinitely" -- is true in its premise and FALSE in its conclusion.

R = prod lambda_j.  A bound ABOVE on each factor, with the factors tending to 1, does not bound the
product.  Demonstrate: if the lap index grows linearly (which is what the deep cascades DO -- mean M
rises 1.73 -> 3.58 across the 23-move case), then lambda_j ~ 1 + c/(8j) and the product DIVERGES.
All arithmetic exact where it matters."""
from math import prod, log
print("  lambda_j = (8M_j + 1)/(8M_j + delta_j),  |delta_j| < 1,  so lambda_j < (8M+1)/(8M-1) -> 1.")
print("  The question is whether prod lambda_j is bounded.  Take the worst case delta = -1:\n")
print(f"  {'M grows as':>14} {'K=50':>10} {'K=200':>10} {'K=1000':>11} {'K=10000':>11}  behaviour")
def prod_lam(Mof, K):
    return prod((8*Mof(j)+1)/(8*Mof(j)-1) for j in range(1, K+1))
for name, Mof in (("M = j",      lambda j: j),
                  ("M = 1+j/4",  lambda j: 1+j/4),
                  ("M = sqrt(j)",lambda j: max(1.0, j**0.5)),
                  ("M = 1 (max)",lambda j: 1)):
    vals=[prod_lam(Mof,K) for K in (50,200,1000,10000)]
    beh = "DIVERGES" if vals[-1] > 10*vals[0] else "grows slowly"
    print(f"  {name:>14} {vals[0]:>10.3f} {vals[1]:>10.3f} {vals[2]:>11.3f} {vals[3]:>11.3f}  {beh}")
print()
print("  With M = j the factors are 9/7, 17/15, 25/23, ... each -> 1, and the product still grows")
print("  without bound: sum log((8j+1)/(8j-1)) ~ sum 1/(4j) ~ (1/4) log K.")
print("  So R ~ K^(1/4) -> infinity.  lambda -> 1 is CONSISTENT WITH R UNBOUNDED.")
print()
print("  This is why MANUSCRIPT_v11 sec 6.14 states the bound as one-sided and says so explicitly:")
print("  'There is no matching upper bound, because lambda -> 1 as M -> infinity.  Steps can be")
print("   arbitrarily unproductive, and no ceiling on the move count follows from the step law.'")
