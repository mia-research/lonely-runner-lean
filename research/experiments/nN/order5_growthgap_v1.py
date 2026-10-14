"""Is `move_growth` alone enough?  No -- it overshoots 4 on the extremal word.

move_growth: a move set at lap Q multiplies the instant by less than (5Q+1)/(5Q-1).
R = 5*t_final and t_0 = 1/5, so R < prod over moves of (5Q+1)/(5Q-1).
"""
from fractions import Fraction as F
def f(Q): return F(5*Q+1, 5*Q-1)
words = {
 "extremal (R=31/9)": [(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)],
 "diff-setter best (R=27/8)": [(1,1),(2,1),(3,1)],
 "Q1=1,Qf=2 (R=11/4)": [(1,1),(2,1),(3,1),(1,2)],
}
for name, w in words.items():
    p = F(1)
    for _, Q in w: p *= f(Q)
    print(f"{name:<28} moves {len(w):>2}  growth bound {float(p):.4f}  {'EXCEEDS 4' if p >= 4 else 'below 4'}")
print()
print("So the product bound is not tight enough on its own: the extremal word's true R is")
print("31/9 = 3.4444 while the growth product allows 4.107.  The realisability constraints")
print("(each setter in the way at the previous instant) supply the missing factor.")
