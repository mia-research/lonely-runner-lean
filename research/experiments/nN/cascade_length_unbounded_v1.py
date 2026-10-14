"""At n=5 with four disparities the cascade length is UNBOUNDED.

four_diffs_stop_ge_six is a MOVE-COUNT theorem: the 7th iterate is fixed, for every n >= 6.
The same shape works at n=3 (1 move) and n=4 (3 moves).  It cannot exist at n=5: the maximisers
found by exhaustive sweep form the family (1, 5k-2, 5k, 10k-2), whose cascade length grows with k.
Exact rational arithmetic; the cascade still TERMINATES in every case (LRC(5) holds) -- what is
unbounded is the number of moves it takes.
"""
from fractions import Fraction as F
import math
def circ(x):
    fl=x-(x.numerator//x.denominator); return min(fl,1-fl)
def cascade(ds,n,cap=4000):
    m=min(ds); t=F(1,n*m); word=[]
    for _ in range(cap):
        inway=[d for d in ds if circ(F(d)*t)<F(1,n)]
        if not inway: return word,t,True
        best=None; s=None
        for d in inway:
            k=math.ceil(F(d)*t-F(1,n)); op=(F(k)+F(1,n))/F(d)
            while op<t: k+=1; op=(F(k)+F(1,n))/F(d)
            if best is None or op>best: best,s=op,d
        t=best; word.append(s)
    return word,t,False
print(f"{'k':>4} {'ds = (1, 5k-2, 5k, 10k-2)':>28} {'moves':>6} {'terminates':>11} {'R = 5*d_min*t':>14}")
for k in list(range(3,21))+[30,40,60,80,100]:
    ds=(1,5*k-2,5*k,10*k-2)
    w,t,done=cascade(ds,5)
    print(f"{k:>4} {str(ds):>28} {len(w):>6} {str(done):>11} {float(t*5*min(ds)):>14.4f}")
print()
print("A move-count theorem at n=5 would need a fixed N with the N-th iterate always fixed.")
print("This family exceeds every such N.  The correct shape at n=5 is a CAP")
print("(Flanks.exists_fixed_of_capped), not a move count.")
