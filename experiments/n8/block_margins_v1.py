from fractions import Fraction as F
# max over s of min_i ||a_i s||, EXACT, for positive integers a_i.
# min_i ||a_i s|| is piecewise linear with slopes +-a_i; local maxima sit where two
# pieces cross with opposite slopes: a_i s + a_j s in Z  (s=p/(a_i+a_j)),
# a_i s - a_j s in Z (s=p/|a_i-a_j|), or a single peak s=p/(2 a_i).
def best_margin(a):
    a=sorted(set(a)); dens=set()
    for i in range(len(a)):
        dens.add(2*a[i])
        for j in range(i+1,len(a)):
            dens.add(a[i]+a[j])
            if a[j]!=a[i]: dens.add(a[j]-a[i])
    cand=set()
    for q in dens:
        if q<=0: continue
        for p in range(0,q+1): cand.add(F(p,q))
    best=F(0); arg=None
    for s in cand:
        if s<0 or s>1: continue
        v=min(min((d*s)%1,1-(d*s)%1) for d in a)
        if v>best: best,arg=v,s
    return best,arg

def show(a,label=""):
    m,s=best_margin(a)
    tag=""
    if m==F(1,8): tag="  <-- EXACTLY 1/8 (tight)"
    elif m<F(1,8): tag="  <-- BELOW 1/8 !!"
    print(f"  {str(a):26s} max min = {str(m):>8} = {float(m):.5f}   at s={s}{tag} {label}")

print("max_s min_i ||a_i s||   (LRC at n=8 needs >= 1/8 = 0.125)\n")
for a in [[1,2,3,4,5,6,7],[1,2,3,4,5,6],[1,2,3,4,5],[1,2,3,4],[1,2,3],
          [2,6,8,9,11,14,15],[2,6,8,9,11,14],[1,3,4,5,6,7,8],[49,205,234,256,286,323,366]]:
    show(a)
print()
print("Block decomposition: rationally independent blocks -> orbit closure is a")
print("product -> lonely iff EVERY block has a clear point; binding = worst block.\n")
b7,_=best_margin([1,2,3,4,5,6,7]); b6,_=best_margin([1,2,3,4,5,6])
print(f"  AP{{1..7}} margin {b7} ; drop to 6 differences -> {b6}")
print(f"  so replacing d7 by an irrational multiple gives min({b6}, 1/2) = {min(b6,F(1,2))}")
print("\nWhat is PROVED at threshold 1/8, by block size:")
print("  <=3 : PROVED (2k<n)   4,5,6 : NOT proved   7 : the conjecture")
