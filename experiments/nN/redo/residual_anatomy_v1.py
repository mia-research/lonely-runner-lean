# One residual set: run the cascade from 1/(8 d_min) (exact), then write the landing (b,k) in grid-and-deviation form.
import sys, itertools
from fractions import Fraction as F
sys.path.insert(0,'..')
src=open('../eight_residual_count_v1.py').read().split("t0 = time.time()")[0]
exec(src.replace("N = int(sys.argv[1]) if len(sys.argv) > 1 else 30","N=30"))
def residual(S):
    if not any(d % 2 for d in S): return False
    if not all(any(d % q == 0 for d in S) for q in (5,6,7,8)): return False
    if not max(S) > 7*min(S): return False
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return False
    if any(free_flank8(S,e) for e in S if e % 8 == 0): return False
    if shifted(S): return False
    srt=sorted(S)
    if srt[-1] > 7*srt[-2]: return False
    return not first_lap(S) and not minus_seven(S)
def cd(x): x=x%1; return min(x,1-x)
def cascade(S):
    t=F(1,8*min(S)); path=[t]
    while True:
        bl=[d for d in S if cd(d*t)<F(1,8)]
        if not bl: return path
        nxt=[]
        for d in bl:
            k=round(d*t); nxt.append((F(8*k+1,8*d),d,k))
        t,_,_=max(nxt); path.append(t)
def allcerts(S):
    return [(e,j) for e in S for j in range(e) if all(e<= (d*(8*j+1))%(8*e) <=7*e for d in S)]
if __name__=="__main__":
    N=int(sys.argv[1]); out=[]
    for S in itertools.combinations(range(1,N+1),7):
        if residual(S): out.append(S)
    print("residual sets, 7-subsets of [1,%d]:"%N,len(out)); print(out[:12])
