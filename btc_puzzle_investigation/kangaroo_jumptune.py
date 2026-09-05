"""GAP 3 (clean subset) — isolate the JUMP-SIZE effect on kangaroo cost.
No negation (no fruitless-cycle handling needed); pure two-herd DP kangaroo.
Shows current mean-jump vs the van Oorschot-Wiener optimum ~0.5*sqrt(W)."""
import random, statistics, sys
from puzzle_kangaroo_distributed import add, mul
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def make_jumps(K, mean_target):
    sizes = [1 + (2*mean_target*i)//max(1,K-1) for i in range(K)]
    return sizes, [mul(s) for s in sizes]

def solve(W, K, mean_target, dp_bits, seed):
    rng = random.Random(seed); s = rng.randrange(W); Q = mul(s)
    sizes, jpts = make_jumps(K, max(1,mean_target)); dpm=(1<<dp_bits)-1
    half=W.bit_length()//2; table={}; total=0
    maxj=300*int(W**0.5); wl=6*int(W**0.5)+20
    while total<maxj:
        for herd in ("tame","wild"):
            if herd=="tame": st=rng.randrange(W); X=mul(W+st); val=W+st
            else: st=rng.randrange(1<<half); X=add(Q, mul(st) if st else None); val=st
            for _ in range(wl):
                total+=1; i=X[0]%K
                if (X[0]&dpm)==0:
                    p=table.get(X)
                    if p and p[0]!=herd:
                        tv,wv=(val,p[1]) if herd=="tame" else (p[1],val)
                        if mul((tv-wv)%N)==Q: return total, ((tv-wv)%N)==s
                    elif not p: table[X]=(herd,val)
                X=add(X,jpts[i]); val+=sizes[i]
    return total, None

if __name__=="__main__":
    B=int(sys.argv[1]) if len(sys.argv)>1 else 18
    W=1<<B; K=max(8,B//2+2); dp=B//2-3; sq=int(W**0.5); T=40
    em=(1<<K)//K
    print(f"width 2^{B} sqrtW=2^{B//2} K={K} dp_bits={dp} {T} trials")
    print(f"(engine mean jump = {em/sq:.3f}*sqrtW; optimum ~0.5*sqrtW)\n")
    base=None
    for name,mt in [("current engine",em),("tuned sqrtW/4",sq//4),
                    ("tuned sqrtW/2 (opt)",sq//2),("tuned sqrtW",sq)]:
        js=[j for j,ok in (solve(W,K,mt,dp,9000+t) for t in range(T)) if ok]
        if js:
            m=statistics.median(js); base=base or m
            print(f"  {name:22s} mean={mt/sq:4.2f}xsqrtW  median={int(m):>7,} ={m/sq:5.2f}xsqrtW  vs_current={base/m:4.2f}x  ({len(js)}/{T})")
        else: print(f"  {name:22s} no solve")
