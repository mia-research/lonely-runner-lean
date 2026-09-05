"""
DECISIVE test of the k%2 <- XY flicker: out-of-sample validation.

The in-sample signal (channel p=0.013) picked the best of ~50 XY features, then
we admired that same feature. That is the look-elsewhere effect. The only honest
adjudication: SELECT the best XY feature on a training split, FREEZE it, and
measure its association with k%2 on keys held out of selection.

  - real leak  -> selected feature keeps MI on the held-out keys.
  - artifact   -> held-out MI collapses to the permutation null.

Protocol: many random 55/27 splits. Per split, argmax-MI XY feature on train,
then that feature's MI on test. Compare mean test-MI to a null where k%2 labels
are permuted before the whole select-then-test pipeline (so the null feels the
same selection). Also report a matched X-only and Y-only channel for contrast.
"""
import csv
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['X'],16),int(r['Y'],16),int(r['k'])))
Xs=[x for x,_,_ in rows]; Ys=[y for _,y,_ in rows]
k=np.array([kk for _,_,kk in rows]); M=len(rows)
tgt=(k%2)

_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)
def build(kind):
    F={}
    if kind=="XY":
        for m in _PR:
            F[f"XY%{m}"]=np.array([(x*y)%m for x,y in zip(Xs,Ys)])
            F[f"X+Y%{m}"]=np.array([(x+y)%m for x,y in zip(Xs,Ys)])
        for p in (3,5,7,11,13,17,19,23):
            F[f"XYleg{p}"]=np.array([pow((x*y)%p,(p-1)//2,p) for x,y in zip(Xs,Ys)])
    else:
        V=Xs if kind=="X" else Ys
        for m in _PR: F[f"{kind}%{m}"]=np.array([v%m for v in V])
        for p in (3,5,7,11,13,17,19,23): F[f"{kind}leg{p}"]=np.array([pow(v%p,(p-1)//2,p) for v in V])
    return F

def mi(f,t):
    if len(f)==0: return 0.0
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    s=j.sum()
    if s==0: return 0.0
    j/=s;pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())

def oos_mean(F,t,rng,nsplit=400):
    tr=[]
    for _ in range(nsplit):
        perm=rng.permutation(M); a=perm[:55]; b=perm[55:]
        best=-1;arg=None
        for name,col in F.items():
            v=mi(col[a],t[a])
            if v>best: best=v;arg=name
        tr.append(mi(F[arg][b],t[b]))     # held-out MI of the train-selected feature
    return float(np.mean(tr))

rng=np.random.default_rng(7)
for kind in ("XY","X","Y"):
    F=build(kind)
    obs=oos_mean(F,tgt,rng)
    null=[oos_mean(F,rng.permutation(tgt),rng,nsplit=120) for _ in range(40)]
    null=np.array(null); p=(1+(null>=obs).sum())/(1+len(null))
    print(f"channel {kind:>2}: held-out mean MI={obs:.4f}  null mean={null.mean():.4f}"
          f"  (null 95pct={np.quantile(null,0.95):.4f})  p={p:.3f}")

print("\nheld-out MI at/below the null => in-sample k%2<-XY signal was look-elsewhere,")
print("not a real public->k hint. Above the null 95th pct => survives, keep it.")
