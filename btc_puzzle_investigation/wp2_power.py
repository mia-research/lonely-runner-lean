"""WP2 at power (the re-run): can a strong nonlinear classifier predict n (or
n-properties) from the PUBLIC (X,Y)?  Prior WP2 was discarded because its planted
control never fired (underpowered). Here the control MUST fire before any null is
believed. Features = bytes of X,Y (public); a GBM catches nonlinear leaks the
linear probe would miss. attack_valid: uses only public X,Y."""
import csv, numpy as np
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import cross_val_score
from sympy import isprime

def load(cap=50000):
    Xb=[]; nn=[]; bits=[]
    with open('constructed_keys_1to160_100k_exact.csv') as f:
        rows=list(csv.DictReader(f))
    rng=np.random.default_rng(0); rng.shuffle(rows)
    for r in rows:
        if int(r['bits'])<20: continue
        x=int(r['X'],16); y=int(r['Y'],16)
        feat=[(x>>(8*i))&0xff for i in range(32)]+[(y>>(8*i))&0xff for i in range(32)]
        Xb.append(feat); nn.append(int(r['n'])); bits.append(int(r['bits']))
        if len(Xb)>=cap: break
    return np.array(Xb,dtype=np.int32), np.array(nn), np.array(bits)

def acc(Xf, y, folds=4):
    clf=HistGradientBoostingClassifier(max_iter=120, max_depth=6, random_state=0)
    return cross_val_score(clf, Xf, y, cv=folds, scoring='accuracy').mean()

if __name__=="__main__":
    Xf, nvals, bits = load()
    N=len(Xf); print(f"loaded {N} rows (bits>=20), features=64 public X,Y bytes\n")

    targets={
        "n (256-way)": (nvals, 1.0/len(set(nvals))),
        "n_is_prime":  (np.array([isprime(int(v)) for v in nvals]),
                        max(np.mean([isprime(int(v)) for v in nvals]),
                            1-np.mean([isprime(int(v)) for v in nvals]))),
        "n mod 3":     (nvals%3, None),
        "n mod 2":     (nvals%2, None),
    }
    print("=== real accuracy vs baseline vs matched-null (shuffled labels) ===")
    for name,(y,base) in targets.items():
        if base is None:
            vals,cnts=np.unique(y,return_counts=True); base=cnts.max()/len(y)
        a=acc(Xf,y)
        yn=y.copy(); np.random.default_rng(1).shuffle(yn); an=acc(Xf,yn)
        flag="LEAK?" if a>base+0.01 and a>an+0.01 else "null"
        print(f"  {name:14s} real={a:.4f}  baseline={base:.4f}  shuffled-null={an:.4f}  -> {flag}")

    print("\n=== POWER CONTROL: plant a graded leak of n_is_prime, confirm detector fires ===")
    yp=np.array([1 if isprime(int(v)) else 0 for v in nvals])
    base_p=max(yp.mean(),1-yp.mean())
    for s in (0.0,0.1,0.25,0.5,1.0):
        # planted feature: the true label, corrupted with prob (1-s)
        rng=np.random.default_rng(7)
        planted=np.where(rng.random(N)<s, yp, rng.integers(0,2,N))
        Xaug=np.concatenate([Xf, planted.reshape(-1,1)], axis=1)
        a=acc(Xaug, yp)
        print(f"  strength={s:.2f}: acc={a:.4f}  (baseline {base_p:.4f}; rises with s => detector powered)")
