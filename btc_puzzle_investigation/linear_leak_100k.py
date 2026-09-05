"""Linear-combination leak probe on 100k: can a linear function of the 256 bits
of X (or Y) predict a bit of the private d that no single bit reveals?
Features (bits) are exact; the linear fit is a monotone statistic whose verdict
is HELD-OUT accuracy (integer count) vs a shuffled-label null. Powered, novel."""
import csv, math
import numpy as np

def load(minbits=42):
    d=[]; X=[]; Y=[]
    with open('constructed_keys_1to160_100k_exact.csv') as f:
        for r in csv.DictReader(f):
            if int(r['bits'])<minbits: continue
            d.append(int(r['d'])); X.append(int(r['X'],16)); Y.append(int(r['Y'],16))
    return d,X,Y

def bits_pm1(vals, nbits, lo=0):
    # +-1 encoded bit matrix, columns = bit positions lo..lo+nbits
    return np.stack([1-2*np.array([(v>>p)&1 for v in vals],dtype=np.float64)
                     for p in range(lo,lo+nbits)],axis=1)

def probe(name, S, dbit_vals, nfeat, seed=0):
    N=S.shape[0]; ntr=N*3//4
    y=(1-2*dbit_vals).astype(np.float64)          # +-1 target
    Xtr,ytr=S[:ntr],y[:ntr]; Xte,yte=S[ntr:],y[ntr:]
    # ridge least-squares (float fit = monotone statistic; verdict is held-out count)
    A=Xtr.T@Xtr + 1e-3*np.eye(Xtr.shape[1]); w=np.linalg.solve(A, Xtr.T@ytr)
    pred=np.sign(Xte@w); acc=int((pred==yte).sum()); n=len(yte)
    # shuffled-label null: refit on permuted y, held-out acc
    rng=np.random.default_rng(seed); yp=ytr.copy(); rng.shuffle(yp)
    wn=np.linalg.solve(A, Xtr.T@yp); accn=int((np.sign(Xte@wn)==yte).sum())
    z=(acc-n/2)/math.sqrt(n/4)
    print(f"  {name:22s} held-out acc={acc}/{n} ({acc/n:.4f})  z={z:+.2f}   "
          f"shuffled-null acc={accn/n:.4f}   {'LEAK' if z>4 else 'noise'}")

if __name__=="__main__":
    d,X,Y=load()
    N=len(d); print(f"loaded {N} rows (bits>=42)\n")
    Xb=bits_pm1(X,256); Yb=bits_pm1(Y,256)
    print("=== linear predictor of a private-d bit from ALL 256 bits of the public coord ===")
    for bit in (0,1,2,5,10,20):
        db=np.array([(v>>bit)&1 for v in d])
        probe(f"X -> d bit {bit}", Xb, db, 256, seed=bit)
    print()
    for bit in (0,1,5):
        db=np.array([(v>>bit)&1 for v in d])
        probe(f"Y -> d bit {bit}", Yb, db, 256, seed=100+bit)
    print()
    print("=== sanity: predict a low bit of d from low bits of d (must be perfect) ===")
    Db=bits_pm1(d,32)
    probe("d[0..31] -> d bit 3", Db, np.array([(v>>3)&1 for v in d]), 32, seed=7)
