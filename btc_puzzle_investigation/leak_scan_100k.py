"""High-power leak scan on the 100k dataset (not the 82 real keys).
Does any bit of the PUBLIC (X,Y) or (n,k,D) reveal any bit of the PRIVATE d?
Exact integer counts + z-scores; numpy used for integer bit-matrix speed only
(no float in the decision — z is a ranked diagnostic vs a multiple-testing bound)."""
import csv, math
import numpy as np

DBITS = 40     # low bits of d (uniform within each band) -- the clean secret bits
def load():
    d=[]; X=[]; Y=[]; nn=[]; kk=[]; DD=[]; bits=[]
    with open('constructed_keys_1to160_100k_exact.csv') as f:
        for r in csv.DictReader(f):
            b=int(r['bits'])
            if b < DBITS+2:      # need enough low bits below the MSB
                continue
            d.append(int(r['d']))
            X.append(int(r['X'],16)); Y.append(int(r['Y'],16))
            nn.append(int(r['n_exact'])); kk.append(int(r['k_exact']))
            DD.append(int(r['D_exact'])); bits.append(b)
    return d,X,Y,nn,kk,DD,bits

def bitmat(vals, positions):
    a=np.array(vals, dtype=object)
    cols=[np.array([(int(v)>>p)&1 for v in vals], dtype=np.int32) for p in positions]
    return np.stack(cols, axis=1)   # (N, len(positions))

def scan(name, Dm, Sm, dpos, spos, N):
    # agreement count per (d-bit i, s-bit j) = Dm[:,i]==Sm[:,j]
    agree = Dm.T @ Sm + (1-Dm).T @ (1-Sm)      # (len(dpos), len(spos)), exact ints
    z = (agree.astype(np.float64) - N/2) / math.sqrt(N/4)
    npair = z.size
    thr = math.sqrt(2*math.log(npair))         # expected max|z| under global null
    ai,aj = np.unravel_index(np.argmax(np.abs(z)), z.shape)
    print(f"  {name:14s} pairs={npair:5d}  max|z|={abs(z[ai,aj]):5.2f} at (d bit {dpos[ai]}, {name} bit {spos[aj]})"
          f"   null-max~{thr:.2f}  -> {'SIGNAL' if abs(z[ai,aj])>thr+1.5 else 'noise'}")
    return abs(z[ai,aj]), thr

if __name__=="__main__":
    d,X,Y,nn,kk,DD,bits = load()
    N=len(d)
    print(f"loaded {N} rows (bits>={DBITS+2}); testing low {DBITS} bits of d\n")
    dpos=list(range(DBITS))
    Dm=bitmat(d,dpos)
    xpos=list(range(0,256,1)); ypos=list(range(0,256,1))
    Xm=bitmat(X,xpos); Ym=bitmat(Y,ypos)
    npos=list(range(0,16)); kpos=list(range(0,64)); Dpos=list(range(0,64))
    print("=== does the PUBLIC value leak a low bit of the private d? (100k, exact) ===")
    scan("X", Dm, Xm, dpos, xpos, N)
    scan("Y", Dm, Ym, dpos, ypos, N)
    scan("n", Dm, bitmat(nn,npos), dpos, npos, N)
    scan("k", Dm, bitmat(kk,kpos), dpos, kpos, N)
    scan("D", Dm, bitmat(DD,Dpos), dpos, Dpos, N)
    # control: does d leak its OWN bits (sanity, must be huge) and a random column (must be null)
    print("\n=== controls ===")
    scan("d(self)", Dm, Dm, dpos, dpos, N)
    rnd=bitmat([np.random.randint(1<<40) for _ in range(N)], list(range(40)))
    scan("random", Dm, rnd, dpos, list(range(40)), N)
