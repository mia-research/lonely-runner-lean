"""
Shared library for the (X,Y)->n/k leak hunt on constructed_keys_1to160_100k.csv.
GUARDRAIL: features are functions of X, Y, and the curve constants ONLY. Never
build a feature from n, k, d, or bits -- that is circular. The goal metric is
MUTUAL INFORMATION IN BITS: MI(feature; target) = expected bits of the target
learned = search-space reduction. A leak of even ~0.05-0.1 bits about k is a win.
"""
import csv, math
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
# secp256k1 GLV endomorphism: (x,y) -> (BETA*x, y) equals LAMBDA*(x,y)
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= (BETA*BETA)%P
DATA = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/constructed_keys_1to160_100k.csv"

def load(min_bits=1):
    """Returns dict with bits,n,k,D as np arrays and X,Y as python-int lists."""
    bits=[];X=[];Y=[];n=[];k=[];D=[]
    with open(DATA) as f:
        for r in csv.DictReader(f):
            b=int(r['bits'])
            if b<min_bits: continue
            bits.append(b); X.append(int(r['X'],16)); Y.append(int(r['Y'],16))
            n.append(int(r['n'])); k.append(int(r['k'])); D.append(int(r['D']))
    return {"bits":np.array(bits),"X":X,"Y":Y,"n":np.array(n),"k":np.array(k),"D":np.array(D),"N":len(X)}

def mi_bits(f, t):
    """MI in bits between integer arrays f,t (small alphabets)."""
    f=np.asarray(f); t=np.asarray(t)
    A=int(f.max())+1; B=int(t.max())+1
    j=np.zeros((A,B)); np.add.at(j,(f,t),1.0)
    Nt=j.sum(); pj=j/Nt
    pa=pj.sum(1); pb=pj.sum(0); outer=np.outer(pa,pb)
    nz=pj>0
    return float((pj[nz]*np.log2(pj[nz]/outer[nz])).sum()), A, B

def gtest_p(mi, N, A, B):
    """analytic p that MI>0: 2 N ln2 MI ~ chi^2((A-1)(B-1)) under independence."""
    df=(A-1)*(B-1); x=2*N*math.log(2)*mi
    if x<=0 or df<=0: return 1.0
    t=(x/df)**(1/3); mu=1-2/(9*df); s=math.sqrt(2/(9*df)); z=(t-mu)/s
    return 0.5*math.erfc(z/math.sqrt(2))

def adj_mi(f, t, iters=8, rng=None):
    """bias-adjusted MI = raw - mean(shuffle MI). Positive => real dependence."""
    rng=rng or np.random.default_rng(0)
    raw,A,B=mi_bits(f,t)
    nb=np.mean([mi_bits(f, rng.permutation(t))[0] for _ in range(iters)])
    return raw-nb, raw, nb, A, B

# ---------- feature transforms of (X,Y) (curve/field only) ----------
def col_mod(vals, m):      return np.array([int(v)%m for v in vals])
def col_legendre(vals, p): return np.array([pow(int(v)%p,(p-1)//2,p) for v in vals])  # 0,1,p-1
def col_bit(vals, b):      return np.array([(int(v)>>b)&1 for v in vals])
def col_hamming(vals):     return np.array([bin(int(v)).count('1') for v in vals])
def tf_glv(X):             return [ (BETA*int(x))%P for x in X ]       # endomorphism image
def tf_glv2(X):            return [ (BETA2*int(x))%P for x in X ]
def tf_inv(vals):          return [ pow(int(v),P-2,P) for v in vals ]  # field inverse
def tf_prod(X,Y):          return [ (int(x)*int(y))%P for x,y in zip(X,Y) ]
def tf_sum(X,Y):           return [ (int(x)+int(y))%P for x,y in zip(X,Y) ]
def tf_diff(X,Y):          return [ (int(x)-int(y))%P for x,y in zip(X,Y) ]
def tf_slope(X,Y):         return [ (int(y)*pow(int(x),P-2,P))%P for x,y in zip(X,Y) ]  # Y/X

SMALL_MODS = [2,3,4,5,7,8,9,11,13,16,17,19,23,29,31,37,41,43,47,53,59,61,64,127,128,251,255,256]
SMALL_PRIMES=[3,5,7,11,13,17,19,23,29,31,37,41,43,47]

def build_target_set(d):
    """Standard n/k targets (small-alphabet). NOT features -- these are what we predict."""
    n=d["n"]; k=d["k"]; T={}
    for m in [2,3,4,5,6,7,8,9,11,13,16]:
        T[f"n%{m}"]=n%m; T[f"k%{m}"]=k%m
    for b in range(0,8): T[f"nbit{b}"]=(n>>b)&1; T[f"kbit{b}"]=(k>>b)&1
    # k/n position bucketed (16 bins) and n bucketed
    T["kn_bucket16"]=np.clip((k/n*16).astype(int),0,15)
    T["n_bucket16"]=np.clip((n/256*16).astype(int),0,15)
    return T

def sweep(features, targets, N, top=25, label=""):
    """features,targets: dict name->int array. Print top MI(feature;target) rows."""
    res=[]
    for tn,t in targets.items():
        for fn,f in features.items():
            mi,A,B=mi_bits(f,t); p=gtest_p(mi,N,A,B)
            res.append((mi,p,fn,tn,A,B))
    res.sort(reverse=True)
    print(f"\n=== {label}: top {top} MI(feature; target) of {len(res)} pairs (N={N}) ===")
    print(f"{'MI(bits)':>9} {'Gtest-p':>9} {'Bonf-p':>9}  feature -> target")
    M=len(res)
    for mi,p,fn,tn,A,B in res[:top]:
        print(f"{mi:9.5f} {p:9.2e} {min(1,p*M):9.2e}  {fn} -> {tn}")
    return res
