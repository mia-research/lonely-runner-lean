"""
FIX the reference bug in decomp_discovery.py [C]/[D]: n and k are NOT uniform for
a random key (Farey denominator weighting; gcd(k,n)=1 forces k odd-biased). So
"chosen n mod 14 / k mod 2 is non-uniform" is expected for uniform keys too.

Correct test: statistic = chi-square-vs-uniform of the CHOSEN residues; NULL =
the same statistic computed on many synthetic datasets of UNIFORM keys matched to
the chosen bit-lengths. p = P(null >= chosen). This asks the right question: are
the chosen keys MORE structured than uniform keys are, in this residue?

If the [D] candidates survive THIS reference, they are real selection handles for a
sieve. If they collapse, they were the construction's own arithmetic.
"""
import csv, random
from fractions import Fraction
import numpy as np
_r=random.Random(77)

def best_nk(u, nmax=256):
    best=(9e9,1,0)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<best[0]: best=(e,n,k)
    return best[1],best[2]

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['private_key'],16),int(r['n']),int(r['k'])))
Bs=[b for b,_,_,_ in rows]
ch_n=np.array([n for _,_,n,_ in rows]); ch_k=np.array([k for _,_,_,k in rows])
ch_d=[d for _,d,_,_ in rows]
M=len(rows)
rng=np.random.default_rng(77)

def chi_uniform(res, m):
    obs=np.bincount(res%m,minlength=m).astype(float); exp=len(res)/m
    return ((obs-exp)**2/exp).sum()

def synth_dataset():
    """one uniform-key dataset matched to the chosen bit-lengths -> (n,k,d) arrays."""
    ns=np.empty(M,int); ks=np.empty(M,int); ds=[]
    for i,b in enumerate(Bs):
        lo=2**(b-1)
        d=lo+_r.randrange(lo)            # uniform in [2^{b-1}, 2^b)
        u=(d-lo)/lo                       # float u: ~52 bits, ample for n<=256
        n,k=best_nk(u); ns[i]=n; ks[i]=k; ds.append(d)
    return ns,ks,ds

# observed statistics
probes={}
for m in range(2,17): probes[f"n%{m}"]=("n",m)
for m in range(2,17): probes[f"k%{m}"]=("k",m)
for m in range(2,33): probes[f"d%{m}"]=("d",m)
obs={}
for name,(which,m) in probes.items():
    arr=ch_n if which=="n" else ch_k if which=="k" else np.array([x%m for x in ch_d])
    obs[name]=chi_uniform(arr if which!="d" else arr, m) if which!="d" else chi_uniform(np.array([x%m for x in ch_d]),m)

# null ensemble
NB=1500
null={name:[] for name in probes}
print(f"building {NB} bit-length-matched uniform-key reference datasets...")
for _ in range(NB):
    ns,ks,ds=synth_dataset()
    for name,(which,m) in probes.items():
        arr=ns if which=="n" else ks if which=="k" else np.array([x%m for x in ds])
        null[name].append(chi_uniform(arr,m))

print("\nprobe : chosen-chi2 : null-median : p=P(null>=chosen) : Bonferroni")
def report(group, count):
    res=[]
    for name,(which,m) in probes.items():
        if not name.startswith(group): continue
        nd=np.array(null[name]); p=(1+(nd>=obs[name]).sum())/(1+len(nd))
        res.append((p,name,m,nd))
    res.sort()
    p,name,m,nd=res[0]
    bonf=min(1.0,p*count)
    print(f"  [{group}] most-extreme: {name}  chosen={obs[name]:.1f}  null-med={np.median(nd):.1f}"
          f"  p={p:.4f}  Bonf({count})={bonf:.3f}{'  << SURVIVES' if bonf<0.05 else ''}")
report("n%",15); report("k%",15); report("d%",31)

print("\nInterpretation: p here already accounts for the Farey/coprimality structure")
print("(the null datasets share it). SURVIVES = real selection handle for a sieve;")
print("otherwise the earlier [D] hits were the construction's own arithmetic.")
