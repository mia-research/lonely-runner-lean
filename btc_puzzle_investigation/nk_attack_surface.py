import numpy as np, pandas as pd
df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str})
Dabs=[abs(int(v)) for v in df.D]; df["Dabs"]=Dabs
bl=np.array([v.bit_length() for v in Dabs])   # bit_length ~ log2|D|+1 ; 0 for D==0
df["bl"]=bl
nzero=(np.array(Dabs)==0)
print(f"keys: {len(df)}  D==0: {nzero.sum()} ({nzero.mean()*100:.2f}%)")
print("\n=== bit_length(|D|) distribution over |D|>0 keys (~log2|D|) ===")
nzbl=bl[~nzero]
for pct in [1,5,25,50,75,95,99]:
    print(f"  {pct:2d}th pctile bitlen|D| = {np.percentile(nzbl,pct):6.1f}")
print("\n=== attack surface: fraction with |D| < 2^B (base-sweep + bounded DLP breaks these) ===")
for B in [0,20,30,40,50,60,70,80,90,100]:
    frac = nzero.mean() if B==0 else np.mean([v < (1<<B) for v in Dabs])
    print(f"  |D| < 2^{B:<3d}: {frac*100:6.2f}%")
print("\n=== by band: median bitlen|D|, %(|D|<2^40), %(|D|<2^60) ===")
for lo in range(1,161,20):
    idx=(df.bits>=lo)&(df.bits<lo+20); sub=df[idx]
    if len(sub)==0: continue
    dv=[abs(int(v)) for v in sub.D]; blv=[x.bit_length() for x in dv if x>0]
    med=np.median(blv) if blv else 0
    f40=np.mean([x<2**40 for x in dv])*100; f60=np.mean([x<2**60 for x in dv])*100
    print(f"  bits {lo:3d}-{lo+19:3d} ({len(sub):5d}): median bitlen|D|={med:5.1f}  |D|<2^40:{f40:5.1f}%  |D|<2^60:{f60:5.1f}%")
cand=df[(df.bits>=120)&(df.Dabs>0)&(df.Dabs<2**28)].sort_values("bits",ascending=False)
print(f"\n=== large-N(>=120) keys with 0<|D|<2^28 (base-sweep + fast BSGS recoverable): {len(cand)} ===")
if len(cand):
    print(cand[["bits","n","k","D","D_terms"]].head(8).to_string(index=False))
    r=cand.iloc[0]; import math
    print(f"\nDEMO TARGET -> bits={r.bits} n={r.n} k={r.k} D={r.D} bitlen|D|={abs(int(r.D)).bit_length()}")
    open("demo_target.txt","w").write(f"{r.bits}|{r.n}|{r.k}|{r.D}|{r.X}|{r.Y}|{r.d}")
print("\nDONE")
