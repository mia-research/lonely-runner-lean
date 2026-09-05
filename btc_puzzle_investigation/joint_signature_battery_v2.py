#!/usr/bin/env python3
"""
Joint-signature battery v2 — v1's positive CONTROLS FAILED (LFSR BM~L/2 not ~23; LCG
ladder=0) because (a) the stream builder reversed each key's bits, killing LFSR linearity,
and (b) the LCG control emitted HIGH bits while the ladder tests LOW bits. Fixed here.
RULE: interpret the real vs 100k-MT comparison ONLY if the controls fire.
"""
import csv, random
def stream_from_keys(keys):  # LSB-first, consistent with generators below
    bits=[]
    for i,k in enumerate(keys):
        b=i+1; low=k-(1<<(b-1)) if b>1 else 0
        for j in range(b-1): bits.append((low>>j)&1)
    return bits
def berlekamp_massey(s):
    n=len(s); C=[0]*(n+1); B=[0]*(n+1); C[0]=B[0]=1; L=0; m=1
    for i in range(n):
        d=s[i]
        for j in range(1,L+1): d^=C[j]&s[i-j]
        if d==0: m+=1
        elif 2*L<=i:
            T=C[:]
            for j in range(n-m):
                if j+m<=n: C[j+m]^=B[j]
            L=i+1-L; B=T; m=1
        else:
            for j in range(n-m):
                if j+m<=n: C[j+m]^=B[j]
            m+=1
    return L
def serial_autocorr(s,lag):
    n=len(s)-lag
    if n<=0: return 0.0
    return (2*sum(1 for i in range(n) if s[i]==s[i+lag])-n)/n
def lcg_ladder(keys,Dtest=32):  # low-bit affine recurrence on keys with enough low bits
    best=0
    for d in range(2,Dtest+1):
        M=1<<d
        seq=[keys[i]%M for i in range(len(keys)) if (i+1)>d]  # bitlen i+1 > d
        if len(seq)<4: break
        x0,x1,x2=seq[0],seq[1],seq[2]
        if (x1-x0)%M==0: continue
        try: a=((x2-x1)*pow((x1-x0)%M,-1,M))%M
        except ValueError: continue
        c=(x1-a*x0)%M
        if all((a*seq[t]+c)%M==seq[t+1] for t in range(len(seq)-1)): best=d
        else: break
    return best
# --- generators, all LSB-first low bits (matching stream_from_keys) ---
def gen_uniform(seed):
    r=random.Random(seed); return [(1<<(i-1))|r.getrandbits(i-1) if i>1 else 1 for i in range(1,71)]
def gen_lfsr(seed):
    st=seed&0x7fffff or 1
    def bit():
        nonlocal st
        b=st&1; fb=((st)^(st>>5))&1; st=(st>>1)|(fb<<22); return b
    out=[]
    for i in range(1,71):
        v=0
        for j in range(i-1): v|=bit()<<j   # LSB-first
        out.append((1<<(i-1))|v if i>1 else 1)
    return out
def gen_lcg_low(seed):  # LOW bits of a pow2 LCG (self-contained affine recurrence)
    x=seed&((1<<64)-1); out=[]
    for i in range(1,71):
        x=(6364136223846793005*x+1442695040888963407)&((1<<64)-1)
        out.append((1<<(i-1))|(x&((1<<(i-1))-1)) if i>1 else 1)
    return out
def gen_mwc(seed):
    s0=seed&0xffffffff or 1; s1=(seed>>32)&0xffffffff or 2
    def nx():
        nonlocal s0,s1
        s0=(18030*(s0&0xffff)+(s0>>16))&0xffffffff; s1=(30903*(s1&0xffff)+(s1>>16))&0xffffffff
        return ((s0<<16)+(s1&0xffff))&0xffffffff
    out=[]
    for i in range(1,71):
        need=i-1; v=0; sh=0
        while need>0:
            w=nx(); t=min(32,need); v|=(w&((1<<t)-1))<<sh; sh+=t; need-=t
        out.append((1<<(i-1))|v if i>1 else 1)
    return out
def detect(keys):
    s=stream_from_keys(keys)
    return dict(BM=berlekamp_massey(s),Lhalf=len(s)//2,ac1=serial_autocorr(s,1),
                ac2=serial_autocorr(s,2),ladder=lcg_ladder(keys),slen=len(s))

print("=== CONTROL calibration (each MUST fire on its target or the battery is void) ===")
ctl={'LFSR(BM should be LOW ~23)':gen_lfsr(99),'LCG-low(ladder should be DEEP)':gen_lcg_low(7),
     'MWC(joint tell)':gen_mwc(123),'uniform/MT(all null)':gen_uniform(5)}
fired={}
for name,g in ctl.items():
    d=detect(g); print(f"  {name:32} BM={d['BM']:4d}/{d['Lhalf']}  ac1={d['ac1']:+.3f}  ladder={d['ladder']}")
fL=detect(gen_lfsr(99))['BM']; fLcg=detect(gen_lcg_low(7))['ladder']
lfsr_ok=fL<100; lcg_ok=fLcg>=8
print(f"\n  CONTROL STATUS: LFSR-BM-detector {'FIRES' if lfsr_ok else 'FAILED'} (BM={fL});"
      f"  LCG-ladder-detector {'FIRES' if lcg_ok else 'FAILED'} (depth={fLcg})")

if not (lfsr_ok and lcg_ok):
    print("\n  >>> controls not all firing -> NOT interpreting real keys. Fix first.")
else:
    rk={}
    with open('puzzles_verified.csv') as f:
        for row in csv.DictReader(f):
            b=int(row['bits'])
            if b<=70: rk[b]=int(row['private_key'],16)
    real=[rk[i] for i in range(1,71)]
    synth={}
    with open('constructed_keys_1to160_100k_exact.csv') as f:
        for row in csv.DictReader(f):
            b=int(row['bits'])
            if b<=70: synth.setdefault(b,[]).append(int(row['d']))
    def ss(j): return [synth[i][j%len(synth[i])] for i in range(1,71)]
    dr=detect(real); import statistics
    print(f"\n=== REAL puzzle-1..70 vs 100k-MT distribution (controls validated) ===")
    dist={k:[detect(ss(j))[k] for j in range(60)] for k in ['BM','ac1','ac2','ladder']}
    for k in ['BM','ac1','ac2','ladder']:
        mu=statistics.mean(dist[k]); sd=statistics.pstdev(dist[k]) or 1e-9
        print(f"  {k:7} REAL={dr[k]:+.3f}  100k-MT={mu:+.3f}±{sd:.3f}  z={(dr[k]-mu)/sd:+.2f}{'  OUTLIER' if abs((dr[k]-mu)/sd)>3 else ''}")
    print("  (real inside 100k-MT band on validated detectors = indistinguishable from MT by these;")
    print("   detectors that FIRE = LFSR/LCG-low -> real is not those. MWC/MT-untemper scope noted.)")
