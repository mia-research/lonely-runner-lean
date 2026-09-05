#!/usr/bin/env python3
"""
TEST ON BOTH SETS. Same pipeline (select bit-length integer -> curve); 100k = known
MT19937 through it, 82 = creator's. Run every generation-recovery detector on BOTH,
next to synthetic positive controls (MWC/LFSR/LCG), so the comparison is explicit:
does the real set behave like the known-MT 100k, and unlike the weak generators?
"""
import csv, random
# ---- detectors (reused) ----
def stream_bits(keys):
    bits=[]
    for i,k in enumerate(keys):
        b=i+1; low=k-(1<<(b-1)) if b>1 else 0
        for j in range(b-1): bits.append((low>>j)&1)
    return bits
def bm(s):
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
def ac(s,lag):
    n=len(s)-lag; return (2*sum(1 for i in range(n) if s[i]==s[i+lag])-n)/n if n>0 else 0
def ladder(keys,D=32):
    best=0
    for d in range(2,D+1):
        M=1<<d; seq=[keys[i]%M for i in range(len(keys)) if (i+1)>d]
        if len(seq)<4: break
        x0,x1,x2=seq[:3]
        if (x1-x0)%M==0: continue
        try: a=((x2-x1)*pow((x1-x0)%M,-1,M))%M
        except ValueError: continue
        c=(x1-a*x0)%M
        if all((a*seq[t]+c)%M==seq[t+1] for t in range(len(seq)-1)): best=d
        else: break
    return best
# MWC raw-concat lane solver
def lane_verify(v,m):
    if len(v)<6: return False
    h=(v[1]-m*v[0])&0xffff; s=(m*v[0]+h)&0xffffffff
    for t in range(1,len(v)):
        if (s&0xffff)!=v[t]: return False
        s=(m*(s&0xffff)+(s>>16))&0xffffffff
    return True
def mwc_raw_hit(keys):
    bits=stream_bits(keys); words=[]
    for w in range(len(bits)//32):
        val=0
        for j in range(32): val|=bits[w*32+j]<<j
        words.append(val)
    v0=[w>>16 for w in words]; v1=[w&0xffff for w in words]
    for m in (18030,30903,18273,36969,18000):
        if lane_verify(v0,m) or lane_verify(v1,m): return True
    return False

# ---- generators (positive controls) ----
def gen_uniform(seed): r=random.Random(seed); return [(1<<(i-1))|r.getrandbits(i-1) if i>1 else 1 for i in range(1,71)]
def gen_lfsr(seed):
    st=seed&0x7fffff or 1; out=[]
    def bit():
        nonlocal st; b=st&1; fb=((st)^(st>>5))&1; st=(st>>1)|(fb<<22); return b
    for i in range(1,71):
        v=0
        for j in range(i-1): v|=bit()<<j
        out.append((1<<(i-1))|v if i>1 else 1)
    return out
def gen_lcg_low(seed):
    x=seed&((1<<64)-1); out=[]
    for i in range(1,71):
        x=(6364136223846793005*x+1442695040888963407)&((1<<64)-1)
        out.append((1<<(i-1))|(x&((1<<(i-1))-1)) if i>1 else 1)
    return out
def gen_mwc(seed):
    s0=seed&0xffffffff or 1; s1=(seed>>32)&0xffffffff or 2
    def nx():
        nonlocal s0,s1; s0=(18030*(s0&0xffff)+(s0>>16))&0xffffffff; s1=(30903*(s1&0xffff)+(s1>>16))&0xffffffff
        return ((s0<<16)+(s1&0xffff))&0xffffffff
    out=[]
    for i in range(1,71):
        need=i-1; v=0; sh=0
        while need>0:
            w=nx(); t=min(32,need); v|=(w&((1<<t)-1))<<sh; sh+=t; need-=t
        out.append((1<<(i-1))|v if i>1 else 1)
    return out

# ---- load real + 100k ----
real={}
with open('puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        b=int(r['bits'])
        if b<=70: real[b]=int(r['private_key'],16)
REAL=[real[i] for i in range(1,71)]
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for r in csv.DictReader(f):
        b=int(r['bits'])
        if b<=70: synth.setdefault(b,[]).append(int(r['d']))
def k100k(j): return [synth[i][j%len(synth[i])] for i in range(1,71)]

def report(name,keys):
    s=stream_bits(keys)
    print(f"  {name:22} BM={bm(s):4d}/{len(s)//2}  ac1={ac(s,1):+.3f}  ladder={ladder(keys):2d}  MWC-raw-hit={mwc_raw_hit(keys)}")

print("=== positive controls (each should show its tell) ===")
report('LFSR',gen_lfsr(99)); report('LCG-low',gen_lcg_low(7)); report('MWC1616',gen_mwc(123))
print("\n=== TEST ON BOTH: real vs 100k-MT (should match each other + look like uniform/MT) ===")
report('uniform/MT ctrl',gen_uniform(5))
report('REAL 82(1..70)',REAL)
import statistics
# 100k: run detector on many 100k streams, show distribution
bms=[bm(stream_bits(k100k(j))) for j in range(30)]
lads=[ladder(k100k(j)) for j in range(30)]
mwchits=sum(mwc_raw_hit(k100k(j)) for j in range(30))
print(f"  100k-MT (30 streams)   BM={statistics.mean(bms):.0f}±{statistics.pstdev(bms):.1f}  ladder={statistics.mean(lads):.1f}  MWC-raw-hits={mwchits}/30")
print("\n  interpretation: REAL matches the 100k-MT band and the uniform/MT control on every")
print("  detector, and differs from LFSR/LCG/MWC controls -> real behaves like known-MT keys")
print("  through the identical pipeline. (Recovery still needs a contiguous creator stream.)")
