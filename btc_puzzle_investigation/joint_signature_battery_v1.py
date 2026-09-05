#!/usr/bin/env python3
"""
Joint-signature battery on the puzzle-1..70 key STREAM (2415 gen-bits = low (i-1) bits
of key i). Tests JOINT/serial/lattice structure (marginals can't distinguish generators).
Control-first: each detector must FIRE on the generator it targets before we trust a null.
Sources: REAL keys; the 100k synthetic (KNOWN MT19937 = calibration/null); synthetic
LCG / MWC1616 / LFSR (positive controls). Exact integer / GF(2).
"""
import csv, random
# ---------- stream builder ----------
def stream_from_keys(keys):  # keys[i] is the (i+1)-bit key for puzzle i+1
    bits=[]
    for i,k in enumerate(keys):
        b=i+1
        low = k-(1<<(b-1)) if b>1 else 0
        for j in range(b-1): bits.append((low>>j)&1)
    return bits
# ---------- detectors ----------
def berlekamp_massey(s):  # GF(2) linear complexity
    n=len(s); C=[0]*n; B=[0]*n; C[0]=B[0]=1; L=0; m=1; b=1
    for i in range(n):
        d=s[i]
        for j in range(1,L+1): d^=C[j]&s[i-j]
        if d==0: m+=1
        elif 2*L<=i:
            T=C[:];
            for j in range(n-m):
                if j+m<n: C[j+m]^=B[j]
            L=i+1-L; B=T; b=d; m=1
        else:
            for j in range(n-m):
                if j+m<n: C[j+m]^=B[j]
            m+=1
    return L
def serial_autocorr(s,lag):  # normalized autocorrelation at lag (0-centered)
    n=len(s)-lag;
    if n<=0: return 0.0
    a=sum(1 for i in range(n) if s[i]==s[i+lag]); return (2*a-n)/n  # in [-1,1]
def lcg_ladder_depth(keys):  # deepest 2^depth where low bits satisfy a consistent affine recurrence
    # low d bits of consecutive keys: k_{i+1} ≡ a k_i + c (mod 2^d). Solve from first two triples, verify.
    ks=[k for k in keys]
    best=0
    for d in range(1,33):
        M=1<<d; ok=True; a=c=None
        for i in range(len(ks)-1):
            x=ks[i]%M; y=ks[i+1]%M
            if a is None:
                if i+2<len(ks):
                    x2=ks[i+1]%M; y2=ks[i+2]%M
                    if (x2-x)%M==0: ok=False; break
                    try: a=((y2-y)*pow((x2-x)%M,-1,M))%M
                    except ValueError: ok=False; break
                    c=(y-a*x)%M
                continue
            if (a*x+c)%M!=y: ok=False; break
        if ok and a is not None: best=d
        else: break
    return best
# ---------- generators (puzzles 1..70) ----------
def gen_uniform(seed):  # Python MT19937 via getrandbits (same class as the 100k)
    r=random.Random(seed); return [(1<<(i-1))|r.getrandbits(i-1) if i>1 else 1 for i in range(1,71)]
def gen_lcg(seed):
    x=seed; out=[]
    for i in range(1,71):
        need=i-1; v=0
        while need>0:
            x=(6364136223846793005*x+1442695040888963407)&((1<<64)-1)
            t=min(32,need); v=(v<<t)|((x>>(64-t))&((1<<t)-1)); need-=t
        out.append((1<<(i-1))|v if i>1 else 1)
    return out
def gen_mwc(seed):  # V8 pre-2016 MWC1616
    s0=seed&0xffffffff or 1; s1=(seed>>32)&0xffffffff or 2; out=[]
    def nx():
        nonlocal s0,s1
        s0=(18030*(s0&0xffff)+(s0>>16))&0xffffffff
        s1=(30903*(s1&0xffff)+(s1>>16))&0xffffffff
        return ((s0<<16)+(s1&0xffff))&0xffffffff
    for i in range(1,71):
        need=i-1; v=0
        while need>0:
            w=nx(); t=min(32,need); v=(v<<t)|(w&((1<<t)-1)); need-=t
        out.append((1<<(i-1))|v if i>1 else 1)
    return out
def gen_lfsr(seed):  # 23-bit LFSR (positive control for BM)
    st=seed&0x7fffff or 1; out=[]
    def bit():
        nonlocal st
        b=((st>>22)^(st>>17))&1; st=((st<<1)|b)&0x7fffff; return b
    for i in range(1,71):
        v=0
        for _ in range(max(0,i-1)): v=(v<<1)|bit()
        out.append((1<<(i-1))|v if i>1 else 1)
    return out

def detect(keys):
    s=stream_from_keys(keys)
    return dict(BM=berlekamp_massey(s), Lhalf=len(s)//2,
               ac1=serial_autocorr(s,1), ac2=serial_autocorr(s,2),
               ladder=lcg_ladder_depth(keys), streamlen=len(s))

# ---- real ----
rk={}
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        b=int(row['bits'])
        if b<=70: rk[b]=int(row['private_key'],16)
real=[rk[i] for i in range(1,71)]
# ---- 100k MT streams: pick j-th synth key of each bit-length ----
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        b=int(row['bits'])
        if b<=70: synth.setdefault(b,[]).append(int(row['d']))
def synth_stream(j): return [synth[i][j % len(synth[i])] for i in range(1,71)]

print("=== CONTROL calibration: detectors on generators they target ===")
for name,g in [('LFSR(seed99)',gen_lfsr(99)),('LCG(seed7)',gen_lcg(7)),
               ('MWC(seed123)',gen_mwc(123)),('uniform/MT(seed5)',gen_uniform(5))]:
    d=detect(g)
    print(f"  {name:18} BM={d['BM']:4d}/{d['Lhalf']}  ac1={d['ac1']:+.3f} ac2={d['ac2']:+.3f}  LCG-ladder={d['ladder']}")
print("  (LFSR: BM<<L/2; LCG: ladder deep; MWC: check ac/ladder; MT: BM~L/2, ac~0, ladder~0)")

print("\n=== REAL puzzle-1..70 stream vs 100k-MT stream DISTRIBUTION ===")
dr=detect(real)
NS=60
dist={k:[] for k in ['BM','ac1','ac2','ladder']}
for j in range(NS):
    d=detect(synth_stream(j))
    for k in dist: dist[k].append(d[k])
import statistics
print(f"  stream length = {dr['streamlen']} bits (L/2={dr['Lhalf']})")
for k in ['BM','ac1','ac2','ladder']:
    mu=statistics.mean(dist[k]); sd=statistics.pstdev(dist[k]) or 1e-9
    z=(dr[k]-mu)/sd
    print(f"  {k:7}: REAL={dr[k]:+.3f}   100k-MT mean={mu:+.3f} sd={sd:.3f}   z={z:+.2f}{'  <- OUTLIER' if abs(z)>3 else ''}")
print("\n  reading: if REAL is inside the 100k-MT distribution (|z|<3) on all detectors,")
print("  the real stream is indistinguishable from MT19937 by these joint tests.")
print("  NOTE: serial/lattice detectors PASS MT by design -> a null here = 'not a weak")
print("  generator', NOT 'not MT'. MT-state untempering needs >=624 contiguous words (have ~75).")
