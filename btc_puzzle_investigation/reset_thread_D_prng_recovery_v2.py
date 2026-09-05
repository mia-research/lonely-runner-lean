#!/usr/bin/env python3
"""
Reset thread D, part 2:
  D2 - V8-2015 Math.random == MWC1616 naive-recipe TELL. The common JS idiom
       Math.floor(Math.random() * 2^(N-1)) draws ONE 32-bit-resolution double, so
       for N-1 > 32 the low (N-1-32) bits are float-quantized -> (d-A) would be
       divisible by 2^(N-33). Direct, decisive test of that recipe.
  D3 - general FULL-OUTPUT LCG recovery (unknown a,c,m) by the difference-gcd
       method, scanning word width w and endianness over the contiguous stream.
       Covers "hidden large-modulus LCG" without a seed brute. Control included.

Exact integers only.
"""
from math import gcd
from reset_common import load_solved, contiguous_run

solved = load_solved()
RUN = contiguous_run(solved, 1)
D   = {N: solved[N]["d"] for N in RUN}
def low(dN, N): return dN & ((1 << (N-1)) - 1)
def v2(m):
    m=abs(m); c=0
    if m==0: return 0
    while m%2==0: m//=2; c+=1
    return c

# ---------------- D2: MWC1616 naive single-call quantization tell ----------------
print("=== D2: V8-2015 Math.floor(Math.random()*2^(N-1)) quantization tell ===")
print("  if used, (d-A) is divisible by 2^(N-33) for N>33.  v2(d-A) vs (N-33):")
tell_hits = 0; tested = 0
for N in RUN:
    if N-1 <= 33: continue
    tested += 1
    dm = D[N] - (1 << (N-1))
    need = (N-1) - 32
    got = v2(dm)
    if got >= need: tell_hits += 1
print(f"  keys with N-1>33 tested: {tested};  showing the 32-bit quantization tell: {tell_hits}")
print(f"  (a real single-call V8 recipe would give {tested}/{tested}; chance gives ~0)\n")

# ---------------- D3: general full-output LCG recovery ----------------
def split_words(bits, w, msb=True):
    words=[]
    for i in range(0, len(bits)-w+1, w):
        chunk = bits[i:i+w]
        val=0
        it = chunk if msb else reversed(chunk)
        for b in it: val=(val<<1)|b
        words.append(val)
    return words

def stream_bits(msb_first=True):
    out=[]
    for N in RUN:
        w=N-1
        if w==0: continue
        v=low(D[N],N)
        rng=range(w-1,-1,-1) if msb_first else range(0,w)
        for j in rng: out.append((v>>j)&1)
    return out

def recover_lcg_full(X):
    """Given >=6 consecutive full LCG outputs X, recover (m,a,c) or None.
    m | (t_{i+2} t_i - t_{i+1}^2), t_i = X_{i+1}-X_i."""
    if len(X) < 6: return None
    t=[X[i+1]-X[i] for i in range(len(X)-1)]
    cand=0
    for i in range(len(t)-2):
        cand=gcd(cand, abs(t[i+2]*t[i]-t[i+1]*t[i+1]))
    if cand<=2: return None
    # strip tiny factors that are coincidental; require m plausibly large
    m=cand
    # a = (X2-X1)/(X1-X0) mod m
    try:
        inv=pow((X[1]-X[0])%m, -1, m)
    except ValueError:
        return None
    a=((X[2]-X[1])*inv)%m
    c=(X[1]-a*X[0])%m
    # verify forward
    ok=all((a*X[i]+c)%m==X[i+1]%m for i in range(len(X)-1))
    return (m,a,c) if ok else None

print("=== D3: full-output LCG recovery over word-width scan ===")
# positive control: build a stream from a known LCG, must recover
mC,aC,cC=(2**48, 25214903917, 11)
xs=[123456789]
for _ in range(40): xs.append((aC*xs[-1]+cC)%mC)
rec=recover_lcg_full(xs[3:20])
print(f"  [CTRL] planted LCG m=2^48: recovered {rec} -> {'FIRES' if rec and rec[0]==mC else 'FAIL'}")

found=[]
for msb in (True,False):
    bits=stream_bits(msb)
    for w in (8,15,16,24,31,32,48,64):
        words=split_words(bits,w,msb)
        if len(words)<8: continue
        # try a few starting offsets
        for off in range(0, min(4, len(words)-7)):
            rec=recover_lcg_full(words[off:off+16])
            if rec and rec[0]>2**8:
                found.append((w,'MSB' if msb else 'LSB',off,rec))
print(f"  real stream: LCG recoveries with m>256: {len(found)}")
for w,e,off,rec in found[:10]:
    print(f"    w={w} {e} off={off}: m={rec[0]} a={rec[1]} c={rec[2]}")
if not found:
    print("    (none) -- scoped to full-output LCG under fixed-width word segmentation;")
    print("    a TRUNCATED LCG (only high bits per call exposed) needs a lattice (FHKLS),")
    print("    which remains open (research-grade per the doc).")
