#!/usr/bin/env python3
"""
MWC1616 (V8 pre-2016 Math.random) multi-draw LANE SOLVER.
Each output out = ((s0<<16)+(s1&0xffff)) reveals the low 16 bits of each 32-bit lane;
the lane recurrence s' = m*(s&0xffff)+(s>>16) lets the hidden high 16 bits be RECOVERED
from 2 consecutive outputs. So a stream of MWC outputs is verifiable/recoverable.
Control-first: generate a real MWC stream, recover it. THEN test the puzzle 1..70 stream
under several bit-assembly recipes + known V8 multiplier pairs.
"""
import csv
def mwc_stream(m0,m1,s0,s1,n):
    out=[]
    for _ in range(n):
        s0=(m0*(s0&0xffff)+(s0>>16))&0xffffffff
        s1=(m1*(s1&0xffff)+(s1>>16))&0xffffffff
        out.append(((s0<<16)+(s1&0xffff))&0xffffffff)
    return out
def lane_verify(v,m,need=3):
    # v[t] = low16 of lane after step t. Recover h[0]=(v[1]-m v[0]) mod 2^16, s=m v[0]+h[0]=s[1].
    if len(v)<need+2: return False
    h0=(v[1]-m*v[0])&0xffff
    s=(m*v[0]+h0)&0xffffffff          # lane state s[1]
    for t in range(1,len(v)):
        if (s&0xffff)!=v[t]: return False
        s=(m*(s&0xffff)+(s>>16))&0xffffffff
    return True
def mwc_recover_verify(words,m0,m1):
    if len(words)<5: return False
    v0=[w>>16 for w in words]; v1=[w&0xffff for w in words]
    return lane_verify(v0,m0) and lane_verify(v1,m1)

# V8 / classic MWC multiplier pairs to try
MULS=[(18030,30903),(18273,18273),(36969,18000),(18000,30903),(30903,18030)]

print("=== CONTROL: generate MWC1616 stream, recover it ===")
for m0,m1 in MULS[:1]:
    w=mwc_stream(m0,m1,0xABCD1234,0x9876FEDC,40)
    print(f"  multipliers ({m0},{m1}): recover+verify = {mwc_recover_verify(w,m0,m1)}  (want True)")
    # negative control: random words
    import random; rr=random.Random(1); rw=[rr.getrandbits(32) for _ in range(40)]
    print(f"  random-words negative control: {mwc_recover_verify(rw,m0,m1)}  (want False)")

# ---- build the puzzle 1..70 stream and slice into 32-bit words under recipes ----
rk={}
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        b=int(row['bits'])
        if b<=70: rk[b]=int(row['private_key'],16)
keys=[rk[i] for i in range(1,71)]
def stream_bits(order='lsb'):
    bits=[]
    for i,k in enumerate(keys):
        b=i+1; low=k-(1<<(b-1)) if b>1 else 0
        rng=range(b-1) if order=='lsb' else range(b-2,-1,-1)
        for j in rng: bits.append((low>>j)&1)
    return bits
def bits_to_words(bits,wordorder='lsb'):
    words=[]
    for w in range(len(bits)//32):
        chunk=bits[w*32:(w+1)*32]; val=0
        for j,bt in enumerate(chunk):
            val |= bt << (j if wordorder=='lsb' else 31-j)
        words.append(val)
    return words

print("\n=== TEST: puzzle 1..70 stream vs MWC (recipes x multiplier pairs) ===")
hit=False
for so in ['lsb','msb']:
    bits=stream_bits(so)
    for wo in ['lsb','msb']:
        words=bits_to_words(bits,wo)
        for m0,m1 in MULS:
            # slide the phase (word alignment) a few bits
            for off in range(0,32,8):
                w2=bits_to_words(bits[off:],wo)
                if len(w2)>=6 and mwc_recover_verify(w2,m0,m1):
                    print(f"  HIT: streamorder={so} wordorder={wo} mult=({m0},{m1}) offset={off}")
                    hit=True
if not hit:
    print("  no recipe/multiplier makes the real stream satisfy the MWC lane recurrence")
    print("  (scope: these recipes + these 5 V8/classic multiplier pairs, index-order stream).")

# also: per-key recipe (each key = one MWC output for small keys) quick check
print("\n=== per-key recipe check (keys 20..51 as single 32-bit-ish outputs) ===")
seg=[keys[i] & 0xffffffff for i in range(19,51)]  # low 32 bits of puzzles 20..51
per=False
for m0,m1 in MULS:
    if mwc_recover_verify(seg,m0,m1): print(f"  HIT per-key mult=({m0},{m1})"); per=True
if not per: print("  no per-key MWC match on puzzles 20..51 low-32-bits.")
