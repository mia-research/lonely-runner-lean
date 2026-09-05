#!/usr/bin/env python3
"""
MWC1616 FLOAT-recipe solver: models key = floor(Math.random()*2^(N-1)) assembled from the
TOP bits of consecutive MWC outputs, with the output boundary RESET at each key (partial
outputs discarded between keys) -- the difference from the raw-concat solver.
out = (s0<<16)+(s1&0xffff): top 16 bits of out = s0's low 16 = recoverable lane-0 data.
Extract the s0-low-16 sequence (top 16 of each 32-bit group, per-key reset), recover the
s0 lane, verify. Control-first.
"""
import csv, random
def mwc_gen(m0,m1,s0,s1):
    def rnd():
        nonlocal s0,s1
        s0=(m0*(s0&0xffff)+(s0>>16))&0xffffffff
        s1=(m1*(s1&0xffff)+(s1>>16))&0xffffffff
        return ((s0<<16)+(s1&0xffff))&0xffffffff
    return rnd
def gen_float_keys(m0,m1,seed):
    rnd=mwc_gen(m0,m1,seed&0xffffffff or 1,(seed>>32)&0xffffffff or 2)
    keys=[]
    for i in range(1,71):
        N=i-1
        if N==0: keys.append(1); continue
        v=0; got=0
        while got<N:
            out=rnd(); take=min(32,N-got); v=(v<<take)|(out>>(32-take)); got+=take
        keys.append((1<<(i-1))|v)
    return keys
def s0lo_seq(keys, msb_top=True):
    """per-key: low N bits sliced into 32-bit groups (MSB-first); each group's top 16 = s0_lo."""
    seq=[]
    for i,k in enumerate(keys):
        N=i  # bit-length-1 = i (since puzzle i+1 has i low bits); index i -> puzzle i+1
        if N<16: continue
        low=k-(1<<N) if N>0 else 0
        bits=[(low>>(N-1-j))&1 for j in range(N)] if msb_top else [(low>>j)&1 for j in range(N)]
        for g in range(0,N,32):
            ch=bits[g:g+32]
            if len(ch)<16: break
            t16=0
            for j in range(16): t16=(t16<<1)|ch[j]
            seq.append(t16)
    return seq
def lane_verify(v,m):
    if len(v)<6: return False
    h0=(v[1]-m*v[0])&0xffff; s=(m*v[0]+h0)&0xffffffff
    for t in range(1,len(v)):
        if (s&0xffff)!=v[t]: return False
        s=(m*(s&0xffff)+(s>>16))&0xffffffff
    return True
MULS=[(18030,30903),(18273,18273),(36969,18000),(18000,30903),(30903,18030)]

print("=== CONTROL: MWC float-recipe keys, recover s0 lane ===")
ck=gen_float_keys(18030,30903,0xABCD1234ABCD)
seq=s0lo_seq(ck,msb_top=True)
print(f"  s0-lo sequence length {len(seq)}; lane recover(18030) = {lane_verify(seq,18030)}  (want True)")
rng=random.Random(2); rk=[(1<<(i-1))|rng.getrandbits(i-1) if i>1 else 1 for i in range(1,71)]
print(f"  random-keys negative control: {lane_verify(s0lo_seq(rk),18030)}  (want False)")

print("\n=== TEST: real puzzle 1..70, float recipe ===")
real={}
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        b=int(row['bits'])
        if b<=70: real[b]=int(row['private_key'],16)
keys=[real[i] for i in range(1,71)]
hit=False
for msb in (True,False):
    seq=s0lo_seq(keys,msb_top=msb)
    for m0,m1 in MULS:
        if lane_verify(seq,m0): print(f"  HIT: msb_top={msb} m0={m0}"); hit=True
        if lane_verify(seq,m1): print(f"  HIT: msb_top={msb} m1={m1}"); hit=True
if not hit:
    print("  no multiplier/bit-order makes the real s0-lane sequence satisfy the MWC recurrence")
    print("  (scope: float top-bits recipe, per-key reset, 5 V8/classic mult pairs, 2 bit-orders).")
