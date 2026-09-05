#!/usr/bin/env python3
"""
MWC float-recipe solver v2 — v1 control FAILED because partial outputs between keys make the
visible lane sequence NON-consecutive (gaps). Fix: reconstruct each output's INDEX in the MWC
stream from the (deterministic) per-key output counts, extract s0_lo only where >=16 bits are
visible, seed recovery from a genuinely CONSECUTIVE index pair, then propagate step-by-step
(skipping gaps) and check at every known index. Control-first.
"""
import csv, random
def mwc_gen(m0,m1,s0,s1):
    def rnd():
        nonlocal s0,s1
        s0=(m0*(s0&0xffff)+(s0>>16))&0xffffffff; s1=(m1*(s1&0xffff)+(s1>>16))&0xffffffff
        return ((s0<<16)+(s1&0xffff))&0xffffffff
    return rnd
def gen_float_keys(m0,m1,seed):
    rnd=mwc_gen(m0,m1,seed&0xffffffff or 1,(seed>>32)&0xffffffff or 2); keys=[]
    for i in range(1,71):
        N=i-1
        if N==0: keys.append(1); continue
        v=0;got=0
        while got<N:
            out=rnd();take=min(32,N-got);v=(v<<take)|(out>>(32-take));got+=take
        keys.append((1<<(i-1))|v)
    return keys
def extract_indexed(keys):
    """return [(out_index, s0_lo)] reconstructing MWC stream positions from per-key output counts"""
    seq=[]; out_idx=0
    for i,k in enumerate(keys):
        N=i  # puzzle i+1 has i low bits
        if N==0: continue
        low=k-(1<<N)
        bits=[(low>>(N-1-j))&1 for j in range(N)]  # MSB-first
        nchunks=(N+31)//32
        for j in range(nchunks):
            width=min(32,N-j*32)
            if width>=16:
                t16=0
                for b in range(16): t16=(t16<<1)|bits[j*32+b]
                seq.append((out_idx+j,t16))
        out_idx+=nchunks
    return seq
def lane_verify_indexed(seq,m):
    d=dict(seq); idxs=sorted(d); seed=None
    for i in idxs:
        if i+1 in d:
            v0=d[i];v1=d[i+1];h=(v1-m*v0)&0xffff;s=(m*v0+h)&0xffffffff; seed=(i+1,s); break
    if seed is None: return None  # no consecutive pair to seed
    start,s=seed; cur=start; checked=0
    for i in idxs:
        if i<start: continue
        while cur<i: s=(m*(s&0xffff)+(s>>16))&0xffffffff; cur+=1
        if (s&0xffff)!=d[i]: return False
        checked+=1
    return checked>=5
MULS=[(18030,30903),(18273,18273),(36969,18000),(18000,30903),(30903,18030)]

print("=== CONTROL: MWC float-recipe keys, indexed lane recovery ===")
ck=gen_float_keys(18030,30903,0xABCD1234ABCD)
print(f"  seq len {len(extract_indexed(ck))}; recover(18030) = {lane_verify_indexed(extract_indexed(ck),18030)}  (want True)")
rng=random.Random(3); rk=[(1<<(i-1))|rng.getrandbits(i-1) if i>1 else 1 for i in range(1,71)]
print(f"  random-keys negative control: {lane_verify_indexed(extract_indexed(rk),18030)}  (want False/None)")

def run_real():
    real={}
    with open('puzzles_verified.csv') as f:
        for row in csv.DictReader(f):
            b=int(row['bits'])
            if b<=70: real[b]=int(row['private_key'],16)
    keys=[real[i] for i in range(1,71)]
    seq=extract_indexed(keys); hit=False
    for m0,m1 in MULS:
        for m in (m0,m1):
            if lane_verify_indexed(seq,m)==True: print(f"  HIT m={m}"); hit=True
    if not hit: print("  no multiplier makes the real indexed lane satisfy the MWC recurrence")

if lane_verify_indexed(extract_indexed(ck),18030)==True:
    print("\n=== TEST real (control validated) ===")
    run_real()
    print("  scope: float top-bits recipe, per-key output-count reconstruction, 5 mult pairs.")
else:
    print("\n  >>> control still not firing; not interpreting real. Solver needs more work.")
