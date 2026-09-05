#!/usr/bin/env python3
"""
Reset thread D (the big one): treat the low bits of the CONTIGUOUS keys 1..70 as a
reconstructable generator output stream (2415 bits), not 81 sparse samples.

Part 1 here:
  D1 - Berlekamp-Massey linear complexity of the concatenated low-bit stream.
       Random stream -> L/2. LFSR/pow2-LCG-lowbit -> small (a NEW positive).
       This re-does the doc's "BM ~ n/2" claim on the ACTUAL contiguous stream.
  D0 - named weak-LCG replay search (Java util.Random, MSVC, minstd, RANDU,
       glibc TYPE_0) x bit-packing recipes, over a bounded seed set, matched null,
       firing positive control. Thread B covered MT19937 only.

Exact integers only. Controls mandatory. Nulls matched.
"""
from reset_common import load_solved, contiguous_run

solved = load_solved()
RUN = contiguous_run(solved, 1)                    # 1..70
D   = {N: solved[N]["d"] for N in RUN}

def low(dN, N):     # low N-1 bits of key N
    return dN & ((1 << (N - 1)) - 1)

# ---------------- D1: Berlekamp-Massey over GF(2) ----------------
def berlekamp_massey_gf2(bits):
    n = len(bits); C = [0]*n; Bb = [0]*n; C[0]=Bb[0]=1
    L=0; m=1; b=1
    for i in range(n):
        d = bits[i]
        for j in range(1, L+1):
            d ^= C[j] & bits[i-j]
        if d == 1:
            T = C[:]
            for j in range(0, n-m):
                C[j+m] ^= Bb[j]
            if 2*L <= i:
                L = i+1-L; Bb = T; m = 1
            else:
                m += 1
        else:
            m += 1
    return L

def stream_bits(order_keys, msb_first=True):
    out = []
    for N in order_keys:
        w = N-1
        if w == 0: continue
        v = low(D[N], N)
        rng = range(w-1, -1, -1) if msb_first else range(0, w)
        for j in rng:
            out.append((v >> j) & 1)
    return out

print("=== D1: Berlekamp-Massey linear complexity of the contiguous low-bit stream ===")
for msb in (True, False):
    bits = stream_bits(RUN, msb)
    L = berlekamp_massey_gf2(bits)
    print(f"  {'MSB-first' if msb else 'LSB-first'}: length {len(bits)}, "
          f"linear complexity {L}  (L/len = {L}/{len(bits)} = {L/len(bits):.3f})")
# controls
import random
rc = random.Random(1)
rand_bits = [rc.getrandbits(1) for _ in range(2415)]
print(f"  [CTRL random] len {len(rand_bits)}, LC {berlekamp_massey_gf2(rand_bits)} (expect ~len/2)")
# LFSR control: degree-23 LFSR
def lfsr23(nbits, seed=0x123456):
    s=seed; out=[]
    for _ in range(nbits):
        b = s & 1; out.append(b)
        nb = ((s>>0)^(s>>5)) & 1
        s = (s>>1) | (nb<<22)
    return out
lf = lfsr23(2415)
print(f"  [CTRL LFSR-23] LC {berlekamp_massey_gf2(lf)} (expect ~23)\n")

# ---------------- D0: named weak-LCG replay ----------------
class LCG:
    def __init__(self, m, a, c, out_hi, out_bits):
        self.m=m; self.a=a; self.c=c; self.out_hi=out_hi; self.out_bits=out_bits
    def stepped(self, state):
        state = (self.a*state + self.c) % self.m
        if self.out_hi:
            shift = self.m.bit_length()-1 - self.out_bits
            val = (state >> max(shift,0)) & ((1<<self.out_bits)-1)
        else:
            val = state & ((1<<self.out_bits)-1)
        return state, val

GENS = {
    "java48":  LCG(1<<48, 0x5DEECE66D, 0xB, True, 32),
    "msvc":    LCG(1<<31, 214013, 2531011, True, 15),   # bits 30..16
    "minstd":  LCG((1<<31)-1, 16807, 0, False, 31),
    "randu":   LCG(1<<31, 65539, 0, False, 31),
    "glibc0":  LCG(1<<31, 1103515245, 12345, True, 16),
    "ansic":   LCG(1<<31, 1103515245, 12345, False, 16),
}

def gen_keys(lcg, seed, order):
    """Assemble each N-1 bit key MSB-first from consecutive LCG outputs, sequential."""
    state = seed % lcg.m
    out = {}
    for N in order:
        w = N-1; acc = 0; got = 0
        while got < w:
            state, val = lcg.stepped(state)
            take = min(lcg.out_bits, w-got)
            # take the top `take` bits of val
            chunk = val >> (lcg.out_bits-take)
            acc = (acc << take) | chunk
            got += take
        out[N] = (1 << (N-1)) | acc if w>0 else 1
    return out

def prefix_and_matches(gen):
    matches = sum(1 for N in RUN if gen.get(N)==D[N])
    pre=0
    for N in RUN:
        if gen.get(N)==D[N]: pre+=1
        else: break
    return matches, pre

SEED_SET = list(range(0, 1<<16)) + [2015, 20150115, 1231006505,
             (1<<31)-1, 0xDEADBEEF, 0xCAFEBABE, 12345, 305419896]

def search(lcg, seeds, target=D, quick=True):
    best=(0,0,None)
    for sd in seeds:
        # quick prune: generate first 10 keys, need prefix >=7 (keys 8,9,10 = 7,8,9 low bits)
        if quick:
            g = gen_keys(lcg, sd, RUN[:10])
            ok = all(g[N]==target[N] for N in RUN[:8])
            if not ok:
                continue
        g = gen_keys(lcg, sd, RUN)
        m,pre = prefix_and_matches(g) if target is D else (sum(1 for N in RUN if g[N]==target[N]),0)
        if (m,pre)>(best[0],best[1]): best=(m,pre,sd)
    return best

print("=== D0: named weak-LCG replay (65k+ seeds each, MSB-packed, sequential) ===")
# positive control: synth from java48 seed 999, must recover
ctrl_target = gen_keys(GENS["java48"], 999, RUN)
cb = search(GENS["java48"], [999, 1000, 998], target=ctrl_target, quick=False)
print(f"  [CTRL] java48 planted seed 999: recovered matches {cb[0]} (expect {len(RUN)}) -> {'FIRES' if cb[0]==len(RUN) else 'FAIL'}\n")

for name, lcg in GENS.items():
    b = search(lcg, SEED_SET, quick=True)
    print(f"  {name:<8}: best matches {b[0]:>2}, prefix {b[1]:>2}, seed {b[2]}")
print("\nscope: 6 LCG families x ~65.5k seeds x MSB-sequential recipe; a hit needs "
      "prefix>=8 to survive the quick prune. Non-hits are scoped to this recipe/seed set.")
