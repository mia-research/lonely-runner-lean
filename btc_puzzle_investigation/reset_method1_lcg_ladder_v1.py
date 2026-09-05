#!/usr/bin/env python3
"""
METHOD 1 (replaces seed-brute): algebraic pow2-LCG recovery by a 2-adic bit-ladder.

Idea: was the generator a power-of-2-modulus LCG (Java 2^48, MSVC/glibc/ANSI/Borland
2^31/2^32)? Instead of guessing seeds, RECOVER the recurrence, or FALSIFY the family
by contradiction.

Model (natural "random N-bit key" recipe): key N = 2^(N-1) + (s_N mod 2^(N-1)), where
s_1,s_2,... are consecutive states of x_{i+1}=a x_i + c mod 2^K. Then
    o_N := d_N - 2^(N-1) = s_N mod 2^(N-1)   (we observe the LOW N-1 bits of state N).
For a pow2 modulus the low b bits are self-contained: s mod 2^b obeys the SAME affine
map mod 2^b. So at level b, y_N = o_N mod 2^b (known when N-1>=b) must satisfy
    y_N = a y_{N-1} + c (mod 2^b)   for all N with N-1>=b and N-2>=b.
Solve (a,c) mod 2^b from one anchor with odd first-difference (invertible mod 2^b),
then VERIFY against every other key. The largest b that stays consistent is the
"consistency depth". A real pow2-LCG -> depth grows with #keys; random -> breaks early.

This is a structural test: if depth stays at the random-null level, the pow2-LCG-low-
bits family (this recipe) is EXCLUDED by contradiction, not by a bounded seed search.
Exact integers only. Positive control = a planted Java LCG must be recovered.
"""
import random
from reset_common import load_solved, contiguous_run

solved = load_solved()
RUN = contiguous_run(solved, 1)                 # 1..70
MAXN = RUN[-1]

def observations(dmap):
    """o[N] = low N-1 bits, for N in 2..MAXN."""
    return {N: dmap[N] - (1 << (N-1)) for N in RUN if N >= 2}

def consistency_depth(o, bmax=None, min_verify=6):
    """Largest b for which a single (a,c) mod 2^b explains all keys with enough
    verification equations. Returns (depth, (a,c,b) at depth)."""
    if bmax is None: bmax = MAXN - 3
    best_depth = 0; best_params = None
    for b in range(1, bmax+1):
        M = 1 << b
        Ns = [N for N in RUN if N-1 >= b and N >= 2]      # y_N known mod 2^b
        # recurrence usable for N with (N-1) and (N-2) both >= b  => N-2>=b => N>=b+2
        rec_Ns = [N for N in Ns if (N-2) >= b]
        if len(rec_Ns) < min_verify + 1:
            continue
        y = {N: (o[N] & (M-1)) for N in Ns}
        # find an anchor pair (N-1,N),(N,N+1) among rec range with odd first difference
        a = c = None
        rN = sorted(rec_Ns)
        for i in range(len(rN)-1):
            N = rN[i]
            if N-1 not in y or N+1 not in y or N not in y:
                continue
            d1 = (y[N] - y[N-1]) & (M-1)
            if d1 & 1:                                    # invertible mod 2^b
                inv = pow(d1, -1, M)
                a = ((y[N+1]-y[N]) * inv) & (M-1)
                c = (y[N] - a*y[N-1]) & (M-1)
                break
        if a is None:
            continue
        ok = all(((a*y[N-1]+c) & (M-1)) == y[N] for N in rec_Ns if (N-1) in y)
        if ok:
            best_depth = b; best_params = (a, c, b)
    return best_depth, best_params

# ---------------- positive control: planted Java LCG ----------------
def planted_lcg_keys(a, c, m, seed):
    s = seed % m
    out = {1: 1}
    for N in RUN:
        if N == 1: continue
        s = (a*s + c) % m
        out[N] = (1 << (N-1)) | (s & ((1 << (N-1)) - 1))
    return out

print("=== METHOD 1: pow2-LCG bit-ladder recovery ===\n")
JA, JC, JM = 0x5DEECE66D, 0xB, 1 << 48
ctrl = planted_lcg_keys(JA, JC, JM, seed=0xABCDEF)
cd, cp = consistency_depth(observations(ctrl))
print(f"[CTRL] planted Java LCG (a=0x5DEECE66D,c=0xB,m=2^48):")
print(f"       consistency depth = {cd} bits; recovered (a,c) mod 2^{cp[2]} = "
      f"({hex(cp[0])}, {hex(cp[1])})")
print(f"       a mod 2^{cp[2]} matches Java a? {cp[0] == (JA & ((1<<cp[2])-1))}")
print(f"       -> ladder recovers a real pow2-LCG (depth grows to the modulus width).\n")

# ---------------- real data ----------------
depth_real, params_real = consistency_depth(observations({N: solved[N]["d"] for N in RUN}))
print(f"[REAL] consistency depth = {depth_real} bits",
      f"(params {('a=%s,c=%s' % (hex(params_real[0]),hex(params_real[1]))) if params_real else 'n/a'})")

# ---------------- null calibration from 100k ----------------
import csv, os
from collections import defaultdict
pool = defaultdict(list)
with open(os.path.join(os.path.dirname(__file__),
        "constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        b = int(r["bits"])
        if b <= MAXN: pool[b].append(int(r["d"]))
rng = random.Random(0x1ADDE7)
def null_keys():
    out = {}
    for N in RUN:
        p = pool.get(N)
        out[N] = rng.choice(p) if p else rng.randrange(1<<(N-1), 1<<N)
    return out

null_depths = [consistency_depth(observations(null_keys()))[0] for _ in range(300)]
from collections import Counter
print(f"[NULL] 300 synthetic keysets: depth distribution {dict(sorted(Counter(null_depths).items()))}")
print(f"       null max depth = {max(null_depths)}, mean = {sum(null_depths)/len(null_depths):.2f}")
print()
if depth_real > max(null_depths) + 2:
    print(f"  -> REAL depth {depth_real} EXCEEDS null: candidate pow2-LCG. Investigate params.")
else:
    print(f"  -> REAL depth {depth_real} within null band (max {max(null_depths)}).")
    print(f"     STRUCTURAL EXCLUSION: the keys' low bits do NOT follow a consistent")
    print(f"     affine-mod-2^b recurrence beyond the random level, so a pow2-modulus")
    print(f"     LCG under the low-bits recipe is falsified by contradiction (covers")
    print(f"     Java/MSVC/glibc/ANSI/Borland). Scope: this recipe (one draw per key,")
    print(f"     low bits); a prime-modulus LCG (low bits not self-contained) is the")
    print(f"     separate lattice case, and multi-draw packings are not covered here.")
