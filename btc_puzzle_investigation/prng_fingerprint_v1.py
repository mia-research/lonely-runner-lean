#!/usr/bin/env python3
"""
PRNG fingerprint / rule-out harness for the Bitcoin puzzle keys.

Goal (per user 2026-07-06): not seed-guessing per se, but to IDENTIFY which PRNG
produced the keys, or to RULE OUT candidate PRNGs.

Information-theoretic ceiling (stated up front, not a limitation of effort):
a well-seeded PRNG's output is by construction indistinguishable from uniform, so
you CANNOT fingerprint the generator from key values UNLESS the seed lived in a
small enumerable space (weak string / small int / time-based). Therefore the only
rigorous, decisive move is to EXHAUSTIVELY sweep each concrete 2015-era candidate's
enumerable seed space. A null sweep rules out "<that PRNG> seeded from <that space>
with <that consumption model>" -- NOT the PRNG in general.

Each key #N has exactly N bits (top bit set), verified. We test sequential
in-order consumption (creator draws key #1, #2, ... from one stream) with several
plausible models, using EARLY ABORT: stop at first mismatch, record the max
consecutive run from #1. A genuine hit = run reaches len(CHECK). Coincidence floor
(from a 5000-seed control) is ~4-5, occasionally 7; only runs >=~15 are meaningful.
"""
import random, csv, os, sys, time, ctypes, ctypes.util

MASTER = os.path.join(os.path.dirname(__file__), 'btc_puzzle_master.csv')

def load_known():
    K = {}
    with open(MASTER) as f:
        for r in csv.DictReader(f):
            if r['status'] == 'SOLVED' and r['priv_dec']:
                K[int(r['puzzle'])] = int(r['priv_dec'])
    return K

KNOWN = load_known()
# longest contiguous run of solved keys starting at #1
CHECK = []
n = 1
while n in KNOWN:
    CHECK.append(n); n += 1
KVAL = [KNOWN[n] for n in CHECK]           # target key values, index = N-1
assert all(v.bit_length() == i+1 for i, v in enumerate(KVAL)), "bit-length invariant broken"

# ---------------- consumption models (Python Mersenne Twister) ----------------
_RNG = random.Random()   # reuse one object; Random() with no arg would getentropy() each call
def run_mt(seed, model):
    rr = _RNG; rr.seed(seed); run = 0
    for i, N in enumerate(CHECK):
        if model == 'randrange':
            k = rr.randrange(1 << (N-1), 1 << N)
        elif model == 'topbit':
            k = (1 << (N-1)) | rr.getrandbits(N-1)
        elif model == 'reject':
            while True:
                k = rr.getrandbits(N)
                if k >= (1 << (N-1)): break
        else:
            raise ValueError(model)
        if k == KVAL[i]: run += 1
        else: break
    return run

# ---------------- glibc C rand() (exact algorithm via libc) ----------------
_libc = ctypes.CDLL(ctypes.util.find_library('c'))
def run_glibc(seed, model):
    _libc.srand(seed & 0xffffffff); run = 0
    for i, N in enumerate(CHECK):
        if model == 'bits':                 # 1 rand() per low bit
            k = 1 << (N-1)
            for b in range(N-1):
                if _libc.rand() & 1: k |= (1 << b)
        elif model == 'mod':                # rand() % range + lo
            k = (1 << (N-1)) + (_libc.rand() % (1 << (N-1)) if N > 1 else 0)
        else:
            raise ValueError(model)
        if k == KVAL[i]: run += 1
        else: break
    return run

# ---------------- old V8 Math.random (MWC1616), pre-2015 ----------------
# Approximate model of the V8 generator used before the 2015/16 xorshift128+ switch.
# Constants are the widely-cited old-V8 MWC pair. Seeding is version-dependent, so
# a null here rules out THIS modeled variant only (documented caveat).
def _v8_stream(seed):
    s0 = (seed & 0xffffffff) or 1
    s1 = ((seed >> 32) & 0xffffffff) or 2
    while True:
        s0 = (18030 * (s0 & 0xffff) + (s0 >> 16)) & 0xffffffff
        s1 = (30903 * (s1 & 0xffff) + (s1 >> 16)) & 0xffffffff
        yield (((s0 << 16) + (s1 & 0xffff)) & 0xffffffff) / 4294967296.0  # [0,1)

def run_v8(seed, model):
    g = _v8_stream(seed); run = 0
    for i, N in enumerate(CHECK):
        if model == 'floor':                # floor(rand()*2^(N-1)) + 2^(N-1)
            k = (1 << (N-1)) + (int(next(g) * (1 << (N-1))) if N > 1 else 0)
        elif model == 'bits':               # rand()<0.5 per low bit
            k = 1 << (N-1)
            for b in range(N-1):
                if next(g) < 0.5: k |= (1 << b)
        else:
            raise ValueError(model)
        if k == KVAL[i]: run += 1
        else: break
    return run

RUNNERS = {'MT': run_mt, 'glibc': run_glibc, 'V8': run_v8}
MODELS  = {'MT': ['randrange', 'topbit', 'reject'],
           'glibc': ['bits', 'mod'],
           'V8': ['floor', 'bits']}

# ---------------- worker CLI: scan one (prng,model) over [lo,hi), early-abort ----------------
# No multiprocessing (hangs on this macOS/py3.14 spawn setup); parallelize by
# launching independent OS processes from the shell, each writing best to a file.
def selftest():
    global KVAL
    save = KVAL[:]
    rr = random.Random(); rr.seed(424242)
    KVAL = [rr.randrange(1 << (N-1), 1 << N) for N in CHECK]
    ok = (run_mt(424242, 'randrange') == len(CHECK))
    KVAL = save
    return ok

def worker(prng, model, lo, hi, outfile):
    runner = RUNNERS[prng]
    bm, bs = 0, None
    for seed in range(lo, hi):
        r = runner(seed, model)
        if r > bm:
            bm, bs = r, seed
            if r >= len(CHECK):   # full hit, stop early
                break
    with open(outfile, 'w') as f:
        f.write(f"{prng}\t{model}\t{lo}\t{hi}\t{bm}\t{bs}\n")

if __name__ == '__main__':
    if len(sys.argv) == 6 and sys.argv[1] == 'selftest':
        pass
    if sys.argv[1] == 'worker':
        _, _, prng, model, lo, hi, outfile = sys.argv
        worker(prng, model, int(lo), int(hi), outfile)
    elif sys.argv[1] == 'info':
        print(f"contiguous solved keys #1..#{len(CHECK)}; hit-run = {len(CHECK)}; "
              f"selftest={'PASS' if selftest() else 'FAIL'}")
        print("models:", {p: MODELS[p] for p in RUNNERS})
