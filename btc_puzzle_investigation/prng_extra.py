#!/usr/bin/env python3
"""Extra PRNG models for the puzzle-key fingerprint: PHP mt_rand (MT19937 mode)
and the Randstorm path (BitcoinJS SecureRandom = RC4 keystream keyed from a pool
of old-V8 Math.random() bytes). Separate file so it doesn't touch the file that
the running full-2^32 sweep imports.

Worker CLI mirrors prng_fingerprint_v1.py: `worker PRNG MODEL LO HI OUT`.
Each key #N has exactly N bits (top bit set); early-abort; hit = run 70/70.
Caveats: (1) PHP mt_rand max is 2^31-1, so N-bit keys must be built from multiple
draws -- we model bit-serial + 31-bit-word fills. (2) BitcoinJS makes 32-byte
keys; the puzzle keys are N-bit, so RC4 here models a hypothetical custom script
consuming SecureRandom's byte stream. The enumerable parameter is the underlying
Math.random (V8 MWC1616) seed."""
import csv, os, sys

MASTER = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'btc_puzzle_master.csv')
KNOWN = {}
with open(MASTER) as f:
    for r in csv.DictReader(f):
        if r['status'] == 'SOLVED' and r['priv_dec']:
            KNOWN[int(r['puzzle'])] = int(r['priv_dec'])
CHECK = []
n = 1
while n in KNOWN:
    CHECK.append(n); n += 1
KVAL = [KNOWN[n] for n in CHECK]

# ------------------------- PHP MT19937 (mt_rand, modern mode) -------------------------
_N, _M = 624, 397
def _php_seed(seed):
    s = [0]*_N
    s[0] = seed & 0xffffffff
    for i in range(1, _N):
        s[i] = (1812433253 * (s[i-1] ^ (s[i-1] >> 30)) + i) & 0xffffffff
    return s
def _php_reload(s):
    def twist(m, u, v):
        return (m ^ (((u & 0x80000000) | (v & 0x7fffffff)) >> 1)
                  ^ (0x9908b0df if (v & 1) else 0)) & 0xffffffff
    for i in range(_N - _M):
        s[i] = twist(s[i+_M], s[i], s[i+1])
    for i in range(_N - _M, _N - 1):
        s[i] = twist(s[i+(_M-_N)], s[i], s[i+1])
    s[_N-1] = twist(s[_M-1], s[_N-1], s[0])
class PhpMT:
    def __init__(self, seed):
        self.s = _php_seed(seed); self.i = _N
    def next31(self):                     # php_mt_rand: 31-bit [0, 2^31)
        if self.i >= _N:
            _php_reload(self.s); self.i = 0
        y = self.s[self.i]; self.i += 1
        y ^= (y >> 11)
        y ^= (y << 7) & 0x9d2c5680
        y ^= (y << 15) & 0xefc60000
        y ^= (y >> 18)
        return (y & 0xffffffff) >> 1
def run_php(seed, model):
    g = PhpMT(seed); run = 0
    for i, N in enumerate(CHECK):
        if model == 'bits':               # top bit + N-1 low bits, LSB of each draw
            k = 1 << (N-1)
            for b in range(N-1):
                if g.next31() & 1: k |= (1 << b)
        elif model == 'words':            # fill low N-1 bits from 31-bit words
            k = 1 << (N-1); need = N-1; acc = 0; have = 0
            while have < need:
                acc = (acc << 31) | g.next31(); have += 31
            k |= (acc >> (have - need)) & ((1 << need) - 1) if need else 0
        else:
            raise ValueError(model)
        if k == KVAL[i]: run += 1
        else: break
    return run

# ------------------------- Randstorm: RC4 keyed from V8 Math.random pool -------------------------
def _v8(seed):
    s0 = (seed & 0xffffffff) or 1
    s1 = ((seed >> 32) & 0xffffffff) or 2
    while True:
        s0 = (18030 * (s0 & 0xffff) + (s0 >> 16)) & 0xffffffff
        s1 = (30903 * (s1 & 0xffff) + (s1 >> 16)) & 0xffffffff
        yield (((s0 << 16) + (s1 & 0xffff)) & 0xffffffff) / 4294967296.0
def _rc4_stream(key_bytes, nbytes):
    S = list(range(256)); j = 0
    for i in range(256):
        j = (j + S[i] + key_bytes[i % len(key_bytes)]) & 0xff
        S[i], S[j] = S[j], S[i]
    out = bytearray(); i = j = 0
    for _ in range(nbytes):
        i = (i + 1) & 0xff; j = (j + S[i]) & 0xff
        S[i], S[j] = S[j], S[i]
        out.append(S[(S[i] + S[j]) & 0xff])
    return out
def run_rc4(seed, model):
    g = _v8(seed)
    pool = bytes(int(256 * next(g)) & 0xff for _ in range(256))   # BitcoinJS-style pool from Math.random
    total_bits = sum(CHECK)                                        # enough keystream
    stream = _rc4_stream(pool, (total_bits // 8) + len(CHECK) + 8)
    bit_src = 0; nbits = 0; pos = 0
    def take(nb):
        nonlocal bit_src, nbits, pos
        while nbits < nb:
            bit_src = (bit_src << 8) | stream[pos]; pos += 1; nbits += 8
        nbits -= nb
        return (bit_src >> nbits) & ((1 << nb) - 1)
    run = 0
    for i, N in enumerate(CHECK):
        k = (1 << (N-1)) | (take(N-1) if N > 1 else 0)             # top bit + N-1 stream bits
        if k == KVAL[i]: run += 1
        else: break
    return run

RUNNERS = {'PHP': run_php, 'RC4': run_rc4}
MODELS = {'PHP': ['bits', 'words'], 'RC4': ['stream']}

def selftest():
    global KVAL
    ok = True
    for prng, models in MODELS.items():
        for model in models:
            planted = 123456789
            save = KVAL[:]
            KVAL = _capture(prng, model, planted)      # keys this seed actually yields
            r = RUNNERS[prng](planted, model)          # detector must recover full run
            KVAL = save
            ok = ok and (r == len(CHECK))
            print(f"  selftest {prng}/{model}: run {r}/{len(CHECK)} {'PASS' if r==len(CHECK) else 'FAIL'}")
    return ok
def _capture(prng, model, seed):
    keys = []
    if prng == 'PHP':
        g = PhpMT(seed)
        for N in CHECK:
            if model == 'bits':
                k = 1 << (N-1)
                for b in range(N-1):
                    if g.next31() & 1: k |= (1 << b)
            else:
                k = 1 << (N-1); need = N-1; acc = 0; have = 0
                while have < need:
                    acc = (acc << 31) | g.next31(); have += 31
                k |= (acc >> (have - need)) & ((1 << need) - 1) if need else 0
            keys.append(k)
    else:  # RC4
        g = _v8(seed)
        pool = bytes(int(256 * next(g)) & 0xff for _ in range(256))
        stream = _rc4_stream(pool, (sum(CHECK)//8) + len(CHECK) + 8)
        bit_src = nbits = pos = 0
        def take(nb):
            nonlocal bit_src, nbits, pos
            while nbits < nb:
                bit_src = (bit_src << 8) | stream[pos]; pos += 1; nbits += 8
            nbits -= nb
            return (bit_src >> nbits) & ((1 << nb) - 1)
        for N in CHECK:
            keys.append((1 << (N-1)) | (take(N-1) if N > 1 else 0))
    return keys

def worker(prng, model, lo, hi, outfile):
    runner = RUNNERS[prng]; bm, bs = 0, None
    for seed in range(lo, hi):
        r = runner(seed, model)
        if r > bm:
            bm, bs = r, seed
            if r >= len(CHECK): break
    with open(outfile, 'w') as f:
        f.write(f"{prng}\t{model}\t{lo}\t{hi}\t{bm}\t{bs}\n")

if __name__ == '__main__':
    if sys.argv[1] == 'worker':
        _, _, prng, model, lo, hi, out = sys.argv
        worker(prng, model, int(lo), int(hi), out)
    elif sys.argv[1] == 'info':
        print(f"CHECK #1..#{len(CHECK)}; models {MODELS}")
        print("selftest:", "PASS" if selftest() else "FAIL")
