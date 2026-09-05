#!/usr/bin/env python3
"""
mt19937_gf2_reduction_v1.py

MT19937 as a GF(2) linear system -- but asked the LATERAL way (user 2026-07-13):
not "recover the full state" (data-gated), but "do the SOLVED puzzle keys linearly
CONSTRAIN an UNSOLVED key at all, and by how many bits?".  A reduction of the
search space for k is the deliverable, not k itself.

Model of the pipeline (the MT19937 hypothesis, stock CPython):
  key_i  =  getrandbits(i-1)  |  (1 << (i-1))      # i-bit key, top bit forced
generated in strict index order (on-chain funding tx confirms index order).
getrandbits consumes ceil((i-1)/32) tempered 32-bit words; the observed bits are
GF(2)-linear functionals of the 19968-bit MT state.

Method: symbolic MT -- every output bit carried as a Python-int BITMASK over the
19968 state unknowns (homogeneous; MT output is linear in the state).  Build the
constraint row-space from the first K contiguous keys; for a held-out later key,
count how many of its bits lie IN that row space (= bits DETERMINED by the solved
run = search reduction).  Rank over GF(2) by bitmask Gaussian elimination.

Controls:
  (+) low-entropy seed: if the state is a function of a 32-bit seed, all outputs
      share those unknowns -> massive cross-constraint (keys determine each other).
  (main) full-entropy seed (default random.seed()): state words independent.
Validated bit-for-bit against CPython random.getrandbits before any conclusion.

Exact integers throughout (bitmasks); no float in the signal path.
"""
import random

N, M = 624, 397
MATRIX_A = 0x9908b0df
UPPER = 0x80000000
LOWER = 0x7fffffff
NBITS = N * 32  # 19968 state unknowns

# ---- symbolic MT: state[w] = list of 32 bitmasks (over NBITS unknowns) --------
class SymMT:
    def __init__(self, pool=None):
        # unknown j = bit j of the flattened state (word w, bit b) -> j = w*32+b.
        # pool=None  -> full-entropy: every state bit an independent unknown.
        # pool=P     -> LOW-ENTROPY control: state bits reuse only P unknowns
        #               (mod P), i.e. the whole state is a function of P bits.
        if pool is None:
            self.mt = [[1 << (w * 32 + b) for b in range(32)] for w in range(N)]
        else:
            self.mt = [[1 << ((w * 32 + b) % pool) for b in range(32)] for w in range(N)]
        self.idx = N  # force a "generate" region check; we read pre-twist by generating on demand

    def _twist(self):
        for i in range(N):
            # y = (mt[i]&UPPER) | (mt[i+1 mod N]&LOWER)
            yb = [self.mt[i][31]] + self.mt[(i + 1) % N][0:31]  # (y>>1) bit layout helper not used; do bitwise below
            # build y's 32 bits: bit31 from mt[i] bit31; bits0..30 from mt[i+1] bits0..30
            y = [None] * 32
            y[31] = self.mt[i][31]
            for b in range(31):
                y[b] = self.mt[(i + 1) % N][b]
            # y>>1 : new bit b = y bit b+1 ; top bit 0
            yshift = [y[b + 1] for b in range(31)] + [0]
            # mag: if y&1 -> XOR MATRIX_A. y&1 = y[0]. linear term: bit b gets y[0] if MATRIX_A bit b set.
            newword = []
            src = self.mt[(i + M) % N]
            for b in range(32):
                v = src[b] ^ yshift[b]
                if (MATRIX_A >> b) & 1:
                    v ^= y[0]
                newword.append(v)
            self.mt[i] = newword
        self.idx = 0

    def genrand(self):
        if self.idx >= N:
            self._twist()
        w = self.mt[self.idx]
        self.idx += 1
        # tempering (linear): y ^= y>>11; y ^= (y<<7)&0x9d2c5680; y ^= (y<<15)&0xefc60000; y ^= y>>18
        y = list(w)
        y = [y[b] ^ (y[b + 11] if b + 11 < 32 else 0) for b in range(32)]
        y = [y[b] ^ ((y[b - 7] if b - 7 >= 0 else 0) if (0x9d2c5680 >> b) & 1 else 0) for b in range(32)]
        y = [y[b] ^ ((y[b - 15] if b - 15 >= 0 else 0) if (0xefc60000 >> b) & 1 else 0) for b in range(32)]
        y = [y[b] ^ (y[b + 18] if b + 18 < 32 else 0) for b in range(32)]
        return y  # 32 bitmasks, LSB..MSB

    def getrandbits(self, k):
        """CPython convention: words=ceil(k/32); each word = genrand>>(32-min(rem,32)).
        Returns list of k bitmasks (LSB first)."""
        out = []
        rem = k
        while rem > 0:
            take = 32 if rem >= 32 else rem
            word = self.genrand()  # bits 0..31 (LSB..MSB) as masks
            # r >>= (32-take): keep HIGH `take` bits -> those become low bits of output chunk
            hi = word[32 - take:32]  # masks for bits (32-take)..31, which map to output bits 0..take-1
            out.extend(hi)
            rem -= 32
        return out[:k]

# ---- concrete oracle to VALIDATE the symbolic engine -------------------------
def state_vector_from_random(r):
    """Flatten CPython random state (624 words) into a NBITS-bit integer."""
    st = r.getstate()[1]  # tuple of 625 (624 words + index)
    words = st[:624]
    v = 0
    for w in range(624):
        v |= (words[w] & 0xffffffff) << (w * 32)
    return v, st[624]

def eval_mask(mask, statevec):
    return bin(mask & statevec).count("1") & 1

# ---- GF(2) row space (bitmask Gaussian elimination) --------------------------
def rank_and_basis(rows):
    """rows: list of bitmask ints. Return (rank, reduced pivot rows list)."""
    basis = []  # list of (pivot_bit, row)
    for row in rows:
        r = row
        for piv, brow in basis:
            if (r >> piv) & 1:
                r ^= brow
        if r:
            piv = r.bit_length() - 1
            basis.append((piv, r))
            basis.sort(key=lambda t: -t[0])
    return len(basis), basis

def in_span(mask, basis):
    r = mask
    for piv, brow in basis:
        if (r >> piv) & 1:
            r ^= brow
    return r == 0  # True => mask is a linear combo of the basis (bit DETERMINED)

# ---- experiments -------------------------------------------------------------
def build_key_masks(sym, upto_index):
    """Symbolic bitmasks for keys 1..upto_index via the pipeline.  Returns
    dict index-> list of masks (the getrandbits(i-1) bits; top forced bit is const=known)."""
    km = {}
    for i in range(1, upto_index + 1):
        w = i - 1
        km[i] = sym.getrandbits(w) if w > 0 else []
    return km

def validate(upto=40):
    """Symbolic getrandbits must reproduce CPython getrandbits bit-for-bit."""
    r = random.Random()
    r.seed(20260713)
    sv, _ = state_vector_from_random(r)
    sym = SymMT()
    ok = True
    for i in range(1, upto + 1):
        w = i - 1
        masks = sym.getrandbits(w)
        sym_val = 0
        for b, mk in enumerate(masks):
            sym_val |= eval_mask(mk, sv) << b
        concrete = r.getrandbits(w) if w > 0 else 0
        if sym_val != concrete:
            ok = False
            print(f"  MISMATCH at key {i} (w={w}): sym={sym_val} vs cpython={concrete}")
            break
    print(f"[VALIDATE] symbolic == CPython getrandbits for keys 1..{upto}: {ok}")
    return ok

def reduction_report(K_solved, targets, pool=None):
    """Build row space from keys 1..K_solved; for each target index, count how many
    of its bits are determined (in span). pool=None full-entropy; pool=P low-entropy."""
    maxidx = max([K_solved] + targets)
    sym = SymMT(pool=pool)
    km = build_key_masks(sym, maxidx)
    rows = []
    for i in range(1, K_solved + 1):
        rows.extend(km[i])
    rank, basis = rank_and_basis(rows)
    obs_bits = sum(len(km[i]) for i in range(1, K_solved + 1))
    print(f"\n  solved keys 1..{K_solved}: observed bits={obs_bits}, GF(2) rank={rank} "
          f"(state unknowns={NBITS})")
    for t in targets:
        if t <= K_solved:
            continue
        tb = km[t]
        det = sum(1 for mk in tb if in_span(mk, basis))
        print(f"    target #{t} ({len(tb)} bits): DETERMINED by solved run = {det} bits "
              f"-> search reduction {det} bits ({'2^%d x' % det if det else 'NONE'})")

def twist_horizon():
    """At what puzzle index does cumulative getrandbits reach the first twist (624 words)?"""
    words = 0
    for i in range(1, 300):
        words += (max(i - 1, 0) + 31) // 32
        if words >= N:
            return i, words
    return None, words

if __name__ == "__main__":
    print("=== MT19937 GF(2) reduction probe (pipeline: getrandbits(i-1)|topbit) ===")
    if not validate(40):
        raise SystemExit("symbolic engine invalid; abort")
    hi, w = twist_horizon()
    print(f"\n[TWIST HORIZON] MT twists at stream start, then again every 624 words. The"
          f"\n  SECOND twist (which re-mixes the already-observed 624-word block) is reached"
          f"\n  at ~puzzle #{hi} (cumulative words = {w}). The ENTIRE puzzle range (<=#160) lives"
          f"\n  inside the FIRST post-twist block: 624 distinct words, each an independent linear"
          f"\n  combo of the seeded state -> reading distinct words gives independent bits, so no"
          f"\n  key linearly constrains any other until #{hi}, beyond the puzzle range.")
    print("\n=== CONTROL (+): LOW-ENTROPY seed (state = function of 64 bits) ===")
    print("    instrument MUST fire: solved keys pin the 64 unknowns -> targets determined")
    reduction_report(70, [71, 100, 160], pool=64)

    print("\n=== CONTROL (+): full-entropy but CROSSING the twist (1..190) ===")
    print("    post-twist outputs mix earlier state -> some determination should appear")
    reduction_report(190, [191, 200])

    print("\n=== MAIN: full-entropy seed (independent state words), puzzle range ===")
    reduction_report(70, [71, 75, 80, 100, 130, 135, 160])
    reduction_report(130, [131, 135, 140, 160])
    reduction_report(160, [161, 200, 256])  # 256 beyond puzzle range, illustrative
