"""Measured interval-DLP solver comparison on secp256k1 (solvable widths).
Correct negation via linear-combination tracking: every walk point carries (a,b)
with point = [a]G + [b]Q; canon negates BOTH (a,b); a collision gives
d = (a1-a2)*(b2-b1)^{-1} mod N, then verified d*G==Q. Exact group ops."""
import random, statistics, math
from puzzle_kangaroo_distributed import P, add, mul, G
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def canon(Q):
    if Q is None: return None, 1
    return (Q, 1) if (Q[1] & 1) == 0 else ((Q[0], (P - Q[1]) % P), -1)
def jumps_for(W, K, frac=0.5):
    m = max(1, int(frac*math.isqrt(W)))
    sizes = [1 + (2*m*i)//max(1, K-1) for i in range(K)]
    return sizes, [mul(s) for s in sizes]

def _finish(a1, b1, a2, b2, secret, Q):
    db = (b2 - b1) % N
    if db == 0: return None
    d = ((a1 - a2) * pow(db, -1, N)) % N
    return (d == secret) if mul(d) == Q else None

def solve(W, secret, Q, seed, mode):
    """mode: 'current' | 'tuned' | 'neg' | 'gs'"""
    rng = random.Random(seed); B = W.bit_length()
    negation = mode in ('neg', 'gs')
    if mode == 'current':
        K = max(8, B//2 + 2); sizes = [1 << i for i in range(K)]; jpts = [mul(s) for s in sizes]
    else:
        K = max(8, B//2); sizes, jpts = jumps_for(W, K, 0.5)
    dpb = max(1, B//2 - 4); dpm = (1 << dpb) - 1
    half = 1 << (B//2 + 1); table = {}; total = 0; cap = 300*math.isqrt(W)
    Qc = add(Q, (Q[0], (P-Q[1]) % P) and None)  # placeholder
    c = W // 2
    Qcent = add(Q, mul((N - c) % N))            # = [secret-c]G, for GS centring
    walklen = 8*math.isqrt(W) + 20
    while total < cap:
        for herd in (0, 1):                     # 0=tame, 1=wild
            if mode == 'gs':
                a0 = rng.randrange(W//2 + 1)
                if herd == 0: pt = mul(a0); a, b = a0, 0
                else:         pt = add(Qcent, mul(a0) if a0 else None); a, b = a0, 1  # b tracks Qcent=Q-[c]G
            else:
                if herd == 0: a0 = W + rng.randrange(W); pt = mul(a0); a, b = a0, 0
                else:         a0 = rng.randrange(half); pt = add(Q, mul(a0) if a0 else None); a, b = a0, 1
            hist = []
            for _ in range(walklen):
                total += 1
                if negation:
                    pc, s = canon(pt)
                    if s == -1: a, b = (-a) % N, (-b) % N
                else:
                    pc = pt
                i = pc[0] % K
                if negation and len(hist) >= 2 and pc == hist[-2]: i = (i + 1) % K
                if negation: hist.append(pc); hist = hist[-3:]
                if (pc[0] & dpm) == 0:
                    prev = table.get(pc)
                    if prev is not None and prev[2] != herd:
                        # gs uses Qcent (b on Q-[c]G); convert: point=[a]G+[b](Q-[c]G) => coeff of Q is b, of G is a-b*c
                        if mode == 'gs':
                            r = _finish(a - b*c, b, prev[0] - prev[1]*c, prev[1], secret, Q)
                        else:
                            r = _finish(a, b, prev[0], prev[1], secret, Q)
                        if r is not None: return total, r
                    elif prev is None:
                        table[pc] = (a, b, herd)
                pt = add(pc, jpts[i]); a = (a + sizes[i]) % N
    return total, None

if __name__ == "__main__":
    import sys
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    W = 1 << B; T = int(sys.argv[2]) if len(sys.argv) > 2 else 21; sq = math.isqrt(W)
    print(f"width 2^{B} (sqrtW=2^{B//2}), {T} trials, median jumps-to-solve\n")
    base = None
    for name, mode in [("0 current (mistuned)", 'current'), ("1 tuned kangaroo", 'tuned'),
                       ("2 tuned + negation", 'neg'), ("3 Gaudry-Schost + neg", 'gs')]:
        js = []
        for t in range(T):
            r = random.Random(9000+t); secret = r.randrange(W); Q = mul(secret)
            j, ok = solve(W, secret, Q, 9000+t, mode)
            if ok: js.append(j)
        if js:
            med = statistics.median(js); base = base or med
            print(f"  {name:24s} median={int(med):>8,} ={med/sq:5.2f}xsqrtW  vs_current={base/med:5.2f}x  solved {len(js)}/{T}")
        else:
            print(f"  {name:24s} FAILED to solve/verify ({len(js)}/{T})")
