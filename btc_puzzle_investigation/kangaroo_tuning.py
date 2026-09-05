"""GAP 3 — demonstrate the kangaroo speedups the current engine leaves on the table.
(1) jump-size mistuning: current mean jump vs the van Oorschot-Wiener optimum ~0.5*sqrt(W).
(2) negation map: identify +-X -> ~sqrt(2) fewer jumps.
Two-kangaroo lambda method with distinguished points. Collision math exact int;
jump *sizing* uses floats (a solver knob, not the signal path).
"""
import random, statistics, sys
from puzzle_kangaroo_distributed import P, add, mul
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def make_jumps(K, mean_target):
    """K distinct jump sizes, linear ramp 1..~2*mean_target => average ~ mean_target."""
    sizes = [1 + (2 * mean_target * i) // max(1, K - 1) for i in range(K)]
    return sizes, [mul(s) for s in sizes]

def canon(X, negation):
    # negation map representative: the point of {X,-X} with even Y (x is shared)
    if negation and X is not None and (X[1] & 1):
        return (X[0], (P - X[1]) % P)
    return X

def kanga_solve(W, K, mean_target, dp_bits, negation=False, seed=None):
    rng = random.Random(seed)
    s = rng.randrange(W); Q = mul(s)
    sizes, jpts = make_jumps(K, max(1, mean_target))
    dp_mask = (1 << dp_bits) - 1
    half = W.bit_length() // 2
    table = {}; total = 0
    max_jumps = 400 * int(W ** 0.5)
    walklen = 8 * int(W ** 0.5) + 20
    while total < max_jumps:
        for herd in ("tame", "wild"):
            if herd == "tame":
                start = rng.randrange(W); X = mul(W + start); val = W + start
            else:
                start = rng.randrange(1 << half)
                X = add(Q, mul(start) if start else None); val = start
            seen = set()
            for _ in range(walklen):
                total += 1
                Xc = canon(X, negation)                 # step from the class representative
                if Xc in seen: break                    # fruitless-cycle escape -> restart
                seen.add(Xc)
                i = Xc[0] % K
                if (Xc[0] & dp_mask) == 0:
                    prev = table.get(Xc)
                    if prev is not None and prev[0] != herd:
                        tv, wv = (val, prev[1]) if herd == "tame" else (prev[1], val)
                        if mul((tv - wv) % N) == Q:
                            return total, ((tv - wv) % N) == s
                    elif prev is None:
                        table[Xc] = (herd, val)
                X = add(Xc, jpts[i]); val += sizes[i]    # advance from representative
    return total, None

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    W = 1 << B; K = max(8, B // 2 + 2); dp_bits = B // 2 - 4
    sqrtW = int(W ** 0.5); TRIALS = 30
    print(f"width 2^{B} (sqrtW=2^{B//2}), K={K}, dp_bits={dp_bits}, {TRIALS} trials\n")
    engine_mean = (1 << K) // K
    designs = [
        (f"current engine mean~sqrtW*{engine_mean/sqrtW:.2f}", engine_mean, False),
        ("tuned mean = sqrtW/2",                                sqrtW // 2,  False),
        ("tuned sqrtW/2 + NEGATION MAP",                        sqrtW // 2,  True),
    ]
    base = None
    for name, mean_t, neg in designs:
        js = [j for j, ok in (kanga_solve(W, K, mean_t, dp_bits, neg, seed=7000 + t)
                              for t in range(TRIALS)) if ok]
        if js:
            med = statistics.median(js); base = base or med
            print(f"  {name:34s} median jumps={int(med):>8,} ={med/sqrtW:5.2f}xsqrtW "
                  f"speedup={base/med:4.2f}x  ({len(js)}/{TRIALS})")
        else:
            print(f"  {name:34s} no solves in budget")
