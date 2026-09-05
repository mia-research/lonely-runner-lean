#!/usr/bin/env python3
"""
Is the ~2.7% inter-coordinate coupling in C_T (deviation from the tensor square
C_1(x)C_1) UNIVERSAL (a geometric constant) or orbit/generator-specific? Compute
max|C_T - C_1(x)C_2| for several generators on p=100003 and across a few primes
p=1(mod3). ~constant -> universal geometric coupling; varying -> orbit-specific.
"""
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}; I3 = {-1: 0, 0: 1, 1: 2}


def setup(p):
    R1, R2 = reduced_basis(p); DET = R1[0] * R2[1] - R1[1] * R2[0]

    def add_c(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    def eis(X):
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def state(z1, z2):
        sx, sy = z1[0] + z2[0], z1[1] + z2[1]
        c1 = rdiv(sx * R2[1] - sy * R2[0], DET); c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
        return (c1, c2)
    return add_c, eis, state


def dev_for(seq):
    Cj = np.zeros((9, 9)); C1 = np.zeros((3, 3)); C2 = np.zeros((3, 3))
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9:
            Cj[I9[a], I9[b]] += 1; C1[I3[a[0]], I3[b[0]]] += 1; C2[I3[a[1]], I3[b[1]]] += 1
    Tj = Cj / Cj.sum(1, keepdims=True); T1 = C1 / C1.sum(1, keepdims=True); T2 = C2 / C2.sum(1, keepdims=True)
    Tf = np.array([[T1[I3[i], I3[k]] * T2[I3[j], I3[l]] for (k, l) in S9] for (i, j) in S9])
    e1 = sorted((abs(e) for e in np.linalg.eigvals(T1)), reverse=True)
    return np.max(np.abs(Tj - Tf)), e1


def gen_of(p):
    for x in range(1, p):
        if pow((x * x * x + 7) % p, (p - 1) // 2, p) == 1:
            y = sqrt_mod((x * x * x + 7) % p, p)
            if y: return (x, int(y))
    return None


def main():
    import random
    rng = random.Random(1)
    # p=100003: several generators (steps H = [h]G)
    p = 100003
    addc, eis, state = setup(p)
    G = gen_of(p); pts = [None, G]; cur = G
    while True:
        cur = addc(cur, G)
        if cur is None: break
        pts.append(cur)
    nn = len(pts) - 1
    zx = [None] + [eis(pts[k][0]) for k in range(1, nn + 1)]
    print(f"p={p}: C_T tensor-factorization deviation across generators:")
    devs = []
    for _ in range(6):
        h = rng.randrange(2, nn); start = rng.randrange(1, nn)
        seq = []; j = start
        for _ in range(50000):
            seq.append(j); j = j + h
            if j > nn: j -= nn
        st = [state(zx[seq[t]], zx[seq[t + 1]]) for t in range(len(seq) - 1)]
        d, e1 = dev_for(st); devs.append(d)
        print(f"    step h~{h:6d}: dev={d:.4f}  C_1 eigs={[f'{a:.3f}' for a in e1]}")
    print(f"  => generator spread: {min(devs):.4f}..{max(devs):.4f}")

    # a few other primes (full group, G)
    print("\nacross primes p=1(mod3) (full G-orbit):")
    cnt = 0; q = 4000
    while cnt < 4 and q < 20000:
        q += 1
        if q % 3 == 1 and isprime(q):
            ac, ei, stt = setup(q)
            g = gen_of(q)
            if g is None: continue
            pp = [None, g]; c = g
            ok = True
            while True:
                c = ac(c, g)
                if c is None: break
                pp.append(c)
                if len(pp) > q + 5: ok = False; break
            if not ok: continue
            m = len(pp) - 1
            zz = [None] + [ei(pp[k][0]) for k in range(1, m + 1)]
            sq = [stt(zz[k], zz[k + 1]) for k in range(1, m)]
            d, e1 = dev_for(sq)
            print(f"    p={q:6d} (n={m}): dev={d:.4f}  C_1 eigs={[f'{a:.3f}' for a in e1]}")
            cnt += 1
    print("\n  ~constant dev across generators & primes => universal geometric coupling;")
    print("  varying => orbit/prime-specific.")


if __name__ == "__main__":
    main()
