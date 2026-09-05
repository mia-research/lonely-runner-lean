#!/usr/bin/env python3
"""
Handover-2 §6 Int.2 — does the exact rank-10 low-prime orthogonality decompose under
the mu3-projection into "core-rotations + flap-reflections"?

RECONSTRUCTION (flagged): the rank-10 matrix (vertical_zfr_replication Finding 1) is
Dirichlet (mu2 units). Finding 3 shows the mu6/CM structure lives in the LARGE-prime
correlation K (CM=3x Dirichlet). So I build the CM/Eisenstein analogue: rows =
characters chi_j of F_{q^2}* for INERT q (q=2 mod3, so Z[omega]/(q)=F_{q^2}, mu6 in
F_{q^2}*), columns = 10 low rational primes. "core-rotations" = mu3-invariant chars
(chi_j(omega)=1 <=> 3|j); "flap-reflections" = the reflection part (chi_j(-1)=-1,
j odd). Question: does the rank-10 orthogonality SPLIT by mu6-type (j mod 6), or is it
PRESERVED within each block?

Prediction (derived): the low primes are not related by mu6 rotation (p1/p2 not in mu6
for distinct rational primes), so each mu6-type block's Gram stays diagonal ->
orthogonality PRESERVED, NOT decomposed. Test it computationally.
Exact discrete-log in F_{q^2}; float only in the character/SVD.
"""
import numpy as np, cmath
from sympy import primerange, isprime

P0 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def Fq2_dlog(q):
    """F_{q^2} = Z[omega]/(q) for inert q (q=2 mod3). Return (order, ind dict on (a,b))."""
    def mul(A, B):
        a, b = A; c, d = B
        return ((a * c - b * d) % q, (a * d + b * c - b * d) % q)  # omega^2=-1-omega
    order = q * q - 1
    # find a generator
    elems = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]
    from sympy import factorint
    fac = list(factorint(order))
    def is_gen(g):
        return all(pow_e(g, order // pr, mul) != (1, 0) for pr in fac)
    def pow_e(g, e, mul):
        r = (1, 0); b = g
        while e:
            if e & 1: r = mul(r, b)
            b = mul(b, b); e >>= 1
        return r
    g = None
    for cand in elems:
        if is_gen(cand): g = cand; break
    ind = {}; cur = (1, 0)
    for e in range(order):
        ind[cur] = e; cur = mul(cur, g)
    return order, ind


def main():
    inert = [q for q in primerange(50, 100) if q % 3 == 2 and isprime(q)]
    print(f"Int.2 (CM/Eisenstein reconstruction): inert q (=2 mod3) in [50,100]: {inert}\n")

    # build feature matrix over all (q, non-principal j), columns = P0
    rows = []; rowtype = []  # rowtype = j mod 6 (mu6-type)
    for q in inert:
        order, ind = Fq2_dlog(q)
        inv = 1.0 / np.sqrt(order)
        idxp = [ind[(p0 % q, 0)] for p0 in P0]
        for j in range(1, order):
            row = [cmath.exp(2j * cmath.pi * jj * idxp[c] / order) * inv for c, jj in [(c, j) for c in range(len(P0))]]
            # simpler: chi_j(p0)=exp(2pi i j ind(p0)/order)
            row = [cmath.exp(2j * cmath.pi * j * idxp[c] / order) * inv for c in range(len(P0))]
            rows.append(row); rowtype.append(j % 6)
    F = np.array(rows); rowtype = np.array(rowtype)
    print(f"  feature matrix F: {F.shape}")

    def gram_report(name, sub):
        G = sub.conj().T @ sub
        ev = np.sort(np.abs(np.linalg.eigvalsh(G)))[::-1]
        offmax = np.max(np.abs(G - np.diag(np.diag(G))))
        print(f"    {name:24s}: rows={sub.shape[0]:5d}  Gram eig max/min={ev[0]/ev[-1]:.3f}  "
              f"offdiag max={offmax:.4f}  ({'ORTHOGONAL (rank-10)' if ev[0]/ev[-1] < 1.3 and offmax < 1e-6*sub.shape[0] else 'not clean'})")

    print("\n  overall + per mu6-type (j mod 6) column-Gram orthogonality:")
    gram_report("ALL characters", F)
    for r in range(6):
        gram_report(f"mu6-type j%6={r}", F[rowtype == r])
    # mu3-core (3|j) vs flap
    gram_report("mu3-CORE (3|j, rotation)", F[rowtype % 3 == 0])
    gram_report("FLAP (j%3 != 0)", F[rowtype % 3 != 0])
    gram_report("reflection-odd (j odd)", F[rowtype % 2 == 1])
    print("\n  => if every block stays ORTHOGONAL (off-diag ~0, flat spectrum), the")
    print("     rank-10 orthogonality is PRESERVED across mu3/mu6, NOT decomposed --")
    print("     the mu6 structure is not in the low-prime orthogonality (it is in the")
    print("     large-prime K, Finding 3). If a block DECOMPOSES (rank drops / off-diag")
    print("     appears), core-rotations+flap-reflections split it -- the Int.2 claim.")


if __name__ == "__main__":
    main()
