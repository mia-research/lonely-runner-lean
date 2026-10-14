"""
Does the sweep used across the nN work actually follow the Boundary Set Method?

The sweeps decide "is there a clear instant" from a CANDIDATE set: the window's left end
plus every zone's RIGHT endpoint. This checks that candidate set against a full BSM
evaluation -- every entry and exit, and then the open cells separately at their midpoints.

The midpoint probe is the step the register warns against (it assumes the breakpoint list is
complete). It is used HERE, and only here, as the test OF that assumption -- if a cell
interior is ever clear while every boundary point is blocked, the candidate set is
incomplete and every sweep built on it is wrong.

Result on 12,800 runner-instances: 0 disagreements, 0 cells clear on their own.

The completeness also has a proof, and the test confirms it rather than replacing it: the
clear set is the complement of finitely many OPEN intervals inside a CLOSED one, so it is
closed, so every component has a left endpoint, and that endpoint is either the window's
left end or some zone's right endpoint.
"""
import random
from fractions import Fraction as F

def zones(ds, n):
    m = min(ds)
    S = [F(d, m) for d in ds if d != m]
    lo, hi = F(1, n), F(n - 1, n)
    Z = []
    for s in S:
        k = 0
        while True:
            a = F(n * k - 1, n) / s
            if a > hi:
                break
            b = F(n * k + 1, n) / s
            if b > lo:
                Z.append((a, b))
            k += 1
    return Z, lo, hi

def candidate_sweep(ds, n):
    Z, lo, hi = zones(ds, n)
    Z.sort()
    cands = sorted({lo} | {b for _, b in Z if lo <= b <= hi})
    ptr, maxb = 0, None
    for u in cands:
        while ptr < len(Z) and Z[ptr][0] < u:
            bb = Z[ptr][1]
            if maxb is None or bb > maxb:
                maxb = bb
            ptr += 1
        if maxb is None or not (maxb > u):
            return True
    return False

def full_bsm(ds, n):
    Z, lo, hi = zones(ds, n)
    bps = sorted({lo, hi} | {x for a, b in Z for x in (a, b) if lo <= x <= hi})
    clear = lambda u: not any(a < u < b for a, b in Z)
    for u in bps:
        if clear(u):
            return True, 'boundary'
    for i in range(len(bps) - 1):
        if clear((bps[i] + bps[i + 1]) / 2):
            return True, 'cell-interior'
    return False, None

if __name__ == "__main__":
    random.seed(99)
    tot = dis = cell_only = 0
    for span in (30, 80, 200, 600):
        for _ in range(400):
            V = sorted(random.sample(range(1, span + 1), 8))
            for i in range(8):
                ds = [abs(V[i] - V[j]) for j in range(8) if j != i]
                tot += 1
                a = candidate_sweep(ds, 8)
                b, where = full_bsm(ds, 8)
                if a != b:
                    dis += 1
                if b and where == 'cell-interior' and not a:
                    cell_only += 1
    print(f"instances {tot}   disagreements {dis}   clear-only-in-a-cell {cell_only}")
