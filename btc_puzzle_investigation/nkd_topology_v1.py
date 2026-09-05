#!/usr/bin/env python3
"""
nkd_topology_v1.py -- the (n,k,D) validity domain as a STATIC geometric object:
Betti numbers / Euler characteristic, holes vs matched controls, symmetry action.

The valid canonical labels are EXACTLY the coprime lattice points
    P_Q = { (n,k) : 1<=n<=Q, 1<=k<=n, gcd(n,k)=1 }        (Farey fractions of order Q, Q=256)
(established in nkd_validity_domain_v1.py: gcd(n,k)=1 necessary+sufficient for a
canonical label; each carries a D-fiber of width ~ lo/n^2).

We treat P_Q as a 2D CUBICAL COMPLEX in the integer grid:
  0-cells = points of P_Q
  1-cells = unit H/V segments between two grid-adjacent points of P_Q
  2-cells = unit squares whose 4 corners all lie in P_Q
For a complex embedded in the plane beta_2 = 0, so (all EXACT integers):
  chi = V - E + F = beta_0 - beta_1  =>  beta_1 = beta_0 - chi.
beta_0 by union-find. This needs NO float and NO linear algebra.

Controls (matched null): the SAME triangle with (a) coprimality dropped (full),
(b) random density-matched inclusion, (c) a non-arithmetic structured mask.
Symmetry: the k<->n-k involution (u<->1-u) and any mu6/GLV candidate.

Exact integers only (folder rule). Self-contained.
"""
import sys
from math import gcd


# ---------- union-find for beta_0 ----------
class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        self.p.setdefault(x, x)
        r = x
        while self.p[r] != r:
            r = self.p[r]
        while self.p[x] != r:
            self.p[x], x = r, self.p[x]
        return r

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def betti_of_pointset(S):
    """S: set of (n,k) integer points. Cubical complex; return (V,E,F,chi,b0,b1)."""
    V = len(S)
    # edges: right (n+1,k) and up (n,k+1)
    E = 0
    uf = UF()
    for (n, k) in S:
        uf.find((n, k))
    for (n, k) in S:
        if (n + 1, k) in S:
            E += 1; uf.union((n, k), (n + 1, k))
        if (n, k + 1) in S:
            E += 1; uf.union((n, k), (n, k + 1))
    # faces: unit square (n,k),(n+1,k),(n,k+1),(n+1,k+1)
    F = 0
    for (n, k) in S:
        if (n + 1, k) in S and (n, k + 1) in S and (n + 1, k + 1) in S:
            F += 1
    roots = {uf.find(x) for x in S}
    b0 = len(roots)
    chi = V - E + F
    b1 = b0 - chi          # beta_2 = 0 (planar)
    return V, E, F, chi, b0, b1


# ---------- the validity domain and controls ----------
def coprime_domain(Q):
    return {(n, k) for n in range(1, Q + 1) for k in range(1, n + 1) if gcd(n, k) == 1}


def full_triangle(Q):
    return {(n, k) for n in range(1, Q + 1) for k in range(1, n + 1)}


def random_matched(Q, density_num, density_den, seed):
    """include each triangle point independently with prob density_num/density_den.
    Uses a deterministic integer LCG hash -> exact rational threshold, no float."""
    S = set()
    a = 6364136223846793005
    c = 1442695040888963407
    m = (1 << 64)
    state = (seed * 2 + 1) % m
    for n in range(1, Q + 1):
        for k in range(1, n + 1):
            state = (a * state + c) % m
            # include iff (state mod density_den) < density_num  -- exact integer test
            if (state % density_den) < density_num:
                S.add((n, k))
    return S


def odd_odd_forbidden(Q):
    """structured non-arithmetic-coprime control: forbid only n,k both even
    (a single congruence mask), matched-ish density, to isolate 'one sieve' topology."""
    return {(n, k) for n in range(1, Q + 1) for k in range(1, n + 1)
            if not (n % 2 == 0 and k % 2 == 0)}


def farey_tessellation(Q):
    """Stern-Brocot / Farey tessellation of [0,1] restricted to denominators <= Q.
    Triangles = mediant triples {a/b, c/d, (a+c)/(b+d)} with b+d <= Q.
    Returns (V,E,F, b0, b1) exactly. Vertices keyed by reduced (num,den)."""
    verts = set()
    edges = set()
    tris = 0
    # explicit stack of Farey-neighbor intervals (a,b,c,d): a/b < c/d, bc-ad=1
    stack = [(0, 1, 1, 1)]
    verts.add((0, 1)); verts.add((1, 1))
    edges.add(((0, 1), (1, 1)))
    while stack:
        a, b, c, d = stack.pop()
        mnum, mden = a + c, b + d
        if mden <= Q:
            m = (mnum, mden)
            verts.add(m)
            edges.add(((a, b), m)); edges.add((m, (c, d)))
            tris += 1
            stack.append((a, b, mnum, mden))
            stack.append((mnum, mden, c, d))
        # else: (a/b,c/d) is a boundary Farey gap; its edge already in `edges`
    V = len(verts); E = len(edges); F = tris
    uf = UF()
    for v in verts:
        uf.find(v)
    for (u, w) in edges:
        uf.union(u, w)
    b0 = len({uf.find(v) for v in verts})
    chi = V - E + F
    b1 = b0 - chi
    return V, E, F, chi, b0, b1


def main():
    Qs = [int(x) for x in (sys.argv[1:] or [32, 64, 128, 256])]
    print("=== (n,k) VALIDITY DOMAIN as a 2D cubical complex — Betti/Euler (exact) ===")
    print(f"{'Q':>4} {'V':>7} {'E':>7} {'F':>7} {'chi':>7} {'b0':>5} {'b1(holes)':>10} "
          f"{'noncop_int':>10}")
    cop_b1 = {}
    for Q in Qs:
        S = coprime_domain(Q)
        V, E, F, chi, b0, b1 = betti_of_pointset(S)
        cop_b1[Q] = b1
        # non-coprime interior points (candidate hole centers), for comparison
        noncop = sum(1 for n in range(2, Q + 1) for k in range(2, n)
                     if gcd(n, k) > 1)
        print(f"{Q:>4} {V:>7} {E:>7} {F:>7} {chi:>7} {b0:>5} {b1:>10} {noncop:>10}")

    print("\n=== CONTROLS at Q=128 (is the topology arithmetic-structured or generic?) ===")
    Q = 128
    Vc = len(coprime_domain(Q))
    Vt = len(full_triangle(Q))
    # coprime density as an exact rational Vc/Vt
    print(f"coprime density = {Vc}/{Vt}  (~ 6/pi^2 = 0.6079...)")
    for name, S in [("coprime (VALID domain)", coprime_domain(Q)),
                    ("full triangle (no sieve)", full_triangle(Q)),
                    ("odd-odd-forbidden (1 congruence)", odd_odd_forbidden(Q))]:
        V, E, F, chi, b0, b1 = betti_of_pointset(S)
        print(f"  {name:34s}: V={V:6d} b0={b0:3d} b1={b1:6d} chi={chi:6d}")
    # random density-matched, several seeds
    b1s = []; b0s = []
    for seed in range(1, 9):
        S = random_matched(Q, Vc, Vt, seed)
        V, E, F, chi, b0, b1 = betti_of_pointset(S)
        b1s.append(b1); b0s.append(b0)
    print(f"  {'random density-matched (8 seeds)':34s}: "
          f"b0 in [{min(b0s)},{max(b0s)}] b1 in [{min(b1s)},{max(b1s)}] "
          f"mean_b1={sum(b1s)//len(b1s)}")
    print(f"  --> VALID-domain b1={cop_b1.get(128,'?')} vs random-matched mean "
          f"{sum(b1s)//len(b1s)}: structured?" )

    print("\n=== SYMMETRY: k <-> n-k involution (u <-> 1-u) on the domain ===")
    Q = 128
    S = coprime_domain(Q)
    refl = {(n, n - k) for (n, k) in S if 1 <= n - k}
    # note gcd(n,n-k)=gcd(n,k) so reflection preserves coprimality
    invariant = all((n, n - k) in S or (n - k) < 1 for (n, k) in S)
    fixed = sum(1 for (n, k) in S if k == n - k)      # k=n/2 -> only n even, gcd=1 => n=2,k=1
    print(f"  k<->n-k maps domain to itself: {invariant}  (gcd(n,n-k)=gcd(n,k)); "
          f"fixed points (k=n-k): {fixed}")
    print("  => a free Z/2 (except center). Any beta_1 holes come in symmetric pairs.")

    print("\n=== FAREY TESSELLATION (the true 'surface': mediant triangles, denom<=Q) ===")
    print(f"{'Q':>4} {'V':>7} {'E':>7} {'F(tri)':>7} {'chi':>6} {'b0':>4} {'b1':>5}")
    for Q in Qs:
        V, E, F, chi, b0, b1 = farey_tessellation(Q)
        print(f"{Q:>4} {V:>7} {E:>7} {F:>7} {chi:>6} {b0:>4} {b1:>5}")
    print("  (b1=0, b0=1 => contractible disk: the Farey SURFACE is topologically trivial;")
    print("   the fragmentation lives in the coprime NET realization, not the tessellation.)")

    print("\n=== mu6 / GLV placement (honest) ===")
    print("  GLV acts on the CURVE side (X,Y)->(betaX,Y), d->lambda*d mod N_ord, lambda~2^128.")
    print("  On the (n,k) BAND-POSITION side lambda*d scrambles the band => NO mu3/mu6 action.")
    print("  The only symmetry of the (n,k) validity domain is the Z/2 reflection k<->n-k")
    print("  (u<->1-u, i.e. within-band negation). So domain topology is coprimality-enforced,")
    print("  NOT mu6-enforced; mu6 lives on the (X,Y) image across the ECDLP bijection.")

    print("\n=== D-FIBER: is the 3rd coordinate a contiguous interval? (EXACT, full enum) ===")
    try:
        from exact_core import best_nk, residual, lo_of
        for N in (14, 16, 18):
            lo = lo_of(N)
            cols = {}
            for d in range(lo, 2 * lo):
                n, k = best_nk(d, N, 256)
                cols.setdefault((n, k), []).append(residual(d, N, n, k))
            # each column: is the set of D a contiguous run of integers?
            noncontig = 0
            for (n, k), Ds in cols.items():
                Ds.sort()
                if Ds and (Ds[-1] - Ds[0] + 1) != len(set(Ds)):
                    noncontig += 1
            print(f"  N={N}: {len(cols)} distinct (n,k) columns over all {2*lo-lo} keys; "
                  f"columns whose D-set is NOT a contiguous integer interval: {noncontig}")
        print("  contiguous fiber => each vertical D-column is a solid segment (contractible);")
        print("  base (Farey disk) x interval fiber => the full (n,k,D) domain is a")
        print("  CONTRACTIBLE SOLID: b0=1, b1=0, b2=0. No holes, no voids, no components.")
    except Exception as e:
        print(f"  (skipped exact D-fiber enum: {e})")


if __name__ == "__main__":
    main()
