r"""
du2_nonrep_deep_v1 -- push the non-representative sweep.

(a) EXHAUSTIVE on the tight absent-pairs, larger q.
(b) RANDOM with large q on all 18 absent pairs.
(c) STRUCTURE of the tight instance |S| = 1/2.

Exact rational arithmetic.  Boundary-exact (entry floors only; entry-vs-exit agreement
is re-audited on a sample).
"""
import sys, random
from fractions import Fraction as F
from itertools import combinations, product

Z8 = frozenset(range(8))
UNITS = frozenset({1, 3, 5, 7})
BAD = {(e, t): frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))
       for e in range(8) for t in range(8)}
HALF = F(1, 2)


def brk(Enon):
    pts = {F(0), F(1)}
    for e in Enon:
        for j in range(1, e):
            pts.add(F(j, e))
    return sorted(pts)


def safe_measure(Enon, audit=False, cells_out=False):
    p = brk(Enon)
    m = F(0)
    n_int = n_mis = n_sd = 0
    cells = []
    for a, b in zip(p, p[1:]):
        cin = set(); cout = set()
        for e in Enon:
            va = e * a
            fe = va.numerator // va.denominator
            cin |= BAD[(e % 8, fe % 8)]
            if audit:
                if F(fe + 1, e) < b:
                    n_int += 1
                vb = e * b
                fx = vb.numerator // vb.denominator - (1 if vb.denominator == 1 else 0)
                if fe != fx:
                    n_mis += 1
                cout |= BAD[(e % 8, fx % 8)]
        if audit and cin != cout:
            n_sd += 1
        U = Z8 - cin
        if U:
            m += b - a
            if cells_out:
                cells.append((a, b, frozenset(U)))
    return m, (n_int, n_mis, n_sd), cells


def part_a(A, Q):
    R = sorted(set(range(1, 8)) - set(A))
    best = None
    below = []
    n = 0
    for qv in product(range(Q + 1), repeat=5):
        Enon = [8 * q + r for q, r in zip(qv, R)]
        if len(set(Enon)) < 5:
            continue
        n += 1
        m, _, _ = safe_measure(Enon)
        if best is None or m < best[0]:
            best = (m, tuple(Enon))
        if m < HALF:
            below.append((m, tuple(Enon)))
    return n, best, below


def part_b(NS, QMAX, seed=20260908, mixed=False):
    rnd = random.Random(seed)
    pairs = [X for X in combinations(range(1, 8), 2) if set(X) & UNITS]
    best = None
    below = []
    audit = [0, 0, 0]
    for i in range(NS):
        A = rnd.choice(pairs)
        R = sorted(set(range(1, 8)) - set(A))
        if mixed:
            Enon = [8 * (rnd.randint(0, 3) if rnd.random() < 0.5
                         else rnd.randint(0, QMAX)) + r for r in R]
        else:
            Enon = [8 * rnd.randint(0, QMAX) + r for r in R]
        if len(set(Enon)) < 5:
            continue
        do = (i % 25 == 0)
        m, au, _ = safe_measure(Enon, audit=do)
        for j in range(3):
            audit[j] += au[j]
        if best is None or m < best[0]:
            best = (m, tuple(Enon), A)
        if m < HALF:
            below.append((m, tuple(Enon), A))
    return best, below, audit


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "a":
        A = tuple(int(c) for c in sys.argv[2].split(","))
        Q = int(sys.argv[3])
        n, best, below = part_a(A, Q)
        print(f"EXHAUSTIVE absent {A}, q in 0..{Q}: {n} admissible E_non")
        print(f"  min |S| = {best[0]} = {float(best[0]):.6f}  at {list(best[1])}")
        print(f"  instances with |S| < 1/2 : {len(below)}")
        for m, E in sorted(below)[:30]:
            print(f"     |S| = {m}  E_non = {list(E)}")
    elif mode == "b":
        NS, QMAX = int(sys.argv[2]), int(sys.argv[3])
        best, below, audit = part_b(NS, QMAX)
        print(f"RANDOM {NS} draws, q in 0..{QMAX}, all 18 absent pairs")
        print(f"  boundary audit on sampled subset: interior={audit[0]} "
              f"mismatch={audit[1]} entry/exit-setdiff={audit[2]}")
        print(f"  min |S| = {best[0]} = {float(best[0]):.6f}  at {list(best[1])} "
              f"(absent {best[2]})")
        print(f"  instances with |S| < 1/2 : {len(below)}")
        for m, E, A in sorted(below)[:30]:
            print(f"     |S| = {m} = {float(m):.6f}  E_non = {list(E)}  absent {A}")
    elif mode == "f":
        NS, QMAX = int(sys.argv[2]), int(sys.argv[3])
        best, below, audit = part_b(NS, QMAX, mixed=True)
        print(f"MIXED-q RANDOM {NS} draws (half the coords small: q<=3), q<= {QMAX}")
        print(f"  boundary audit on sampled subset: interior={audit[0]} "
              f"mismatch={audit[1]} entry/exit-setdiff={audit[2]}")
        print(f"  min |S| = {best[0]} = {float(best[0]):.6f}  at {list(best[1])} "
              f"(absent {best[2]})")
        print(f"  instances with |S| < 1/2 : {len(below)}")
        for m, E, A in sorted(below)[:30]:
            print(f"     |S| = {m} = {float(m):.6f}  E_non = {list(E)}  absent {A}")
    elif mode == "e":
        Q = int(sys.argv[2])
        pairs = [X for X in combinations(range(1, 8), 2) if set(X) & UNITS]
        gbest = None; nbelow = 0; ntot = 0
        for A in pairs:
            n, best, below = part_a(A, Q)
            ntot += n; nbelow += len(below)
            if gbest is None or best[0] < gbest[0]:
                gbest = (best[0], best[1], A)
            print(f"  absent {str(A):>7}: {n:>6} instances, min |S| = "
                  f"{str(best[0]):>16} = {float(best[0]):.6f} at {list(best[1])}"
                  f"   <1/2: {len(below)}")
        print(f"EXHAUSTIVE all 18 pairs, q in 0..{Q}: {ntot} instances, "
              f"{nbelow} with |S| < 1/2")
        print(f"  global min |S| = {gbest[0]} = {float(gbest[0]):.6f} at "
              f"{list(gbest[1])} (absent {gbest[2]})")
    elif mode == "c":
        Enon = [int(v) for v in sys.argv[2].split(",")]
        m, au, cells = safe_measure(Enon, audit=True, cells_out=True)
        print(f"E_non = {Enon}   residues {[e % 8 for e in Enon]}   |S| = {m} = {float(m):.6f}")
        print(f"boundary audit: interior={au[0]} mismatch={au[1]} entry/exit-setdiff={au[2]}")
        # merge contiguous safe cells into windows
        wins = []
        for a, b, U in cells:
            if wins and wins[-1][1] == a:
                wins[-1][1] = b; wins[-1][2].append((a, b, U))
            else:
                wins.append([a, b, [(a, b, U)]])
        print(f"{len(cells)} safe cells in {len(wins)} maximal windows")
        for lo, hi, parts in wins:
            common = frozenset.intersection(*[U for _, _, U in parts])
            print(f"  W=[{lo},{hi}) len {hi-lo} = {float(hi-lo):.6f}  cells {len(parts)}"
                  f"  common uncovered {sorted(common) if common else 'EMPTY'}")
            for a, b, U in parts:
                print(f"      [{a},{b})  U={sorted(U)}")
