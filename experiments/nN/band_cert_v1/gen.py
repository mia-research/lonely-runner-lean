"""Search (floating point) for a nested-partition certificate.  NO decision is taken here:
every certificate produced is re-verified in exact arithmetic by verify.py.

Tree format: a node for level L (6..2) is a list of cells [(a, b, sub)], a partition of the
level-L range into consecutive closed intervals; `sub` is the node for level L-1 (range [1,b]),
or None when L == 2 (the level-1 coordinate is then settled by the exact bad-set criterion).
All endpoints are dyadic rationals, stored as floats (exactly representable)."""
import sys, math, pickle, time
from multiprocessing import Pool
import proto
from proto import TS, last_ok

MINW = 2.0 ** -int(sys.argv[4]) if len(sys.argv) > 4 else 2.0 ** -14

def cover(S, L, a, b):
    """Return list of cells partitioning [a,b] at level L, or None."""
    S2 = TS(S, a, b)
    if S2:
        if L == 2:
            if last_ok(S2, b):
                return [(a, b, None)]
        else:
            sub = cover(S2, L - 1, 1.0, b)
            if sub is not None:
                return [(a, b, sub)]
    if b - a <= MINW:
        return None
    m = (a + b) / 2
    left = cover(S, L, a, m)
    if left is None:
        return None
    right = cover(S, L, m, b)
    if right is None:
        return None
    return left + right

def job(args):
    a, b, Rhi = args
    S0 = [(1.0, 7.0), (9.0, Rhi)]
    t = time.time()
    tree = cover(S0, 6, a, b)
    return (a, b, tree, time.time() - t)

def count(node):
    if node is None: return 0
    return sum(1 + count(sub) for (_, _, sub) in node)

if __name__ == "__main__":
    Rhi = float(sys.argv[1]); ncell = int(sys.argv[2]); out = sys.argv[3]
    w = 2.0 / ncell
    cells = [(7.0 + i * w, 7.0 + (i + 1) * w, Rhi) for i in range(ncell)]
    with Pool(10) as p:
        res = p.map(job, cells, chunksize=1)
    fails = [(a, b) for a, b, t, _ in res if t is None]
    print("top cells:", ncell, "failed:", fails)
    tot = sum(count(t) for _, _, t, _ in res if t is not None)
    print("certificate cells (all levels):", tot)
    pickle.dump({"Rhi": Rhi, "top": [(a, b, t) for a, b, t, _ in res]}, open(out, "wb"))
