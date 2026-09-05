#!/usr/bin/env python3
"""interval_sumobject_v1.py -- ITEM 3: the two readouts of the interval channel that were never run.

NEXT_SESSION_PROMPT_2026-08-01_v2.md Sec C:
  C.1  the swap-invariant SUM object x(P_i + P_j).  ANALYSIS_diffset_readout_parity_void_v1.md
       proves that on a NEGATION-CLOSED index set (field differences) every odd character is
       ill-posed unordered / identically zero symmetrized, so chi_3 is the only readout there.
       The SUM set is swap-invariant, so the FULL chi_2/chi_3/chi_6 family is legal.  NEVER RUN.
  C.2  chi_2 and chi_6 on the GROUP-LAW difference.  Also legal -- x(-Q) = x(Q) removes the sign
       ambiguity -- and never read, because interval_multireadout_v3.py printed them with a
       [parity-void] tag that the same analysis file's SCOPE CORRECTION shows is wrong for the
       group arm.  The numbers were computed and discarded.

Both are exactly x([d_i +- d_j]G): the sum object is the scalar SUMSET, the difference object the
scalar DIFFERENCE SET, mapped through d -> x([d]G) and read by a mu_6 character.

STANDING REPAIRS APPLIED (from the record):
  * C-NEG must be n >= 20 independent draws, not one (a single draw false-alarms 5% of the time).
  * exact integer statistics; percentiles by integer rank, never a float threshold.
  * readout parity x index-set parity checked BEFORE running (done above: SUM is swap-invariant,
    group DIFF has x(-Q)=x(Q); both admit all three readouts).
  * plant must fire; GLV closure reported per object per readout rather than assumed.
"""

import sys
import time
from itertools import combinations
from random import Random

sys.path.insert(0, ".")
from interval_multireadout_v3 import (P, N, GX, GY, BETA, mu6, jadd, jneg, jmul,
                                      batch_x, stats, counts_of, group_classes)


def sum_classes(pts):
    """mu_6 classes of x(P_i + P_j), i<j -- the swap-invariant SUM object."""
    s = [jadd(pts[i], pts[j]) for i, j in combinations(range(len(pts)), 2)]
    s = [q for q in s if q[2] != 0]
    return [v for v in (mu6(x) for x in batch_x(s)) if v is not None]


def pool_pts(n, rng):
    out = []
    while len(out) < n:
        x = rng.randrange(0, P)
        r = (x*x % P*x + 7) % P
        if pow(r, (P - 1)//2, P) != 1:
            continue
        out.append((x, pow(r, (P + 1)//4, P), 1))
    return out


def pool_table(pool, mode):
    """mu_6 class of the SUM (or group DIFFERENCE) for every pool pair, computed once."""
    n = len(pool)
    T = [[None]*n for _ in range(n)]
    idx = []
    q = []
    for i in range(n):
        for j in range(i + 1, n):
            r = jadd(pool[i], pool[j]) if mode == "sum" else jadd(pool[i], jneg(pool[j]))
            if r[2] == 0:
                continue
            idx.append((i, j))
            q.append(r)
    for (i, j), x in zip(idx, batch_x(q)):
        v = mu6(x)
        T[i][j] = T[j][i] = v
    return T


def counts_from_table(T, sel):
    c = [0]*6
    for a in range(len(sel)):
        for b in range(a + 1, len(sel)):
            v = T[sel[a]][sel[b]]
            if v is not None:
                c[v] += 1
    return c


def plant_indices(T, M, n, rng, target=0, scan=250):
    cand = list(range(n))
    rng.shuffle(cand)
    out = [cand.pop()]
    while len(out) < M and cand:
        bi, bh = 0, -1
        for i, qq in enumerate(cand[:scan]):
            row = T[qq]
            h = sum(1 for z in out if row[z] == target)
            if h > bh:
                bi, bh = i, h
        out.append(cand.pop(bi))
    return out


def glv_set(M, pool):
    out = []
    for (x, y, _) in pool:
        if len(out) + 3 > M:
            break
        out += [(x, y, 1), (BETA*x % P, y, 1), (BETA*BETA % P*x % P, y, 1)]
    return out


def pct_rank(sorted_vals, v):
    """integer-rank percentile: how many null draws lie strictly below v."""
    return sum(1 for z in sorted_vals if z < v), len(sorted_vals)


def run(mode, M, R, NP, rng, label):
    t0 = time.time()
    print("\n" + "=" * 84)
    print("%s   mode=%s  M=%d  R=%d  pool=%d" % (label, mode, M, R, NP))
    print("=" * 84, flush=True)
    pool = pool_pts(NP, rng)
    T = pool_table(pool, mode)
    print("  pool table built [%ds]" % (time.time() - t0), flush=True)
    idx = list(range(NP))
    nl = [stats(counts_from_table(T, rng.sample(idx, M))) for _ in range(R)]
    cols = list(zip(*nl))
    q = {}
    for i, nm in enumerate(("E2", "E3", "E6")):
        s = sorted(cols[i])
        q[nm] = s
        print("  null %s: median=%d  95th=%d  99th=%d"
              % (nm, s[R//2], s[(95*R)//100], s[(99*R)//100]), flush=True)

    def ro(pts):
        return stats(counts_of(sum_classes(pts) if mode == "sum" else group_classes(pts)))

    def line(tag, e):
        out = []
        for i, nm in enumerate(("E2", "E3", "E6")):
            below, tot = pct_rank(q[nm], e[i])
            fire = "FIRE" if e[i] >= q[nm][(99*R)//100] else ""
            out.append("%s=%-12d (%3d/%d)%s" % (nm, e[i], below, tot, fire))
        print("   %-10s %s" % (tag, "  ".join(out)), flush=True)

    print("  -- controls --", flush=True)
    e = stats(counts_from_table(T, plant_indices(T, M, NP, rng)))
    plant_ok = e[1] >= q["E3"][(99*R)//100] or e[0] >= q["E2"][(99*R)//100]
    line("C-PLANT", e)
    eg = ro(glv_set(min(M, 90), pool))
    line("C-GLV", eg)
    print("        GLV forcing: E2==0 %s | E3==0 %s | E6==0 %s"
          % (eg[0] == 0, eg[1] == 0, eg[2] == 0), flush=True)
    # C-NEG: >= 20 independent draws (standing repair), report how many exceed the 95th/99th
    neg95 = neg99 = 0
    NDR = 20
    for _ in range(NDR):
        e = ro([jmul(rng.randrange(1, N)) for _ in range(M)])
        for i, nm in enumerate(("E2", "E3", "E6")):
            if e[i] >= q[nm][(99*R)//100]:
                neg99 += 1
            elif e[i] >= q[nm][(95*R)//100]:
                neg95 += 1
    print("   C-NEG      %d draws x 3 readouts = %d cells | above 95th: %d (expect ~3) | above 99th: %d (expect ~0.6)"
          % (NDR, 3*NDR, neg95, neg99), flush=True)
    if not plant_ok:
        print("   F-VOID: plant did not fire -- no arm number is read.", flush=True)
        return
    print("  -- arms (scalars drawn from the dyadic interval [2^(k-1), 2^k)) --", flush=True)
    for k in (40, 64, 96, 128, 135, 160, 200):
        lo, hi = 2**(k - 1), 2**k
        e = ro([jmul(rng.randrange(lo, hi)) for _ in range(M)])
        line("k=%d" % k, e)
    print("  [%ds total]" % (time.time() - t0), flush=True)


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 96
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    NP = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    rng = Random(20260801)
    run("sum", M, R, NP, rng,
        "C.1  SWAP-INVARIANT SUM OBJECT  x(P_i + P_j)  -- full chi_2/chi_3/chi_6 legal, NEVER RUN")
    run("group", M, R, NP, rng,
        "C.2  GROUP-LAW DIFFERENCE  x(P_i - P_j)  -- chi_2/chi_6 legal, never read ([parity-void] tag was wrong)")
