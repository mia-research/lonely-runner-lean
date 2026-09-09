r"""
rt_sweep_v1 -- targeted exhaustive sweep for (H''), run against the pre-registration
recorded in reports/n8_o_rate.md section 6.

TARGETING.  rt_lattice_v1 computes the EXACT limit of o on every resonance class of
rank <= 2 with generators of height <= R.  The maximum over all such classes is 1/4,
and BOTH known exceptions -- (1,3,5,7) and (1,11,5,7) -- lie in rank-2 classes whose
limit is exactly 1/4.  So the danger zone is not "resonant tuples" in general (the +-1
families have limit 1/6) but the rank-2 classes at the top of the limit table.  This
sweep enumerates those classes EXHAUSTIVELY (they are 2-parameter, so exhaustion to
large speeds is cheap) and, separately, the two +-1 families exhaustively by SPEED
rather than by the parameter box the previous sweep used.

DECISION RULE.  o = Fraction(p,q), q > 0.  Flag iff 3*p > q.  No float in the decision
path.  Both the `o > Fraction(1,3)` form and the `3*p > q` form are asserted equal.

ARMS
  T1  every member of every rank-2 class with limit 1/4 (height <= R), speeds <= SMAX2
  T2  the two +-1 families (rank-1, limit 1/6), EXHAUSTIVE over speeds <= SMAX1
  C4  matched control: primitive unit tuples carrying NO resonance of height <= R,
      matched 1:1 on max speed with the T1 + T2 sample, seeded

CONTROLS THAT MUST FIRE
  C1  the enumerator recovers (1,3,5,7) with o = 16/35 and (1,11,5,7) with o = 26/77
  C2  a planted target on a height-3 resonance is recovered by the class enumerator
  C3  the comparator, re-run at t = 3/10, returns a non-empty flagged set, every member
      independently re-verified by ob_core_v1.o_x

usage:  python3 rt_sweep_v1.py [R] [SMAX2] [SMAX1] [SEED]
"""
import sys, itertools, random
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce

import rt_limit_v2 as RL
from ob_fast_v1 import o_fast, audit
from ob_core_v1 import o_x

R      = int(sys.argv[1]) if len(sys.argv) > 1 else 3
SMAX2  = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
SMAX1  = int(sys.argv[3]) if len(sys.argv) > 3 else 300
SEED   = int(sys.argv[4]) if len(sys.argv) > 4 else 20260909

RHO = (1, 3, 5, 7)
THIRD = F(1, 3)
EXC = {(1, 3, 5, 7), (1, 11, 5, 7)}
DELTAS = [F(0), F(1, 100), F(1, 50), F(1, 30), F(1, 20)]


def guard(e):
    """int64 overflow guard for ob_fast_v1: it forms (4*e_rho) * pts with pts < D."""
    D = 4 * reduce(lcm, e)
    return max(4 * x for x in e) * D < 2 ** 63


def o_exact(e):
    assert guard(e), f"int64 overflow guard tripped at {e}"
    o = o_fast(e)
    p, q = o.numerator, o.denominator
    assert (3 * p > q) == (o > THIRD)
    return o


# ------------------------------------------------------- rank-2 class members
def class_members(M, smax):
    """every primitive unit 4-tuple with max speed <= smax in the saturated kernel of M."""
    B, rk = RL.kernel_basis(M)
    assert rk == 2
    idx = None
    for i in range(4):
        for j in range(i + 1, 4):
            det = B[i][0] * B[j][1] - B[i][1] * B[j][0]
            if det:
                idx = (i, j, det)
                break
        if idx:
            break
    i, j, det = idx
    alim = int(smax * (abs(B[j][1]) + abs(B[i][1])) / abs(det)) + 2
    out = []
    for a in range(-alim, alim + 1):
        # 0 < B[r][0]*a + B[r][1]*b <= smax for every r  ->  an interval in b
        lo, hi = None, None
        ok = True
        for r in range(4):
            c0, c1 = B[r][0] * a, B[r][1]
            if c1 == 0:
                if not (0 < c0 <= smax):
                    ok = False
                    break
                continue
            x1 = F(1 - c0, c1)
            x2 = F(smax - c0, c1)
            l, h = (x1, x2) if c1 > 0 else (x2, x1)
            l = -(-l.numerator // l.denominator)          # ceil
            h = h.numerator // h.denominator              # floor
            lo = l if lo is None else max(lo, l)
            hi = h if hi is None else min(hi, h)
        if not ok:
            continue
        if lo is None:
            continue
        for b in range(lo, hi + 1):
            e = tuple(B[r][0] * a + B[r][1] * b for r in range(4))
            if any(x % 8 != RHO[k] % 8 for k, x in enumerate(e)):
                continue
            if len(set(e)) != 4 or reduce(gcd, e) != 1:
                continue
            out.append(e)
    return out


def pm1_family_members(smax):
    """EXHAUSTIVE over speed: every primitive unit tuple with all speeds <= smax lying on
    e1 + e7 = e3 + e5  (family A) or  e1 + e3 = e5 + e7  (family B)."""
    Q = (smax - 1) // 8
    out = []
    for fam, f in (("A", lambda a, b, c: b + c - a),
                   ("B", lambda a, b, c: a + b - c - 1)):
        for a in range(Q + 1):
            for b in range(Q + 1):
                for c in range(Q + 1):
                    d = f(a, b, c)
                    if d < 0:
                        continue
                    e = (8 * a + 1, 8 * b + 3, 8 * c + 5, 8 * d + 7)
                    if max(e) > smax or len(set(e)) != 4:
                        continue
                    if reduce(gcd, e) != 1:
                        continue
                    out.append(e)
    return out


def has_low_resonance(e, adm):
    """any primitive resonance of height <= R.  Testing PRIMITIVE vectors suffices:
    if n is a resonance then so is n / content(n), which has no larger height."""
    for n in adm:
        if n[0] * e[0] + n[1] * e[1] + n[2] * e[2] + n[3] * e[3] == 0:
            return True
    return False


def profile(tag, tuples, top=20):
    """returns (N_exc, max, near-miss counts) and prints the required profile."""
    vals = []
    for e in tuples:
        vals.append((o_exact(e), e))
    vals.sort(reverse=True)
    exc = [(o, e) for o, e in vals if o > THIRD and e not in EXC]
    counts = []
    for d in DELTAS:
        counts.append(sum(1 for o, e in vals if o >= THIRD - d))
    print(f"\n--- {tag}: {len(tuples)} tuples")
    if not vals:
        print("    EMPTY ARM")
        return 0, None, counts, vals
    print(f"    max o = {vals[0][0]} = {float(vals[0][0]):.8f} at {vals[0][1]}")
    print(f"    N_exc (o > 1/3, excluding the two known exceptions) = {len(exc)}")
    print("    near-miss counts  #{o >= 1/3 - d} for d = 0, 1/100, 1/50, 1/30, 1/20:")
    print(f"        {counts}")
    print(f"    top {min(top,len(vals))} by o:")
    for o, e in vals[:top]:
        print(f"        {str(e):>26}  o = {str(o):>22} = {float(o):.8f}"
              f"{'   *** EXCEEDS 1/3' if o > THIRD else ''}")
    if exc:
        print("    *** TUPLES ABOVE 1/3 OUTSIDE THE EXCEPTION LIST:")
        for o, e in exc:
            print(f"        {e}  o = {o} = {float(o):.8f}")
    return len(exc), vals[0], counts, vals


def do_audit(tag, tuples, rng, nsample=200):
    sample = list(tuples)
    if len(sample) > nsample:
        sample = rng.sample(sample, nsample)
    bad = 0
    for e in sample:
        cells, n_int, n_mis = audit(e)
        if n_int or n_mis:
            bad += 1
            print(f"    BOUNDARY AUDIT FAILURE at {e}: {(cells, n_int, n_mis)}")
    print(f"    [{tag}] boundary audit on {len(sample)} tuples: failures {bad}")
    return bad


if __name__ == "__main__":
    rng = random.Random(SEED)
    print("=" * 80)
    print(f"rt_sweep_v1   R={R}  SMAX2={SMAX2}  SMAX1={SMAX1}  seed={SEED}")
    print("=" * 80)

    # ---------------------------------------------------------------- C1
    print("\n[C1] enumerator-alive control -- must fire")
    ok1 = (o_exact((1, 3, 5, 7)) == F(16, 35)) and (o_exact((1, 11, 5, 7)) == F(26, 77))
    print(f"    o(1,3,5,7)  = {o_exact((1,3,5,7))}  expected 16/35")
    print(f"    o(1,11,5,7) = {o_exact((1,11,5,7))}  expected 26/77")
    print(f"    C1 fires: {ok1}")

    # -------------------------------------------- rank-2 classes at the top
    print(f"\nenumerating rank-2 classes of height <= {R} and their exact limits ...")
    adm = [v for v in itertools.product(range(-R, R + 1), repeat=4) if RL.admissible(v)]
    seen = {}
    for i in range(len(adm)):
        for j in range(i + 1, len(adm)):
            M = [list(adm[i]), list(adm[j])]
            B, rk = RL.kernel_basis(M)
            if rk != 2:
                continue
            k, _ = RL.lattice_key(M)
            if k in seen:
                continue
            if not RL.witnesses(M, PMAX=24, want=1):
                continue
            seen[k] = (M, RL.rank2_limit(M))
    lim_max = max(L for _, L in seen.values())
    top = {k: v for k, v in seen.items() if v[1] == lim_max}
    print(f"    realisable rank-2 classes: {len(seen)};  max limit = {lim_max}"
          f" = {float(lim_max):.6f};  classes attaining it: {len(top)}")

    # ---------------------------------------------------------------- C2
    print("\n[C2] planted-target control -- must fire")
    hmax = max(max(abs(x) for x in v) for v in adm)
    cand = sorted(v for v in adm if max(abs(x) for x in v) == hmax)
    plant_n = cand[0]                       # deterministic, height = R
    ws = RL.witnesses([list(plant_n)], PMAX=24, want=1)
    print(f"    planted resonance {plant_n}, witness tuple {ws}")
    print(f"    C2 fires: {bool(ws)}")

    # ---------------------------------------------------------------- T1
    T1 = set()
    for k, (M, L) in top.items():
        mem = class_members(M, SMAX2)
        T1.update(mem)
    T1 = sorted(T1)
    T1 = [e for e in T1 if guard(e)]
    T1CAP = 250000
    if len(T1) > T1CAP:
        step = len(T1) // T1CAP + 1
        keep = set(T1[::step]) | {(1, 3, 5, 7), (1, 11, 5, 7)} & set(T1)
        print(f"    T1 has {len(T1)} members; deterministically thinned by step {step} "
              f"to {len(keep)} (memory cap).  THE T1 ARM IS THEN NOT EXHAUSTIVE.")
        T1 = sorted(keep)
    n1, mx1, c1, v1 = profile(f"T1  rank-2 classes with limit {lim_max}, speeds <= {SMAX2}", T1)
    do_audit("T1", [e for o, e in v1[:20]] + [e for o, e in v1 if o >= THIRD - F(1, 20)], rng)
    do_audit("T1-random", T1, rng)

    # ---------------------------------------------------------------- T2
    T2 = pm1_family_members(SMAX1)
    T2 = [e for e in T2 if guard(e)]
    n2, mx2, c2, v2 = profile(f"T2  +-1 families A and B, EXHAUSTIVE over speeds <= {SMAX1}", T2)
    do_audit("T2", [e for o, e in v2[:20]] + [e for o, e in v2 if o >= THIRD - F(1, 20)], rng)

    # ---------------------------------------------------------------- C4
    print("\nbuilding the matched non-resonant control arm (1:1 on max speed) ...")
    treat = T1 + T2
    want = {}
    for e in treat:
        want[max(e)] = want.get(max(e), 0) + 1
    CAPC = 40000
    scale = min(1.0, CAPC / max(1, len(treat)))
    C4 = []
    inexact = 0
    for s, cnt in sorted(want.items()):
        need = max(1, int(round(cnt * scale))) if cnt else 0
        got = tries = 0
        while got < need and tries < 200 * need + 500:
            tries += 1
            # force the max: exactly one rho can have e_rho = s, namely s = rho mod 8
            star = [k for k in range(4) if s % 8 == RHO[k] % 8]
            e = [8 * rng.randrange(0, s // 8 + 1) + r for r in RHO]
            if star:
                e[star[0]] = s
            e = tuple(e)
            if len(set(e)) != 4 or reduce(gcd, e) != 1 or max(e) > s:
                continue
            if has_low_resonance(e, adm):
                continue
            if max(e) != s:
                inexact += 1
            C4.append(e)
            got += 1
    print(f"    control arm size {len(C4)} (subsampled at rate {scale:.4f}),"
          f" treatment size {len(treat)}, inexact max-speed matches {inexact}")
    n4, mx4, c4, v4 = profile("C4  matched non-resonant control", C4)

    # ---------------------------------------------------------------- C3
    print("\n[C3] comparator control at the lowered threshold t = 3/10 -- must fire")
    flagged = [(o, e) for o, e in (v1 + v2) if o > F(3, 10)]
    print(f"    flagged at t = 3/10: {len(flagged)}")
    reverify = 0
    for o, e in flagged[:12]:
        if o_x(e) == o:
            reverify += 1
    print(f"    independently re-verified by ob_core_v1.o_x: {reverify} of "
          f"{min(12,len(flagged))} checked")
    print(f"    C3 fires: {len(flagged) > 0 and reverify == min(12, len(flagged))}")

    # ---------------------------------------------------------------- verdict
    print("\n" + "=" * 80)
    print("RESULT")
    print("=" * 80)
    print(f"  N_exc(T1) = {n1}    N_exc(T2) = {n2}    N_exc(C4) = {n4}")
    print(f"  max o : T1 {mx1}   T2 {mx2}   C4 {mx4}")
    print(f"  near-miss counts (d = 0, 1/100, 1/50, 1/30, 1/20)")
    print(f"      T1 {c1}\n      T2 {c2}\n      C4 {c4}")
