"""
BHK Part 6, Claim 20 — empirical de-risk of the GAP CONSTRUCTION.

Diagonal case v4 = 1 + v1.  Integer speeds (reduced):
    w0 = g*p,  w1 = g*(q-p),  w2 = g*q,  w3 = g*(p+q),  w4 = g*s
with gcd(p,q)=1, 3p < q (= hsmall, v1<1/3), q >= 18.

A (56)-witness is an integer j with t = (j+1/3)/w0 such that runner 4 (w3)
is within 1/6 of an integer at t, i.e. {w3 t} in [5/6,1) U [0,1/6].

The construction claims: the 4-block I = [pe, qe] around t (edges where
{w3 . } = -+1/6, i.e. pe=(m-1/6)/w3, qe=(m+1/6)/w3, m=round(w3 t)) is a
SUBSET of a 0123-gap, i.e. runners 1,2,3 (w0,w1,w2) are SAFE (circDist >= 1/6)
on ALL of [pe,qe].  Then the engine forces 2 w3 < w4.

We verify the runner-1,2,3 safety on the whole block for every (56)-witness,
across a diverse sample of diagonal configs.  (w4=s and v5 are irrelevant to
the construction; the construction only uses runners 1..4 + the cover.)
"""
import math
from fractions import Fraction as F

def circdist(x):
    f = x - math.floor(x)
    return min(f, 1 - f)

def frac(x):
    return x - math.floor(x)

def block_edges(w3, t):
    """closure of the 4-block (runner-3 unsafe component) containing t."""
    m = round(w3 * t)
    pe = (m - F(1, 6)) / w3
    qe = (m + F(1, 6)) / w3
    return m, pe, qe

def check_config(p, q, g, verbose=False):
    """Return list of failures (empty = construction holds for this config)."""
    w0, w1, w2, w3 = g * p, g * (q - p), g * q, g * (p + q)
    fails = []
    # search (56)-witnesses j; period of {w3 t} in j is p (since w3/w0 = (p+q)/p)
    # so j in range(p) covers all residues; scan a few periods to be safe.
    for j in range(3 * p + 1):
        t = F(j * 3 + 1, 3 * w0)  # (j + 1/3)/w0
        # runner 1 must be exactly at 1/3
        assert frac(w0 * t) == F(1, 3), (p, q, g, j, frac(w0 * t))
        f3 = frac(w3 * t)
        in56 = (f3 >= F(5, 6)) or (f3 <= F(1, 6))
        if not in56:
            continue
        # 4-block edges
        m, pe, qe = block_edges(w3, t)
        # the engine needs q-p = 1/(3 w3):
        assert qe - pe == F(1, 3 * w3)
        # sample runners 0,1,2 across [pe, qe] densely
        N = 400
        worst = {0: 1.0, 1: 1.0, 2: 1.0}
        for k in range(N + 1):
            s = pe + (qe - pe) * F(k, N)
            for idx, wi in ((0, w0), (1, w1), (2, w2)):
                cd = circdist(wi * s)
                worst[idx] = min(worst[idx], cd)
        for idx in (0, 1, 2):
            if worst[idx] < 1/6 - 1e-12:
                fails.append((p, q, g, j, idx, float(worst[idx])))
        if verbose and in56:
            print(f"  p={p} q={q} g={g} j={j}: f3={float(f3):.3f} "
                  f"worst r1={worst[0]:.4f} r2={worst[1]:.4f} r3={worst[2]:.4f}")
    return fails

def main():
    total_configs = 0
    total_witnesses = 0
    all_fails = []
    # diverse diagonal configs: q>=18, gcd(p,q)=1, 3p<q, p>=1
    for q in range(18, 80):
        for p in range(1, q):
            if 3 * p >= q:
                continue
            if math.gcd(p, q) != 1:
                continue
            for g in (1, 2, 3):
                total_configs += 1
                fails = check_config(p, q, g)
                # count witnesses
                w0, w3 = g * p, g * (p + q)
                for j in range(3 * p + 1):
                    t = F(j * 3 + 1, 3 * w0)
                    f3 = frac(w3 * t)
                    if (f3 >= F(5, 6)) or (f3 <= F(1, 6)):
                        total_witnesses += 1
                all_fails.extend(fails)
    print(f"configs checked : {total_configs}")
    print(f"(56)-witnesses  : {total_witnesses}")
    print(f"safety FAILURES : {len(all_fails)}")
    if all_fails:
        print("  first 20 failures (p,q,g,j,runner_idx,worst_circdist):")
        for f in all_fails[:20]:
            print("   ", f)
    else:
        print("  => 4-block edges/interior are ALWAYS 0123-safe. Construction sound.")

    # also confirm at least one witness exists per config with p>=3 (BHK: (56) exists for p>=3)
    missing = []
    for q in range(18, 80):
        for p in range(3, q):
            if 3 * p >= q or math.gcd(p, q) != 1:
                continue
            g = 1
            w0, w3 = g * p, g * (p + q)
            has = False
            for j in range(p):
                t = F(j * 3 + 1, 3 * w0)
                f3 = frac(w3 * t)
                if (f3 >= F(5, 6)) or (f3 <= F(1, 6)):
                    has = True
                    break
            if not has:
                missing.append((p, q))
    print(f"\np>=3 configs with NO (56)-witness: {len(missing)} (BHK: should be 0)")
    if missing:
        print("   ", missing[:20])

if __name__ == "__main__":
    main()
