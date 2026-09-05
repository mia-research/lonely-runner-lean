#!/usr/bin/env python3
"""
t2d_soft_exclusion_run_v1.py — RUN of PREREG_soft_exclusion_dmodk_v1.md.

Do public invariants V statistically under-represent residues of the SECRET d (bits removed)?
Primary: per-k omnibus G on J=(chi3, eps, chi2y) [18 cells] vs d0 mod k, over ONE rep per <±λ>-orbit
(removes the μ6-forced coupling). Control = permute residue across reps. Holm over k∈{2,3,4,6,7}.
Exclusion = control-calibrated bits_removed_net = H_ctrl(d mod k|J) − H_real(d mod k|J).
Fence premise: a scoped null is scoped to method+power+curves, NEVER "impossible".
Signal path exact int; G/entropy are float statistics ranked vs integer permutation nulls.
"""
import math
import random
from fractions import Fraction as Fr
from collections import Counter, defaultdict
from eps_to_d_run_v1 import prime_order_curve, full_orbit, padd, find_glv, chi3_index
from eps_to_d_family_v2 import gstat, holm
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)


def cond_entropy(J, r):
    """H(r | J) in bits, finite-sample plugin."""
    byj = defaultdict(Counter); nj = Counter()
    for j, rr in zip(J, r):
        byj[j][rr] += 1; nj[j] += 1
    U = len(J); H = 0.0
    for j, cnt in byj.items():
        pj = nj[j] / U
        h = 0.0
        for rr, c in cnt.items():
            pr = c / nj[j]
            h -= pr * math.log2(pr)
        H += pj * h
    return H


def run(p, m, G, B=3000, rng=None):
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    ys = [None] * m; acc = None
    for d in range(1, m):
        acc = padd(acc, G, p); ys[d] = acc[1]
    lam, beta, wp = find_glv(xs, p, m)
    eis, eps = build(p)
    # one rep per <±λ>-orbit
    seen = set(); reps = []
    for d in range(1, m):
        orb = []
        for kk in range(3):
            lk = pow(lam, kk, m); orb += [(lk * d) % m, (-lk * d) % m]
        d0 = min(x for x in orb if x)
        if d0 in seen:
            continue
        seen.add(d0)
        reps.append(dict(d=d0,
                         J=(chi3_index(xs[d0], p, wp), eps(xs[d0]),
                            1 if legendre(ys[d0], p) == 1 else 0)))
    U = len(reps)
    Js = [r['J'] for r in reps]

    out = {}
    for k in (2, 3, 4, 6, 7):
        rvals = [r['d'] % k for r in reps]
        pbs = {0: list(zip(Js, rvals))}       # single stratum (orbit-quotient already applied)
        G_real = gstat(pbs)
        Hr = cond_entropy(Js, rvals)
        # control: permute residues across reps
        cnt = 0; Hc = 0.0
        for _ in range(B):
            perm = rvals[:]; rng.shuffle(perm)
            if gstat({0: list(zip(Js, perm))}) >= G_real:
                cnt += 1
            Hc += cond_entropy(Js, perm)
        Hc /= B
        p_perm = Fr(cnt + 1, B + 1)
        bits_net = Hc - Hr                      # control-calibrated bits removed
        out[k] = dict(U=U, G_real=G_real, p_perm=p_perm, bits_net=bits_net, base=math.log2(k))
    # plants (on k=3): positive feature:=residue; negative random; forced-coupling
    r3 = [r['d'] % 3 for r in reps]
    G_pos = gstat({0: [((x,), x) for x in r3]})
    cntp = sum(1 for _ in range(200)
               if gstat({0: [((x,), y) for x, y in zip(r3, random.sample(r3, len(r3)))]}) >= G_pos)
    rndf = [rng.randint(0, 2) for _ in reps]
    G_neg = gstat({0: list(zip([(x,) for x in rndf], r3))})
    return out, dict(pos_ok=cntp <= 2, G_pos=G_pos, G_neg=G_neg, U=U)


def main():
    print("PREREG_soft_exclusion_dmodk_v1 — RUN (scan; confirm gated on a Holm survivor)\n")
    for (lo, hi) in [(547, 548), (907, 908)]:
        r = prime_order_curve(lo, hi)
        p, m, G = r
        out, pl = run(p, m, G, B=3000, rng=random.Random(50 + p))
        hm = holm([(f"k={k}", out[k]['p_perm']) for k in out])
        surv = [lab for (lab, pv, rej) in hm if rej]
        print(f"=== p={p} m={m} U={pl['U']}  plant pos_ok={pl['pos_ok']} (G_pos={pl['G_pos']:.0f}) "
              f"G_neg={pl['G_neg']:.2f} ===")
        for k in out:
            o = out[k]
            print(f"    k={k}: omnibus p={o['p_perm'].numerator}/{o['p_perm'].denominator}  "
                  f"G={o['G_real']:.2f}  bits_removed_net={float(o['bits_net']):+.4f} (base H={o['base']:.3f})")
        print(f"    Holm/k survivors: {surv if surv else 'NONE'}\n")
    print("Read (fence premise): Holm survivor with bits_net>0 & plant fired -> EXPLORATORY, confirm OOS.")
    print("All p>0.05 -> SCOPED null on soft exclusion at this power/curves; NOT 'impossible'.")


if __name__ == "__main__":
    main()
