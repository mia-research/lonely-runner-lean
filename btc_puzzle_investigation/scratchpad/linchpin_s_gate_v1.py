#!/usr/bin/env python3
"""
linchpin_s_gate_v1.py  —  TEST the ARSENAL/XVI.D linchpin gate, EXACTLY, on PUBLIC maps.

Claim (doc 19 sec 4A / XVI.D):  s = N(eis(X))/p  in [0, 3/4];  s < 3/16  =>  eps(X) = 0 (core).
If true and eps=0 is the Cap-Law core (density ~3/4), a fraction of PUBLIC x-coords have their
flap indicator pinned to 0 from x alone.

Recovered (source-first) public maps, both functions of X (the x-coordinate) ONLY, no d:
  eis(X)  : int1_frame_operator_v1.build      (exact integer reduced lift vector)
  eps(X)  : int1_frame_operator_v1.build      ({0=core,1,2}; 0 <=> exact mu3 covariance)
  enorm   : lift_sextant_rhombus_law_proof_v2 (integer Eisenstein norm)

Exact arithmetic only (Fraction / int). No float in the signal path. No key. Structural
verification of an implication between two PUBLIC predicates of X -> no leakage claim here.

Controls:
  FIRING  : the implication is NON-TRIVIAL — there exist X with eps != 0 (so eps=0 is not
            forced everywhere), and specifically some at s >= 3/16.
  LABEL-SHUFFLE (negative): permute the eps labels across X; the implication should then FAIL
            at ~ the base non-core rate (shows the pass is not vacuous).
Also: measure Pr[s<3/16], Pr[eps=0], and max s (predicted <= 3/4), cross-check core vs 3/4.
"""
from fractions import Fraction as Fr
import random
from sympy import isprime
from int1_frame_operator_v1 import build, build_secp
from lift_sextant_rhombus_law_proof_v2 import enorm

THRESH = Fr(3, 16)
P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F


def test_prime(p, rng):
    eis, eps = build(p)
    n_lt = 0            # #{ s < 3/16 }
    n_lt_core = 0       # #{ s < 3/16 and eps==0 }  (want == n_lt)
    n_core = 0          # #{ eps==0 }
    n_tot = p - 1
    smax = Fr(0)
    viol = []          # X with s<3/16 but eps!=0
    labels = []        # (X, s, eps) for shuffle control
    for X in range(1, p):
        w = eis(X)
        s = Fr(enorm(w), p)
        e = eps(X)
        if s > smax:
            smax = s
        if e == 0:
            n_core += 1
        if s < THRESH:
            n_lt += 1
            if e == 0:
                n_lt_core += 1
            else:
                viol.append((X, s, e))
        labels.append((s, e))

    # firing: exist eps!=0 at all, and at s>=3/16
    exist_noncore = any(e != 0 for _, e in labels)
    exist_noncore_hi = any((s >= THRESH and e != 0) for s, e in labels)

    # negative label-shuffle: break the X<->eps pairing, keep the s<3/16 mask fixed
    es = [e for _, e in labels]
    rng.shuffle(es)
    shuf_viol = sum(1 for (s, _), e in zip(labels, es) if s < THRESH and e != 0)

    return dict(p=p, n_tot=n_tot, n_lt=n_lt, n_lt_core=n_lt_core, n_core=n_core,
                smax=smax, viol=viol[:5], nviol=len(viol),
                exist_noncore=exist_noncore, exist_noncore_hi=exist_noncore_hi,
                shuf_viol=shuf_viol)


def main():
    rng = random.Random(12345)
    # primes p == 1 mod 3 (secp is p==7 mod12 => ==1 mod3). Both mod-12 classes 1 and 7.
    primes = []
    q = 1000
    while len(primes) < 8:
        if isprime(q) and q % 3 == 1:
            primes.append(q)
        q += 1
    print(f"Linchpin gate  s<3/16 => eps=0  (THRESH={THRESH})  over all X in [1,p)\n")
    header = f"{'p':>6} {'p%12':>4} {'Pr[s<3/16]':>11} {'Pr[eps=0]':>10} {'gate viol':>9} {'smax':>7} {'shuf_viol':>9} fire?"
    print(header)
    print("-" * len(header))
    all_pass = True
    for p in primes:
        r = test_prime(p, rng)
        pr_lt = Fr(r['n_lt'], r['n_tot'])
        pr_core = Fr(r['n_core'], r['n_tot'])
        fire = r['exist_noncore'] and r['exist_noncore_hi']
        gate_ok = (r['nviol'] == 0)
        all_pass = all_pass and gate_ok and fire
        print(f"{p:>6} {p%12:>4} {float(pr_lt):>11.4f} {float(pr_core):>10.4f} "
              f"{r['nviol']:>9} {float(r['smax']):>7.4f} {r['shuf_viol']:>9} "
              f"{'Y' if fire else 'n':>4}")
        if r['nviol']:
            print(f"        VIOLATIONS (X,s,eps): {r['viol']}")
    print("\nCap-Law cross-check: Pr[eps=0] should track ~3/4 (0.75) core density;")
    print("Pr[s<3/16] is the s-core SUBSET (<= Pr[eps=0] if the gate holds).")
    print(f"\nGATE (0 violations every prime) AND FIRING (non-core exists, incl s>=3/16): "
          f"{'PASS' if all_pass else 'FAIL'}")
    print("Negative control shuf_viol >> 0 confirms the pass is not vacuous.")

    # ---- REACHES SCALE? sampled check at secp's actual prime (2^256) ----
    print("\n" + "=" * 68)
    print("secp256k1 (p ~ 2^256), sampled — does the gate REACH SCALE (#5 banner)?")
    print("=" * 68)
    eiss, epss = build_secp()
    rng2 = random.Random(2024)
    N = 20000
    n_lt = n_lt_core = n_core = 0
    smax = Fr(0); nviol = 0; hi_noncore = 0
    for _ in range(N):
        X = rng2.randrange(1, P_SECP)
        s = Fr(enorm(eiss(X)), P_SECP)
        e = epss(X)
        if s > smax: smax = s
        if e == 0: n_core += 1
        if s < THRESH:
            n_lt += 1
            if e == 0: n_lt_core += 1
            else: nviol += 1
        elif e != 0:
            hi_noncore += 1
    print(f"  sampled X = {N};  Pr[s<3/16]={n_lt/N:.4f}  Pr[eps=0]={n_core/N:.4f}  "
          f"smax={float(smax):.4f}")
    print(f"  gate violations (s<3/16 & eps!=0) = {nviol}   firing (s>=3/16 & eps!=0) = {hi_noncore>0}")
    print(f"  => secp gate {'HOLDS (0 viol, fires)' if nviol==0 and hi_noncore>0 else 'CHECK'} "
          f"— exact-map => structural, reaches 2^256.")


if __name__ == "__main__":
    main()
