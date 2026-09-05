#!/usr/bin/env python3
"""case_63 branch-8 fallback, nu(e45)=1: END-TO-END integer simulation.

Builds random integer configs matching the Lean branch hypotheses:
  h = m (>=2), ratio 3:  d1,d2,d3 == 1 (mod 7),
     d1-d3 = 7^m * r1 (7 !| r1),  d2-d3 = 7^m * r2 with r2 == 3*r1 (mod 7)
  d4 == 2 (mod 7), e34 = 2*d3-d4 with nu(e34) = m and T34 = qz(m, u*e34) in {3,4,5}
  d5 == 4 (mod 7), e45 = 2*d4-d5 with nu(e45) = 1 exactly
  plain u-frame fails: etilde34(u) in {2,3,4,5}   (hetil34)

Recipe under test (the proposed Lean wiring):
  r    = (d1-d3)/7^m mod 7, u = r^{-1} mod 7 (positive rep)
  P    = qz(m, 7*u*d3); E = qz(m, u*e45); rho' = (u*e45/7) mod 7
  rho  = r*rho' mod 7;  e0 = E - P*rho mod 7
  pick pin p by the fallback_63_l1 decide; k2 = (p-P)*r mod 7
  w    = (1 + k2*7^(m-1)) * u
  VERIFY: qz(m,7*w*d3) = p; qz(m, w*e45) = e0+p*rho;
          eps1 := qz(m,2*w*d3)-2*qz(m,w*d3) in {0,1}, compatible with p;
          cc   := qz(m,w*d5)-2*qz(m,w*d4)+qz(m,w*e45) in {0,1,6};
          exists Atar: final Lambda_m shift avoids {0,6} on all five arcs,
          final arc(i) = qz(m, w*d_i) + (Atar-A0)*res(d_i).
"""
import random

BAD = {0, 6}


def qz(m, x):
    return (x % 7 ** (m + 1)) // 7 ** m  # Int.emod semantics: always in [0,7^(m+1))


def nu7(x):
    assert x != 0
    n = 0
    while x % 7 == 0:
        x //= 7
        n += 1
    return n


def compatible_eps1(p):
    return [0] if p in (0, 1, 2) else ([1] if p in (4, 5, 6) else [0, 1])


def placement_ok(Atar, T34, eps1, e_val, cc):
    a1 = [Atar, Atar + 1, Atar + 3]
    d4 = 2 * Atar + eps1 - T34
    d5 = 4 * Atar + 2 * eps1 - 2 * T34 - e_val + cc
    return all((x % 7) not in BAD for x in a1 + [d4, d5])


def pick_pin(T34, e0, rho):
    for p in range(7):
        e_val = (e0 + p * rho) % 7
        if all(any(placement_ok(A, T34, eps1, e_val, cc) for A in range(7))
               for eps1 in compatible_eps1(p) for cc in (0, 1, 6)):
            return p
    return None


def run_config(m, d1, d2, d3, d4, d5, verbose=False):
    e34 = 2 * d3 - d4
    e45 = 2 * d4 - d5
    r = ((d1 - d3) // 7 ** m) % 7
    u = pow(r, -1, 7)
    e34u, e45u = u * e34, u * e45
    T34 = qz(m, e34u)
    # branch guards
    assert nu7(e34) == m and T34 in (3, 4, 5) and nu7(e45) == 1
    P = qz(m, 7 * u * d3)
    E = qz(m, e45u)
    rho_p = (e45u // 7) % 7
    rho = (r * rho_p) % 7
    e0 = (E - P * rho) % 7
    p = pick_pin(T34, e0, rho)
    if p is None:
        return "NO_PIN"
    k2 = ((p - P) * r) % 7
    w = (1 + k2 * 7 ** (m - 1)) * u
    # verify the tracked identities
    if qz(m, 7 * w * d3) != p:
        return "PIN_MISMATCH"
    e_val = qz(m, w * e45)
    if e_val != (e0 + p * rho) % 7:
        return "EVAL_MISMATCH"
    eps1 = (qz(m, 2 * w * d3) - 2 * qz(m, w * d3)) % 7
    if eps1 not in (0, 1) or eps1 not in compatible_eps1(p):
        return f"EPS1_BAD(p={p},eps1={eps1})"
    cc = (qz(m, w * d5) - 2 * qz(m, w * d4) + e_val) % 7
    if cc not in (0, 1, 6):
        return f"CC_BAD({cc})"
    # d4 arc consistency: qz(w*d4) = 2*qz(w*d3)+eps1-T34
    if qz(m, w * d4) % 7 != (2 * qz(m, w * d3) + eps1 - T34) % 7:
        return "D4_MISMATCH"
    # final placement
    A0 = qz(m, w * d3)
    ds = [d1, d2, d3, d4, d5]
    for Atar in range(7):
        if placement_ok(Atar, T34, eps1, e_val, cc):
            k = (Atar - A0) % 7
            arcs = [(qz(m, w * dd) + k * (dd % 7)) % 7 for dd in ds]
            if all(a not in BAD for a in arcs):
                return "OK"
            return f"FINAL_ARC_BAD arcs={arcs} (Atar={Atar},eps1={eps1},cc={cc},e_val={e_val})"
    return "NO_ATAR"


def gen_config(rng, m):
    """Random config satisfying all branch hypotheses; d3 possibly negative."""
    while True:
        d3 = rng.randrange(-7 ** (m + 3), 7 ** (m + 3))
        if d3 % 7 != 1:
            continue
        r1 = rng.randrange(1, 7 ** 2)
        if r1 % 7 == 0:
            continue
        d1 = d3 + 7 ** m * r1
        r2 = r1 * 3 + 7 * rng.randrange(-3, 4)  # r2 == 3*r1 mod 7
        if r2 % 7 == 0 or r2 == 0:
            continue
        d2 = d3 + 7 ** m * r2
        # d4: e34 = 2*d3-d4 = 7^m * g with g !=0 mod 7 and qz(m,u*e34) in {3,4,5}
        u = pow(((d1 - d3) // 7 ** m) % 7, -1, 7)
        g_ok = [g for g in range(-3 * 7, 3 * 7 + 1)
                if g % 7 != 0 and qz(m, u * 7 ** m * g) in (3, 4, 5)]
        if not g_ok:
            continue
        g = rng.choice(g_ok)
        d4 = 2 * d3 - 7 ** m * g
        if d4 % 7 != 2:
            continue
        # d5: e45 = 2*d4-d5 = 7*s with s !=0 mod 7  -> nu(e45)=1
        s = rng.randrange(-7 ** (m + 1), 7 ** (m + 1))
        if s == 0 or s % 7 == 0:
            continue
        d5 = 2 * d4 - 7 * s
        if d5 % 7 != 4:
            continue
        # plain-frame failure guard (the sub-branch hypothesis hetil34)
        et34_u = (2 * qz(m, u * d3) - qz(m, u * d4)) % 7
        if et34_u not in (2, 3, 4, 5):
            continue  # that config is closed earlier; not this branch
        if len({d1, d2, d3, d4, d5}) < 5:
            continue
        return d1, d2, d3, d4, d5


def main():
    rng = random.Random(63)
    results = {}
    N = 6000
    for i in range(N):
        m = rng.choice([2, 2, 3, 4])
        cfg = gen_config(rng, m)
        res = run_config(m, *cfg)
        results[res] = results.get(res, 0) + 1
        if res != "OK" and results[res] <= 3:
            print(f"  [{res}] m={m} cfg={cfg}")
    print(f"\ntotal {N}: {results}")
    print("PASS" if set(results) == {"OK"} else "FAIL")


if __name__ == "__main__":
    main()
