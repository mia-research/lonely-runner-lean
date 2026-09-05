#!/usr/bin/env python3
"""
joint_fiber_carry_mi_v1.py  —  EXECUTE the FROZEN pre-registration
PREREG_joint_fiber_carry_mi_v1.md  (repaired cross-channel carry-leak test).

Original single-point statistic I(c;(I1,I2)) is graded ILL-POSED (not run).

  FEATURE (coordinate channel):  b_eps = [ eps(x_P) != 0 ] in {0,1}
          eps = int1_frame_operator_v1.build_secp  (exact int fn of x_P ALONE, no d)
  TARGET  (scalar channel):      eps_carry(d) = [ (d*LAM mod n) >= n - r1 ],  r1 = floor(n/2)
          coupling-carry bit in Z/n via LAM -- DISJOINT ring from the feature.
  PRIMARY   Ihat( eps_carry ; b_eps )         (2x2, df=1)   -- verdict-driving
  SECONDARY Ihat( eps_carry ; (j,s_neg,eps) ) (18-cell, df=17) -- NOT verdict-driving

Null (matched): mu6-canonicalize + orbit-dedup keys, then permute TARGET labels, b_eps fixed.
  PRIMARY & PLANTS (2x2): the label-permutation null with fixed margins IS the hypergeometric
    distribution of n11 -> EXACT permutation p-value by enumeration (the >=10^4-perm limit, exact).
  SECONDARY (18-cell): sampled label permutations (n_perm), same null.
Planted controls: strong q=0.25 (MUST fire) + floor q=0.41 validate the instrument at each N.
Arms: real 82 puzzle keys (post-dedup) + constructed known-generator (full + puzzle-bit-matched).

EXACT arithmetic in the SIGNAL PATH (int only): b_eps, eps_carry, phi, scalar_mul, mu6 dedup,
all counts, the hypergeometric weights (math.comb, Fraction).  Float appears ONLY as the log2
inside the MI statistic and the p reporting -- applied to already-exact integer counts, ranked
against the matched null; never a threshold on key-derived data (PREREG sec 8).
"""
import csv, os, sys, math, random
from fractions import Fraction as Fr
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # project root modules
from ecc_secp256k1 import scalar_mul, N_ORDER
from int1_frame_operator_v1 import build_secp
from glv_fundamental_domain_law_v1 import cube_roots

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
P_FIELD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = N_ORDER
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
assert (LAM*LAM + LAM + 1) % N == 0
R1 = N // 2
THR = N - R1                                   # threshold = ceil(n/2)

_eis_secp, _eps_secp = build_secp()
_Z3 = cube_roots(P_FIELD)[0]
_Z3b = (_Z3 * _Z3) % P_FIELD
assert (_Z3*_Z3 + _Z3 + 1) % P_FIELD == 0


# ---------- disjoint maps (exact integers) ----------
def b_eps_of_x(x):      return 0 if _eps_secp(x % P_FIELD) == 0 else 1
def eps_carry_of_d(d):  return 1 if (d * LAM % N) >= THR else 0
def chi3_index(x):
    t = pow(x % P_FIELD, (P_FIELD - 1)//3, P_FIELD)
    return 0 if t == 1 else (1 if t == _Z3 else 2)
def phi_state(x, y):    return (chi3_index(x), y & 1, _eps_secp(x % P_FIELD))


# ---------- MI (bits) : float log2 on exact integer counts ----------
def mi_from_joint(joint, mf, mt, n):
    mi = 0.0  # noqa: float
    for (a, b), nab in joint.items():
        mi += (nab / n) * math.log2((nab * n) / (mf[a] * mt[b]))  # noqa: float
    return mi

def mutual_information_bits(feat, targ):
    n = len(feat)
    return mi_from_joint(Counter(zip(feat, targ)), Counter(feat), Counter(targ), n)


# ---------- EXACT 2x2 permutation p-value (hypergeometric on n11) ----------
def mi_2x2(n11, n10, n01, n00):
    n = n11 + n10 + n01 + n00
    m1 = n11 + n10; m0 = n01 + n00; k1 = n11 + n01; k0 = n10 + n00
    mi = 0.0  # noqa: float
    for nab, ra, cb in [(n11, m1, k1), (n10, m1, k0), (n01, m0, k1), (n00, m0, k0)]:
        if nab:
            mi += (nab / n) * math.log2((nab * n) / (ra * cb))  # noqa: float
    return mi

def exact_2x2_perm_p(feat, targ):
    """feat,targ binary. Returns (Ihat_obs, exact permutation p) under fixed-margin label perm."""
    n = len(feat)
    n11 = sum(1 for a, b in zip(feat, targ) if a == 1 and b == 1)
    m1 = sum(feat); k1 = sum(targ); m0 = n - m1; k0 = n - k1
    obs = mi_2x2(n11, m1 - n11, k1 - n11, m0 - (k1 - n11))
    denom = math.comb(n, m1)
    lo = max(0, m1 - k0); hi = min(m1, k1)
    p = Fr(0)
    for t in range(lo, hi + 1):
        mit = mi_2x2(t, m1 - t, k1 - t, m0 - (k1 - t))
        if mit >= obs - 1e-12:  # noqa: float
            p += Fr(math.comb(k1, t) * math.comb(k0, m1 - t), denom)
    return obs, p


# ---------- sampled permutation p (for 18-cell secondary) ----------
def sampled_perm_p(feat, targ, obs, n_perm, seed):
    rng = random.Random(seed)
    t = list(targ); cnt = 0
    for _ in range(n_perm):
        rng.shuffle(t)
        if mutual_information_bits(feat, t) >= obs - 1e-12:  # noqa: float
            cnt += 1
    return cnt, Fr(1 + cnt, 1 + n_perm)


# ---------- mu6 orbit dedup ----------
def mu6_canonical(d):
    d %= N; orbit = set(); v = d
    for _ in range(3):
        orbit.add(v); orbit.add(N - v); v = v * LAM % N
    return min(orbit)

def dedup_keys(records):
    seen = set(); kept = []
    for r in records:
        c = mu6_canonical(r['d'])
        if c not in seen:
            seen.add(c); kept.append(r)
    return kept, len(records) - len(kept)


# ---------- one arm ----------
def run_arm(name, records, sec_perm, seed):
    kept, ndrop = dedup_keys(records)
    Nk = len(kept)
    b = [r['b_eps'] for r in kept]
    e = [r['eps_carry'] for r in kept]
    phi = [r['phi'] for r in kept]
    mb = Counter(b); me = Counter(e)
    mi_min = 8.43 / Nk  # noqa: float

    I_prim, p_prim = exact_2x2_perm_p(b, e)                      # verdict-driving, exact

    # plants (2x2, exact p)
    rng = random.Random(seed + 100)
    b_strong = [t ^ (1 if rng.random() < 0.25 else 0) for t in e]  # noqa: float
    I_str, p_str = exact_2x2_perm_p(b_strong, e)
    b_floor = [t ^ (1 if rng.random() < 0.41 else 0) for t in e]  # noqa: float
    I_flo, p_flo = exact_2x2_perm_p(b_floor, e)

    # secondary (18-cell, sampled)
    I_sec = mutual_information_bits(phi, e)
    c_sec, p_sec = sampled_perm_p(phi, e, I_sec, sec_perm, seed + 1)

    print(f"\n===== ARM: {name} =====")
    print(f"  N(raw)={len(records)}  mu6-dropped={ndrop}  N(kept)={Nk}")
    print(f"  b_eps: core={mb[0]} flap={mb[1]} (Pr[flap]={float(Fr(mb[1],Nk)):.4f}) | "  # noqa: float
          f"eps_carry: 0={me[0]} 1={me[1]} (Pr[1]={float(Fr(me[1],Nk)):.4f})")  # noqa: float
    print(f"  MI_min(80%pow,df=1)={mi_min:.5f} bits")
    print(f"  PLANTS  strong q=.25: Ihat={I_str:.4f} p={float(p_str):.2e} "  # noqa: float
          f"[{'FIRES' if p_str<0.05 else 'DEAD->VOID'}]   floor q=.41: Ihat={I_flo:.4f} p={float(p_flo):.2e}")  # noqa: float
    print(f"  PRIMARY Ihat(carry;b_eps)={I_prim:.5f} bits  EXACT perm-p={float(p_prim):.5f}  "  # noqa: float
          f"-> {'ABOVE floor & p<.05' if (I_prim>=mi_min and p_prim<0.05) else 'below power/null'}")  # noqa: float
    print(f"  SECOND. Ihat(carry;(j,s,eps))={I_sec:.5f} bits  perm-p={float(p_sec):.5f} "  # noqa: float
          f"({c_sec}/{sec_perm}) [not verdict-driving]")
    return dict(name=name, Nk=Nk, ndrop=ndrop, mi_min=mi_min, I_prim=I_prim, p_prim=p_prim,
                p_str=p_str, p_flo=p_flo, I_sec=I_sec, p_sec=p_sec)


# ---------- key sets ----------
def load_real():
    recs = []
    with open(os.path.join(ROOT, "puzzles_verified.csv")) as f:
        for row in csv.DictReader(f):
            recs.append(dict(d=int(row["private_key"], 16),
                             x=int(row["X"], 16), y=int(row["Y"], 16)))
    for r in recs[:5] + recs[-3:]:                # correctness gate vs on-chain
        xx, yy = scalar_mul(r['d'])
        assert xx == r['x'] and yy == r['y'], f"pubkey mismatch d={r['d']}"
    for r in recs:
        r['b_eps'] = b_eps_of_x(r['x']); r['eps_carry'] = eps_carry_of_d(r['d'])
        r['phi'] = phi_state(r['x'], r['y'])
    return recs

def make_constructed(kind, count, seed):
    rng = random.Random(seed)
    real_bits = sorted({int(r["bits"]) for r in
                        csv.DictReader(open(os.path.join(ROOT, "puzzles_verified.csv")))})
    recs = []
    for i in range(count):
        if kind == 'full':
            d = rng.randrange(1, N)
        else:
            k = rng.choice(real_bits)
            d = rng.randrange(1 << (k-1), 1 << k) if k > 1 else 1
        x, y = scalar_mul(d)
        recs.append(dict(d=d, x=x, y=y, b_eps=b_eps_of_x(x),
                         eps_carry=eps_carry_of_d(d), phi=phi_state(x, y)))
        if (i+1) % 5000 == 0: print(f"    [{kind}] {i+1}/{count}")
    return recs


def main():
    print("FROZEN PREREG joint_fiber_carry_mi_v1 (repaired cross-channel carry-leak)")
    print("Original single-point I(c;(I1,I2)) = ILL-POSED (not run).")
    results = []
    results.append(run_arm("real-82 (on-chain pubkeys)", load_real(), sec_perm=50000, seed=11))
    print("\n  building constructed known-generator sets (scalar_mul)...")
    results.append(run_arm("constructed-full (uniform d, N=10000)",
                           make_constructed('full', 10000, 7), sec_perm=3000, seed=21))
    results.append(run_arm("constructed-matched (puzzle bit-bands, N=10000)",
                           make_constructed('matched', 10000, 8), sec_perm=3000, seed=31))

    print("\n" + "="*74 + "\nVERDICT (PREREG sec 9 grade slots)\n" + "="*74)
    for r in results:
        plant = r['p_str'] < 0.05  # noqa: float
        if not plant:
            g = "VOID (strong plant dead at N)"
        elif r['p_prim'] < 0.05 and r['I_prim'] >= r['mi_min']:  # noqa: float
            g = "PRIMARY POSITIVE at scope (p<.05, MI>=MI_min)"
        else:
            g = f"scope NULL (MI<MI_min={r['mi_min']:.4f}); NOT a closure, KS floor 2^-128 uncrossed"
        print(f"  {r['name']:46s} plant={'FIRE' if plant else 'DEAD'} prim-p={float(r['p_prim']):.4f} -> {g}")  # noqa: float


if __name__ == "__main__":
    main()
