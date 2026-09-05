#!/usr/bin/env python3
"""
joint_carry_twokey_mi_v1.py  —  EXECUTE the FROZEN pre-registration
PREREG_joint_carry_twokey_mi_v1.md  (two-key joint-carry synergy test).

Reduction ruling (frozen): F0=b_eps(x_Psum) REDUCES to v1; F1=b_eps(x_P2) = v1 replay.
REGISTERED PRIMARY = the SYNERGY object  Ihat( eps ; A | B )  (conditional MI, df=2),
  A = b_eps(x_P2)   (unknown-summand flap)
  B = b_eps(x_Psum) (sum-point flap; already v1-null as a marginal)
Distinct because x_P2 = x(P_sum - P1) is NOT a function of x_Psum alone (group law uses y_Psum).
Any signal in Ihat(eps;A|B) is pure cross-point synergy = coordinate shadow of the addition
P2+P1 where the tool-7 scalar carry eps physically sits.

TARGET  eps(d_sum) = [ (d1+d2)*LAM mod n  <  r1 ],  r1 = floor(n/2),  d1 fixed KNOWN so r1=floor(n/2).
  (= tool-7 boundary bit  eps=[r1+r2>=n], branch j=1; verified algebra in PREREG (a).)
FEATURE A,B from the exact integer eps-map (fn of x alone, no d/lambda); disjoint ring from target.

Null: mu6-dedup on d2, GLOBAL permutation of eps labels (A,B fixed), MC >=10^4, p = exact count/#perm.
Plant: MUST fire, injected into A (into B would leave CMI~0 and silently fail) -- strong q=0.25, floor q=0.30.
Arms: real 82 puzzle keys as d2 + constructed known-generator d2 sets; identical fixed d1.
Grades: null bounded by bilinear_closure Cor B1 -> VERIFIED-scope; a positive CONTRADICTS B1 -> EMPIRICAL(bug-hunt).

EXACT integer signal path; float only as log2 in MI + p reporting (PREREG sec 8 carve-out).
"""
import csv, os, sys, math, random
from fractions import Fraction as Fr
from collections import Counter
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from ecc_secp256k1 import scalar_mul, N_ORDER, P as P_FIELD, _add
from int1_frame_operator_v1 import build_secp

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
N = N_ORDER
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
assert (LAM*LAM + LAM + 1) % N == 0
R1 = N // 2
D1 = (R1 * pow(LAM, -1, N)) % N            # fixed KNOWN d1 s.t. r1 = d1*LAM mod n = floor(n/2)
assert (D1 * LAM) % N == R1
P1 = scalar_mul(D1)                        # fixed public translate

_eis, _eps = build_secp()
def b_eps(x):        return 0 if _eps(x % P_FIELD) == 0 else 1
def eps_carry(d2):   return 1 if ((D1 + d2) * LAM % N) < R1 else 0

def point_add_affine(a, b):
    X, Y, Z = _add((a[0], a[1], 1), (b[0], b[1], 1))
    assert Z != 0, "point at infinity (d2 == -d1?)"
    zi = pow(Z, P_FIELD-2, P_FIELD); zi2 = zi*zi % P_FIELD
    return (X*zi2 % P_FIELD, Y*zi2*zi % P_FIELD)


# ---------- MI from the 8-vector cnt[b*4 + a*2 + e]  (b=B, a=A, e=eps) ----------
def _cmi_bits(cnt):
    """conditional MI  I(eps;A|B) in bits, from integer counts cnt[8]."""
    Ntot = cnt.sum()
    if Ntot == 0: return 0.0  # noqa: float
    cmi = 0.0  # noqa: float
    for bb in (0, 1):
        base = bb*4
        nB = cnt[base:base+4].sum()
        if nB == 0: continue
        for aa in (0, 1):
            for ee in (0, 1):
                nae = int(cnt[base + aa*2 + ee])
                if nae == 0: continue
                nA = int(cnt[base+aa*2] + cnt[base+aa*2+1])   # A=aa within B=bb
                nE = int(cnt[base+ee] + cnt[base+2+ee])       # eps=ee within B=bb
                cmi += (nae / Ntot) * math.log2((nae * nB) / (nA * nE))  # noqa: float
    return cmi

def _jmi_bits(cnt):
    """joint MI  I(eps ; (A,B)) in bits (2x4 table), from cnt[8]."""
    Ntot = cnt.sum()
    if Ntot == 0: return 0.0  # noqa: float
    nE = [int(cnt[0]+cnt[2]+cnt[4]+cnt[6]), int(cnt[1]+cnt[3]+cnt[5]+cnt[7])]  # eps=0,1
    mi = 0.0  # noqa: float
    for f in range(4):                          # f = (B,A) 4-valued feature
        nF = int(cnt[f*2] + cnt[f*2+1])
        if nF == 0: continue
        for ee in (0, 1):
            n = int(cnt[f*2+ee])
            if n == 0: continue
            mi += (n / Ntot) * math.log2((n * Ntot) / (nF * nE[ee]))  # noqa: float
    return mi


def perm_test(strat, eps, obs_cmi, obs_jmi, n_perm, seed):
    """global permutation of eps labels; strat = B*4+A*2 fixed. ranks obs against null."""
    rng = np.random.default_rng(seed)
    e = np.array(eps, dtype=np.int64); s = np.array(strat, dtype=np.int64)
    c_cmi = c_jmi = 0
    for _ in range(n_perm):
        ep = rng.permutation(e)
        cnt = np.bincount(s + ep, minlength=8)
        if _cmi_bits(cnt) >= obs_cmi - 1e-12: c_cmi += 1  # noqa: float
        if _jmi_bits(cnt) >= obs_jmi - 1e-12: c_jmi += 1  # noqa: float
    return (c_cmi, Fr(1+c_cmi, 1+n_perm)), (c_jmi, Fr(1+c_jmi, 1+n_perm))


# ---------- mu6 dedup on d2 ----------
def mu6_canon(d):
    d %= N; orb = set(); v = d
    for _ in range(3):
        orb.add(v); orb.add(N-v); v = v*LAM % N
    return min(orb)
def dedup(recs):
    seen = set(); kept = []
    for r in recs:
        c = mu6_canon(r['d2'])
        if c not in seen: seen.add(c); kept.append(r)
    return kept, len(recs)-len(kept)


def build_records(d2_list, verify=False):
    recs = []
    for d2 in d2_list:
        P2 = scalar_mul(d2)
        Psum = point_add_affine(P2, P1)
        if verify:
            assert Psum == scalar_mul((D1 + d2) % N), "group-law != scalar_mul(d_sum)"
        A = b_eps(P2[0]); B = b_eps(Psum[0]); e = eps_carry(d2)
        recs.append(dict(d2=d2, A=A, B=B, eps=e))
    return recs


def run_arm(name, recs, n_perm, seed):
    kept, ndrop = dedup(recs); Nk = len(kept)
    A = [r['A'] for r in kept]; B = [r['B'] for r in kept]; eps = [r['eps'] for r in kept]
    strat = [B[i]*4 + A[i]*2 for i in range(Nk)]
    cnt = np.bincount(np.array(strat)+np.array(eps), minlength=8)
    I_cmi = _cmi_bits(cnt); I_jmi = _jmi_bits(cnt)
    mi_min = 10.0 / Nk                        # PREREG sec 5, df=2  # noqa: float

    (c_c, p_cmi), (c_j, p_jmi) = perm_test(strat, eps, I_cmi, I_jmi, n_perm, seed)

    # plants into A (must fire), B real ; strong q=.25, floor q=.30
    rng = random.Random(seed+100)
    def plant(q):
        Ap = [e ^ (1 if rng.random() < q else 0) for e in eps]
        st = [B[i]*4 + Ap[i]*2 for i in range(Nk)]
        cp = np.bincount(np.array(st)+np.array(eps), minlength=8)
        Ic = _cmi_bits(cp)
        (cc, pc), _ = perm_test(st, eps, Ic, 0.0, n_perm, seed+7)  # noqa: float
        return Ic, pc
    Is, ps = plant(0.25); If, pf = plant(0.30)  # noqa: float

    mb = Counter(B); ma = Counter(A); me = Counter(eps)
    print(f"\n===== ARM: {name} =====")
    print(f"  N(raw)={len(recs)} mu6-drop={ndrop} N(kept)={Nk}")
    print(f"  A(flap P2): 0={ma[0]} 1={ma[1]} | B(flap Psum): 0={mb[0]} 1={mb[1]} | "
          f"eps: 0={me[0]} 1={me[1]} (Pr[eps=1]={float(Fr(me[1],Nk)):.4f})")  # noqa: float
    print(f"  MI_min(80%pow,df=2)={mi_min:.5f} bits")
    print(f"  PLANTS(into A) strong q=.25: Ihat={Is:.4f} p={float(ps):.2e} "  # noqa: float
          f"[{'FIRES' if ps<0.05 else 'DEAD->VOID'}]   floor q=.30: Ihat={If:.4f} p={float(pf):.2e}")  # noqa: float
    print(f"  PRIMARY  Ihat(eps;A|B)={I_cmi:.5f} bits  perm-p={float(p_cmi):.5f} ({c_c}/{n_perm})  "  # noqa: float
          f"-> {'ABOVE floor & p<.05' if (I_cmi>=mi_min and p_cmi<0.05) else 'below power/null'}")  # noqa: float
    print(f"  SECOND.  Ihat(eps;(A,B))={I_jmi:.5f} bits  perm-p={float(p_jmi):.5f} [not verdict-driving]")  # noqa: float
    return dict(name=name, Nk=Nk, ndrop=ndrop, mi_min=mi_min, I_cmi=I_cmi, p_cmi=p_cmi,
                p_str=ps, p_flo=pf, I_jmi=I_jmi, p_jmi=p_jmi)


def load_real_d2():
    ds = []
    with open(os.path.join(ROOT, "puzzles_verified.csv")) as f:
        for row in csv.DictReader(f):
            ds.append(int(row["private_key"], 16))
    return ds

def make_d2(kind, count, seed):
    rng = random.Random(seed)
    bits = sorted({int(r["bits"]) for r in
                   csv.DictReader(open(os.path.join(ROOT, "puzzles_verified.csv")))})
    out = []
    for _ in range(count):
        if kind == 'full': out.append(rng.randrange(1, N))
        else:
            k = rng.choice(bits); out.append(rng.randrange(1 << (k-1), 1 << k) if k > 1 else 1)
    return out


def main():
    print("FROZEN PREREG joint_carry_twokey_mi_v1 (two-key joint-carry SYNERGY)")
    print(f"d1 fixed (r1=floor(n/2)); P1 public; target eps=[(d1+d2)*LAM mod n < r1]; branch j=1")
    print("F0/F1 = REDUCES-TO-v1 (not run). Primary = synergy Ihat(eps;A|B).")
    res = []
    print("\n  real-82 (verifying group-law addition == scalar_mul(d_sum))...")
    res.append(run_arm("real-82 (d2=puzzle keys)", build_records(load_real_d2(), verify=True),
                       n_perm=20000, seed=11))
    print("\n  building constructed known-generator d2 sets...")
    res.append(run_arm("constructed-full (uniform d2, N=10000)",
                       build_records(make_d2('full', 10000, 7)), n_perm=10000, seed=21))
    res.append(run_arm("constructed-matched (puzzle bit-bands, N=10000)",
                       build_records(make_d2('matched', 10000, 8)), n_perm=10000, seed=31))

    print("\n" + "="*76 + "\nVERDICT (PREREG sec 9 grade slots)\n" + "="*76)
    for r in res:
        plant = r['p_str'] < 0.05  # noqa: float
        if not plant: g = "VOID (strong plant dead at N)"
        elif r['p_cmi'] < 0.05 and r['I_cmi'] >= r['mi_min']:  # noqa: float
            g = "POSITIVE at scope -> CONTRADICTS bilinear Cor B1 => EMPIRICAL(bug-hunt), not a leak yet"
        else:
            g = f"scope NULL (MI<MI_min={r['mi_min']:.4f}); bounded by Cor B1; NOT a closure, KS floor 2^-128 uncrossed"
        print(f"  {r['name']:42s} plant={'FIRE' if plant else 'DEAD'} prim-p={float(r['p_cmi']):.4f} -> {g}")  # noqa: float


if __name__ == "__main__":
    main()
