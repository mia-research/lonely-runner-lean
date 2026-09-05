#!/usr/bin/env python3
"""
Eisenstein 2-D LIFT angle, redone EXACT (no float) + STRONG instrument.

Prior work (cm_deep_probes_v1 P1) found the lift angle non-uniform ("sectors 4,10
~3x") but SCALAR-INDEPENDENT -- using (a) a float atan2 binning (provisional under
the no-float rule) and (b) a marginal chi^2 (the self-audit flagged marginals as
too weak for structural questions). This upgrades both:

  * EXACT 6-sextant of the lift Eisenstein integer w=u+v*omega via integer
    omega-rotation (u,v)->(v, v-u) is -60deg; count rotations to the base wedge.
    (Sectors 4 and 10 of the 12-way fold to the SAME sextant 4, so the ~3x
    enhancement shows as one hot sextant -- float-free.)
  * STRONG conditional: power-scaling MI(sextant ; d-target) at growing M -- a
    plateau+z~sqrt(M) would be a real scalar leak; 1/M decay = none.

Sets: gen256 (non-degenerate), gen130, d100k. Controls: MI(sextant;sextant) fires
(sanity the detector sees dependence); MI(sextant;chi6(X)) fires (lift relates to
sextic); MI(sextant;d-target) is the real (expected-null) test.
Exact integers in the signal path.
"""
import numpy as np
from angular_interference_scaling_v1 import gen_keys, conditional, loglog_slope, mi_bits, load_100k, chi6

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171
assert aP*aP - aP*bP + bP*bP == p

def rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2*r >= de else q
def gauss(u, v):
    dot = lambda a, b: a[0]*b[0] + a[1]*b[1]
    while True:
        if dot(v, v) < dot(u, u): u, v = v, u
        m = rdiv(dot(u, v), dot(u, u)); v = (v[0]-m*u[0], v[1]-m*u[1])
        if dot(v, v) >= dot(u, u): return u, v
R1, R2 = gauss((aP, bP), (-bP, aP-bP))
DET = R1[0]*R2[1] - R1[1]*R2[0]
def eis(X):
    c1 = rdiv(X*R2[1], DET); c2 = rdiv(-X*R1[1], DET)
    return (X - (c1*R1[0] + c2*R2[0]), -(c1*R1[1] + c2*R2[1]))

def sextant(u, v):
    """Exact 0..5 sextant of w=u+v*omega. Rotate by -60deg: (u,v)->(v, v-u), until
    the point lies in the base wedge [0,60): v>=0 and u-v>=0 (u+v*omega with both
    'barycentric' coords >=0 along units 1 and 1+omega). Count rotations."""
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0:
            return k
        u, v = v, v - u      # -60 degrees, exact
    # fallback (on an exact boundary): classify by sign of v then u
    return 0 if v >= 0 else 3

def lift_sextant(X):
    u, v = eis(X); return sextant(u, v)

def run(name, ds, Xs, Bnull=300):
    sxt = np.array([lift_sextant(x) for x in Xs], dtype=np.int64)
    hist = np.bincount(sxt, minlength=6)
    exp = len(sxt) / 6                              # noqa: float (report stat)
    print(f"\n=== {name} (M={len(ds)}) ===")
    print(f"  lift 6-sextant marginal: {hist.tolist()}  (uniform={exp:.0f}; "
          f"max/exp={hist.max()/exp:.2f})")          # noqa: float (report)
    # exact chi^2 (report) for the marginal non-uniformity
    chi2 = float(((hist - exp)**2 / exp).sum())     # noqa: float (report stat)
    print(f"  marginal chi^2 (df5, uniform~5) = {chi2:.1f}  "
          f"-> {'NON-UNIFORM (curve-fixed geometry)' if chi2 > 20 else 'uniform'}")
    # STRONG conditional at growing M
    Ms = [m for m in (2000, 5000, 10000, 20000, 40000) if m <= len(ds)]
    rng = np.random.default_rng(4242)
    dmods = {"d%2": np.array([int(v) % 2 for v in ds]),
             "d%3": np.array([int(v) % 3 for v in ds]),
             "d%6": np.array([int(v) % 6 for v in ds]),
             "bit_mid": np.array([(int(v) >> (int(v).bit_length()//2)) & 1 for v in ds])}
    # controls: sextant itself (must fire) and chi6(X) (lift relates to sextic)
    ctrl = {"[ctrl]sextant": sxt.copy(),
            "[ctrl]chi6(X)": np.array([chi6(x) if chi6(x) is not None else 0 for x in Xs])}
    print("  STRONG conditional MI (I_c bits, z) at M_max; controls must fire:")
    for tn, tv in {**ctrl, **dmods}.items():
        res = conditional(sxt, tv, Ms, Bnull, rng)
        Ic = [r[1] for r in res]; z = [r[2] for r in res]
        s_mi = loglog_slope(Ms, Ic)
        s_z = float(np.polyfit(np.sqrt(np.array(Ms, float)), np.array(z, float), 1)[0])  # noqa: float
        tag = "SIGNAL" if (s_mi > -0.5 and s_z > 0 and z[-1] > 4) else "null"  # noqa: float (classifier)
        print(f"    sextant vs {tn:14}: I_c={Ic[-1]:+.5f}  z={z[-1]:+.2f}  "
              f"loglogslope={s_mi:+.2f}  => {tag}")

if __name__ == "__main__":
    print("Eisenstein lift 6-sextant (EXACT) + power-scaling conditional")
    print(f"lift lattice reduced basis R1={R1}\n                          R2={R2}")
    d, X, Y = gen_keys(256, 40000, 7); run("gen256", d, X)
    d, X, Y = gen_keys(130, 40000, 11); run("gen130", d, X)
    d, X, Y = load_100k(); run("d100k", d, X)
