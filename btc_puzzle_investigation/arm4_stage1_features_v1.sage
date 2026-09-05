#!/usr/bin/env sage
# arm4_stage1_features_v1.sage — ARM 4 stage 1: build the two sextant readouts
# at FULL secp256k1 scale, and print ONLY the forced ledger.
#
# ORDERING (spec section 5.1).  This stage must not reveal the primary.  It
# writes s_u / s_w to disk and prints only:
#   - the rdiv tie count and the on-ray count (the two named exception classes),
#   - the 18 FORCED-ZERO isotypes U_{j,k}, j+k odd, which are zero for ANY
#     pairing of two parity-closed readouts and therefore say nothing about T_4.
# T_4 and T_off are computed only in stage 3, after the calibration hash.
#
#   s_u(d) = sextant( eis_n( cent( y([d]G) ) ) )     ODD in d  -> parity-legal
#   s_w(d) = sextant( eis_n( d ) )                   ODD in d
#
# The x-readout is NOT used: eis_p(x([d]G)) is EVEN in d, and the channel between
# an even and an odd function is zero by parity before any data -- which is why
# the prior amicable null was uninformative.
#
# Both signs are computed INDEPENDENTLY (never by applying the +3 rule), so that
# the tie / on-ray exceptions can actually break the forced zeros and be caught.

import numpy as np, random as _r, json, hashlib
from arm4_setup_v1 import (P, N, GX, GY, lattice_n, eis_n, cent, U_from_table,
                           absU2)
from lift_sextant_rhombus_law_proof_v2 import sextant

K0 = int(200000)                      # positive scalars; K = 2*K0 = 400000
SEED = int(20260724)

(A0, B0), (A, B), R1, R2, DET = lattice_n()
p_i = int(P); n_i = int(N)

E = EllipticCurve(GF(p_i), [0, 7])
G = E(GX, GY)
assert int(G.order()) == n_i, "generator order != n"

rng = _r.Random(SEED)
ds = [rng.randrange(1, n_i) for _ in range(K0)]

su_p = np.zeros(K0, dtype=np.uint8); su_n = np.zeros(K0, dtype=np.uint8)
sw_p = np.zeros(K0, dtype=np.uint8); sw_n = np.zeros(K0, dtype=np.uint8)
ties = 0; onray = 0


def feat(X):
    """sextant of eis_n(X), plus the two exception flags."""
    global ties, onray
    (u, v), tie = eis_n(int(X), R1, R2, DET)
    if tie: ties += 1
    if u == 0 or v == 0 or u == v: onray += 1
    return sextant(u, v)


import time
t0 = time.time()
for i, d in enumerate(ds):
    Q = Integer(d) * G
    y = int(Q[1])
    su_p[i] = feat(cent(y))
    su_n[i] = feat(cent((-y) % p_i))          # y(-P) = -y(P); computed, not assumed
    sw_p[i] = feat(d)
    sw_n[i] = feat(n_i - d)                   # -d mod n; computed, not assumed
    if i and i % 25000 == 0:
        print(f"   {i}/{K0}  ({time.time()-t0:.0f}s)", flush=True)

print("=" * 78)
print("ARM 4 STAGE 1 — features at secp256k1, K0 =", K0, " K =", 2 * K0)
print("=" * 78)
print(f"  elapsed {time.time()-t0:.0f}s")
print(f"  rdiv TIE count   (of {4*K0} reductions): {ties}")
print(f"  ON-RAY count     (of {4*K0} reductions): {onray}")

# --- forced ledger: independently-computed antipodes must satisfy s(-d)=s(d)+3
viol_u = int(((su_n.astype(int) - su_p.astype(int)) % 6 != 3).sum())
viol_w = int(((sw_n.astype(int) - sw_p.astype(int)) % 6 != 3).sum())
print(f"  s_u(-d) != s_u(d)+3 : {viol_u} of {K0}")
print(f"  s_w(-d) != s_w(d)+3 : {viol_w} of {K0}")

# --- 6x6 table of the TRUE pairing (saved, NOT printed)
tab = [[0] * 6 for _ in range(6)]
for i in range(K0):
    tab[int(su_p[i])][int(sw_p[i])] += 1
    tab[int(su_n[i])][int(sw_n[i])] += 1

print("\n  FORCED ZEROS  U_{j,k}, j+k ODD  (18 isotypes; zero for ANY parity-closed pairing)")
bad = []
for j in range(6):
    for k in range(6):
        if (j + k) % 2 == 1:
            u2 = absU2(U_from_table(tab, j, k))
            if u2 != 0: bad.append((j, k, u2))
print(f"   non-zero forced isotypes: {len(bad)} of 18")
if bad:
    print(f"   {bad[:6]}")
    print(f"   exception ledger: ties={ties}, on-ray={onray}, "
          f"viol_u={viol_u}, viol_w={viol_w}")
    print("   *** HALT CONDITION (spec 4.7): a forced zero is non-zero.")
    print("   *** It is admissible ONLY if it matches the exception signature above.")
else:
    print("   all 18 forced isotypes are exactly zero -- parity premise holds,")
    print("   so the df ledger (17 real df; 5 on the equivariant diagonal) stands.")

np.savez("arm4_features_v1.npz", su_p=su_p, su_n=su_n, sw_p=sw_p, sw_n=sw_n,
         tab=np.array(tab, dtype=np.int64),
         meta=np.array([K0, SEED, ties, onray, viol_u, viol_w], dtype=np.int64))
h = hashlib.sha256(open("arm4_features_v1.npz", "rb").read()).hexdigest()
print(f"\n  features written: arm4_features_v1.npz  sha256 {h[:32]}...")
print("  (T_4 / T_off NOT computed here -- stage 3, after the calibration hash)")
