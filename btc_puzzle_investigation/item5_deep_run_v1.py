#!/usr/bin/env python3
"""item5_deep_run_v1.py -- Item 5 deep run, chunked + parallel + checkpointed.

Frozen spec: PREREG_item5_deep_inversion_v1.md.  Nothing here may be changed after launch.

STRUCTURE
  * work is split into CHUNKS of `CH` scalars; each chunk is an independent job.
  * every finished chunk is checkpointed to chunks/<arm>_<idx>.npz, so a crash or a kill loses at
    most one chunk and a restart skips completed work.
  * the null uses EXACT permutation moments (O(M)) rather than 2000 shuffles of a 6.25M array,
    and those moments are VALIDATED against explicit shuffles on a subsample (C-NULLSD).
"""

import os
import sys
import time
import numpy as np
from random import Random
from multiprocessing import Pool
from gmpy2 import powmod, invert, mpz

P = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
N = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
GX = mpz(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
GY = mpz(0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
LAM = mpz(0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72)
HALF = (P - 1)//2

M_TARGET = 6_250_000
CH = 62_500                      # 100 chunks per arm
OUT = "chunks_item5"
ARMS = [("k128", 2**127, 2**128), ("k135", 2**134, 2**135),
        ("k160", 2**159, 2**160), ("ctrl", 1, int(N))]


def jdbl(A):
    X, Y, Z = A
    if Y == 0:
        return (mpz(0), mpz(0), mpz(0))
    S = 4*X*Y*Y % P
    M_ = 3*X*X % P
    Xr = (M_*M_ - 2*S) % P
    return (Xr, (M_*(S - Xr) - 8*Y**4) % P, 2*Y*Z % P)


def jadd(A, B):
    X1, Y1, Z1 = A
    X2, Y2, Z2 = B
    if Z1 == 0:
        return B
    if Z2 == 0:
        return A
    Z1Z1 = Z1*Z1 % P
    Z2Z2 = Z2*Z2 % P
    U1 = X1*Z2Z2 % P
    U2 = X2*Z1Z1 % P
    S1 = Y1*Z2*Z2Z2 % P
    S2 = Y2*Z1*Z1Z1 % P
    if U1 == U2:
        return jdbl(A) if S1 == S2 else (mpz(0), mpz(0), mpz(0))
    H = (U2 - U1) % P
    R = (S2 - S1) % P
    H2 = H*H % P
    H3 = H2*H % P
    U1H2 = U1*H2 % P
    X3 = (R*R - H3 - 2*U1H2) % P
    return (X3, (R*(U1H2 - X3) - S1*H3) % P, Z1*Z2*H % P)


def jmul(k):
    R = (mpz(0), mpz(0), mpz(0))
    Q = (GX, GY, mpz(1))
    while k:
        if k & 1:
            R = jadd(R, Q)
        Q = jdbl(Q)
        k >>= 1
    return R


def batch_x(pts):
    zs = [p[2] for p in pts]
    pre = [mpz(1)]*(len(zs)+1)
    for i, z in enumerate(zs):
        pre[i+1] = pre[i]*z % P
    inv = invert(pre[-1], P)
    out = [None]*len(zs)
    for i in range(len(zs)-1, -1, -1):
        zi = inv*pre[i] % P
        inv = inv*zs[i] % P
        out[i] = pts[i][0]*zi % P*zi % P
    return out


def readout(ds):
    return np.array([1 if powmod(x, HALF, P) == 1 else -1 for x in batch_x([jmul(d) for d in ds])],
                    dtype=np.int8)


def work(job):
    name, lo, hi, idx, seed = job
    path = "%s/%s_%04d.npz" % (OUT, name, idx)
    if os.path.exists(path):
        return path
    rng = Random(seed)
    ds = [mpz(rng.randrange(lo, hi)) for _ in range(CH)]
    inv = [invert(d, N) for d in ds]
    nfix = sum(1 for d, e in zip(ds, inv) if e == d or e == (N - d) % N)
    keep = [i for i in range(CH) if not (inv[i] == ds[i] or inv[i] == (N - ds[i]) % N)]
    a = readout([ds[i] for i in keep])
    b = readout([inv[i] for i in keep])
    # C-DUP key: canonical mu_6 class representative of d
    keys = np.array([int(min(int(ds[i]), int(N - ds[i]),
                             int(LAM*ds[i] % N), int(N - LAM*ds[i] % N),
                             int(LAM*LAM*ds[i] % N), int(N - LAM*LAM*ds[i] % N)) % (2**62))
                     for i in keep], dtype=np.int64)
    np.savez_compressed(path, a=a, b=b, nfix=nfix, keys=keys)
    return path


if __name__ == "__main__":
    NW = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    os.makedirs(OUT, exist_ok=True)
    jobs = []
    nch = M_TARGET//CH
    for ai, (name, lo, hi) in enumerate(ARMS):
        for i in range(nch):
            jobs.append((name, lo, hi, i, 20260801 + 1000*ai + i))
    todo = [j for j in jobs if not os.path.exists("%s/%s_%04d.npz" % (OUT, j[0], j[3]))]
    print("item5 deep run: %d arms x %d chunks x %d = %d scalars/arm; %d chunks to do, %d workers"
          % (len(ARMS), nch, CH, nch*CH, len(todo), NW), flush=True)
    t0 = time.time()
    done = len(jobs) - len(todo)
    with Pool(NW) as pool:
        for _ in pool.imap_unordered(work, todo, chunksize=1):
            done += 1
            if done % 10 == 0:
                el = time.time() - t0
                frac = (done - (len(jobs)-len(todo)))/max(1, len(todo))
                print("  %d/%d chunks  [%.0fs elapsed, ~%.0fs left]"
                      % (done, len(jobs), el, el/max(frac, 1e-9) - el), flush=True)
    print("ALL CHUNKS DONE [%.0fs]" % (time.time()-t0), flush=True)
