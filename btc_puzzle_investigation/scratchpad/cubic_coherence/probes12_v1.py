#!/usr/bin/env python3
"""
probes12_v1.py — two PRE-COMMITTED characterizations (no new verdict):
  Probe 1 = X1 subspace-localization secondary of PREREG_subrayleigh_deficit_scaling_v1 (frozen):
            the N7 mean|U| deficit restricted to strata {c=0}(x-only), {b=0}(y-only), {b=c}, bulk, global.
            Question: where does the sub-Rayleigh deficit live now that c=0 is known super-Rayleigh?
  Probe 2 = MC-HP control of PREREG_subrayleigh_cubic_coherence_v1 §4 on the c=0 slice:
            is the slice super-Rayleigh character-specific (Weil) or a generic unit-weight artifact?
Signal path exact int (signal_path_v1). Float = transform/ensemble carve-out.
Model scale only; no transfer to secp.
"""
import numpy as np, sys, time
import signal_path_v1 as sp
import harness_v1 as H

def hermitian_unit_null(n, rng):
    g = np.zeros(n, dtype=np.complex128)
    for d in range(1, n):
        nd = n-d
        if d < nd:
            phi = rng.uniform(0, 2*np.pi); g[d] = np.exp(1j*phi); g[nd] = np.exp(-1j*phi)
        elif d == nd:
            g[d] = rng.choice([1.0, -1.0])
    return g

def mchp_weight(n, rng):
    """permuted character g(d)=zeta_n^{sigma(d)}, sigma(n-d)=-sigma(d): Hermitian + exact value multiset."""
    half = [d for d in range(1, n) if d < n-d]
    vals = list(range(1, len(half)+1)); rng.shuffle(vals)
    sig = np.zeros(n, dtype=np.int64)
    for d, v in zip(half, vals):
        sig[d] = v; sig[n-d] = (n-v) % n
    en = np.exp(2j*np.pi*np.arange(n)/n)
    return en[sig]

def strata_masks(p):
    b = np.arange(p)[:,None]*np.ones(p,dtype=int)[None,:]
    c = np.ones(p,dtype=int)[:,None]*np.arange(p)[None,:]
    m_c0 = (c==0) & (b!=0)                     # x-only slice
    m_b0 = (b==0) & (c!=0)                     # y-only slice
    m_bc = (b==c) & (b!=0)                     # diagonal
    notO = ~((b==0)&(c==0))
    m_bulk = notO & (c!=0) & (b!=0) & (b!=c)
    return dict(c0=m_c0, b0=m_b0, bc=m_bc, bulk=m_bulk, glob=notO)

def probe1(primes, K, seed=101):
    print("=== PROBE 1 — N7 deficit by stratum (D>0 = sub-Rayleigh; D<0 = super-Rayleigh) ===")
    print("    p |   c=0(x) |   b=0(y) |    b=c   |   bulk   |  GLOBAL")
    for p in primes:
        r = sp.orbit(p); n,X,Y,facs = r; X=np.array(X); Y=np.array(Y)
        ep,en = H.root_tables(p,n)
        Uc = H.U_transform(H.char_weight(n,en),X,Y,p,n,ep)
        M = strata_masks(p)
        ac = np.abs(Uc)
        char = {k: ac[m].sum() for k,m in M.items()}
        rng = np.random.default_rng(seed+p)
        acc = {k: 0.0 for k in M}
        for _ in range(K):
            Un = H.U_transform(hermitian_unit_null(n,rng),X,Y,p,n,ep)
            an = np.abs(Un)
            for k,m in M.items(): acc[k] += an[m].sum()
        D = {k: (acc[k]/K - char[k])/(acc[k]/K) for k in M}
        print(f"{p:6d} | {D['c0']:+7.3%} | {D['b0']:+7.3%} | {D['bc']:+7.3%} | {D['bulk']:+7.3%} | {D['glob']:+7.3%}")

def probe2(primes, K, seed=202):
    print("\n=== PROBE 2 — c=0 slice: character vs permuted-character (MC-HP) vs random-magnitude (B0) ===")
    print("    p | Dchar/B0 | DMCHP/B0 | (both<0 super-R; Dchar<<DMCHP => character-specific, not generic)")
    for p in primes:
        r = sp.orbit(p); n,X,Y,facs = r; X=np.array(X)
        en = np.exp(2j*np.pi*np.arange(n)/n)
        # character slice
        def slice_L1(weight):
            A = np.zeros(p, dtype=np.complex128)
            np.add.at(A, X, weight); A[0]-=weight[0]
            T = np.fft.ifft(A)*p
            return np.abs(T[1:]).sum()
        L1_char = slice_L1(en[(np.arange(n))%n])
        rng = np.random.default_rng(seed+p)
        # MC-HP mean
        L1_mchp = np.mean([slice_L1(mchp_weight(n,rng)) for _ in range(K)])
        # B0 max-entropy magnitude null mean (Rayleigh at fixed slice-L2)
        E = sp.slice_L2_anchor(p,n); nreps=(p-1)//2; N0=20000; L1b=np.empty(N0)
        for i in range(0,N0,4000):
            m=min(4000,N0-i); xi=rng.standard_exponential((m,nreps))
            rho=np.sqrt(xi*(E/(2*xi.sum(axis=1)))[:,None]); L1b[i:i+m]=2*rho.sum(axis=1)
        B0 = L1b.mean()
        print(f"{p:6d} | {(B0-L1_char)/B0:+7.3%} | {(B0-L1_mchp)/B0:+7.3%}")

if __name__ == "__main__":
    t0=time.time()
    P1 = [349,577,823,1093,1471,1987]
    P2 = [349,577,823,1093,1471,1987,2671,3607,4861,6571]
    probe1(P1, K=60)
    probe2(P2, K=40)
    print(f"\nwall={time.time()-t0:.1f}s")
