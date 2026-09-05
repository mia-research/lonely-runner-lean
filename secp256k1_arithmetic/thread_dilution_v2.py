#!/usr/bin/env python3
"""
Dilution test v2 (2026-07-11): built on the EXACT ZFR Gram construction
(btc_puzzle_investigation/zfr_rank2_reproduce.py), extended to the CM Hecke
character, with the decisive PROJECT-OUT-THE-CONDUCTOR test.

ZFR template:
  features  = low primes P0 (this is the user's "X" = number of primes)
  samples   = (q, chi_j),  q prime in [Q/2,Q],  chi_j the characters mod q
  F[(q,j), p0] = (chi_j(p0) - mu) / sqrt(q-1)
  G_Q = F^H F   (|P0| x |P0| Hermitian);   ratio = lambda_max(G_Q)/Tr(G_Q).

Variants:
  DIR   chi_j = ALL non-principal Dirichlet characters mod q   (ZFR -> flat/orthogonal)
  CM6   chi_j = the SEXTIC (order-6) characters mod q, q==1 mod 6
        (the CM Hecke finite part is order 6 -> shares the chi_-3 conductor)
  Each low prime p0 also carries a chi_-3 value; the conductor direction is the
  loading  c_{p0} = chi_-3(p0)  projected into feature space.

Decisive tests (per DILUTION_CHECK_v1 sec 4):
  T1  ratio vs Q, and vs X (|P0|)   -> reproduce "depends on Q not X"
  T2  lambda_max absolute + lambda_max/lambda_2 (gap)  -> Tr-growth vs real mode
  T3  PROJECT OUT the chi_-3 / conductor direction; re-measure ratio.
      If ratio collapses toward the flat 1/|P0| floor  => the common mode WAS the
      conductor shadow (residue shadows of one conductor), not a spectral gap.

(Spectral/statistical analysis of the CM L-function's characters; floats are the
correct tool here -- this is NOT the puzzle key signal path.)
"""
import numpy as np, cmath, math

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
PR=sieve(300000)
def primitive_root(q):
    facs=set(); m=q-1; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//f,q)!=1 for f in facs): return g
def chi3(p):            # Dirichlet character mod 3 (the CM conductor)
    r=p%3
    return 0 if r==0 else (1 if r==1 else -1)

def build_F(P0, Q, kind):
    """rows = (q, character); cols = low primes P0."""
    qs=[q for q in PR if Q//2<=q<=Q]
    if kind=="CM6": qs=[q for q in qs if q%6==1]     # need order-6 chars => q==1 mod6
    rows=[]
    for q in qs:
        g=primitive_root(q); ind={}; cur=1
        for e in range(q-1): ind[cur%q]=e; cur=cur*g%q
        inv=1.0/math.sqrt(q-1)
        if kind=="DIR":  js=range(1,q-1)             # all non-principal
        elif kind=="CM6":js=[k*(q-1)//6 for k in (1,2,3,4,5)]  # the order-6 characters
        for j in js:
            row=[cmath.exp(2j*cmath.pi*j*ind[p0%q]/(q-1))*inv if p0%q!=0 else 0.0 for p0 in P0]
            rows.append(row)
    return np.array(rows,dtype=complex), qs

def stats(P0, Q, kind):
    F,qs=build_F(P0,Q,kind)
    G=F.conj().T@F
    ev=np.linalg.eigvalsh(G)[::-1].real
    tr=ev.sum()
    # conductor (chi_-3) loading in feature space, normalized
    c=np.array([chi3(p) for p in P0],dtype=float)
    c=c/ (np.linalg.norm(c)+1e-12)
    # also the empirical top eigenvector alignment with c
    _,evec=np.linalg.eigh(G); top=evec[:,-1].real; top=top/(np.linalg.norm(top)+1e-12)
    align=abs(np.dot(top,c))
    # project out conductor direction
    P=np.eye(len(P0))-np.outer(c,c)
    Gp=P@G@P
    evp=np.linalg.eigvalsh(Gp)[::-1].real
    return dict(ratio=ev[0]/tr, lmax=ev[0], l2=ev[1] if len(ev)>1 else 0.0,
                gap=ev[0]/max(ev[1],1e-12), tr=tr, d=len(P0), nsamp=F.shape[0],
                align=align, ratio_proj=evp[0]/max(evp.sum(),1e-12), floor=1.0/len(P0))

print("=== T1: reproduce 'ratio depends on Q, not X' (DIR = Dirichlet ZFR) ===")
for kind in ("DIR","CM6"):
    print(f"\n[{kind}]  ratio = lambda_max/Tr")
    print(f"  {'X\\Q':>6}" + "".join(f"{q:>9}" for q in (5,10,20,50)))
    for X in (30,60,120):
        P0=PR[:X]
        row=[]
        for Q in (5,10,20,50):
            try: row.append(stats(P0,Q,kind)["ratio"])
            except Exception: row.append(float('nan'))
        print(f"  {X:>6}" + "".join(f"{r:>9.3f}" for r in row))

print("\n=== T2 + T3: gap, alignment, project-out  (X=120 low primes) ===")
P0=PR[:120]
print(f"{'kind':>5} {'Q':>4} {'d':>4} {'nsamp':>6} | {'ratio':>7} {'floor1/d':>8} "
      f"{'lmax':>8} {'gap l1/l2':>9} | {'align χ₋₃':>9} {'ratio_projout':>13}")
for kind in ("DIR","CM6"):
    for Q in (10,20,50,100):
        try:
            s=stats(P0,Q,kind)
            print(f"{kind:>5} {Q:>4} {s['d']:>4} {s['nsamp']:>6} | {s['ratio']:>7.3f} "
                  f"{s['floor']:>8.3f} {s['lmax']:>8.2f} {s['gap']:>9.2f} | "
                  f"{s['align']:>9.3f} {s['ratio_proj']:>13.3f}")
        except Exception as e:
            print(f"{kind:>5} {Q:>4}  -- {e}")

print("\nRead-out:")
print(" DIR flat (ratio ~ 1/d, gap ~1, align low) = orthogonal, NO conductor mode.")
print(" CM6 elevated ratio + gap>1 + align~1 + ratio COLLAPSES after project-out")
print("   => the elevated top mode IS the chi_-3 conductor shadow (user's hypothesis).")
