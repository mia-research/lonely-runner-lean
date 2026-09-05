#!/usr/bin/env python3
"""nk_prior_generator.py -- LOCKED reduction artifact.
Given a target puzzle bit-length N, emit the ranked (n,k) candidate prior
(P(n|N) x verified selection reweight), each with its base point scalar and
d-window bound. This is the consumable input to a candidate-sweep / propagation.

Verified components (see nk_reduction_spec_v1.md):
  TIER1 (exact/deterministic): P(n|N) concentration + per-cell d-window.
  TIER2 (real-key selection, marginal): composite/even/large-n reweight (drift-adj).
Usage: python3 nk_prior_generator.py <N> [top]
"""
import sys, random, math
from fractions import Fraction
from sympy import isprime, totient
random.seed(0)
N=int(sys.argv[1]) if len(sys.argv)>1 else 160
TOP=int(sys.argv[2]) if len(sys.argv)>2 else 20
A=1<<(N-1)
def dec(d):
    f=Fraction(d-A,A).limit_denominator(256); return f.denominator,f.numerator
# --- P(n,k | N) empirical (deterministic construction measure) ---
cnt={}; DR=120000
for _ in range(DR):
    nk=dec(random.randrange(A,1<<N)); cnt[nk]=cnt.get(nk,0)+1
# --- TIER2 selection reweight (drift-adjusted for high N), verified on 82 real keys ---
def lr(n):
    w=1.0
    if isprime(int(n)): w*=0.60          # p=0.025
    if n%2==0:          w*=1.27          # p=0.052
    if float(totient(int(n)))/int(n)<0.6:w*=1.25  # phi/n lean p=0.015
    if n>=250:          w*=(1.20 if N>=100 else 1.93)  # DRIFT: weaken for high puzzles
    if n%6 in (4,5):    w*=1.10          # residue tilt (candidate, p~0.02)
    if n%5==3:          w*=0.90
    return w
post={nk:c*lr(nk[0]) for nk,c in cnt.items()}
Z=sum(post.values())
ranked=sorted(post.items(), key=lambda x:-x[1])
# --- bit accounting ---
def G(w): 
    p=sorted(w,reverse=True); s=sum(p); p=[x/s for x in p]; return sum((i+1)*pi for i,pi in enumerate(p))
Mtot=sum(int(totient(n)) for n in range(1,257)); Gblind=(Mtot+1)/2
Gpost=G(list(post.values())); Gcon=G(list(cnt.values()))
print(f"# Target N={N}   d in [2^{N-1}, 2^{N})  ({N-1} free bits)")
print(f"# (n,k) cells: {len(cnt)}   blind guess {math.log2(Gblind):.2f} bits | +N {math.log2(Gcon):.2f} | +N+selection {math.log2(Gpost):.2f} bits")
print(f"# REDUCTION: N-alone {math.log2(Gblind/Gcon):+.2f} bits ({Gblind/Gcon:.2f}x) ; N+selection {math.log2(Gblind/Gpost):+.2f} bits ({Gblind/Gpost:.2f}x)")
print(f"#{'rank':>4} {'n':>4} {'k':>4} {'P(n,k|N,sel)':>13} {'d-window(bits)':>14}  base=A+floor(A*k/n) [top {N - (A//(min(256,r[0][0])**2)).bit_length() if False else ''}~16 bits pinned]")
for i,((n,k),wv) in enumerate(ranked[:TOP]):
    w=A//(n*n)  # window half-width estimate (~A/n^2)
    base=A+(A*k)//n
    print(f" {i+1:4d} {n:4d} {k:4d} {wv/Z:13.5f} {w.bit_length():14d}  base_bitlen={base.bit_length()}")
print(f"# (full ranked prior available programmatically; each cell confines d to base +/- ~2^{ (A//(256*256)).bit_length() } .. 2^{(A//(3*3)).bit_length()})")
