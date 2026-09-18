"""Parallel session claims K = 28 is "the absolute geometric limit for 8 runners", arguing that for
K >= 29 the system of 29 half-spaces "becomes over-constrained and empty".

That is a non-sequitur: adding half-spaces contracts a cone, it does not empty it at any particular
K.  And it is not a small claim -- a uniform bound on the cascade is EQUIVALENT to Existence at
order 8 (LRC/Spec/Target.lean, existence_of_capped / capped_of_existence, both proved).  So the
claim, if true, settles the open problem, and cannot follow from "constraints accumulate".

Two tests:
 (1) verify their two wall derivations and the 224.999 / 225.001 claim
 (2) the measured trend: does cell width hit zero at 28, or decay smoothly through it?
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, log, exp
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def depth(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
A=[30,74,96,127,159,175,224]
print("(1) their wall derivations")
print(f"    wall 1: 175/41 = d0/7  =>  d0 = 1225/41 = {float(F(1225,41)):.6f}")
print(f"       depth just below: {depth(sorted([F(1225,41)-F(1,100000)]+A[1:]))}"
      f"   just above: {depth(sorted([F(1225,41)+F(1,100000)]+A[1:]))}   (they say 18 / 23)")
print(f"    wall 2: d6/9 = 175/7 = 25  =>  d6 = 225")
print(f"       d6 = 224.999: {depth(sorted(A[:6]+[F(224999,1000)]))}"
      f"   d6 = 225.001: {depth(sorted(A[:6]+[F(225001,1000)]))}   (they say 23 / 1)")

print("\n(2) does the depth-K cell measure hit zero at 28, or decay smoothly?")
print("    measured width law: log(width) = 3.710 - 0.1754 K   (corr -0.718, 96 cells)")
for K in (20,23,25,28,29,32,40):
    print(f"      K = {K:>3}: predicted cell width {exp(3.710-0.1754*K):.6f}")
print("    -> the fit decays smoothly and is positive at every K; nothing in it singles out 29.")

print("\n(3) the depth-28 cell's own width, measured (family B, d_min axis):")
REST=[205,234,256,286,323,366]
L,H=F(488,10),F(489,10)
for _ in range(50):
    M=(L+H)/2
    if depth(sorted([M]+REST))==28: H=M
    else: L=M
lo=H
L,H=F(490,10),F(491,10)
for _ in range(50):
    M=(L+H)/2
    if depth(sorted([M]+REST))==28: L=M
    else: H=M
print(f"      [{float(lo):.6f}, {float(L):.6f}]  width {float(L-lo):.6f}")
print(f"      predicted by the law at K=28: {exp(3.710-0.1754*28):.6f}")
print("      -> the depth-28 cell has POSITIVE, ordinary width; it is not a degenerate limit point.")
