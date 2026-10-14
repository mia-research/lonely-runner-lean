#!/usr/bin/env python3
"""HONEST BRUTE FORCE -- simulate the runners, no criterion, no shortcut.
Speeds 2,6,7,8,10,13,14 plus the stationary runner. Step through time, sort the
positions, measure the minimum gap. Run until all runners are back home together."""
import math
V=[0,2,6,7,8,10,13,14]; n=len(V)
def mingap(t):
    P=sorted((v*t)%1.0 for v in V)
    g=min(P[i+1]-P[i] for i in range(n-1))
    return min(g, 1.0-P[-1]+P[0])
print("simulating 8 runners at speeds", V)
print("threshold for GLOBAL isolation (all 8 gaps): 1/8 = 0.125")
print()
# when does everyone get home together?
print("all runners at position 0 simultaneously requires v*t integer for every v.")
print("speeds are integers, so t = 1 works, and t = 1 is the smallest such time.")
for t in (0.25,0.5,1.0):
    P=[(v*t)%1.0 for v in V]
    print(f"   t = {t}: positions {[round(p,6) for p in P]}  all home: {all(abs(p)<1e-12 for p in P)}")
print()
STEP=10**7
print(f"sweeping t from 0 to 1 in {STEP:,} steps (dt = 1e-7) ...")
best=0.0; bestt=0.0; hits=0
for k in range(1,STEP):
    t=k/STEP
    g=mingap(t)
    if g>best: best,bestt=g,t
    if g>=0.125: hits+=1
print(f"   best minimum gap seen: {best:.9f}  at t = {bestt:.7f}")
print(f"   number of sampled times with min gap >= 1/8: {hits}")
print()
print("continuing PAST t=1, to t=5, in case something new happens:")
best2=0.0; bestt2=0.0; hits2=0
for k in range(1,5*10**6):
    t=k/10**6
    g=mingap(t)
    if g>best2: best2,bestt2=g,t
    if g>=0.125: hits2+=1
print(f"   best over [0,5]: {best2:.9f} at t = {bestt2:.6f};  times with gap >= 1/8: {hits2}")
print()
print("EXACT confirmation. The min-gap is piecewise linear; two gaps are equal when")
print("((v_a-v_b)-(v_c-v_d))*t is an integer, so every candidate optimum is t = k/D with")
print("D a difference-of-differences. For these speeds those all divide lcm(1..14)=360360.")
from fractions import Fraction as F
D=360360; best3=(F(0),None)
for k in range(D):
    t=F(k,D); P=sorted({F(v)*t%1 for v in V})
    if len(P)<n: continue
    g=min(min(P[i+1]-P[i] for i in range(n-1)), 1-P[-1]+P[0])
    if g>best3[0]: best3=(g,t)
print(f"   exact maximum of the minimum gap = {best3[0]} = {float(best3[0]):.9f} at t = {best3[1]}")
print(f"   global isolation needs 1/8 = 0.125  ->  attained: {best3[0]>=F(1,8)}")
