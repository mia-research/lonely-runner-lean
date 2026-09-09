r"""
ok_extremal_v1 -- understand the exception.  E = (2,6,7,8,10,13,14), int X = 93/1820.

Note the decomposition   E = 2*{1,3,4,5,7}  u  {7,13},
and {1,3,4,5,7} is exactly the unique cell where (H') failed (u = 9/14, |S| = 5/14).
u is dilation-invariant, so u(2F) = u(F) = 9/14; adding 7 and 13 lifts it to 1727/1820.

Work in t directly: a witness is t with ||e t|| >= 1/8 for all e.  All breakpoints are at
multiples of 1/(8L), L = lcm(E), so the loneliness set G is an exact union of such cells and
|G| = int X / 8.
"""
from fractions import Fraction as F
from functools import reduce
from math import lcm, gcd

E=(2,6,7,8,10,13,14)
L=reduce(lcm,E); N=8*L
print(f"E = {E}   L = lcm = {L}   N = 8L = {N}")
print(f"decomposition: 2*(1,3,4,5,7) = {tuple(2*e for e in (1,3,4,5,7))}, plus {sorted(set(E)-{2,6,8,10,14})}")

def nrm(a,b):
    """||a/b|| as a Fraction"""
    r=F(a%b,b)
    return min(r,1-r)

G=[]
for k in range(N):
    if all(nrm(e*k, N) >= F(1,8) for e in E):
        G.append(k)
print(f"\nwitnesses k in [0,{N}) : {len(G)}   measure |G| = {F(len(G),N)} = {float(F(len(G),N)):.8f}")
print(f"   int X = 8|G| = {8*F(len(G),N)}   (target 93/1820 = {F(93,1820)})  MATCH: {8*F(len(G),N)==F(93,1820)}")

# group consecutive k into intervals
runs=[]; s=G[0]; p=G[0]
for k in G[1:]:
    if k==p+1: p=k
    else: runs.append((s,p)); s=k; p=k
runs.append((s,p))
print(f"\n{len(runs)} maximal runs of consecutive witnesses (out of {len(G)} points):")
for a,b in runs[:8]:
    print(f"   k in [{a},{b}]  ({b-a+1} pts)  t = [{F(a,N)}, {F(b,N)}] ~ [{float(F(a,N)):.6f},{float(F(b,N)):.6f}]")
if len(runs)>8: print(f"   ... and {len(runs)-8} more")

k0=G[0]
print(f"\nat the first witness k = {k0}  (t = {F(k0,N)} = {float(F(k0,N)):.8f}):")
print(f"   {'e':>4} {'||e t||':>12} {'~':>10}  {'slack over 1/8':>16}")
for e in sorted(E):
    v=nrm(e*k0,N)
    print(f"   {e:>4} {str(v):>12} {float(v):10.6f}  {str(v-F(1,8)):>16}")
tight=[e for e in E if nrm(e*k0,N)==F(1,8)]
print(f"   runners exactly AT the 1/8 boundary: {tight}")

# how much does each subset contribute?  u of the doubled (H') set alone
def u_of(S):
    Ls=reduce(lcm,S); Ns=8*Ls
    good=sum(1 for k in range(Ns) if all(nrm(e*k,Ns)>=F(1,8) for e in S))
    return 1-F(good*8,Ns)*F(1,8)*8/8, F(good,Ns)
for S in [(1,3,4,5,7),(2,6,8,10,14),(2,6,8,10,14,7),(2,6,8,10,14,13),E]:
    Ls=reduce(lcm,S); Ns=8*Ls
    good=sum(1 for k in range(Ns) if all(nrm(e*k,Ns)>=F(1,8) for e in S))
    print(f"   |G({S})| = {F(good,Ns)} = {float(F(good,Ns)):.8f}   int X = {8*F(good,Ns)}")
