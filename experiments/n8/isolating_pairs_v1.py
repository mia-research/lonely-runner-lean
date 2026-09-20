"""Which PAIRS of moduli leave an admissible u-set with no two consecutive members?
That is the b=2 phenomenon one level up: b=2 in q-space forced odd q; here a pair forces an
isolated set in u-space."""
from math import lcm, gcd
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clr(b,u): return L(b) <= (2*u+1) % b <= U(b)
def allowed(bs):
    M=lcm(*bs)
    return [u for u in range(M) if all(clr(b,u) for b in bs)], M
def has_consec(A,M): return any(((u+1)%M) in set(A) for u in A)
print("the 5 & 10 pair, worked out:")
A5,_=allowed([5]); A10,_=allowed([10]); A,M=allowed([5,10])
print(f"   b=5  admissible u mod 5 : {A5}")
print(f"   b=10 admissible u mod 10: {A10}")
print(f"   together, mod {M}: {A}   two consecutive? {has_consec(A,M)}")
print(f"   gaps between consecutive members (cyclic): "
      f"{[ (A[(i+1)%len(A)]-A[i])%M for i in range(len(A))]}")
print()
print("all pairs (b, b') with b < b' <= 60 whose admissible set has NO two consecutive:")
bad=[]
for b in range(2,61):
    for bp in range(b+1,61):
        if lcm(b,bp)>4000: continue
        A,M=allowed([b,bp])
        if A and not has_consec(A,M): bad.append((b,bp,len(A),M))
print(f"   {len(bad)} such pairs:")
for b,bp,n,M in bad[:25]:
    print(f"      ({b:2d},{bp:2d})  admissible {n}/{M}   ratio b'/b = {bp/b:.2f}"
          f"{'   b_prime = 2b' if bp==2*b else ''}")
print()
print("   of those, how many have b' = 2b?", sum(1 for b,bp,_,_ in bad if bp==2*b))
print("   single moduli with no two consecutive:",
      [b for b in range(2,61) if (lambda r: r[0] and not has_consec(*r))(allowed([b]))])
