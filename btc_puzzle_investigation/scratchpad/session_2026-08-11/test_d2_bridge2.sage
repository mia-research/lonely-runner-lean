p=43; B=7; Fp=GF(p)
E=EllipticCurve(Fp,[0,B]); G=E(2,12); n=31
# doc's convention: lambda=5
lam=5; assert (lam*G).order()==31
# beta for THIS lambda: [5]G = (beta*2, 12) -> beta = x([5]G)/2
P5=5*G; beta=Fp(P5[0])/Fp(2); print("lambda=5 => beta =", beta, " beta^3=",beta^3)
b2=beta^2
def j_chi3(x):  # public cubic-char orbit coordinate
    t=Fp(x)^((p-1)//3); return {Fp(1):0,beta:1,b2:2}[t]

# ---- §3 as the doc states it: j = lambda-orbit position, d0 = j=0 rep ----
orbits={}
for d in range(1,n):
    key=tuple(sorted([(d*lam**k)%n for k in range(3)]))
    orbits.setdefault(key,[]).append(d)
# for the formula we need, for each d, its (d0, j) with d = d0*lam^j mod n
dj={}
for key,mem in orbits.items():
    d0=min(mem)  # doc uses the small representative (orbit lists start at d0)
    for d in mem:
        j=[k for k in range(3) if (d0*lam**k)%n==d][0]
        dj[d]=(d0,j)
print("\n§3 congruence law d ≡ d0*(-1)^j - floor(d0*lam^j/n) (mod 3), j = lambda-orbit position:")
ok=0
for d in range(1,n):
    d0,j=dj[d]; carry=(d0*lam**j)//n
    if (d0*(-1)**j - carry)%3 == d%3: ok+=1
print(f"  holds {ok}/{n-1}  (this is the identity d=d0*lam^j - n*floor(...), reduced mod 3)")

# ---- CRUX A: does the PUBLIC chi3 orbit-coordinate j equal the lambda-orbit position? ----
print("\n§2 check: public j_chi3(x_P) vs lambda-orbit position:")
match=sum(1 for d in range(1,n) if j_chi3((d*G)[0])==dj[d][1])
print(f"  j_chi3 == lambda-orbit j for {match}/{n-1} points")

# ---- CRUX B: does PUBLIC data (j_chi3) determine d mod 3? ----
from collections import defaultdict
pub=defaultdict(set)
for d in range(1,n):
    pub[j_chi3((d*G)[0])].add(d%3)
print("\nCRUX: public j_chi3 -> possible d mod 3:")
for j in [0,1,2]: print(f"  j_chi3={j}: d mod 3 in {sorted(pub[j])}")

# ---- CRUX C: is d mod 3 recoverable WITHOUT d0? The formula needs d0 & carry(d0). ----
# Show: fixing the PUBLIC j, the carry floor(d0*lam^j/n) ranges over multiple values as d0 varies.
print("\nDoes the carry floor(d0*lam^j/n) follow from public data? (needs d0=DLP)")
for j in [0,1,2]:
    carries=set((dj[d][0]*lam**j)//n for d in range(1,n) if dj[d][1]==j)
    print(f"  j={j}: carry takes values {sorted(carries)} across the different d0 (unknown without DLP)")
