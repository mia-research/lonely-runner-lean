import numpy as np, sys
def PR(*a): print(*a); sys.stdout.flush()
def sat(p,B=7):
    E=EllipticCurve(GF(p),[0,B]); n=E.order()
    if not is_prime(n): return None
    G=E.gens()[0]; s=np.zeros(n,dtype=np.int64); P=E(0)
    for d in range(1,n):
        P=P+G; x,y=P.xy(); y=ZZ(y)
        s[d]= 0 if y==0 else kronecker(y,p)
    odd = all(s[n-d]==-s[d] for d in range(1,n))
    even= all(s[n-d]== s[d] for d in range(1,n))
    V=np.fft.fft(s.astype(float)); m=np.abs(V[1:]).max()
    return n,float(m/(4*sqrt(p))),odd,even
c1=c3=0
PR("p%4 | p     | n     | sat   | odd  | even")
for p in primes(500,4000):
    if c1>=5 and c3>=5: break
    if p%4==1 and c1>=5: continue
    if p%4==3 and c3>=5: continue
    r=sat(p)
    if r is None: continue
    n,st,od,ev=r
    if n<1000: continue
    PR(" %d  | %-5d | %-5d | %.4f | %-4s | %-4s"%(p%4,p,n,st,od,ev))
    if p%4==1: c1+=1
    else: c3+=1
