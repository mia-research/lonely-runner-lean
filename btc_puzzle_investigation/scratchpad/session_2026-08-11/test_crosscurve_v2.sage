CDFp=CDF
def V1(E, a):
    n=E.gens()[0].order(); G=E.gens()[0]; p=E.base_field().order()
    s=CDF(0)
    cur=G
    for d in range(1,n):
        yd=ZZ(cur[1])
        chi=1 if kronecker(yd, p)==1 else (-1 if kronecker(yd,p)==-1 else 0)
        s+= chi*CDF(exp(2*pi*I*a*d/n))
        cur=cur+G
    return s

p=43
curves=[("CM A=0 B=7",0,7),("nonCM A=1 B=3",1,3),("nonCM A=1 B=5",1,5)]
print(f"p={p}. §2A: is V1(a)=sum chi2(y_d) e_n(ad) purely imaginary for ALL curves?", flush=True)
for name,A,B in curves:
    E=EllipticCurve(GF(p),[A,B]); n=E.gens()[0].order()
    for a in [1,2]:
        v=V1(E,a)
        re,im=v.real(),v.imag()
        # census: e2(a) = e1(a)^2 + p  -> if e1=V1 imaginary, e1^2+p = p - |V1|^2
        cen = p + v^2   # complex; should be real
        print(f"  {name:14s} n={n} a={a}: V1={re:+.4f}{im:+.4f}i  purely-imag:{abs(re)<1e-6} | V1^2+p={cen.real():+.4f}{cen.imag():+.4f}i (real:{abs(cen.imag())<1e-6})", flush=True)

# doc's e1(CM,a=1) = -3.496863i ; e1(nonCM1,a=1)=+11.461683i ; check we reproduce magnitudes
print("\n  doc values: CM a=1 e1=-3.4969i; nonCM1 a=1 e1=+11.4617i; nonCM2 a=1 e1=+8.7876i", flush=True)

print("\n§3 CM gate: GLV (beta x,y) on curve iff A=0:", flush=True)
Fp=GF(p); beta=[Fp(b) for b in range(2,p) if Fp(b)^3==1 and Fp(b)!=1][0]
for name,A,B in curves:
    E=EllipticCurve(Fp,[A,B]); P=E.gens()[0]
    print(f"  {name:14s}: GLV exists {P[1]^2==(beta*P[0])^3+A*(beta*P[0])+B}", flush=True)
