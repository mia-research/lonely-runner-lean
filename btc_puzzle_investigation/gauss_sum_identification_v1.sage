# Identify the Gauss-sum building blocks exactly.  G(chi) = sum_{x in F_q^*} chi(x) psi(x),
# psi = additive char of F_q via absolute trace to F_p.  Exact in Q(zeta_lcm(12,p)).
import sys
def PR(*a): print(*a); sys.stdout.flush()

def gauss(p):
    q=p*p; F=GF(q,'a'); g=F.multiplicative_generator(); N=q-1
    L=lcm(12,p); C=CyclotomicField(L); zL=C.gen()
    z12=zL**(L//12); zp=zL**(L//p)
    z3=z12**4; z4=z12**3
    dl={}; acc=F(1)
    for e in range(N): dl[acc]=e; acc*=g
    def psi(x): return zp**(ZZ(x.trace()))          # trace to F_p
    def c3(u): return C(0) if u==0 else z3**(dl[u]%3)
    def c4(u): return C(0) if u==0 else z4**(dl[u]%4)
    def Gs(ch): return sum(ch(x)*psi(x) for x in F if x!=0)
    G3=Gs(c3); G4=Gs(c4); G34=Gs(lambda u: c3(u)*c4(u))
    J =sum(c3(t)*c4(F(1)-t) for t in F)
    Jb=sum(c3(t)**2*c4(F(1)-t) for t in F)
    PR("p=%d (p mod 3=%d)" % (p, p%3))
    PR("   G(chi4)          = %s      [is it +p = %d ?]" % (G4, p))
    PR("   G(chi3)          = %s" % G3)
    PR("   G(chi3*chi4)     = %s" % G34)
    PR("   G3*G4/G34        = %s" % (G3*G4/G34))
    PR("   J(chi3,chi4)     = %s" % J)
    PR("   J(chi3bar,chi4)  = %s   [equal to J ? %s]" % (Jb, Jb==J))
for p in (7,19,11):
    gauss(p)
