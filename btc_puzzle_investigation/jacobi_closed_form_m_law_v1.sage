# EXACT. Test:  J(chi3,chi4) = -p  on F_{p^2} for p = 7 mod 12,
# and that it reproduces m = Re(S)/p with S = sum_{x in F_q} chi4(x^3+B).
# Characters via discrete log in F_q^*; values as exact CyclotomicField(12) elements.
import sys
def PR(*a): print(*a); sys.stdout.flush()
C = CyclotomicField(12); z12 = C.gen()
z3 = z12**4          # primitive cube root
z4 = z12**3          # primitive 4th root (i)

def analyze(p, Bs=(7,2,11)):
    q = p*p
    F = GF(q, 'a'); g = F.multiplicative_generator()
    N = q - 1
    dlog = {}
    acc = F(1)
    for e in range(N):
        dlog[acc] = e; acc *= g
    def chi3(u):  # order-3 character
        if u == 0: return C(0)
        return z3**( (dlog[u] * (N//3)) % N // (N//3) % 3 ) if False else z3**( dlog[u] % 3 )
    def chi4(u):  # order-4 character
        if u == 0: return C(0)
        return z4**( dlog[u] % 4 )
    # J(chi3,chi4) = sum_t chi3(t) chi4(1-t)
    J = sum( chi3(t) * chi4(F(1)-t) for t in F )
    Jb = sum( chi3(t)**2 * chi4(F(1)-t) for t in F )
    PR("p=%d (p mod 12=%d)  J(chi3,chi4)=%s   |J|^2=%s   [-p = %d]"
       % (p, p%12, J, (J*J.conjugate()).simplify_full() if hasattr(J,'simplify_full') else J*J.conjugate(), -p))
    for B in Bs:
        if B % p == 0: continue
        S = sum( chi4(x**3 + F(B)) for x in F )
        # m = Re(S)/p ; Re of a cyclotomic elt via complex embedding, then round (exact check after)
        Sc = CC(S); m_re = Sc.real()/p
        cub = (pow(B, (p-1)//3, p) == 1)
        pred = -2 if cub else 1
        PR("   B=%2d  cubic-residue=%-5s  S=%s  Re(S)/p=%.6f  law predicts m=%d  MATCH=%s"
           % (B, cub, S, m_re, pred, abs(m_re - pred) < 1e-9))

for p in (7, 19, 31, 43, 67, 79):
    analyze(p)
