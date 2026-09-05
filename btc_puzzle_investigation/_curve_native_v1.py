import csv
from math import gcd
from fractions import Fraction

n_curve = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
p_field = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

# --- lambda = primitive cube root of unity mod n_curve (the GLV/CM eigenvalue) ---
print("n_curve mod 3 =", n_curve % 3, "(==1 => cube roots of unity exist => CM by Z[w])")
def sqrt_mod(a,q):
    a%=q
    if pow(a,(q-1)//2,q)!=1: return None
    # Tonelli-Shanks (q odd prime)
    s,qq=0,q-1
    while qq%2==0: qq//=2; s+=1
    if s==1: return pow(a,(q+1)//4,q)
    z=2
    while pow(z,(q-1)//2,q)!=q-1: z+=1
    m,c,t,r=s,pow(z,qq,q),pow(a,qq,q),pow(a,(qq+1)//2,q)
    while t!=1:
        i,tt=0,t
        while tt!=1: tt=tt*tt%q; i+=1
        b=pow(c,1<<(m-i-1),q); m=i; c=b*b%q; t=t*c%q; r=r*b%q
    return r
rt=sqrt_mod(n_curve-3, n_curve)           # sqrt(-3)
lam=((n_curve-1)*pow(2,n_curve-2,n_curve) + rt*pow(2,n_curve-2,n_curve))%n_curve  # (-1+sqrt(-3))/2
print("lambda^2+lambda+1 mod n =", (lam*lam+lam+1)%n_curve, " (==0 confirms lambda is the CM cube root)")

# --- GLV decomposition: d = d1 + d2*lambda (mod n), d1,d2 ~128 bit (the mutually-constrained pair) ---
a1=0x3086D221A7D46BCDE86C90E49284EB15; b1=-0xE4437ED6010E88286F547FA90ABFE4C3
a2=0x114CA50F7A8E2F3F657C1108D9D44CFD8; b2=0x3086D221A7D46BCDE86C90E49284EB15
def rnd_div(x,y): return (x + (y//2 if x>=0 else -(y//2)))//y
def glv(d):
    c1=rnd_div(b2*d, n_curve); c2=rnd_div(-b1*d, n_curve)
    d1=d - c1*a1 - c2*a2
    d2=    - c1*b1 - c2*b2
    assert (d1 + d2*lam)%n_curve == d%n_curve
    return d1,d2

# --- best simple fraction of a position u in [0,1), denom<=256 ---
def simple_frac(u_num,u_den,NMAX=256):
    best=None
    for nn in range(1,NMAX+1):
        kk=rnd_div(nn*u_num, u_den); kk=max(0,min(nn,kk))
        err=abs(nn*u_num - kk*u_den)
        key=(Fraction(err,u_den), nn)
        if best is None or key<best: best=(key,(nn,kk))
    (_,_),(nn,kk)=best; g=gcd(kk,nn) if nn else 1
    return (nn//g,kk//g) if g>1 else (nn,kk)

rows=[(int(r["bits"]),int(r["private_key"],16),r["puzzle"]) for r in csv.DictReader(open("puzzles_verified.csv"))]
rows=sorted([r for r in rows if r[0]>=40])

print("\nCURVE-NATIVE view of solved keys:  position on the GROUP circle d/n_curve,")
print("and the GLV pair (d1,d2) [the curve's own mutually-constrained coordinate]")
print(f"{'pz':>3} {'P':>3} {'d/2^P frac':>10} {'d/n_curve frac(<=256)':>20} {'|d1|bits':>8} {'|d2|bits':>8} {'d2/d1~':>8}")
for P,d,pz in rows[:8]+rows[-8:]:
    band=simple_frac(d-(1<<(P-1)), 1<<(P-1))
    grp =simple_frac(d, n_curve)
    d1,d2=glv(d)
    ratio = Fraction(abs(d2), abs(d1)) if d1 else 0
    print(f"{pz:>3} {P:>3} {str(band):>10} {str(grp):>20} {abs(d1).bit_length():>8} {abs(d2).bit_length():>8} {float(ratio):>8.3f}")

# --- the curtain: decompose the curve's OWN constants ---
print("\nD-signature of the curve's defining constants (range=2^256):")
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
N=1<<256
for name,val in [("p_field",p_field),("n_curve",n_curve),("n_curve-p",n_curve-p_field),("lambda",lam)]:
    s=d_recursion(N,val)
    print(f"  {name:10s}: {len(s)} terms  bitlens={[max(x.bit_length()-1,0) for x in s][:8]}")
