#!/usr/bin/env python3
"""
φ(n)-residue lens on the public-point coordinates X, Y  (100k constructed keys).

Framework-native statistic: the Ramanujan sum c_q(a) is the exact kernel of the
reduced-residue averaging operator P_q (its 'surviving mode'). So for each modulus
q we measure
    S_q(V) = Σ_i c_q(V_i mod q)          (exact integer; V ∈ {X, Y, X+Y, X*Y})
which projects the empirical coordinate distribution onto the operator's surviving
reduced-residue mode. Under 'V mod q uniform', E[S_q]=0 and Var=N·(1/q)Σ_a c_q(a)²
(both exact). We also compute the full-histogram χ² (exact Fraction) — catches ANY
deviation, not just the reduced-residue one — and the curve-native characters
(quadratic/cubic/sextic character of X, Y-parity, primes 3/6/7).

EXACT ONLY (int / Fraction; z shown via isqrt, no '/'/float in signal path).
"""
import csv
from math import gcd, isqrt
from fractions import Fraction

p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
beta = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE  # β³≡1
CUBE = [1, beta, (beta*beta) % p]
SIX  = [1, beta, (beta*beta) % p, p-1, (p-beta) % p, (p-(beta*beta)) % p]

# ---------- exact number theory ----------
def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
def mobius(m):
    if m==1: return 1
    f=factorize(m)
    return 0 if any(e>1 for e in f.values()) else (-1 if len(f)%2 else 1)
def ramanujan_table(q):
    """c_q(a) for a=0..q-1, exact int:  c_q(a) = Σ_{d | gcd(a,q)} d·μ(q/d)."""
    divs=[d for d in range(1,q+1) if q%d==0]
    tab=[]
    for a in range(q):
        g=gcd(a,q); s=0
        for d in divs:
            if g%d==0: s += d*mobius(q//d)
        tab.append(s)
    return tab
def ramanujan_var_num(q, tab):
    """(1/q)Σ_a c_q(a)²  as exact Fraction (per-sample variance of c_q under unif)."""
    return Fraction(sum(c*c for c in tab), q)

def z_centi(S, var):
    """signed z*100 as int, no '/'/float:  z = S/sqrt(var)."""
    if var == 0: return 0
    z2 = Fraction(S*S) * (var ** -1)          # exact; ** -1 = reciprocal (not Div)
    mag = isqrt(int(z2 * 10000))
    return mag if S >= 0 else -mag
def show_z(zc):
    s = '-' if zc < 0 else ' '
    zc = abs(zc)
    return f"{s}{zc//100}.{zc%100:02d}"
def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"

# ---------- load ----------
BITS=[]; XS=[]; YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        BITS.append(int(r["bits"]))
        XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
Ntot=len(XS)
print(f"loaded {Ntot} keys\n")

def analyze(idx, label):
    M=len(idx)
    X=[XS[i] for i in idx]; Y=[YS[i] for i in idx]
    print(f"===== {label}  (M={M}) =====")
    # --- Ramanujan surviving-mode S_q survey ---
    rows=[]
    for q in range(2, 65):
        tab=ramanujan_table(q); var1=ramanujan_var_num(q, tab)
        var=Fraction(M)*var1
        Sx=sum(tab[x % q] for x in X); Sy=sum(tab[y % q] for y in Y)
        rows.append((q, Sx, Sy, z_centi(Sx,var), z_centi(Sy,var)))
    rows_x=sorted(rows, key=lambda r: -abs(r[3]))[:6]
    rows_y=sorted(rows, key=lambda r: -abs(r[4]))[:6]
    print(" Ramanujan reduced-residue mode  S_q  (z vs uniform, top |z|):")
    print("   X:  " + "  ".join(f"q{q}:z={show_z(zx)}" for q,_,_,zx,_ in rows_x))
    print("   Y:  " + "  ".join(f"q{q}:z={show_z(zy)}" for q,_,_,_,zy in rows_y))
    # --- full-histogram χ² survey (all modes) ---
    chi=[]
    for q in range(2, 65):
        hx=[0]*q
        for x in X: hx[x % q]+=1
        exp=Fraction(M,q)
        c2=sum((Fraction(h)-exp)**2 for h in hx)*(exp**-1)
        chi.append((q, c2))
    chi_top=sorted(chi, key=lambda r: -(r[1]-Fraction(r[0]-1)))[:6]   # excess over df
    print(" Full-histogram χ² of X mod q (excess over df=q-1, top):")
    print("   " + "  ".join(f"q{q}:χ²={frac3(c2)}(df{q-1})" for q,c2 in chi_top))
    # --- curve-native characters ---
    # quadratic character of X (Legendre (X|p)); Y parity
    qr=sum(1 for x in X if pow(x,(p-1)//2,p)==1)
    yev=sum(1 for y in Y if y%2==0)
    # cubic + sextic class of X
    cub=[0,0,0]; sxt=[0]*6
    for x in X:
        c=pow(x,(p-1)//3,p)
        cub[CUBE.index(c) if c in CUBE else 0]+=1
        s=pow(x,(p-1)//6,p)
        if s in SIX: sxt[SIX.index(s)]+=1
    def bal_z(a, tot):   # z of a vs tot/2 (exact integers under p=1/2)
        S=2*a-tot
        var=Fraction(tot)                 # Var(2·Binom-tot)=tot for p=1/2 -> S has var tot
        return z_centi(S, var)
    print(f" Quadratic char (X|p)=+1: {qr}/{M}  (bal z={show_z(bal_z(qr,M))})")
    print(f" Y even: {yev}/{M}  (bal z={show_z(bal_z(yev,M))})")
    # cubic uniformity χ²
    ec=Fraction(M,3); c2c=sum((Fraction(h)-ec)**2 for h in cub)*(ec**-1)
    es=Fraction(M,6); c2s=sum((Fraction(h)-es)**2 for h in sxt)*(es**-1)
    print(f" Cubic class of X: {cub}  χ²={frac3(c2c)}(df2)")
    print(f" Sextic class of X: {sxt}  χ²={frac3(c2s)}(df5)")
    # explicit curve primes
    for q in (3,6,7):
        hx=[0]*q
        for x in X: hx[x % q]+=1
        print(f"   X mod {q}: {hx}")
    print()
    return rows

# full set and the large-d (uniform-point) subset
full=list(range(Ntot))
big=[i for i in range(Ntot) if BITS[i]>=64]
analyze(big, "N>=64  (large-d, point ≈ uniform)")
analyze(full, "FULL 1..160")
