"""S08: as S07 but records BOTH readings of the goal:
   LIT  = 'some b in the two windows is SAFE'                (task's literal claim, B_div = [L/8,7L/8])
   CERT = 'some b in the two windows is SAFE and admissible for every divisible runner'
          (what is needed for x_0 >= 1)
Exhaustive over all E with lcm(E)=L for 8 | L <= LMAX."""
import sys
from itertools import combinations, product
from math import gcd
from n8_fibre_core import L_of, split, safe, div_ok

def divisors(n):
    d=[];i=1
    while i*i<=n:
        if n%i==0:
            d.append(i)
            if i!=n//i: d.append(n//i)
        i+=1
    return sorted(d)

def gen_E(L):
    D=divisors(L); Ddiv=[d for d in D if d%8==0]
    if not Ddiv: return
    cls={r:[d for d in D if d%8==r] for r in range(1,8)}
    for z in (2,4,6):
        classes=[1,3,5,7,z]
        if any(not cls[r] for r in classes): continue
        for base in product(*[cls[r] for r in classes]):
            base=tuple(sorted(base))
            for dv in combinations(Ddiv,2):
                E=tuple(sorted(base+dv))
                if len(set(E))==7: yield E
            for dcls in classes:
                for extra in cls[dcls]:
                    if extra in base: continue
                    non=tuple(sorted(base+(extra,)))
                    for dv in Ddiv:
                        E=tuple(sorted(non+(dv,)))
                        if len(set(E))==7: yield E

def analyse(E,L):
    Ed,En=split(E)
    lo,hi=-(-L//8),(7*L)//8
    W=[(-(-2*L//7),(2*L)//5),(-(-3*L//5),(5*L)//7)]
    lit_w=cert_w=cert_B=0
    for b in range(lo,hi+1):
        if not safe(En,b,L): continue
        inw=any(a<=b<z for a,z in W)
        if inw: lit_w+=1
        if div_ok(Ed,b,L):
            cert_B+=1
            if inw: cert_w+=1
    return lit_w,cert_w,cert_B

LMAX=int(sys.argv[1]) if len(sys.argv)>1 else 1000
seen=set(); tot=0
fail_lit=[]; fail_cert=[]; fail_B=[]; tot_e8=0; fail_lit_e8=[]; fail_cert_e8=[]
for L in range(8,LMAX+1,8):
    for E in gen_E(L):
        if E in seen or L_of(E)!=L: continue
        g=0
        for e in E: g=gcd(g,e)
        if g!=1: continue
        seen.add(E); tot+=1
        lit_w,cert_w,cert_B=analyse(E,L)
        Ed,_=split(E)
        e8 = (Ed==[8])
        if e8: tot_e8+=1
        if lit_w==0:
            fail_lit.append((E,L,cert_B,tuple(Ed)))
            if e8: fail_lit_e8.append((E,L))
        if cert_w==0:
            fail_cert.append((E,L,cert_B,tuple(Ed)))
            if e8: fail_cert_e8.append((E,L))
        if cert_B==0: fail_B.append((E,L))
print(f"LMAX={LMAX}  exhaustive admissible configurations: {tot}   (of which E_div=={{8}}: {tot_e8})")
print(f"  LIT  fails (no SAFE b in either window)                 : {len(fail_lit)}    [E_div=={{8}}: {len(fail_lit_e8)}]")
print(f"  CERT fails (no SAFE+admissible b in either window)      : {len(fail_cert)}   [E_div=={{8}}: {len(fail_cert_e8)}]")
print(f"  no SAFE+admissible b anywhere in B_hon                  : {len(fail_B)}")
print()
print("LIT failures (counterexamples to the goal as literally stated):")
for E,L,cB,Ed in fail_lit:
    print(f"    E={E} L={L} E_div={list(Ed)} safe+admissible fibres in B_hon={cB}")
print()
print("CERT failures with |E_div|==1 (cleanest, twin present):")
for E,L,cB,Ed in fail_cert:
    if len(Ed)==1:
        print(f"    E={E} L={L} E_div={list(Ed)} safe+admissible fibres in B_hon={cB}")
