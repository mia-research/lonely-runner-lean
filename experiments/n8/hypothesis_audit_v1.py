"""Audit: which of my hypotheses are required by the CATEGORY, and which did I add?
Target 1: profile_clear_of_order6 demands EVERY modulus >= 10. The per-modulus theorem only
needs b >= 10 at that modulus. Is the homogeneity binding, or an artefact of my proof?
The window conditions needed are b <= 8r+1 <= 7b; the 1/6-band gives b-3 <= 6r <= 5b+3.
For b < 10 the band does not IMPLY the window -- but the actual rounded q may satisfy the
window anyway."""
from math import lcm, gcd
from functools import reduce
from fractions import Fraction as F
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
def band_ok(b,q):
    """does q sit in the 1/6 band of modulus b (the hypothesis my proof uses)?"""
    r = q % b
    return b-3 <= 6*r and 6*r <= 5*b+3
random.seed(31)
tot=0; has_wit=0; band_wit=0; band_and_clear=0; small_ok=0
rows=[]
for _ in range(120000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if max(bs)<=9 or min(bs)>=10: continue      # MIXED only
    M=reduce(lcm,bs)
    if M>200000: continue
    tot+=1
    W=[q for q in range(M) if clears(bs,q)]
    if W: has_wit+=1
    # q's that satisfy the 1/6 band at EVERY modulus (what my proof's hypothesis asks)
    B=[q for q in range(M) if all(band_ok(b,q) for b in bs)]
    if B: band_wit+=1
    if B and any(clears(bs,q) for q in B): band_and_clear+=1
    # do the band-q's clear the SMALL moduli (b < 10) too?
    if B and all(all(L(b) <= q % b <= U(b) for b in bs if b<10) for q in B[:50]): small_ok+=1
    if tot>=6000: break
print(f"mixed divisor-closed profiles: {tot}")
print(f"   have a witness at all:                         {100*has_wit/tot:6.2f}%")
print(f"   have a q in the 1/6 band at EVERY modulus:      {100*band_wit/tot:6.2f}%")
print(f"   ... and some such q clears:                     {100*band_and_clear/tot:6.2f}%")
print(f"   ... and every sampled band-q clears the b<10s:  {100*small_ok/tot:6.2f}%")
print()
print("So: is 'b >= 10 at every modulus' binding, or is the 1/6-band detour the binding thing?")
print("   my theorem's reach on these mixed profiles = 0% by construction (some b < 10)")
print(f"   but a band witness exists and clears in {100*band_and_clear/tot:.2f}% of them")
