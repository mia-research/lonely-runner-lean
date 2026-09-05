#!/usr/bin/env python3
"""AUDIT: independent-sample retest of (E1)-(E4), and the P(s=0) deficit with
ONE TWIST PER p (independent draws across p, fixing the non-independence
suspected of causing the z=-1.92 deficit).

Independent of the discovery sample: different seed, different bit size (32 vs 26),
one twist per p instead of all four. Exact integers only."""
from math import isqrt
import random, sys
from collections import Counter
exec(open('cubic_bridge_v1.py').read().split('print("=== CONTROLS ===")')[0])

def prim_with_sign(lam):
    for u, s, sg in UNITS:
        m = emul(u, lam)
        if m[0] % 3 == 2 and m[1] % 3 == 0:
            return m, s, sg
    return None, None, None

BITS = 32
TARGET = 40000
rnd = random.Random(20260724_2)   # different seed from discovery sample

rows = []
tries = 0
while len(rows) < TARGET:
    tries += 1
    p = rnd.randrange(1 << (BITS-1), 1 << BITS) | 1
    p += (1-p) % 3
    if p % 2 == 0: p += 3
    if p % 3 != 1 or not is_prime(p, bases=(2,3,5,7,11,13)): continue
    rep = cornacchia3(p, rnd)
    if rep is None: continue
    a, b = rep
    if a*a + 3*b*b != p: continue
    # ---- ONE TWIST PER p, chosen uniformly among the valid ones ----
    cands = []
    for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
        I = instance(p, t, rnd)
        if I is not None: cands.append(I)
    if not cands: continue
    I = cands[rnd.randrange(len(cands))]
    r = analyse(I)
    _, s1, sg1 = prim_with_sign(I["nu"])
    rows.append(dict(t=I["t"], s=s1, sg=sg1, e_nu=r["e_nu_w"], e_pib=r["e_pib_w"],
                     c3=r["pred"], j=r["j"], k=r["k"], nvalid=len(cands)))
    if len(rows) % 10000 == 0:
        print(f"  ... {len(rows)}"); sys.stdout.flush()

N = len(rows)
for r in rows: r["m3"] = ((r["t"]-1)//3) % 3
print(f"\n=== AUDIT RETEST — independent sample: {BITS}-bit p, ONE twist per p, N={N} ===")
print(f"    (discovery sample was 26-bit p, all four twists, N=12000, different seed)\n")

def law(label, pred):
    v = sum(1 for r in rows if not pred(r))
    print(f"  {label:<44} violations {v}/{N}   {'HOLDS' if v==0 else '*** FAILS ***'}")
    return v == 0

ok = []
ok.append(law("(E1) e(nu')+e(pib') != 2 mod 3",
              lambda r: (r["e_nu"]+r["e_pib"]) % 3 != 2))
ok.append(law("(E2) s=0 <=> e(nu')+e(pib') = 1 mod 3",
              lambda r: (r["s"] == 0) == ((r["e_nu"]+r["e_pib"]) % 3 == 1)))
ok.append(law("(E3) e(pib')-e(nu') = (t-1)/3 mod 3",
              lambda r: (r["e_pib"]-r["e_nu"]) % 3 == r["m3"]))
ok.append(law("(E3b) primarizing unit sign is always +1",
              lambda r: r["sg"] == 1))
ok.append(law("(E4) c3=0 <=> (s=0 or 9 | t-1)",
              lambda r: (r["c3"] == 0) == (r["s"] == 0 or r["m3"] == 0)))
ok.append(law("(E5) c3 = s*(t-1)/3 mod 3   [closed form]",
              lambda r: r["c3"] == (r["s"]*r["m3"]) % 3))

print(f"\n  ALL EXACT LAWS HOLD ON THE INDEPENDENT SAMPLE: {all(ok)}")

print("\n=== the P(s=0) deficit, with independent draws ===")
cs = Counter(r["s"] for r in rows)
n_s0 = cs[0]; sd = (N*(1/3)*(2/3))**0.5
print(f"  s distribution      : {dict(sorted(cs.items()))}   expect {N/3:.0f} each")
print(f"  P(s=0) = 1/3        : {n_s0}/{N} = {n_s0/N:.4f}   z = {(n_s0-N/3)/sd:+.2f}")
n9 = sum(1 for r in rows if r["m3"] == 0)
print(f"  P(9 | t-1) = 1/3    : {n9}/{N} = {n9/N:.4f}   z = {(n9-N/3)/sd:+.2f}")
c0 = sum(1 for r in rows if r["c3"] == 0)
sd5 = (N*(5/9)*(4/9))**0.5
print(f"  P(c3=0) = 5/9       : {c0}/{N} = {c0/N:.4f}   z = {(c0-N*5/9)/sd5:+.2f}")
agree = sum(1 for r in rows if r["j"] == 0 and r["k"] == 0)
E = sum(1 for r in rows if r["j"] == 0)*sum(1 for r in rows if r["k"] == 0)/N
print(f"  association ratio   : {agree/E:.4f}   (predicted 5/3 = 1.6667)")
jt = Counter((r["s"] == 0, r["m3"] == 0) for r in rows)
exp_tt = sum(1 for r in rows if r["s"]==0)*sum(1 for r in rows if r["m3"]==0)/N
print(f"  s=0 vs 9|(t-1)      : (T,T)={jt[(True,True)]} vs {exp_tt:.1f} expected under independence")
print(f"  twists available per p: {dict(sorted(Counter(r['nvalid'] for r in rows).items()))}")
