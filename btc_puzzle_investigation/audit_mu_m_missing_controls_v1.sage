# AUDIT: run the two controls PREREG_mu_m_vanishing_law_v2.md specified and the run
# NEVER IMPLEMENTED -- C4b (anchor / validates prank_pointcount) and C2 (wrong-pairing
# firing control).  Also compare the two instruments, which C1 never did.
import random
exec(open("mu_m_vanishing_law_v1.sage").read().split("# ------------- report")[0].split("# ---------------------------------------------------------------- report")[0])

print("="*96); print("AUDIT 1 -- C4b: does prank_pointcount agree with an INDEPENDENT quantity?"); print("="*96)
print("  (4,3): p-rank(Jac C) must equal p-rank(E), E: y^2=f, i.e. 1 iff a_p(E) != 0 mod p")
bad = 0; n = 0
rng = random.Random(int(11))
for p in (7, 11, 19, 23, 31, 43, 47):
    R = PolynomialRing(GF(p),'x')
    for _ in range(6):
        co = [rng.randrange(p) for _ in range(3)] + [rng.randrange(1,p)]
        f = R([GF(p)(c) for c in co])
        if f.discriminant() == 0: continue
        a3 = co[3]
        E = EllipticCurve(GF(p), [0, GF(p)(co[2]), 0, GF(p)(co[1])*GF(p)(a3), GF(p)(co[0])*GF(p)(a3)**2])
        ap = p + 1 - E.cardinality()
        expect = 1 if (ap % p != 0) else 0
        pc, _ = prank_pointcount(p, co, 4, 3)
        M, B = cartier_general(p, f, 4, 3); cart = stable_rank(M)
        n += 1
        ok = (pc == expect and cart == expect)
        if not ok:
            bad += 1
            print("   MISMATCH p=%d f=%s  a_p=%d expect=%d  pointcount=%d cartier=%d" % (p,co,ap,expect,pc,cart))
print("  C4b: %d rows, %d mismatches -> %s" % (n, bad, "PASS" if bad==0 else "FAIL"))
print("  (this also validates prank_pointcount AND compares the two instruments -- neither was done in the run)")

print("\n" + "="*96); print("AUDIT 2 -- C2: the wrong-pairing FIRING control, p NOT = +-1 mod m"); print("="*96)
print("  At p != +-1 mod m the Cartier orbit is b -> b*p^-1, NOT b <-> m-b, so S should MISPREDICT.")
fires = 0; cells = 0
rng = random.Random(int(12))
for (m,d,plist) in [(5,3,(7,13,17,23,29)), (7,3,(11,17,23,29,37))]:
    D = dimsV(m,d); S = S_of(m,d)
    for p in plist:
        if p % m in (1, m-1): continue
        if p**genus(m,d) > 10**6: continue
        # true bound under the ACTUAL orbit structure of multiplication by p^-1
        pinv = inverse_mod(p, m); seen=set(); Strue=0
        for b in range(1,m):
            if b in seen: continue
            orb=[]; x=b
            while x not in seen:
                seen.add(x); orb.append(x); x=(x*pinv)%m
            Strue += len(orb)*min(D[o] for o in orb)
        R = PolynomialRing(GF(p),'x'); mis = 0; tot = 0
        for _ in range(4):
            co = [rng.randrange(p) for _ in range(d)] + [rng.randrange(1,p)]
            f = R([GF(p)(c) for c in co])
            if f.discriminant() == 0: continue
            pc, _ = prank_pointcount(p, co, m, d); tot += 1
            if pc != S: mis += 1
        cells += 1
        if mis > 0: fires += 1
        print("   (m,d)=(%d,%d) p=%-3d (p mod m=%d)  S=%d  S_true(orbit)=%d  |  p-rank != S on %d/%d rows"
              % (m,d,p,p%m,S,Strue,mis,tot))
print("  C2: %d/%d eligible cells mispredict -> %s" % (fires, cells, "FIRES" if fires >= 1 else "DOES NOT FIRE"))
