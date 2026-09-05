import csv
# Doc 14: lattice-carry / BDD. Test §1 (congruence sweep + control), §3 (is c public?), §4 (82 keys).

n_secp = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
lam_secp = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
assert pow(lam_secp,3,n_secp)==1 and lam_secp!=1

def orbit_data(d, n, lam):
    orb = [d % n, (lam*d)%n, (lam*lam*d)%n]
    d0 = min(orb)
    # j: position with d = d0*lam^j mod n
    j = next(k for k in range(3) if (d0*pow(lam,k,n))%n == d%n)
    # negation parity s: doc uses (-1)^s; test s=0 (no negation) primarily
    s = 0
    # integer carry c = ((-1)^s d0 lam^j - d)/n   (exact integer)
    num = ((-1)**s)*d0*pow(lam,j,n) - (d%n)
    c = num // n if num % n == 0 else num / n
    return d0, j, s, c

print("=== §4: the 82 real solved keys — compute (d0, j, s, c) ===")
rows=[]
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        d=int(r['private_key'],16); rows.append((int(r['puzzle_num']),d))
c_all=[]; j_all=[]; dmin_all=[]
for pz,d in rows:
    d0,j,s,c = orbit_data(d, n_secp, lam_secp)
    c_all.append(c); j_all.append(j); dmin_all.append(d0==d)
print(f"  keys: {len(rows)}")
print(f"  d0==d (d is its own orbit min): {sum(dmin_all)}/{len(rows)}")
print(f"  j==0 for all: {all(x==0 for x in j_all)}   c==0 for all: {all(x==0 for x in c_all)}")
print(f"  distinct c values across 82 keys: {set(c_all)}")
# BDD interval for c=0,j=0: d0 in [c*n/lam^j, (c+1)*n/lam^j] = [0, n] -> size n (whole range)
print(f"  BDD interval for (c=0,j=0): [0*n, 1*n] = [0, n)  -> size n  => constrains d0 to the WHOLE range")

print("\n=== §3 CRUX: is the carry c computable from PUBLIC data? ===")
print("  c = ((-1)^s d0 lam^j - d)/n  contains d explicitly.")
print("  d0 = min(d, lam d, lam^2 d mod n) also needs d.  So c needs d (the DLP).")
# demonstrate: for a key, c is NOT a function of the public point alone -- two scalars giving DIFFERENT c
d1 = 0x1000000000000000000000000000001   # arbitrary ~121-bit
d2 = 0x1000000000000000000000000000002
print(f"  example: d1,d2 differ by 1 -> c(d1)={orbit_data(d1,n_secp,lam_secp)[3]}, c(d2)={orbit_data(d2,n_secp,lam_secp)[3]}  (need d to know c)")

print("\n=== §1: congruence law + planted control on small curves (is 100% a tautology?) ===")
# sweep a couple prime-order curves p=7 mod 12; law: d ≡ (-1)^s lam^j d0 - c*n (mod 3) with c defined from d
sweep = [(43,31,5),(67,79,23),(79,67,29)]
for p,n,lam in sweep:
    if pow(lam,3,n)!=1:
        # find lambda of order 3 mod n
        lam=next(L for L in range(2,n) if pow(L,3,n)==1 and L!=1)
    ok=0; ctrl=0
    lam_fake=(lam+2)%n
    for d in range(1,n):
        d0,j,s,c = orbit_data(d,n,lam)
        lhs=(((-1)**s)*pow(lam,j,n)*d0 - c*n) % 3
        if lhs==d%3: ok+=1
        # planted control: use lam_fake in the SAME formula (c still real) -> should break
        d0f,jf,sf,cf = orbit_data(d,n,lam_fake) if pow(lam_fake,3,n)==1 else (d0,j,s,c)
        lhsf=(((-1)**sf)*pow(lam_fake,jf,n)*d0f - cf*n)%3
        if lhsf==d%3: ctrl+=1
    print(f"  p={p} n={n} lam={lam}: real {ok}/{n-1} ({100*ok/(n-1):.0f}%)  | control(lam+2) {ctrl}/{n-1} ({100*ctrl/(n-1):.0f}%)")
print("  (real=100% is BY CONSTRUCTION: c is defined as ((-1)^s d0 lam^j - d)/n, forcing the identity.)")

print("\n=== §2: Aut(E) for y^2=x^3+7 -> mu_6, caps extraction at mod 6 ===")
print("  j=0 curve automorphism group = mu_6 (order 6); no order-9 automorphism => point-automorphism")
print("  extraction saturates at mod 3 (j) x mod 2 (s) = mod 6. Structural; true for j-invariant 0.")
