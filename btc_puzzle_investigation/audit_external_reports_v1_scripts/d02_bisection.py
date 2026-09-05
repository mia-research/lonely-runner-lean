# ---- Doc 2 / Doc 8: the "D2 bisection" / "Dirichlet island sieve" ----
# Run THEIR exact code (doc 8) verbatim, then expose what it actually does.
import random
random.seed(1)
p = 2**256 - 2**32 - 977
n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
lam = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

d_true = random.randint(2**134, 2**135 - 1)
j_true = 2
d0_true = (d_true * pow(lam, j_true, n)) % n
lam_exponent = (3 - j_true) % 3
lam_inv = pow(lam, lam_exponent, n)

candidates_d0 = [random.randint(1, n - 1) for _ in range(5)]
candidates_d0.append(d0_true)
random.shuffle(candidates_d0)

print("=== their sieve, verbatim ===")
survivors=[]
for idx, d0_cand in enumerate(candidates_d0):
    val = d0_cand * lam_inv
    c_cand = val // n
    d_cand = val - c_cand * n
    is_valid = d_cand < 2**135
    if is_valid: survivors.append(d0_cand)
    print(f"Island #{idx+1}: bits={d_cand.bit_length():3d}  <2^135? {is_valid}")
print("survivors:", len(survivors), " matches d_true:", survivors==[d0_true])

print("\n=== what the 'reconstruction' actually computes ===")
# d_cand = d0_cand*lam_inv - (d0_cand*lam_inv // n)*n  ==  (d0_cand * lam_inv) mod n
print("d_cand == (d0_cand*lam_inv) mod n ? test on true island:",
      ((d0_true*lam_inv) - (d0_true*lam_inv//n)*n) == (d0_true*lam_inv)%n)
# and d0_true = d_true*lam^j mod n, lam_inv=lam^{3-j}=lam^{-j}, so (d0_true*lam_inv) mod n = d_true
print("(d0_true*lam_inv) mod n == d_true ?", (d0_true*lam_inv)%n == d_true)
print(">>> So the 'surviving island' is d_true reconstructed from d0_true, and d0_true was DEFINED as d_true*lam^j.")
print(">>> The filter 'bits<2^135' passes ONLY the candidate that was built from a <2^135 key. Circular.")

print("\n=== the honest version: can you get d0_true from the PUBLIC key without knowing d? ===")
print("d0 = d*lam^j mod n requires d. Public key P=[d]G gives you a POINT, not d or d0.")
print("The GLV representative [d0]G = phi^j(P) is computable, but recovering the SCALAR d0 from [d0]G")
print("is itself an ECDLP instance. Nothing here extracts a scalar from a point.")
