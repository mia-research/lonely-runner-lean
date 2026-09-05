#!/usr/bin/env sage
# Step 1 of PREREG_diffset_cubic_cmvanishing_v1.md
# Select + verify a non-CM curve E': y^2 = x^3 + a*x + b over secp's prime P.
# Frozen prereg spec: y^2 = x^3 + x + 1 first, with a documented fallback chain.
# Output: diffset_cubic_Eprime_meta_v1.json with (P, a, b, j, N, h, n, G', prereg_sha).

import json, hashlib, os

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

# Fallback chain per prereg (all non-CM, all over secp's P).
# Order matters: the first that meets the cofactor/subgroup requirements is used.
CANDIDATES = [(1,1), (2,3), (5,7), (9,11)]

def jinv(a, b):
    # j-invariant of y^2 = x^3 + a x + b:  1728 * 4 a^3 / (4 a^3 + 27 b^2)
    num = 1728 * 4 * pow(a, 3)
    den = (4 * pow(a, 3) + 27 * pow(b, 2))
    return num, den  # return as (num, den) rational -- sage handles the reduction later

def pick_curve():
    Fp = GF(P)
    for (a, b) in CANDIDATES:
        disc = (4*pow(a,3) + 27*pow(b,2)) % P
        assert disc != 0, f"candidate {a},{b} singular"
        E = EllipticCurve(Fp, [a, b])
        j = E.j_invariant()
        N = E.order()
        # factor order, find largest prime divisor
        Nfac = factor(N)
        n_prime = max(p for p, e in Nfac)   # largest prime-order subgroup
        h = N // n_prime
        print(f"[try a={a} b={b}]  j={j}  N={N}  #bits(N)={N.nbits()}  n_prime={n_prime}  h={h}  #bits(n')={n_prime.nbits()}", flush=True)
        # AMENDED criterion (see PREREG Amendment Note 2026-07-28):
        # non-CM (j!=0,1728) checked separately; require n' > 2^130 for distinctness of [d]G'
        # across all 82 puzzle d's (max ~2^130). Cofactor h is not constrained -- both the real
        # 82 and the matched null are computed identically as [d]G' in the same subgroup, so the
        # cofactor does not affect the comparison. (Original h<=4 AND n'>2^254 was met by no
        # candidate over secp's P; the cofactor requirement was inherited from crypto convention
        # and is not load-bearing for a characterization test.)
        if n_prime > (2**130):
            # generator of that subgroup: take any point, multiply by h, check order == n_prime
            Graw = E.gens()[0]
            Gcand = h * Graw
            # confirm order
            ord_G = Gcand.order()
            if ord_G == n_prime:
                Gxy = (int(Gcand.xy()[0]), int(Gcand.xy()[1]))
                return dict(a=int(a), b=int(b), j=str(j), N=int(N),
                            n_prime=int(n_prime), h=int(h),
                            Gx=Gxy[0], Gy=Gxy[1], used_candidate=(int(a),int(b)),
                            Nfac=str(Nfac))
            else:
                print(f"   h*gen has order {ord_G} != n_prime {n_prime}; searching another point", flush=True)
                # try more points until a generator of the n'-subgroup is found
                found = False
                # enumerate small multiples of gens
                for c1 in range(1, 20):
                    for c2 in range(0, 20):
                        Q = c1*E.gens()[0] + c2*(E.gens()[1] if E.rank() > 1 else E.gens()[0])
                        Qh = h * Q
                        if Qh.order() == n_prime:
                            Gxy = (int(Qh.xy()[0]), int(Qh.xy()[1]))
                            return dict(a=int(a), b=int(b), j=str(j), N=int(N),
                                        n_prime=int(n_prime), h=int(h),
                                        Gx=Gxy[0], Gy=Gxy[1], used_candidate=(int(a),int(b)),
                                        Nfac=str(Nfac))
                print(f"   no generator found for {a},{b}, trying next candidate", flush=True)
        else:
            print(f"   reject: n'={n_prime} not > 2^130", flush=True)
    raise RuntimeError("no candidate in the fallback chain met the prereg requirements (n' > 2^130)")

meta = pick_curve()

# sanity: confirm non-CM
Fp = GF(P)
E = EllipticCurve(Fp, [meta["a"], meta["b"]])
j = E.j_invariant()
assert j != 0 and j != 1728, f"chosen curve has CM j-invariant {j}!"
meta["j_is_zero_or_1728"] = False
meta["P"] = int(P)

# verify the generator: [n']G' = O and G' != O
Gpt = E(meta["Gx"], meta["Gy"])
assert meta["n_prime"] * Gpt == E(0,1,0), "generator order check failed"
assert Gpt != E(0,1,0), "generator is the identity"

# SHA-256 of the prereg (freeze-integrity)
prereg_path = os.path.join(BASE, "PREREG_diffset_cubic_cmvanishing_v1.md")
with open(prereg_path, "rb") as f:
    prereg_sha = hashlib.sha256(f.read()).hexdigest()
meta["prereg_sha256"] = prereg_sha
meta["prereg_path"] = "PREREG_diffset_cubic_cmvanishing_v1.md"

out = os.path.join(BASE, "diffset_cubic_Eprime_meta_v1.json")
with open(out, "w") as f:
    json.dump(meta, f, indent=2)

print(f"\n########## CURVE SELECTED ##########", flush=True)
print(f"E': y^2 = x^3 + {meta['a']}*x + {meta['b']}  over secp P", flush=True)
print(f"j(E') = {meta['j']}   (non-CM: {not meta['j_is_zero_or_1728']})", flush=True)
print(f"N' = {meta['N']}  ({meta['N'].bit_length()} bits)", flush=True)
print(f"n' = {meta['n_prime']}  ({meta['n_prime'].bit_length()} bits)   h' = {meta['h']}", flush=True)
print(f"G' = ({hex(meta['Gx'])}, {hex(meta['Gy'])})", flush=True)
print(f"N' factored: {meta['Nfac']}", flush=True)
print(f"prereg_sha256 = {prereg_sha}", flush=True)
print(f"wrote {out}", flush=True)
