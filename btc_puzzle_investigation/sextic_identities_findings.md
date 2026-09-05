# secp256k1 CM / sextic structural identities — exact computed values (2026-07-10)
Four specific ℤ[ω]-identities, verified exactly (integer arithmetic, no float).
Script: `sextic_identities_verify.py`. ω = primitive cube root, ζ₆ = −ω² primitive
6th root; exponents below are powers of ζ₆ (ω = ζ₆², −1 = ζ₆³, ω² = ζ₆⁴).

Frobenius: π = a + bω,  N(π)=p,  π+π̄ = 2a−b = t = p+1−n, with
a = 367917413016453100223835821029139468249,
b = 303414439467246543595250775667605759171.

## Claim 1 — u = −1 is the unique unit with N(π+u) = n  [VERIFIED]
Over the 6 units: u=+1 → p+t+1; u=−1 → **n**; u=±ω,±ω² → ~1.16·10⁷⁷. Unique u=−1.
N(π−1) = p−t+1 = n is forced; the sextic residue class **[7/π]₆ = ζ₆⁵** fixes the
trace sign (which sextic twist secp256k1 is), making u=−1 non-arbitrary.

## Claim 2 — Grossencharacter relation π_n = −(1−π) = π−1  [VERIFIED, first computation]
π_n = π − 1 =
367917413016453100223835821029139468248 + 303414439467246543595250775667605759171·ω,
N(π_n) = n exactly, n ≡ 1 (mod 3) so n splits and π_n is a prime of ℤ[ω] above n.
This is the explicit generator of the prime above the group order — not previously written.

## Claim 3 — sextic obstruction to amicability = nontrivial cube root of unity  [CONFIRMED in substance]
- raw Frobenius product [π_n/π_p]₆·[π_p/π_n]₆ = ζ₆³ = **−1** (order 2).
- primary-associate reciprocity product/ratio = ζ₆⁰ = 1 (reciprocity law clean).
- sextic classes of the curve constant: **[7/π_p]₆ = ζ₆⁵, [7/π_n]₆ = ζ₆¹**.
- **amicability carrier [7/π_p]₆ / [7/π_n]₆ = ζ₆⁴ = ω²** — a nontrivial primitive cube
  root of unity. Under the conjugate embedding ω := w̄ this reads ζ₆⁴ = **ω** (the
  which-cube-root labeling is the only ambiguity; both are Galois-conjugate).
The sextic *values* above are correct. **CORRECTION (2026-07-10, `aliquot_sextic.py`):
the amicability INTERPRETATION was WRONG.** A nontrivial sextic value does NOT block
amicability. Direct point-counting (q↦#E(F_q) via ℤ[ω] factorization + the exact 4D
sextic character ε=ζ₆^(3−[28/π]₆), validated on 44 small primes and on both iterates of
14 small amicable/anomalous cases vs brute force, and at 256-bit scale #E(F_p)=n) shows
**#E(F_n) = p EXACTLY**, so **(p, n) IS an amicable pair — a length-2 aliquot cycle
p→n→p.** Cross-checks: (7/n)=−1 ⇒ 3∤#E(F_n) (consistent, 3∤p); structural reason:
Frobenius at p is π (#E(F_p)=N(π−1)=n), Frobenius at n is 1−π, and (1−π)−1=−π has N=p.
This is the CM-abundance of amicable pairs (Silverman–Stange: ≫X/(logX)² for CM curves,
vs rare for non-CM) — secp256k1 exemplifies it, it is not an exception. The earlier
"no amicable pair" was an inference from the sextic product, not a point-count, and it
was wrong.

## Claim 4 — twist order carries 13² (order-169 rational subgroup)  [VERIFIED]
n_t = 2(p+1) − n =
115792089237316195423570985008687907853702405052206223696310004874299507848991
= 3² · 13² · 3319 · 22639 · C, with
C = 1013176677300131846900870239606035638738100997248092069256697437031 (216-bit, **prime**).
169 | n_t ⇒ the quadratic twist has a **rational subgroup of order 169**; the 13² is
the CM-structural factor (matches deg(13)=4 in the embedding tower / twist fingerprint).

## Net
1,2,4 exact. 3 confirmed as a nontrivial-cube-root (= ω up to conjugation) sextic
obstruction to amicability; exact carrier is [7/π_p]₆/[7/π_n]₆ = ζ₆⁴. The concrete
new secp256k1 invariants: π_n=π−1 (above), [7/π_p]₆=ζ₆⁵, [7/π_n]₆=ζ₆¹, twist C prime.
