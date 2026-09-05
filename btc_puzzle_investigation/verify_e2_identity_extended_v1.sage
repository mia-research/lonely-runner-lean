#!/usr/bin/env sage
# verify_e2_identity_extended_v1.sage
#
# Push the char-poly collapse identity  e2 = e1^2 + p  (equiv.  V2 = V1^2 + 2p  for all a!=0)
# far beyond the 3 primes (43,67,127) checked in verify_charpoly_collapse_v1.sage, and HUNT for
# a counterexample at some (a,p) -- which under the separation thesis would be the leak.
#
# FLOAT-FREE METHOD (pure integer arithmetic).
#   hist_k normalization (matching the record): trace-zero points P (P+P^p+...+P^{p^{k-1}}=O) are
#   counted into bin 0 (dlog[O]=0). Then sum h2 = 2p, and the identity V2(a)-V1(a)^2=2p for a!=0
#   is equivalent (by inverse DFT) to the circular-convolution sequence
#        f[d] := h2[d] - (h1*h1)[d]
#   satisfying BOTH  (i) f[d] constant c for all d != 0,  and  (ii) f[0] - c == 2p.
#   Exact integer check: no complex field, no precision.
#
# Validated at p=43,67,127 against the record's 160-bit DFT route (which reports ~1e-45).
# The two agree once the histogram normalizations are matched (see diag3.sage notes).
#
# Exactness discipline (CLAUDE.md): Python int + Sage GF / EllipticCurve only.

B = 7  # secp's curve y^2 = x^3 + 7


def curve_data(p):
    """Return (E, G, n, dlog) with dlog: point -> discrete log in <G>, for prime n.
    Returns None if p not prime, p<=7 (x^3+7 singular), or n not prime."""
    if not is_prime(p) or p <= 7:
        return None
    F = GF(p); E = EllipticCurve(F, [0, B]); n = E.cardinality()
    if not is_prime(n):
        return None
    G = E.gens()[0]
    dlog = {}; Q = E(0)
    for d in range(n):
        dlog[Q] = d; Q = Q + G
    return E, G, n, dlog


def hist_k(p, k, Ep, n, dlog):
    """Exact integer histogram h[d] over E(F_{p^k}), record normalization:
    trace-zero points counted into bin 0 (dlog[O]=0). O(p^k)."""
    q = p ** k; Fq = GF(q, 'g'); Eq = EllipticCurve(Fq, [0, Fq(B)])
    h = [0] * n; half = (q - 1) // 2
    for P in Eq.points():
        if P.is_zero():
            continue
        y = P[1]
        if y == 0:
            continue
        chi = 1 if y ** half == 1 else -1
        T = Eq(0); Q = P
        for _ in range(k):
            T = T + Q; Q = Eq(Q[0] ** p, Q[1] ** p)
        # coerce trace back to the F_p curve (record's Tp=E1(T[0],T[1])); trace-zero -> bin 0
        Tp = Ep(T[0], T[1]) if not T.is_zero() else Ep(0)
        h[dlog[Tp]] += chi
    return h


def conv_circ(a, b, n):
    c = [0] * n
    for i in range(n):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(n):
            c[(i + j) % n] += ai * b[j]
    return c


def integer_check(p):
    """Identity V2(a)-V1(a)^2=2p for all a!=0  iff  (i) f[d] const for d!=0  AND  (ii) f[0]-c==2p."""
    cd = curve_data(p)
    if cd is None:
        return None
    Ep, G, n, dlog = cd
    h1 = hist_k(p, 1, Ep, n, dlog)
    h2 = hist_k(p, 2, Ep, n, dlog)
    h1star = conv_circ(h1, h1, n)
    f = [h2[d] - h1star[d] for d in range(n)]
    vals_nonzero = set(f[d] for d in range(1, n))
    const_nonzero = (len(vals_nonzero) == 1)
    c = next(iter(vals_nonzero)) if vals_nonzero else None
    ok = const_nonzero and (f[0] - c == 2 * p)
    return dict(p=p, n=n, nfreqs=n - 1, c=c, f0=f[0], sumh2=sum(h2), ok=ok)


# ---- PHASE 0: validate at the 3 known primes (must be ok=True) ----
print("=" * 72)
print("PHASE 0 -- VALIDATION at p=43,67,127 (expect ok=True, sumh2=2p)")
print("=" * 72)
for p in [43, 67, 127]:
    r = integer_check(p)
    print(f"  p={p:4d} n={r['n']:4d}  ok={r['ok']}  c(d!=0)={r['c']}  f0-c={r['f0']-r['c']}  2p={2*p}  sumh2={r['sumh2']}")

# ---- PHASE 1: sweep secp-class primes, hunt for counterexample ----
print()
print("=" * 72)
print("PHASE 1 -- EXTENDED SWEEP over p == 7 mod 12 (secp's class), p<=2000, n prime")
print("=" * 72)
ps = [p for p in prime_range(11, 2001) if p % 12 == 7]
results = []
for p in ps:
    r = integer_check(p)
    if r is None:
        continue
    results.append(r)
    flag = "OK" if r['ok'] else "*** COUNTEREXAMPLE ***"
    print(f"  p={p:5d} n={r['n']:7d}  freqs={r['nfreqs']:7d}  {flag}")

n_ok = sum(1 for r in results if r['ok'])
n_bad = [r for r in results if not r['ok']]
total_freqs = sum(r['nfreqs'] for r in results)
print()
print(f"PHASE 1 SUMMARY: {len(results)} primes, {total_freqs} (a,p) frequencies checked")
print(f"  OK ............ {n_ok}")
print(f"  COUNTEREXAMPLES {len(n_bad)}")
for r in n_bad:
    print(f"    p={r['p']} n={r['n']}")
