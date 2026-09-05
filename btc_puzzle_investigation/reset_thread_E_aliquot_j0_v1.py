#!/usr/bin/env python3
"""
Reset thread E (literature-gap probe): aliquot cycles of the FIXED curve
E: y^2 = x^3 + 7  (j=0, CM by Z[omega]).

Silverman-Stange (arXiv:0912.1831) prove: no aliquot cycle of length >= 3 for
elliptic curves with j != 0. Our curve is j = 0 -- the EXCLUDED case. So whether
length-3+ cycles exist here is genuinely open, not settled by their theorem.

An aliquot chain: q_0 -> q_1 -> ... where #E(F_{q_i}) = q_{i+1}, all primes, same E.
Known length-2 (the secp256k1 amicable pair): p -> n -> p. This searches small
starting primes for cycles of length >= 3.

Point count exact via Legendre sum: #E(F_q) = q + 1 + sum_x ((x^3+7)/q).
Sanity control: the machinery must reproduce a known small amicable pair.
"""
from sympy import isprime, primerange

B = 7  # curve constant

def npoints(q):
    """#E(F_q) for y^2 = x^3 + 7, exact, O(q). q prime, good reduction (q not 2,3,7)."""
    s = 0
    e = (q - 1) // 2
    for x in range(q):
        v = (x * x % q * x + B) % q
        if v == 0:
            continue
        s += 1 if pow(v, e, q) == 1 else -1
    return q + 1 + s

def aliquot_chain(q0, maxlen=12, bound=10**7):
    """Follow q0 -> #E -> ... ; return (chain, kind) where kind in
    {'cycle-L', 'terminates', 'escapes'}."""
    chain = [q0]; seen = {q0: 0}
    cur = q0
    for step in range(maxlen):
        if cur in (2, 3, 7) or cur > bound:
            return chain, "bad/large"
        m = npoints(cur)
        if not isprime(m):
            return chain, "terminates(composite)"
        if m in seen:
            # cycle detected: from seen[m] to end
            cyc = chain[seen[m]:]
            return cyc, f"cycle-{len(cyc)}"
        chain.append(m); seen[m] = len(chain) - 1; cur = m
    return chain, "unresolved(maxlen)"

# ---- sanity control: known small amicable pairs for j=0 family ----
print("=== Thread E: aliquot cycles of y^2 = x^3 + 7 (j=0) ===\n")
print("[control] verify machinery on small primes (look for any 2-cycle p->q->p):")
ctrl_found = []
for q in primerange(5, 200):
    if q in (7,): continue
    m = npoints(q)
    if isprime(m) and m != q and m < 10**7:
        back = npoints(m) if m not in (2,3,7) else None
        tag = "  <== amicable 2-cycle" if back == q else ""
        if back == q:
            ctrl_found.append((q, m))
        if tag:
            print(f"   {q:>4} -> {m:<6} -> {back}{tag}")
print(f"   amicable 2-cycles found below 200: {ctrl_found}  "
      f"({'machinery OK' if ctrl_found else 'none in range'})\n")

# ---- main search for length >= 3 cycles ----
print("searching starting primes up to 20000 for aliquot cycles of length >= 3 ...")
cycles3 = {}
longest = 1
for q0 in primerange(5, 20000):
    if q0 in (7,):
        continue
    chain, kind = aliquot_chain(q0, maxlen=12, bound=10**7)
    if kind.startswith("cycle-"):
        L = int(kind.split("-")[1])
        longest = max(longest, L)
        if L >= 3:
            key = tuple(sorted(chain))
            cycles3[key] = chain

print(f"  longest cycle length observed: {longest}")
print(f"  distinct cycles of length >= 3: {len(cycles3)}")
for key, chain in list(cycles3.items())[:20]:
    print(f"    {' -> '.join(map(str, chain))} -> (loops)")
if not cycles3:
    print("    none below 20000. Scoped: no length-3 aliquot cycle for y^2=x^3+7")
    print("    among start primes < 20000 with chain bound 10^7. The j=0 case is")
    print("    still not covered by Silverman-Stange's theorem; this is an empirical")
    print("    null over a bounded window, not a proof of nonexistence.")
