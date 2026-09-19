"""Why does q = L(m) clear so often, and what exactly blocks it?
Divisor-closed: b | m, reading s = m/b, and L(m) = ceil((m-1)/8) ~ m/8.
Read: L(m) mod b depends on s mod 8, so the failures should be exactly the COLLIDERS 8 | s."""
from math import gcd
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clear(q,b): return L(b) <= q % b <= U(b)
bad=[]; tot=0; byres={r:[0,0] for r in range(8)}
for m in range(2,3000):
    q=L(m)
    for b in range(2,m+1):
        if m % b: continue
        s=m//b; tot+=1
        got=clear(q,b); want=(s % 8 != 0)
        byres[s%8][0]+=1
        if got: byres[s%8][1]+=1
        if got!=want: bad.append((m,b,s,got,want))
print(f"'q = L(m) clears modulus b  <=>  8 does not divide s = m/b'")
print(f"   over {tot} (m,b) pairs, m < 3000: {'HOLDS' if not bad else f'FAILS {len(bad)}'}")
for x in bad[:8]: print(f"      m={x[0]} b={x[1]} s={x[2]} got={x[3]} want={x[4]}")
print(f"\n   clear-rate by s mod 8:")
for r in range(8):
    n,c=byres[r]
    print(f"      s = {r} (mod 8): {c}/{n} clear   {100*c/n if n else 0:6.2f}%")
