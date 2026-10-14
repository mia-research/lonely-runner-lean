from fractions import Fraction as F
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def blocks(r,k): return cd(r*(k+TH)) < TH
cov = [F(1,10), F(1,5), F(3,10), F(1,2), F(7,10)]
print("candidate cover at c = 10:", [str(r) for r in cov])
print("differences at d_max = 10:", sorted(int(10*r) for r in cov), "+ free x + 10")
print()
print("opening-by-opening (period lcm = 10):")
for k in range(10):
    who = [str(r) for r in cov if blocks(r,k)]
    print(f"  k={k}: {'blocked by ' + ','.join(who) if who else '*** FREE ***'}")
print()
print("minimality — each member's private openings (blocked by it alone):")
for r in cov:
    priv = [k for k in range(10) if blocks(r,k) and not any(blocks(s,k) for s in cov if s!=r)]
    print(f"  {str(r):6}: private openings {priv}")
print()
ok = all(any(blocks(r,k) for r in cov) for k in range(10))
minimal = all(any(blocks(r,k) and not any(blocks(s,k) for s in cov if s!=r) for k in range(10)) for r in cov)
print(f"shadows every opening: {ok}     minimal (every member has a private opening): {minimal}")
print()
print("is it the eighth-pattern {1/8,3/8,1/2,5/8,7/8}? ", sorted(cov)==sorted([F(1,8),F(3,8),F(1,2),F(5,8),F(7,8)]))
print()
print("cross-check the eighth pattern with the same code (should shadow, period 8):")
e8 = [F(1,8),F(3,8),F(1,2),F(5,8),F(7,8)]
print("  shadows:", all(any(blocks(r,k) for r in e8) for k in range(8)))
