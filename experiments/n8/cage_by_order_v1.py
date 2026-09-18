"""Where does n = 8 sit?  The cage is gcd-driven, so it is a COMPOSITE-order phenomenon.

At order n, a grid's subject sees offsets 1..n-1, and offset d can ever be the tight pair exactly
when gcd(d,n) = 1.  So phi(n) of the n-1 disparities are rigid and the rest are caged.  At PRIME n
the unit group acts transitively on the nonzero residues -- phi(n) = n-1 -- and the cage is EMPTY.

That is why BS's Lemma 2 works at n = 7 and has no analogue at n = 8: their Lambda_m,p = {1..p-1}
are all units only because p is prime.  Exhaustive, no sampling."""
from math import gcd
print("   n   phi(n)  rigid/total  caged offsets                cage empty?")
for n in range(3,21):
    rig=[d for d in range(1,n) if gcd(d,n)==1]
    cag=[d for d in range(1,n) if gcd(d,n)!=1]
    lvl={}
    for d in cag: lvl.setdefault(gcd(d,n),[]).append(d)
    desc="  ".join(f"g={g}:{v}" for g,v in sorted(lvl.items())) or "-"
    star=" <-- n=8" if n==8 else (" (prime)" if len(cag)==0 else "")
    print(f"  {n:2}    {len(rig):2}     {len(rig)}/{n-1}        {desc:<34} {'YES' if not cag else 'no'}{star}")
print()
print("  BS use p = n = 7, prime: Lambda_m,p = {1,...,p-1} are ALL units, so q(Lambda_m,p . d)")
print("  covers every arc and Lemma 2's counting closes.  At n = 8 only {1,3,5,7} are units.")
