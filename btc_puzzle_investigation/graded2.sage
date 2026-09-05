import math
def nsig_synth(p, mk): return len(set(mk(a) for a in range(1,p)))
feats = {
 "const  (a mod 12)"    : (lambda p:(lambda a:a%12),                       0.0),
 "sqrt   (a mod round p^.5)":(lambda p:(lambda a:a%max(2,round(p**0.5))),  0.5),
 "p^0.75 (a mod round p^.75)":(lambda p:(lambda a:a%max(2,round(p**0.75))),0.75),
 "linear (a)"           : (lambda p:(lambda a:a),                          1.0),
}
primes=[p for p in prime_range(20,4300) if p%12==7]
def slope(pairs):
    xs=[math.log(p) for p,_ in pairs]; ys=[math.log(max(1,n)) for _,n in pairs]
    n=len(xs);mx=sum(xs)/n;my=sum(ys)/n
    return sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print("GRADED POSITIVE CONTROLS: does the SAME N_sig detector track a KNOWN scaling leak?")
print(" feature                       expect   measured slope   N_sig: p=43 -> p=%d"%primes[-1])
for k,(mk,exp) in feats.items():
    d=[(p,nsig_synth(p,mk(p))) for p in primes]
    print("  %-27s  %.2f     %.3f            %d -> %d"%(k,exp,slope(d),dict(d)[43],d[-1][1]))
