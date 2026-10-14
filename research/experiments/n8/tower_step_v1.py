"""The inductive step, in the ALIGNED setting that the tower actually produces.
After processing b the surviving interval I sits inside [L(b),U(b)], and b' | b, so the
b'-arcs [kb'+L(b'), kb'+U(b')] are aligned to I's frame -- no adversarial offset.
STEP to test:  |I| >= w(b)-1  and  b' | b, b' < b   =>   new run >= w(b')-1."""
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def w(b): return U(b)-L(b)+1
def longest(lo,hi,b):
    best=0
    j=(lo-L(b))//b - 1
    while j*b+L(b) <= hi+b:
        a=max(lo,j*b+L(b)); c=min(hi,j*b+U(b))
        if a<=c: best=max(best,c-a+1)
        j+=1
    return best
print("step: I any sub-interval of [L(b),U(b)] with |I| >= w(b)-1;  b' | b, b' < b")
print("      does the surviving run have length >= w(b')-1 ?")
bad=[]; tot=0
for b in range(2,700):
    for bp in range(2,b):
        if b % bp: continue
        need=max(w(b)-1,1)
        # every aligned sub-interval of [L(b),U(b)] of length exactly `need`
        for lo in range(L(b), U(b)-need+2):
            tot+=1
            if longest(lo,lo+need-1,bp) < w(bp)-1:
                bad.append((b,bp,lo,longest(lo,lo+need-1,bp),w(bp)-1))
            break   # worst case is the shortest interval; take the first placement
print(f"   pairs tested: {tot};  {'HOLDS' if not bad else f'FAILS {len(bad)}'}")
for x in bad[:10]: print(f"      b={x[0]} b'={x[1]} lo={x[2]} run={x[3]} needed>={x[4]}")
print("\n   all placements (not just the first), b <= 200:")
bad2=[]; tot2=0
for b in range(2,201):
    for bp in range(2,b):
        if b % bp: continue
        need=max(w(b)-1,1)
        for lo in range(L(b), U(b)-need+2):
            tot2+=1
            if longest(lo,lo+need-1,bp) < w(bp)-1:
                bad2.append((b,bp,lo,longest(lo,lo+need-1,bp),w(bp)-1))
print(f"   placements tested: {tot2};  {'HOLDS' if not bad2 else f'FAILS {len(bad2)}'}")
for x in bad2[:10]: print(f"      b={x[0]} b'={x[1]} lo={x[2]} run={x[3]} needed>={x[4]}")
