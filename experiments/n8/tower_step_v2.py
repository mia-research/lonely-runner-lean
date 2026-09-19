"""Try the weaker invariant: |I| >= ceil(b/2), I a sub-interval of [L(b),U(b)].
Step: b' | b, b' < b  =>  surviving run >= ceil(b'/2)?"""
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def w(b): return U(b)-L(b)+1
def ceil2(x): return -((-x)//2)
def longest(lo,hi,b):
    best=0; j=(lo-L(b))//b - 1
    while j*b+L(b) <= hi+b:
        a=max(lo,j*b+L(b)); c=min(hi,j*b+U(b))
        if a<=c: best=max(best,c-a+1)
        j+=1
    return best
for name,need_f,want_f in (("ceil(b/2)", ceil2, ceil2),):
    bad=[]; tot=0
    for b in range(2,401):
        for bp in range(2,b):
            if b % bp: continue
            need=need_f(b)
            if need > w(b): continue
            for lo in range(L(b), U(b)-need+2):
                tot+=1
                r=longest(lo,lo+need-1,bp)
                if r < want_f(bp): bad.append((b,bp,lo,r,want_f(bp)))
    print(f"invariant |I| >= {name}:  placements {tot};  {'HOLDS' if not bad else f'FAILS {len(bad)}'}")
    for x in bad[:8]: print(f"   b={x[0]} b'={x[1]} lo={x[2]} run={x[3]} needed>={x[4]}")
print("\nbase case: |[L(b),U(b)]| = w(b) >= ceil(b/2)?")
bad=[b for b in range(2,50001) if w(b) < ceil2(b)]
print(f"   b=2..50000: {'HOLDS' if not bad else f'FAILS {bad[:5]}'}")
print("\nand the tower terminates: the last modulus needs only a nonempty run")
