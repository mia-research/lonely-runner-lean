def clear(ds,e,k): return all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)
def wit(ds,e): return [k for k in range(e) if clear(ds,e,k)]

print("CANDIDATE CLOSED FORM for the critical family ds = {2,3,4,5,6,7,x}, 16 | x:")
print("   witness set at flank x  ==  [x/16, x/8)  U  [7x/8, 15x/16)")
print("   single witness map:      (e,k) = (x, x/16)\n")

bad_set=0; bad_map=0; n=0
xs=[16*m for m in range(1,201)] + [2**j for j in range(4,20)] + [16*m for m in (1000,2500,4001,5077)]
for x in sorted(set(xs)):
    ds=sorted(set([2,3,4,5,6,7,x]))
    if len(ds)<7: continue
    n+=1
    pred=set(range(x//16,x//8)) | set(range(7*x//8,15*x//16))
    if x<=4096:
        act=set(wit(ds,x))
        if act!=pred:
            bad_set+=1
            if bad_set<=3: print(f"  SET MISMATCH x={x}: extra {sorted(act-pred)[:5]} missing {sorted(pred-act)[:5]}")
    if not clear(ds,x,x//16):
        bad_map+=1
        if bad_map<=5: print(f"  MAP FAILS at x={x}")
print(f"  x values tested: {n}  (full-set check for x<=4096)")
print(f"  witness-set formula mismatches: {bad_set}")
print(f"  single-map (x, x/16) failures : {bad_map}")

print("\nIs the map the FIRST witness (smallest k)?")
for x in [16,32,48,64,144,496]:
    ds=sorted([2,3,4,5,6,7,x]); w=wit(ds,x)
    print(f"  x={x:>4}: min k = {min(w)}, x/16 = {x//16}, equal: {min(w)==x//16}")

print("\nSanity: does the formula respect |S| = 1 (no other flank supports)?")
for x in [16,32,48,64,144,496,1024]:
    ds=sorted([2,3,4,5,6,7,x])
    S={e for e in ds if wit(ds,e)}
    print(f"  x={x:>4}: supporting flanks = {sorted(S)}  -> |S| = {len(S)}")
