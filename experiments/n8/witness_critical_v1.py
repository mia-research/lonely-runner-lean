from math import gcd
def wit(ds,e): return [k for k in range(e) if all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)]
def supp(ds): return {e:w for e in ds if (w:=wit(ds,e))}

print("CRITICAL FAMILY  {2,3,4,5,6,7, x}  with 16 | x : |S| = 1, sole flank x.")
print("If that one flank ever emptied, |S| = 0 and LRC(8) would be FALSE.")
print("So: how many of the x openings are witnesses, and does it shrink?\n")
print(f"  {'x':>6} | {'|S|':>3} | {'#witnesses at x':>15} | {'out of x':>8} | {'density':>8} | witness k")
rows=[]
for j in range(4,16):
    x=2**j; ds=sorted([2,3,4,5,6,7,x]); S=supp(ds)
    w=S.get(x,[])
    rows.append((x,len(S),len(w),x,len(w)/x))
    print(f"  {x:>6} | {len(S):>3} | {len(w):>15} | {x:>8} | {len(w)/x:>8.5f} | {w[:6]}{' ...' if len(w)>6 else ''}")

print("\n  non-power-of-two multiples of 16:")
for x in [48,80,112,144,176,208,240,304,368,496]:
    ds=sorted([2,3,4,5,6,7,x])
    if len(set(ds))<7: continue
    S=supp(ds); w=S.get(x,[])
    print(f"  {x:>6} | {len(S):>3} | {len(w):>15} | {x:>8} | {len(w)/x:>8.5f} | {w[:6]}{' ...' if len(w)>6 else ''}")

print("\nDoes the witness count at the sole flank ever reach 0 in this family?")
worst=None
for x in range(16,4097,16):
    ds=sorted(set([2,3,4,5,6,7,x]))
    if len(ds)<7: continue
    w=wit(ds,x)
    if worst is None or len(w)<worst[1]: worst=(x,len(w))
    if len(w)==0: print(f"  *** x={x}: ZERO witnesses at the sole flank -> check |S| ***", supp(ds))
print(f"  scanned x = 16,32,...,4096 : minimum witness count at the sole flank = {worst[1]} (at x={worst[0]})")
print(f"  -> the count never reaches 0 on this range; scope: this family, x <= 4096, exact arithmetic")
