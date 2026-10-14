"""The two arithmetic facts that close the tower induction, plus the interval lemma."""
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def w(b): return U(b)-L(b)+1
print("(A) w(b) >= b/2 for b >= 2:")
bad=[b for b in range(2,50001) if 2*w(b) < b]
print(f"    b = 2..50000: {'HOLDS' if not bad else f'FAILS {bad[:5]}'}")
print("(B) w(b) - 1 >= b/2 for b >= 4:")
bad=[b for b in range(4,50001) if 2*(w(b)-1) < b]
print(f"    b = 4..50000: {'HOLDS' if not bad else f'FAILS {bad[:5]}'}")
print(f"    (fails at b = 2,3 as expected: "
      f"{[(b, 2*(w(b)-1), b) for b in (2,3)]} -- those force the next modulus to be 1)")
print("\n(C) interval lemma: an interval of length >= b contains a good run of length >= w(b)-1")
worst=None
for b in range(2,400):
    for lo in range(0, 2*b):
        hi=lo+b-1
        best=0
        cur=0
        for q in range(lo,hi+1):
            if L(b) <= q % b <= U(b): cur+=1; best=max(best,cur)
            else: cur=0
        if worst is None or best-(w(b)-1) < worst[0]:
            worst=(best-(w(b)-1), b, lo, best, w(b)-1)
print(f"    minimum of (longest run) - (w(b)-1) over b=2..399, all offsets: {worst[0]}")
print(f"       attained b={worst[1]} offset={worst[2]}: longest run {worst[3]} vs w-1 = {worst[4]}")
print("\n(D) so the induction closes: surviving length w(b)-1 >= b/2 >= next modulus")
print("    tower step needs: next modulus b' | b, b' < b, so b' <= b/2 <= w(b)-1 for b >= 4")
