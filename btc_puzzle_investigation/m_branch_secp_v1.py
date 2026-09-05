# Exact integers only. Which branch of the measured law does secp land in?
p = 2**256 - 2**32 - 977
print("p mod 12 =", p % 12, " (law's p=7 mod 12 branch applies)" if p%12==7 else "")
print("p mod 4  =", p % 4, "  (mu4 argument needs p=3 mod 4)")
print("p mod 3  =", p % 3, "  (cubic residue symbol defined iff p=1 mod 3)")
assert (p-1) % 3 == 0
for B in (7, 2, 11):
    t = pow(B, (p-1)//3, p)
    print("B=%2d : B^((p-1)/3) mod p == 1 ? %s  -> %s  => law predicts m = %s"
          % (B, t == 1, "cubic RESIDUE" if t==1 else "cubic NON-residue",
             -2 if t==1 else 1))
