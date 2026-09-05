# ---- Doc 7: Farey/Egyptian for Puzzle 140. Spot-check the numeric substrate. ----
p = 2**256 - 2**32 - 977
x140 = 0x1f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640
y140 = 0xf96923e4c4e959430c81a73a62a05609b2bbea22620cefc54a58182b9f2a2ae9
print("Puzzle-140 pubkey on secp256k1 (y^2 == x^3+7)?", (y140*y140 - (x140**3+7)) % p == 0)

# their Eisenstein decomposition p = N(a+b*omega) = a^2 - a b + b^2
a=367917413016453100223835821029139468249
b=64502973549206556628585045361533709078
print("N(a+b w)=a^2-ab+b^2 == p ?", a*a-a*b+b*b == p, " (their claimed Gauss basis for p)")

# their 'normalized norm s' for formula1 ~0.0198 ; core gate threshold 3/16=0.1875
print("3/16 =", 3/16)
print("Note: whether s<3/16 holds is a computation on public data; it gates the (nonexistent) d-mod-6 bridge.")
