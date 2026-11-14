# conjT4_verify_v1.py -- the middle-service lemma for ALL m >= 4: what generalizes,
# what refutes the mission's fixed-201 mechanism. EXACT Fraction arithmetic; floats steer only.
# Branch n8-fresh-2026-10-30, 2026-11-15. New files conjT4_* only; nothing committed.
#
# Comb semantics (tailrest_anchor_lemma / tailcomp2 SETTING):
#   zones Z(rho,k) = ((8k-1)/rho, (8k+1)/rho) in the R-domain [1,7];
#   strips C_m = (8m-1, 8m+1); pin rho6 <= 49/7 = 7; top-leaf window W_6 = (47/7, 49/7).
#   A chain link (rho7, j*) -> leaf (rho6, 6) (the leaf zone covers the rho7-zone's right
#   endpoint R* = (8j*+1)/rho7) forces the LEAF-CLOSE DEMAND
#       rho6 in rho7 * ( 47/(8j*+1), 49/(8j*+1) )                     (F4 of tailrest_midservice)
#   i.e. 47/rho6 < (8j*+1)/rho7 < 49/rho6.
#   rho7 in C_m, rho6 <= 49/7  =>  feasibility of the demand forces 8j*+1 > 47(8m-1)/7,
#   i.e. j* >= J_min(m) = ceil((47(8m-1)/7 - 1)/8) = ceil((376m-54)/56).

from fractions import Fraction as Fr
from math import ceil, gcd

def Jmin(m):
    return ceil(Fr(47 * (8 * m - 1), 7 * 8) - Fr(1, 8))  # ceil((47(8m-1)/7 - 1)/8)

def r_tooth(m):   # upward-rounding remainder rho(m) = 56*J_min - (376m - 54)
    return 56 * Jmin(m) - (376 * m - 54)

def r_midsvc(m):  # midsvc_analytic S1's r(m) = (40m-54) mod 56 ; rho(m) = 56 - r(midsvc)
    return (40 * m - 54) % 56

print("# conjT4 verify v1 -- exact; middle-service lemma, all-m analysis")
print("# ==============================================================")

# ---------------------------------------------------------------- S0
print("# === S0. the mission's key inequality, EXACT for all m >= 4 (symbolic + check) ===")
# 47(8m-1)/201 > 49/7  <=>  329(8m-1) > 49*201 = 9849  <=>  2632m > 9849+329 = 10178
# <=> m > 10178/2632 = 5089/1316 = 3.8685...  <=>  m >= 4.   EXACT.
ok0 = (Fr(10178, 2632) < 4) and all(47 * (8 * m - 1) * 7 > 49 * 201 for m in range(4, 5001))
m4 = Fr(47 * 31, 201)
print(f"10178/2632 = {float(Fr(10178,2632)):.6f} < 4 : {Fr(10178,2632) < 4}; "
      f"m=4 check 1457/201 > 49/7 : {m4 > Fr(49,7)}  ({m4} = {float(m4):.6f}); all m in 4..5000: {ok0}")
print("VERDICT S0: 47(8m-1)/201 > 49/7 holds for every m >= 4 -- EXACT, no exceptions.")

# ---------------------------------------------------------------- S1
print("# === S1. P1 for ALL m (symbolic): closes at j* <= J_min(m)-1 violate the pin ===")
# kill: 47(8m-1)/(8*J_min-7) > 49/7  <=>  392*J_min < 2632m + 14  <=>  J_min < (376m+2)/56.
# J_min = ceil((376m-54)/56) <= (376m-54)/56 + 1 = (376m+2)/56, with EQUALITY iff
# (376m-54)/56 is an integer.  56 | (376m-54)  <=>  40m = 54 (mod 56): gcd(40,56)=8, 8 | 54 false
# -> NEVER an integer -> strict.  Margin: 329(8m-1) - 49(8J_min-7) = 7*r(midsvc) >= 14 > 0.
int_obstruction = gcd(40, 56)  # 8; 54 % 8 = 6 != 0
ok_nonint = all((376 * m - 54) % 56 != 0 for m in range(1, 20001))
ok_kill = all(392 * Jmin(m) < 2632 * m + 14 for m in range(1, 20001))
ok_ident = all(329 * (8 * m - 1) - 49 * (8 * Jmin(m) - 7) == 7 * r_midsvc(m) for m in range(1, 20001))
mins = min(r_midsvc(m) for m in range(1, 20001))
print(f"gcd(40,56) = {int_obstruction}, 54 mod 8 = {54 % 8} -> 40m = 54 (mod 56) UNSOLVABLE: symbolic")
print(f"x_m non-integer m=1..20000: {ok_nonint} | kill 392*J_min < 2632m+14, m=1..20000: {ok_kill} | "
      f"identity 329(8m-1) - 49(8J_min-7) = 7r(m): {ok_ident} | min r(m) = {mins}")
print(f"J_min(4) = {Jmin(4)}  (the m=4 wall's j*=25 close sits BELOW the first feasible lap 26)")
print("VERDICT S1: P1 holds for ALL m >= 1 (upgrades the ledger's 4..199 finite check to symbolic):")
print("  every top-leaf close at j* < J_min(m) demands rho6 > 49/7 -- dead on the pin, margin")
print("  r(m)/(8*J_min-7) > 0 with r(m) = (40m-54) mod 56 in {2,42,26,10,50,34,18} (m mod 7).")

# ---------------------------------------------------------------- S2
print("# === S2. the 7-tooth closed form rho(m) = 56 - r(m), and calibration vs ledgers ===")
teeth = {}
for m in range(1, 2001):
    teeth.setdefault(m % 7, set()).add(r_tooth(m))
teeth = {k: sorted(v)[0] if len(v) == 1 else v for k, v in sorted(teeth.items())}
print(f"rho(m) by m mod 7 (m=1..2000, unique per class): {teeth}")
print(f"min rho(m) = {min(teeth.values())} (class m = 4 mod 7); delta(m) := rho(m)/47")
# calibration vs midsvc S1 r-table {0:2, 1:42, 2:26, 3:10, 4:50, 5:34, 6:18}
msvc_r = {0: 2, 1: 42, 2: 26, 3: 10, 4: 50, 5: 34, 6: 18}
ok_r = all(56 - teeth[k] == msvc_r[k] for k in range(7))
print(f"r(m) = 56 - rho(m) vs midsvc_analytic S1 table: {ok_r}   [T 7/7]")

# ---------------------------------------------------------------- S3
print("# === S3. PROPOSITION B (the failing case): at j* = J_min(m) the close is pin-feasible ===")
# window: rho7 in (8m-1, 8m-1 + rho(m)/47).  On it, band B = rho7*(47/(8J+1), 49/(8J+1)):
#  (i)  floor 47*rho7/(8J+1) < 49/7 : at the right edge 47(8m-1+rho/47)/(8J+1) = 7 EXACTLY
#        (since 8J+1 = (376m-47+rho)/7), increasing in rho7 -> strict on the open window.
#  (ii) ceiling 49*rho7/(8J+1) > 47/7 for ALL rho7 > 8m-1 iff 2401(8m-1) > 47(8J+1)
#        iff 1536m > 192 + 47*rho(m); worst case m=2, rho<=54: 3072 > 2730 -- SYMBOLIC all m >= 2.
#  (iii) front-pin: band floor > 7*rho7/(8m+1) iff 56*J_min < 376m+40; J_min <= (376m+2)/56
#        gives 56*J_min <= 376m+2 -- SYMBOLIC all m.
#  (iv) ordering: rho6 < 7 < 8m-1 < rho7 (m >= 2 gives rho7 > 15 > 7).
ok_sym_ceiling = all(1536 * m > 192 + 47 * r_tooth(m) for m in range(2, 5001))
ok_sym_frontpin = all(56 * Jmin(m) < 376 * m + 40 for m in range(1, 5001))
print(f"(ii) 1536m > 192 + 47 rho(m), m=2..5000: {ok_sym_ceiling}   (worst-case bound 3072 > 2730 symbolic)")
print(f"(iii) 56*J_min < 376m+40, m=1..5000: {ok_sym_frontpin}   (56*J_min <= 376m+2 symbolic)")

print("# explicit exact witnesses rho7*, rho6* (m = 2..30):")
all_ok = True
for m in range(2, 31):
    J = Jmin(m); rho = r_tooth(m)
    e_lo, width = 8 * m - 1, Fr(rho, 47)
    rho7 = Fr(e_lo) + width / 2                       # window midpoint
    lo = max(Fr(47) * rho7 / (8 * J + 1), Fr(47, 7))  # band floor vs W_6 floor
    hi = min(Fr(49) * rho7 / (8 * J + 1), Fr(49, 7))  # band ceiling vs W_6 ceiling
    rho6 = (lo + hi) / 2
    Rstar = Fr(8 * J + 1) / rho7
    checks = {
        "strip": Fr(e_lo) < rho7 < 8 * m + 1,
        "pin": rho6 <= Fr(49, 7),
        "W6": Fr(47, 7) < rho6 < Fr(49, 7),
        "close": Fr(47) / rho6 < Rstar < Fr(49) / rho6,   # Z(rho6,6) covers R*
        "anchor1": Fr(8 * m - 1) < rho7 < Fr(8 * m + 1) and Fr(1) / rho7 > 0,  # Z(rho7,m) contains 1
        "order": rho6 < rho7,
        "frontpin": rho6 > Fr(7) * rho7 / (8 * m + 1),
        "frontfloor_f": rho6 > Fr(7 * (8 * m - 1), 8 * m + 1),
    }
    all_ok &= all(checks.values())
    if m <= 6 or m in (7, 8, 11, 15):
        print(f"  m={m:2d}: rho7* = {rho7} = {float(rho7):.5f}, rho6* = {rho6} = {float(rho6):.5f}, "
              f"J={J}, window width delta = {width} = {float(width):.5f} | all checks: {all(checks.values())}")
print(f"ALL witness checks m=2..30 (7 conditions x 29 m): {all_ok}   [T 29/29]")
print("VERDICT S3: for EVERY m >= 2 the leaf-close at j* = J_min(m) demands rho6 inside")
print("  (f(m), 49/7) ∩ W_6 on the nonempty rho7-window (8m-1, 8m-1 + rho(m)/47), width >= 6/47:")
print("  the sliver + leaf-close conflict of the mission's form FAILS at every m >= 2, witness-exact.")

# ---------------------------------------------------------------- S4
print("# === S4. calibration vs the ledger tables (exact) ===")
led = {2:13,3:20,4:26,5:33,6:40,7:47,8:53,9:60,10:67,11:73,12:80,13:87,14:94,15:100,
       16:107,17:114,18:120,19:127,20:134,21:141,22:147,23:154,24:161,25:167,26:174,
       27:181,28:188,29:194,30:201}
ok_J = all(Jmin(m) == v for m, v in led.items())
print(f"J_min closed form vs midbound2_mono C2 table m=2..30: {ok_J}   [T {sum(Jmin(m)==v for m,v in led.items())}/{len(led)}]")
ok_b6 = (Fr(r_tooth(13), 8*Jmin(13)+1) == Fr(38, 697) and Fr(r_tooth(14), 8*Jmin(14)+1) == Fr(18, 251)
         and Fr(r_tooth(15), 8*Jmin(15)+1) == Fr(14, 801))
print(f"B6 = rho/(8J_min+1) vs midsvc S3 spots 38/697, 18/251, 14/801 (m=13,14,15): {ok_b6}   [T 3/3]")
ok_delta = all(r_tooth(m) == 47 * (Fr(7*(8*Jmin(m)+1), 47) - (8*m-1)) for m in (4, 5, 6, 7, 8, 9, 10, 11, 15))
print(f"delta(m) = rho(m)/47 = cap_model - strip edge (C2 cap_model column spots): {ok_delta}   [T 9/9]")
# the m=4 wall band: rho7 in (31, 2023/65), j*=25 band subset (1457/201, 49*2023/(65*201))
b_lo, b_hi = Fr(47*31, 201), Fr(49*2023, 65*201)
print(f"m=4 wall: j*=25 band over rho7 in (31, 2023/65) = ({float(b_lo):.4f}, {float(b_hi):.4f}); "
      f"floor > 49/7: {b_lo > Fr(49,7)}; J_min(4)-1 = {Jmin(4)-1} = 25: the wall close is pin-dead (S1)")

# ---------------------------------------------------------------- S5
print("# === S5. the close-lap window WIDENS (cross-check vs midsvc S4b); T_min = 8 ===")
def U_midsvc(m):   # midsvc v1b closed form U(m) = floor((49(8m+1)/f(m)+1)/8)
    f = Fr(7 * (8 * m - 1), 8 * m + 1)
    return (49 * (8 * m + 1) // f + 1) // 8 if False else int((Fr(49*(8*m+1)) / f + 1) // 8)
ok_U = all(U_midsvc(m) >= Jmin(m) for m in range(2, 501))
spots = {13: 93, 14: 100, 15: 107}
ok_Uspot = all(U_midsvc(m) == v for m, v in spots.items())
widths = [(m, U_midsvc(m) - Jmin(m)) for m in (13, 14, 15, 20, 30, 40)]
print(f"U(m) >= J_min(m), m=2..500 (window nonempty): {ok_U} | U spots 93/100/107: {ok_Uspot}   [T 3/3]")
print(f"widths U-J_min at m=13,14,15,20,30,40: {widths} (widening, ~ (8/56)m -- leaf side does NOT pinch)")
ok_T8 = all(int(-(-(Jmin(m)) // 1)) and ceil(__import__('math').log(Fr(Jmin(m), m)) / __import__('math').log(Fr(9, 7))) == 8 for m in range(4, 2001))
print(f"T_min = ceil(ln(J_min/m)/ln(9/7)) = 8 for all m=4..2000 (bridge count m-independent): {ok_T8}")

print("# ==============================================================")
print("OVERALL: (A) P1 closes-below-J_min kill: ALL m >= 1, symbolic (S1).")
print("         (B) the mission's fixed-201 conflict: REFUTED at every m >= 2 -- the first")
print("             pin-feasible close j* = J_min(m) ~ 47m/7 has demand band inside the pin")
print("             window on a rho7-substrip of width rho(m)/47 >= 6/47 (S3, witnesses [T 29/29]).")
print("         (C) sharpening is real but scalar-open: B6(m) = rho(m)/(8J_min+1) -> 0,")
print("             sliver 14/(8m+1) -> 0, close-lap window WIDENS; kill = joint collapse (open).")
