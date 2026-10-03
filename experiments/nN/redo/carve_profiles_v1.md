# carve_profiles_v1 -- the carving profile as a catalogue of outcomes

Directory `experiments/nN/redo/`. Every stated fact is an exact-Fraction computation (windows by interval intersection, cross-checked by `path()` and by `clear_components`), or "not reached by (search)". No floats entered any fact (one printed decimal, 0.9957, is a label for an exact comparison `lmax6*rho_7/2 < 1`, checked in Fractions).

## 0. Record searched first; reused, not rebuilt
grep of `MANUSCRIPT_v21.md`, `MECHANISM_MAP_v5.md`, `RUNNING_LOG_order8_v1.md` for "carv"/"profile": no carving object exists (the word "profile" there means a reading tuple, MANUSCRIPT_v21 sec. 11-12). Reused: `path()` (`cascade_path_map_v1.py`), `clear_components`, `in_zone7` (`ceil_k6_lib_v1.py`, Lemma 2 of `ceil_gate_crosser_v1.md`), the member lists `cell_members7_J1.pkl`, `cell_members7_J2.pkl`, `taxo_sample_v1.pkl`, the lattice definition of `lat_exhaustive_v1.md` (integer sets, gcd 1, readings a_i/s), the K6 / K_7 windows of `k6map_structure_v1.md` and `win_lonely_set_v1.md` (the [1,7] part of its windows is K_7; first window = landing).

## 1. Method and scripts
- `carve_lib_v1.py`: `clear_pieces(r)` = closed pieces of C_r in [1,7] (complement of the open zones); `inter` = intersection of sorted closed-interval lists (single points kept); `carve(rhos, order)` returns K_1..K_7 with K_1=[1,7], K_k = K_{k-1} ∩ C_k in rank order 2..7; `checks()` per member.
- `carve_run_v1.py DATASET [start end]` -> `carve_rec_*_v1.pkl`; logs `carve_run_v1.out`, `carve_run3_v1.out`. `carve_analyse_v1.py` -> `carve_analyse_v1.out`, `carve_table_v1.out` (every profile with member counts per dataset and one exact example: 43,635 rows). `carve_extra_v1.py` -> `carve_extra_v1.out`.
- Exact checks on EVERY member (all datasets): (a) K_7 by two further random orders of readings 2..7 equals the rank-order K_7; (b) K_7 equals `clear_components(readings 2..7, H=7)` (independent sweep over zones); (c) K_6 equals `clear_components(readings 1..6, H=7)`; (d) `path()` landing equals the left end of the first window of K_7 when K_7 is non-empty, and `path()` landing > 7 when K_7 is empty; (e) K_7 empty iff every component of K_6 lies in one open zone of reading 7 (`in_zone7`, Lemma 2). Failures: 0 in every dataset.
- Datasets: J1 = 18,452 stored exact members (one point per outcome region, not the box); J2s = 20,000 members drawn with `random.Random(20261004).sample` from the 271,361 J2 members; taxo = the 52,000 sampler arrangements; lat1_24 = ALL 100,947 sets 1<a_2<...<a_7<=24 (s=1, exhaustive; lat1_16, lat1_20 are the sub-collections a_7 <= 16 (5,005 sets), <= 20 (27,132)); additionally lat2_24 = all 74,151 sets 2<a_2<...<a_7<=24, gcd 1 (readings a/2, rho_7 <= 12) and lat3_24 = all 54,257 sets 3<...<=24, gcd 1 (rho_7 <= 8). Run time: J1 83 s, J2s 86 s, taxo 258 s, lat chunks 66-205 s.
- Process note: one duplicate chain of `carve_run_v1.py` (taxo, lat1_24) was started by mistake while the first chain was still running; two processes ran for about 2 minutes, then the duplicate was killed. Its output was not used; the records come from the first chain (`carve_run_v1.out`), and lat2_24, lat3_24 ran alone.

Profile = (n_1..n_7), n_k = number of windows of K_k (n_1 = 1); "profile" in the counts below is (n_2..n_7).

## 2. Catalogue: distinct profiles (n_2..n_7)
| dataset | members | distinct profiles | profiles with exactly one member | with #one-point windows added |
|---|---|---|---|---|
| J1 | 18,452 | 1,914 | 674 | 2,342 |
| J2s | 20,000 | 7,512 | 4,473 | 8,579 |
| taxo | 52,000 | 28,228 | 23,504 | 29,726 |
| lat1_24 | 100,947 | 10,408 | 3,605 | 19,144 |
| lat2_24 | 74,151 | 6,221 | 2,002 | 12,497 |
| lat3_24 | 54,257 | 3,721 | 1,097 | 6,840 |
| lat1_16 | 5,005 | 1,082 | 476 | 1,738 |
| lat1_20 | 27,132 | 3,743 | 1,416 | 6,637 |
Distinct over all families: 43,635. Full list with counts and one exact example per profile: `carve_table_v1.out`. Longest window of K_7 and the number of one-point windows are stored per member in the `carve_rec_*` pickles (key `longest`, `onept`).

## 3. Does the profile set stabilise? Evidence: it does not, in any family tested
- Lattice s=1, profiles first seen at a_7 = N (new relative to all smaller a_7): N=12: 74, 13: 119, 14: 168, 15: 291, 16: 338, 17: 422, 18: 484, 19: 686, 20: 1069, 21: 1282, 22: 1555, 23: 1657, 24: 2171; cumulative 166 (N=12), 1,082 (16), 3,743 (20), 10,408 (24). Inclusions: lat1_16 profiles ⊂ lat1_20 profiles ⊂ lat1_24 profiles (A−B = 0 both times), with 2,661 and 6,665 profiles added. Singletons among a_7 <= N: 476 (16), 1,416 (20), 3,605 (24). The increments by N do not decrease through N=24. Not reached: any N at which a new a_7 adds no profile.
- J2s: distinct profiles among the first 1,000 / 2,500 / 5,000 / 10,000 / 15,000 / 20,000 members of the sample: 796 / 1,680 / 2,825 / 4,461 / 6,166 / 7,512; 4,473 of the 7,512 occur once. By rho_7: (0,9] 413 profiles (1,085 members); (9,13] 911 (1,551); (13,17] 6,686 (16,109); (17,100] 1,018 (1,255).
- J1 against J2s: of the 413 J2s profiles with rho_7 <= 9, 410 occur in J1's 1,914 and 3 do not. J1 profiles absent from J2s: 796; J2s absent from J1: 6,394 (the J2s sample includes rho_7 up to 17).
- J1 is a smaller object than J2: J1 by rho_7: (7,8] 755 profiles, (8,9] 1,574 profiles (one member with rho_7 = 7 not in the bins above: 1 profile).
- Within rho_7 <= 9: lat1_24 gives 20 profiles, 6 in the J1 set, 2 in the J2s set, 20 in the taxo set; lat2_24 gives 1,360 (324 in J1); lat3_24 gives 3,721 (733 in J1). So lattice profiles within the J1 box are mostly absent from the J1 stored points (J1 holds one point per region; lattice points are tie points, one-point windows included); this is a statement about the stored points.
- The profile count therefore grows with the window (rho_7 range) and with the sample in every family: the set (n_2..n_7) is not finite-and-stable on this evidence. Largest n_k seen: J1 (k=2..7) 6, 9, 11, 11, 11, 9; J2s 10, 18, 23, 24, 20, 19; taxo 77, 121, 149, 155, 160, 244; lat1_24 15, 26, 32, 32, 32, 32; lat2_24 8, 12, 16, 16, 16, 17; lat3_24 6, 9, 11, 11, 10, 10.

## 4. Gate crossers (K_7 empty)
Crossers occur only in J1 (7,567 of 18,452) and J2s (568 of 20,000); taxo, lat1_24, lat2_24, lat3_24: 0 crossers (not reached by those sets).
- Exact separator (this is Lemma 2, tested): K_7 empty iff every component of K_6 is inside one open zone of reading 7. Tested on 18,452 + 20,000 + 52,000 + 100,947 + 74,151 + 54,257 members: agreement in all (`gate_cond == crosser`), including 0 members where the condition holds with K_7 non-empty and 0 where it fails with K_7 empty.
- Profile separator: not found. (n_2..n_7) of a crosser ends in 0, so trivially no crosser profile is shared with a non-crosser. On the prefix (n_2..n_6): J1 117 crosser prefixes, 77 shared with non-crossers, 40 occur only for crossers (2,752 members); J2s 75 crosser prefixes, 48 shared, 27 crosser-only (265 members); all 75 J2s crosser prefixes occur among J1's 117.
- n_6: crossers have n_6 in {2,3,4,5,6} (J1: 876, 3,794, 2,313, 580, 4; J2s: 70, 280, 173, 44, 1). Non-crossers: J1 n_6 from 2 to 11 (7,803 with n_6 <= 6, 258 with n_6 <= 3); J2s from 2 to 20 (2,884 with n_6 <= 6). So "n_6 <= 6" holds for every crosser tested and is not sufficient.
- (W): every component of K_6 shorter than 2/rho_7 holds for all 7,567 + 568 crossers (exact, `lmax6*rho_7/2 < 1`; largest value 0.99570 J1, 0.99529 J2s as exact Fractions in the records) and fails for 8,727 of 10,885 J1 non-crossers and 19,163 of 19,432 J2s non-crossers; it holds for 2,158 J1 and 269 J2s non-crossers (1,439 and 102 of them with n_6 <= 6). So (W) is necessary on this data (it is a proved consequence, Lemma 2) and not sufficient.
- Crosser profile list with member counts and examples: rows of `carve_table_v1.out` ending in 0 (117 + 75 prefixes; J1 crossers have 117 distinct (n_2..n_7), J2s 75).

## 5. Monotonicity of n_k
n_k is not monotone in any family. Members with some k in 2..7 and n_k > n_{k-1} (k=2 compares with n_1 = 1, so an increase at k=2 means K_2 has more than one window): J1 18,452 of 18,452; J2s 20,000; taxo 50,694; lat1_24 100,947; lat2_24 74,151; lat3_24 54,257. Members with an increase at k = 5/6/7 (n_k > n_{k-1}): J1 3,704 / 479 / 98; J2s 10,404 / 4,788 / 1,977; taxo 37,676 / 31,162 / 26,178; lat1_24 75,174 / 51,975 / 31,315; lat2_24 49,840 / 32,080 / 20,741; lat3_24 32,586 / 21,712 / 8,907. n_7 < n_6: J1 17,721, J2s 13,819, taxo 11,753, lat1_24 29,917, lat2_24 24,139, lat3_24 23,577.
Exact examples of an increase at the last step (n_7 > n_6): J1 readings [1, 3091954958755321/1125899906842624, 2338136490985017/562949953421312, 1436032755370731/281474976710656, 1827993782655639/281474976710656, 7, 4263660660031501/562949953421312], ns = (1,3,5,6,6,5,6); J2s [1, 107546238493087/35184372088832, 5171038937377903/1125899906842624, 3250286318902185/562949953421312, 7, 8009717714575995/1125899906842624, 8794892392323559/1125899906842624], ns = (1,3,5,6,7,6,7); lat1 [1,2,4,5,7,8,9], ns = (1,2,4,6,6,4,6); lat2 [1,3/2,2,5/2,3,7/2,9/2], ns = (1,2,3,4,4,2,3); lat3 [1,4/3,5/3,2,7/3,8/3,11/3], ns = (1,2,2,2,1,1,2); taxo [1,4419/4000,5/4,209/160,3/2,377/250,1959/1000], ns = (1,1,1,1,1,1,2).
Largest single profile row: taxo [1, 589/200, 1097/125, 26443/1000, 79133/1000, 12073/50, 149683/200], ns = (1,3,7,17,40,100,244). Largest in a lattice: lat1 [1,2,10,18,20,22,24], ns = (1,2,8,16,22,30,32). Largest in J1: ns = (1,5,9,11,10,10,7) at the first listed example in `carve_analyse_v1.out` section 4b; J2s ns = (1,10,16,21,24,20,15).

## 6. Profiles without a counterpart in another family (within the sets tested)
Union over J1, J2s, taxo = 34,980 profiles; over lat1_24, lat2_24, lat3_24 = 18,480; common 6,631; only in the lattices 11,849; only in the non-lattice sets 28,349. Profiles in no other dataset: J1 516, J2s 3,949, taxo 22,972, lat1_24 8,598, lat2_24 1,951, lat3_24 988. These counts depend on sample sizes (taxo 52,000 and J2s 20,000 are samples; lattices exhaustive over their ranges), so they are statements about the stated sets only; "not reached by" the other families.
Exact examples:
- taxo only, profile (1,1,1,1,1,1) (K_2..K_7 each one window; 1,306 taxo members; none in J1, J2s, lattices): [1, 253/200, 269/200, 186/125, 367/200, 1029/500, 2209/1000].
- lattice only: lat3 [1, 4/3, 5/3, 2, 7/3, 8/3, 20/3], profile (2,2,2,1,1,3); lat3 [1,4/3,5/3,2,7/3,17/3,6], (2,2,2,1,3,3) with a one-point window; lat1 [1,2,3,4,7,8,15], (2,4,6,6,4,8); lat1 [1,2,3,4,7,15,16], (2,4,6,6,10,8); lat2 [1, 3/2, 2, 7/2, 4, 10, 12], (2,3,3,3,6,8).
- J1 only: profile (1,1,3,5,6,4), readings in `carve_analyse_v1.out` section 5 (first of 516).
- Gate-crossing profiles occur only in J1/J2s (section 4).

## 7. Exceptions and limits
1. No stabilisation: counts grow through lattice N = 24 and across J2s sample sizes; no family reached a saturation point.
2. The profile (n_2..n_7) does not separate crossers from non-crossers; only the Lemma-2 gate condition does, exactly.
3. n_k is non-monotone for every family; n_7 up to 244 (taxo), 32 (integer lattice a_7 <= 24), 19 (J2s).
4. J1 and J2s are stored points (one per outcome region), J2s is a 20,000-member draw; lattice runs are exhaustive over a_7 <= 24 (s = 1), gcd-1 sets with a_7 <= 24 for s = 2, 3. Nothing here covers s >= 4 or a_7 > 24.
5. Longest window of K_7 and one-point-window counts were recorded per member but are not tabulated beyond the (profile, #one-point) distinct counts in section 2.
