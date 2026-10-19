import LonelyRunner.LRC.Spec.OrderSevenP2RootN
import LonelyRunner.LRC.Spec.OrderSevenP2Blk0N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk1N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk2N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk3N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk4N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk5N
import LonelyRunner.LRC.Spec.OrderSevenP2Blk6N
import LonelyRunner.LRC.Spec.OrderSevenP2Cap0N
import LonelyRunner.LRC.Spec.OrderSevenP2Cap1N
import LonelyRunner.LRC.Spec.OrderSevenP2Cap2N
import LonelyRunner.LRC.Spec.OrderSevenP2ClsN
import LonelyRunner.LRC.Spec.OrderSevenP2Dom0N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom1N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom2N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom3N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom4N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom5N
import LonelyRunner.LRC.Spec.OrderSevenP2Dom6N

/-!
# AbsP2 proved

`absP2 : LRC.O7Abs.AbsP2`: a runner with top digits 0 and any three unit abstract states share an instant with
`c <= 5`.  Runner 1's good instants contain a base set `AB b` (`bdomP`); the three units contain table states over
the 245 instants (`domP`); `Claim (AB b) 3` from the certificate.  No `sorry`, no `native_decide`.
-/

namespace LRC.O7P2
open LRC.O7Abs

theorem blkSpec : BlkSpec := by
  intro x hx k hk
  interval_cases x
  · exact blk_of blkX0 (by omega) (by omega) hk
  · exact blk_of blkX1 (by omega) (by omega) hk
  · exact blk_of blkX2 (by omega) (by omega) hk
  · exact blk_of blkX3 (by omega) (by omega) hk
  · exact blk_of blkX4 (by omega) (by omega) hk
  · exact blk_of blkX5 (by omega) (by omega) hk
  · exact blk_of blkX6 (by omega) (by omega) hk
  · exact blk_of blkX7 (by omega) (by omega) hk
  · exact blk_of blkX8 (by omega) (by omega) hk
  · exact blk_of blkX9 (by omega) (by omega) hk
  · exact blk_of blkX10 (by omega) (by omega) hk
  · exact blk_of blkX11 (by omega) (by omega) hk
  · exact blk_of blkX12 (by omega) (by omega) hk
  · exact blk_of blkX13 (by omega) (by omega) hk
  · exact blk_of blkX14 (by omega) (by omega) hk
  · exact blk_of blkX15 (by omega) (by omega) hk
  · exact blk_of blkX16 (by omega) (by omega) hk
  · exact blk_of blkX17 (by omega) (by omega) hk
  · exact blk_of blkX18 (by omega) (by omega) hk
  · exact blk_of blkX19 (by omega) (by omega) hk
  · exact blk_of blkX20 (by omega) (by omega) hk
  · exact blk_of blkX21 (by omega) (by omega) hk
  · exact blk_of blkX22 (by omega) (by omega) hk
  · exact blk_of blkX23 (by omega) (by omega) hk
  · exact blk_of blkX24 (by omega) (by omega) hk
  · exact blk_of blkX25 (by omega) (by omega) hk
  · exact blk_of blkX26 (by omega) (by omega) hk
  · exact blk_of blkX27 (by omega) (by omega) hk
  · exact blk_of blkX28 (by omega) (by omega) hk
  · exact blk_of blkX29 (by omega) (by omega) hk
  · exact blk_of blkX30 (by omega) (by omega) hk
  · exact blk_of blkX31 (by omega) (by omega) hk
  · exact blk_of blkX32 (by omega) (by omega) hk
  · exact blk_of blkX33 (by omega) (by omega) hk
  · exact blk_of blkX34 (by omega) (by omega) hk
  · exact blk_of blkX35 (by omega) (by omega) hk
  · exact blk_of blkX36 (by omega) (by omega) hk
  · exact blk_of blkX37 (by omega) (by omega) hk
  · exact blk_of blkX38 (by omega) (by omega) hk
  · exact blk_of blkX39 (by omega) (by omega) hk
  · exact blk_of blkX40 (by omega) (by omega) hk
  · exact blk_of blkX41 (by omega) (by omega) hk
  · exact blk_of blkX42 (by omega) (by omega) hk
  · exact blk_of blkX43 (by omega) (by omega) hk
  · exact blk_of blkX44 (by omega) (by omega) hk
  · exact blk_of blkX45 (by omega) (by omega) hk
  · exact blk_of blkX46 (by omega) (by omega) hk
  · exact blk_of blkX47 (by omega) (by omega) hk
  · exact blk_of blkX48 (by omega) (by omega) hk
  · exact blk_of blkX49 (by omega) (by omega) hk
  · exact blk_of blkX50 (by omega) (by omega) hk
  · exact blk_of blkX51 (by omega) (by omega) hk
  · exact blk_of blkX52 (by omega) (by omega) hk
  · exact blk_of blkX53 (by omega) (by omega) hk
  · exact blk_of blkX54 (by omega) (by omega) hk
  · exact blk_of blkX55 (by omega) (by omega) hk
  · exact blk_of blkX56 (by omega) (by omega) hk
  · exact blk_of blkX57 (by omega) (by omega) hk
  · exact blk_of blkX58 (by omega) (by omega) hk
  · exact blk_of blkX59 (by omega) (by omega) hk
  · exact blk_of blkX60 (by omega) (by omega) hk
  · exact blk_of blkX61 (by omega) (by omega) hk
  · exact blk_of blkX62 (by omega) (by omega) hk
  · exact blk_of blkX63 (by omega) (by omega) hk
  · exact blk_of blkX64 (by omega) (by omega) hk
  · exact blk_of blkX65 (by omega) (by omega) hk
  · exact blk_of blkX66 (by omega) (by omega) hk
  · exact blk_of blkX67 (by omega) (by omega) hk
  · exact blk_of blkX68 (by omega) (by omega) hk
  · exact blk_of blkX69 (by omega) (by omega) hk
  · exact blk_of blkX70 (by omega) (by omega) hk
  · exact blk_of blkX71 (by omega) (by omega) hk
  · exact blk_of blkX72 (by omega) (by omega) hk
  · exact blk_of blkX73 (by omega) (by omega) hk
  · exact blk_of blkX74 (by omega) (by omega) hk
  · exact blk_of blkX75 (by omega) (by omega) hk
  · exact blk_of blkX76 (by omega) (by omega) hk
  · exact blk_of blkX77 (by omega) (by omega) hk
  · exact blk_of blkX78 (by omega) (by omega) hk
  · exact blk_of blkX79 (by omega) (by omega) hk
  · exact blk_of blkX80 (by omega) (by omega) hk
  · exact blk_of blkX81 (by omega) (by omega) hk
  · exact blk_of blkX82 (by omega) (by omega) hk
  · exact blk_of blkX83 (by omega) (by omega) hk
  · exact blk_of blkX84 (by omega) (by omega) hk
  · exact blk_of blkX85 (by omega) (by omega) hk
  · exact blk_of blkX86 (by omega) (by omega) hk
  · exact blk_of blkX87 (by omega) (by omega) hk
  · exact blk_of blkX88 (by omega) (by omega) hk
  · exact blk_of blkX89 (by omega) (by omega) hk
  · exact blk_of blkX90 (by omega) (by omega) hk
  · exact blk_of blkX91 (by omega) (by omega) hk
  · exact blk_of blkX92 (by omega) (by omega) hk
  · exact blk_of blkX93 (by omega) (by omega) hk
  · exact blk_of blkX94 (by omega) (by omega) hk
  · exact blk_of blkX95 (by omega) (by omega) hk
  · exact blk_of blkX96 (by omega) (by omega) hk
  · exact blk_of blkX97 (by omega) (by omega) hk
  · exact blk_of blkX98 (by omega) (by omega) hk
  · exact blk_of blkX99 (by omega) (by omega) hk
  · exact blk_of blkX100 (by omega) (by omega) hk
  · exact blk_of blkX101 (by omega) (by omega) hk
  · exact blk_of blkX102 (by omega) (by omega) hk
  · exact blk_of blkX103 (by omega) (by omega) hk
  · exact blk_of blkX104 (by omega) (by omega) hk
  · exact blk_of blkX105 (by omega) (by omega) hk
  · exact blk_of blkX106 (by omega) (by omega) hk
  · exact blk_of blkX107 (by omega) (by omega) hk
  · exact blk_of blkX108 (by omega) (by omega) hk
  · exact blk_of blkX109 (by omega) (by omega) hk
  · exact blk_of blkX110 (by omega) (by omega) hk
  · exact blk_of blkX111 (by omega) (by omega) hk
  · exact blk_of blkX112 (by omega) (by omega) hk
  · exact blk_of blkX113 (by omega) (by omega) hk
  · exact blk_of blkX114 (by omega) (by omega) hk
  · exact blk_of blkX115 (by omega) (by omega) hk
  · exact blk_of blkX116 (by omega) (by omega) hk
  · exact blk_of blkX117 (by omega) (by omega) hk
  · exact blk_of blkX118 (by omega) (by omega) hk
  · exact blk_of blkX119 (by omega) (by omega) hk
  · exact blk_of blkX120 (by omega) (by omega) hk
  · exact blk_of blkX121 (by omega) (by omega) hk
  · exact blk_of blkX122 (by omega) (by omega) hk
  · exact blk_of blkX123 (by omega) (by omega) hk
  · exact blk_of blkX124 (by omega) (by omega) hk
  · exact blk_of blkX125 (by omega) (by omega) hk
  · exact blk_of blkX126 (by omega) (by omega) hk
  · exact blk_of blkX127 (by omega) (by omega) hk
  · exact blk_of blkX128 (by omega) (by omega) hk
  · exact blk_of blkX129 (by omega) (by omega) hk
  · exact blk_of blkX130 (by omega) (by omega) hk
  · exact blk_of blkX131 (by omega) (by omega) hk
  · exact blk_of blkX132 (by omega) (by omega) hk
  · exact blk_of blkX133 (by omega) (by omega) hk
  · exact blk_of blkX134 (by omega) (by omega) hk
  · exact blk_of blkX135 (by omega) (by omega) hk
  · exact blk_of blkX136 (by omega) (by omega) hk
  · exact blk_of blkX137 (by omega) (by omega) hk
  · exact blk_of blkX138 (by omega) (by omega) hk
  · exact blk_of blkX139 (by omega) (by omega) hk
  · exact blk_of blkX140 (by omega) (by omega) hk
  · exact blk_of blkX141 (by omega) (by omega) hk
  · exact blk_of blkX142 (by omega) (by omega) hk
  · exact blk_of blkX143 (by omega) (by omega) hk
  · exact blk_of blkX144 (by omega) (by omega) hk
  · exact blk_of blkX145 (by omega) (by omega) hk
  · exact blk_of blkX146 (by omega) (by omega) hk
  · exact blk_of blkX147 (by omega) (by omega) hk
  · exact blk_of blkX148 (by omega) (by omega) hk
  · exact blk_of blkX149 (by omega) (by omega) hk
  · exact blk_of blkX150 (by omega) (by omega) hk
  · exact blk_of blkX151 (by omega) (by omega) hk
  · exact blk_of blkX152 (by omega) (by omega) hk
  · exact blk_of blkX153 (by omega) (by omega) hk
  · exact blk_of blkX154 (by omega) (by omega) hk
  · exact blk_of blkX155 (by omega) (by omega) hk
  · exact blk_of blkX156 (by omega) (by omega) hk
  · exact blk_of blkX157 (by omega) (by omega) hk
  · exact blk_of blkX158 (by omega) (by omega) hk
  · exact blk_of blkX159 (by omega) (by omega) hk
  · exact blk_of blkX160 (by omega) (by omega) hk
  · exact blk_of blkX161 (by omega) (by omega) hk
  · exact blk_of blkX162 (by omega) (by omega) hk
  · exact blk_of blkX163 (by omega) (by omega) hk
  · exact blk_of blkX164 (by omega) (by omega) hk
  · exact blk_of blkX165 (by omega) (by omega) hk
  · exact blk_of blkX166 (by omega) (by omega) hk
  · exact blk_of blkX167 (by omega) (by omega) hk
  · exact blk_of blkX168 (by omega) (by omega) hk
  · exact blk_of blkX169 (by omega) (by omega) hk
  · exact blk_of blkX170 (by omega) (by omega) hk
  · exact blk_of blkX171 (by omega) (by omega) hk
  · exact blk_of blkX172 (by omega) (by omega) hk
  · exact blk_of blkX173 (by omega) (by omega) hk
  · exact blk_of blkX174 (by omega) (by omega) hk
  · exact blk_of blkX175 (by omega) (by omega) hk
  · exact blk_of blkX176 (by omega) (by omega) hk
  · exact blk_of blkX177 (by omega) (by omega) hk
  · exact blk_of blkX178 (by omega) (by omega) hk
  · exact blk_of blkX179 (by omega) (by omega) hk
  · exact blk_of blkX180 (by omega) (by omega) hk
  · exact blk_of blkX181 (by omega) (by omega) hk
  · exact blk_of blkX182 (by omega) (by omega) hk
  · exact blk_of blkX183 (by omega) (by omega) hk
  · exact blk_of blkX184 (by omega) (by omega) hk
  · exact blk_of blkX185 (by omega) (by omega) hk
  · exact blk_of blkX186 (by omega) (by omega) hk
  · exact blk_of blkX187 (by omega) (by omega) hk
  · exact blk_of blkX188 (by omega) (by omega) hk
  · exact blk_of blkX189 (by omega) (by omega) hk
  · exact blk_of blkX190 (by omega) (by omega) hk
  · exact blk_of blkX191 (by omega) (by omega) hk
  · exact blk_of blkX192 (by omega) (by omega) hk
  · exact blk_of blkX193 (by omega) (by omega) hk
  · exact blk_of blkX194 (by omega) (by omega) hk
  · exact blk_of blkX195 (by omega) (by omega) hk
  · exact blk_of blkX196 (by omega) (by omega) hk
  · exact blk_of blkX197 (by omega) (by omega) hk
  · exact blk_of blkX198 (by omega) (by omega) hk
  · exact blk_of blkX199 (by omega) (by omega) hk
  · exact blk_of blkX200 (by omega) (by omega) hk
  · exact blk_of blkX201 (by omega) (by omega) hk
  · exact blk_of blkX202 (by omega) (by omega) hk
  · exact blk_of blkX203 (by omega) (by omega) hk
  · exact blk_of blkX204 (by omega) (by omega) hk
  · exact blk_of blkX205 (by omega) (by omega) hk
  · exact blk_of blkX206 (by omega) (by omega) hk
  · exact blk_of blkX207 (by omega) (by omega) hk
  · exact blk_of blkX208 (by omega) (by omega) hk
  · exact blk_of blkX209 (by omega) (by omega) hk
  · exact blk_of blkX210 (by omega) (by omega) hk
  · exact blk_of blkX211 (by omega) (by omega) hk
  · exact blk_of blkX212 (by omega) (by omega) hk
  · exact blk_of blkX213 (by omega) (by omega) hk
  · exact blk_of blkX214 (by omega) (by omega) hk
  · exact blk_of blkX215 (by omega) (by omega) hk
  · exact blk_of blkX216 (by omega) (by omega) hk
  · exact blk_of blkX217 (by omega) (by omega) hk
  · exact blk_of blkX218 (by omega) (by omega) hk
  · exact blk_of blkX219 (by omega) (by omega) hk
  · exact blk_of blkX220 (by omega) (by omega) hk
  · exact blk_of blkX221 (by omega) (by omega) hk
  · exact blk_of blkX222 (by omega) (by omega) hk
  · exact blk_of blkX223 (by omega) (by omega) hk
  · exact blk_of blkX224 (by omega) (by omega) hk
  · exact blk_of blkX225 (by omega) (by omega) hk
  · exact blk_of blkX226 (by omega) (by omega) hk
  · exact blk_of blkX227 (by omega) (by omega) hk
  · exact blk_of blkX228 (by omega) (by omega) hk
  · exact blk_of blkX229 (by omega) (by omega) hk
  · exact blk_of blkX230 (by omega) (by omega) hk
  · exact blk_of blkX231 (by omega) (by omega) hk
  · exact blk_of blkX232 (by omega) (by omega) hk
  · exact blk_of blkX233 (by omega) (by omega) hk
  · exact blk_of blkX234 (by omega) (by omega) hk
  · exact blk_of blkX235 (by omega) (by omega) hk
  · exact blk_of blkX236 (by omega) (by omega) hk
  · exact blk_of blkX237 (by omega) (by omega) hk
  · exact blk_of blkX238 (by omega) (by omega) hk
  · exact blk_of blkX239 (by omega) (by omega) hk
  · exact blk_of blkX240 (by omega) (by omega) hk
  · exact blk_of blkX241 (by omega) (by omega) hk
  · exact blk_of blkX242 (by omega) (by omega) hk
  · exact blk_of blkX243 (by omega) (by omega) hk
  · exact blk_of blkX244 (by omega) (by omega) hk

theorem capSpec : CapSpec := by
  intro c hc k hk
  have hNS : NS = 10290 := rfl
  have hj : k / 128 < 81 := by omega
  generalize hjv : k / 128 = j at hj
  interval_cases j
  · exact cap_of capJ0 (by omega) (by omega) hk hc
  · exact cap_of capJ1 (by omega) (by omega) hk hc
  · exact cap_of capJ2 (by omega) (by omega) hk hc
  · exact cap_of capJ3 (by omega) (by omega) hk hc
  · exact cap_of capJ4 (by omega) (by omega) hk hc
  · exact cap_of capJ5 (by omega) (by omega) hk hc
  · exact cap_of capJ6 (by omega) (by omega) hk hc
  · exact cap_of capJ7 (by omega) (by omega) hk hc
  · exact cap_of capJ8 (by omega) (by omega) hk hc
  · exact cap_of capJ9 (by omega) (by omega) hk hc
  · exact cap_of capJ10 (by omega) (by omega) hk hc
  · exact cap_of capJ11 (by omega) (by omega) hk hc
  · exact cap_of capJ12 (by omega) (by omega) hk hc
  · exact cap_of capJ13 (by omega) (by omega) hk hc
  · exact cap_of capJ14 (by omega) (by omega) hk hc
  · exact cap_of capJ15 (by omega) (by omega) hk hc
  · exact cap_of capJ16 (by omega) (by omega) hk hc
  · exact cap_of capJ17 (by omega) (by omega) hk hc
  · exact cap_of capJ18 (by omega) (by omega) hk hc
  · exact cap_of capJ19 (by omega) (by omega) hk hc
  · exact cap_of capJ20 (by omega) (by omega) hk hc
  · exact cap_of capJ21 (by omega) (by omega) hk hc
  · exact cap_of capJ22 (by omega) (by omega) hk hc
  · exact cap_of capJ23 (by omega) (by omega) hk hc
  · exact cap_of capJ24 (by omega) (by omega) hk hc
  · exact cap_of capJ25 (by omega) (by omega) hk hc
  · exact cap_of capJ26 (by omega) (by omega) hk hc
  · exact cap_of capJ27 (by omega) (by omega) hk hc
  · exact cap_of capJ28 (by omega) (by omega) hk hc
  · exact cap_of capJ29 (by omega) (by omega) hk hc
  · exact cap_of capJ30 (by omega) (by omega) hk hc
  · exact cap_of capJ31 (by omega) (by omega) hk hc
  · exact cap_of capJ32 (by omega) (by omega) hk hc
  · exact cap_of capJ33 (by omega) (by omega) hk hc
  · exact cap_of capJ34 (by omega) (by omega) hk hc
  · exact cap_of capJ35 (by omega) (by omega) hk hc
  · exact cap_of capJ36 (by omega) (by omega) hk hc
  · exact cap_of capJ37 (by omega) (by omega) hk hc
  · exact cap_of capJ38 (by omega) (by omega) hk hc
  · exact cap_of capJ39 (by omega) (by omega) hk hc
  · exact cap_of capJ40 (by omega) (by omega) hk hc
  · exact cap_of capJ41 (by omega) (by omega) hk hc
  · exact cap_of capJ42 (by omega) (by omega) hk hc
  · exact cap_of capJ43 (by omega) (by omega) hk hc
  · exact cap_of capJ44 (by omega) (by omega) hk hc
  · exact cap_of capJ45 (by omega) (by omega) hk hc
  · exact cap_of capJ46 (by omega) (by omega) hk hc
  · exact cap_of capJ47 (by omega) (by omega) hk hc
  · exact cap_of capJ48 (by omega) (by omega) hk hc
  · exact cap_of capJ49 (by omega) (by omega) hk hc
  · exact cap_of capJ50 (by omega) (by omega) hk hc
  · exact cap_of capJ51 (by omega) (by omega) hk hc
  · exact cap_of capJ52 (by omega) (by omega) hk hc
  · exact cap_of capJ53 (by omega) (by omega) hk hc
  · exact cap_of capJ54 (by omega) (by omega) hk hc
  · exact cap_of capJ55 (by omega) (by omega) hk hc
  · exact cap_of capJ56 (by omega) (by omega) hk hc
  · exact cap_of capJ57 (by omega) (by omega) hk hc
  · exact cap_of capJ58 (by omega) (by omega) hk hc
  · exact cap_of capJ59 (by omega) (by omega) hk hc
  · exact cap_of capJ60 (by omega) (by omega) hk hc
  · exact cap_of capJ61 (by omega) (by omega) hk hc
  · exact cap_of capJ62 (by omega) (by omega) hk hc
  · exact cap_of capJ63 (by omega) (by omega) hk hc
  · exact cap_of capJ64 (by omega) (by omega) hk hc
  · exact cap_of capJ65 (by omega) (by omega) hk hc
  · exact cap_of capJ66 (by omega) (by omega) hk hc
  · exact cap_of capJ67 (by omega) (by omega) hk hc
  · exact cap_of capJ68 (by omega) (by omega) hk hc
  · exact cap_of capJ69 (by omega) (by omega) hk hc
  · exact cap_of capJ70 (by omega) (by omega) hk hc
  · exact cap_of capJ71 (by omega) (by omega) hk hc
  · exact cap_of capJ72 (by omega) (by omega) hk hc
  · exact cap_of capJ73 (by omega) (by omega) hk hc
  · exact cap_of capJ74 (by omega) (by omega) hk hc
  · exact cap_of capJ75 (by omega) (by omega) hk hc
  · exact cap_of capJ76 (by omega) (by omega) hk hc
  · exact cap_of capJ77 (by omega) (by omega) hk hc
  · exact cap_of capJ78 (by omega) (by omega) hk hc
  · exact cap_of capJ79 (by omega) (by omega) hk hc
  · exact cap_of capJ80 (by omega) (by omega) hk hc

theorem clsSpec : ClassSpec ∧ CBSpec := cls_of clsP

theorem dom_all {T : Nat} (hT : T < 49) {gi ri : Nat} (hg : gi < 12) (hr : ri < 42) :
    ∃ k, k < NS ∧ ∀ x, x < 245 → (MT k).testBit x = true →
      ok T (fvecs.getD gi []) (units49L.getD ri 0) (inst x).1 (inst x).2 := by
  interval_cases T
  · exact dom_of domP0 hg hr
  · exact dom_of domP1 hg hr
  · exact dom_of domP2 hg hr
  · exact dom_of domP3 hg hr
  · exact dom_of domP4 hg hr
  · exact dom_of domP5 hg hr
  · exact dom_of domP6 hg hr
  · exact dom_of domP7 hg hr
  · exact dom_of domP8 hg hr
  · exact dom_of domP9 hg hr
  · exact dom_of domP10 hg hr
  · exact dom_of domP11 hg hr
  · exact dom_of domP12 hg hr
  · exact dom_of domP13 hg hr
  · exact dom_of domP14 hg hr
  · exact dom_of domP15 hg hr
  · exact dom_of domP16 hg hr
  · exact dom_of domP17 hg hr
  · exact dom_of domP18 hg hr
  · exact dom_of domP19 hg hr
  · exact dom_of domP20 hg hr
  · exact dom_of domP21 hg hr
  · exact dom_of domP22 hg hr
  · exact dom_of domP23 hg hr
  · exact dom_of domP24 hg hr
  · exact dom_of domP25 hg hr
  · exact dom_of domP26 hg hr
  · exact dom_of domP27 hg hr
  · exact dom_of domP28 hg hr
  · exact dom_of domP29 hg hr
  · exact dom_of domP30 hg hr
  · exact dom_of domP31 hg hr
  · exact dom_of domP32 hg hr
  · exact dom_of domP33 hg hr
  · exact dom_of domP34 hg hr
  · exact dom_of domP35 hg hr
  · exact dom_of domP36 hg hr
  · exact dom_of domP37 hg hr
  · exact dom_of domP38 hg hr
  · exact dom_of domP39 hg hr
  · exact dom_of domP40 hg hr
  · exact dom_of domP41 hg hr
  · exact dom_of domP42 hg hr
  · exact dom_of domP43 hg hr
  · exact dom_of domP44 hg hr
  · exact dom_of domP45 hg hr
  · exact dom_of domP46 hg hr
  · exact dom_of domP47 hg hr
  · exact dom_of domP48 hg hr

theorem wit_of {T : Nat} {g : List Nat} {ρ : Nat} (h : UnitSt T g ρ) :
    ∃ k, k < NS ∧ ∀ x, x < 245 → (MT k).testBit x = true → ok T g ρ (inst x).1 (inst x).2 := by
  obtain ⟨hT, hg, hρ, hρ7⟩ := h
  obtain ⟨gi, hgi, rfl⟩ := fvec_index hg
  obtain ⟨ri, hri, rfl⟩ := unit_index hρ hρ7
  exact dom_all hT hgi hri

theorem absP2 : AbsP2 := by
  intro g1 ρ1 T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4 h1 h2 h3 h4
  obtain ⟨-, hg1, hρ1, hρ17⟩ := h1
  obtain ⟨gi, hgi, rfl⟩ := fvec_index hg1
  obtain ⟨ri, hri, rfl⟩ := unit_index hρ1 hρ17
  obtain ⟨b, hb, w1⟩ := bdom_of bdomP hgi hri
  obtain ⟨k2, hk2, w2⟩ := wit_of h2
  obtain ⟨k3, hk3, w3⟩ := wit_of h3
  obtain ⟨k4, hk4, w4⟩ := wit_of h4
  obtain ⟨x, hx, hAx, hks⟩ := p2_all blkSpec capSpec clsSpec.1 clsSpec.2 hb [k2, k3, k4] rfl
    (by intro k hk; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> assumption)
  obtain ⟨hc1, hc5⟩ := c_of cP hx
  exact ⟨(inst x).1, (inst x).2, hc1, hc5, w1 x hx hAx, w2 x hx (hks k2 (by simp)), w3 x hx (hks k3 (by simp)),
    w4 x hx (hks k4 (by simp))⟩

end LRC.O7P2
