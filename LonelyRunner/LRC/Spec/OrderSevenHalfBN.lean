import LonelyRunner.LRC.Spec.OrderSevenHalfBP0N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP1N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP2N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP3N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP4N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP5N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP6N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP7N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP8N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP9N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP10N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP11N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP12N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP13N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP14N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP15N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP16N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP17N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP18N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP19N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP20N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP21N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP22N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP23N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP24N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP25N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP26N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP27N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP28N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP29N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP30N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP31N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP32N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP33N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP34N
import LonelyRunner.LRC.Spec.OrderSevenHalfBP35N

/-!
# Order seven, half-unit certificate B assembled

`chunkBH_all`: `chunkBH i2 i2 147 = true` for every `i2 < 147`, joined from the 147 kernel-checked pieces in
`OrderSevenHalfBP*N` by `chunkBH_split`.  Generator: `experiments/n7_native/cascade/o7_half_assemble_v1.py`.
-/

namespace LRC.O7L3

theorem chunkBH_split {i2 lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    chunkBH i2 lo hi = (chunkBH i2 lo mid && chunkBH i2 mid hi) := by
  unfold chunkBH
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, allR_append, show lo + (mid - lo) = mid by omega]

theorem chunkBH_full_0 : chunkBH 0 0 147 = true := chunkBH_0_0
theorem chunkBH_full_1 : chunkBH 1 1 147 = true := chunkBH_1_1
theorem chunkBH_full_2 : chunkBH 2 2 147 = true := chunkBH_2_2
theorem chunkBH_full_3 : chunkBH 3 3 147 = true := chunkBH_3_3
theorem chunkBH_full_4 : chunkBH 4 4 147 = true := chunkBH_4_4
theorem chunkBH_full_5 : chunkBH 5 5 147 = true := chunkBH_5_5
theorem chunkBH_full_6 : chunkBH 6 6 147 = true := chunkBH_6_6
theorem chunkBH_full_7 : chunkBH 7 7 147 = true := chunkBH_7_7
theorem chunkBH_full_8 : chunkBH 8 8 147 = true := chunkBH_8_8
theorem chunkBH_full_9 : chunkBH 9 9 147 = true := chunkBH_9_9
theorem chunkBH_full_10 : chunkBH 10 10 147 = true := chunkBH_10_10
theorem chunkBH_full_11 : chunkBH 11 11 147 = true := chunkBH_11_11
theorem chunkBH_full_12 : chunkBH 12 12 147 = true := chunkBH_12_12
theorem chunkBH_full_13 : chunkBH 13 13 147 = true := chunkBH_13_13
theorem chunkBH_full_14 : chunkBH 14 14 147 = true := chunkBH_14_14
theorem chunkBH_full_15 : chunkBH 15 15 147 = true := chunkBH_15_15
theorem chunkBH_full_16 : chunkBH 16 16 147 = true := chunkBH_16_16
theorem chunkBH_full_17 : chunkBH 17 17 147 = true := chunkBH_17_17
theorem chunkBH_full_18 : chunkBH 18 18 147 = true := chunkBH_18_18
theorem chunkBH_full_19 : chunkBH 19 19 147 = true := chunkBH_19_19
theorem chunkBH_full_20 : chunkBH 20 20 147 = true := chunkBH_20_20
theorem chunkBH_full_21 : chunkBH 21 21 147 = true := chunkBH_21_21
theorem chunkBH_full_22 : chunkBH 22 22 147 = true := chunkBH_22_22
theorem chunkBH_full_23 : chunkBH 23 23 147 = true := chunkBH_23_23
theorem chunkBH_full_24 : chunkBH 24 24 147 = true := chunkBH_24_24
theorem chunkBH_full_25 : chunkBH 25 25 147 = true := chunkBH_25_25
theorem chunkBH_full_26 : chunkBH 26 26 147 = true := chunkBH_26_26
theorem chunkBH_full_27 : chunkBH 27 27 147 = true := chunkBH_27_27
theorem chunkBH_full_28 : chunkBH 28 28 147 = true := chunkBH_28_28
theorem chunkBH_full_29 : chunkBH 29 29 147 = true := chunkBH_29_29
theorem chunkBH_full_30 : chunkBH 30 30 147 = true := chunkBH_30_30
theorem chunkBH_full_31 : chunkBH 31 31 147 = true := chunkBH_31_31
theorem chunkBH_full_32 : chunkBH 32 32 147 = true := chunkBH_32_32
theorem chunkBH_full_33 : chunkBH 33 33 147 = true := chunkBH_33_33
theorem chunkBH_full_34 : chunkBH 34 34 147 = true := chunkBH_34_34
theorem chunkBH_full_35 : chunkBH 35 35 147 = true := chunkBH_35_35
theorem chunkBH_full_36 : chunkBH 36 36 147 = true := chunkBH_36_36
theorem chunkBH_full_37 : chunkBH 37 37 147 = true := chunkBH_37_37
theorem chunkBH_full_38 : chunkBH 38 38 147 = true := chunkBH_38_38
theorem chunkBH_full_39 : chunkBH 39 39 147 = true := chunkBH_39_39
theorem chunkBH_full_40 : chunkBH 40 40 147 = true := chunkBH_40_40
theorem chunkBH_full_41 : chunkBH 41 41 147 = true := chunkBH_41_41
theorem chunkBH_full_42 : chunkBH 42 42 147 = true := chunkBH_42_42
theorem chunkBH_full_43 : chunkBH 43 43 147 = true := chunkBH_43_43
theorem chunkBH_full_44 : chunkBH 44 44 147 = true := chunkBH_44_44
theorem chunkBH_full_45 : chunkBH 45 45 147 = true := chunkBH_45_45
theorem chunkBH_full_46 : chunkBH 46 46 147 = true := chunkBH_46_46
theorem chunkBH_full_47 : chunkBH 47 47 147 = true := chunkBH_47_47
theorem chunkBH_full_48 : chunkBH 48 48 147 = true := chunkBH_48_48
theorem chunkBH_full_49 : chunkBH 49 49 147 = true := chunkBH_49_49
theorem chunkBH_full_50 : chunkBH 50 50 147 = true := chunkBH_50_50
theorem chunkBH_full_51 : chunkBH 51 51 147 = true := chunkBH_51_51
theorem chunkBH_full_52 : chunkBH 52 52 147 = true := chunkBH_52_52
theorem chunkBH_full_53 : chunkBH 53 53 147 = true := chunkBH_53_53
theorem chunkBH_full_54 : chunkBH 54 54 147 = true := chunkBH_54_54
theorem chunkBH_full_55 : chunkBH 55 55 147 = true := chunkBH_55_55
theorem chunkBH_full_56 : chunkBH 56 56 147 = true := chunkBH_56_56
theorem chunkBH_full_57 : chunkBH 57 57 147 = true := chunkBH_57_57
theorem chunkBH_full_58 : chunkBH 58 58 147 = true := chunkBH_58_58
theorem chunkBH_full_59 : chunkBH 59 59 147 = true := chunkBH_59_59
theorem chunkBH_full_60 : chunkBH 60 60 147 = true := chunkBH_60_60
theorem chunkBH_full_61 : chunkBH 61 61 147 = true := chunkBH_61_61
theorem chunkBH_full_62 : chunkBH 62 62 147 = true := chunkBH_62_62
theorem chunkBH_full_63 : chunkBH 63 63 147 = true := chunkBH_63_63
theorem chunkBH_full_64 : chunkBH 64 64 147 = true := chunkBH_64_64
theorem chunkBH_full_65 : chunkBH 65 65 147 = true := chunkBH_65_65
theorem chunkBH_full_66 : chunkBH 66 66 147 = true := chunkBH_66_66
theorem chunkBH_full_67 : chunkBH 67 67 147 = true := chunkBH_67_67
theorem chunkBH_full_68 : chunkBH 68 68 147 = true := chunkBH_68_68
theorem chunkBH_full_69 : chunkBH 69 69 147 = true := chunkBH_69_69
theorem chunkBH_full_70 : chunkBH 70 70 147 = true := chunkBH_70_70
theorem chunkBH_full_71 : chunkBH 71 71 147 = true := chunkBH_71_71
theorem chunkBH_full_72 : chunkBH 72 72 147 = true := chunkBH_72_72
theorem chunkBH_full_73 : chunkBH 73 73 147 = true := chunkBH_73_73
theorem chunkBH_full_74 : chunkBH 74 74 147 = true := chunkBH_74_74
theorem chunkBH_full_75 : chunkBH 75 75 147 = true := chunkBH_75_75
theorem chunkBH_full_76 : chunkBH 76 76 147 = true := chunkBH_76_76
theorem chunkBH_full_77 : chunkBH 77 77 147 = true := chunkBH_77_77
theorem chunkBH_full_78 : chunkBH 78 78 147 = true := chunkBH_78_78
theorem chunkBH_full_79 : chunkBH 79 79 147 = true := chunkBH_79_79
theorem chunkBH_full_80 : chunkBH 80 80 147 = true := chunkBH_80_80
theorem chunkBH_full_81 : chunkBH 81 81 147 = true := chunkBH_81_81
theorem chunkBH_full_82 : chunkBH 82 82 147 = true := chunkBH_82_82
theorem chunkBH_full_83 : chunkBH 83 83 147 = true := chunkBH_83_83
theorem chunkBH_full_84 : chunkBH 84 84 147 = true := chunkBH_84_84
theorem chunkBH_full_85 : chunkBH 85 85 147 = true := chunkBH_85_85
theorem chunkBH_full_86 : chunkBH 86 86 147 = true := chunkBH_86_86
theorem chunkBH_full_87 : chunkBH 87 87 147 = true := chunkBH_87_87
theorem chunkBH_full_88 : chunkBH 88 88 147 = true := chunkBH_88_88
theorem chunkBH_full_89 : chunkBH 89 89 147 = true := chunkBH_89_89
theorem chunkBH_full_90 : chunkBH 90 90 147 = true := chunkBH_90_90
theorem chunkBH_full_91 : chunkBH 91 91 147 = true := chunkBH_91_91
theorem chunkBH_full_92 : chunkBH 92 92 147 = true := chunkBH_92_92
theorem chunkBH_full_93 : chunkBH 93 93 147 = true := chunkBH_93_93
theorem chunkBH_full_94 : chunkBH 94 94 147 = true := chunkBH_94_94
theorem chunkBH_full_95 : chunkBH 95 95 147 = true := chunkBH_95_95
theorem chunkBH_full_96 : chunkBH 96 96 147 = true := chunkBH_96_96
theorem chunkBH_full_97 : chunkBH 97 97 147 = true := chunkBH_97_97
theorem chunkBH_full_98 : chunkBH 98 98 147 = true := chunkBH_98_98
theorem chunkBH_full_99 : chunkBH 99 99 147 = true := chunkBH_99_99
theorem chunkBH_full_100 : chunkBH 100 100 147 = true := chunkBH_100_100
theorem chunkBH_full_101 : chunkBH 101 101 147 = true := chunkBH_101_101
theorem chunkBH_full_102 : chunkBH 102 102 147 = true := chunkBH_102_102
theorem chunkBH_full_103 : chunkBH 103 103 147 = true := chunkBH_103_103
theorem chunkBH_full_104 : chunkBH 104 104 147 = true := chunkBH_104_104
theorem chunkBH_full_105 : chunkBH 105 105 147 = true := chunkBH_105_105
theorem chunkBH_full_106 : chunkBH 106 106 147 = true := chunkBH_106_106
theorem chunkBH_full_107 : chunkBH 107 107 147 = true := chunkBH_107_107
theorem chunkBH_full_108 : chunkBH 108 108 147 = true := chunkBH_108_108
theorem chunkBH_full_109 : chunkBH 109 109 147 = true := chunkBH_109_109
theorem chunkBH_full_110 : chunkBH 110 110 147 = true := chunkBH_110_110
theorem chunkBH_full_111 : chunkBH 111 111 147 = true := chunkBH_111_111
theorem chunkBH_full_112 : chunkBH 112 112 147 = true := chunkBH_112_112
theorem chunkBH_full_113 : chunkBH 113 113 147 = true := chunkBH_113_113
theorem chunkBH_full_114 : chunkBH 114 114 147 = true := chunkBH_114_114
theorem chunkBH_full_115 : chunkBH 115 115 147 = true := chunkBH_115_115
theorem chunkBH_full_116 : chunkBH 116 116 147 = true := chunkBH_116_116
theorem chunkBH_full_117 : chunkBH 117 117 147 = true := chunkBH_117_117
theorem chunkBH_full_118 : chunkBH 118 118 147 = true := chunkBH_118_118
theorem chunkBH_full_119 : chunkBH 119 119 147 = true := chunkBH_119_119
theorem chunkBH_full_120 : chunkBH 120 120 147 = true := chunkBH_120_120
theorem chunkBH_full_121 : chunkBH 121 121 147 = true := chunkBH_121_121
theorem chunkBH_full_122 : chunkBH 122 122 147 = true := chunkBH_122_122
theorem chunkBH_full_123 : chunkBH 123 123 147 = true := chunkBH_123_123
theorem chunkBH_full_124 : chunkBH 124 124 147 = true := chunkBH_124_124
theorem chunkBH_full_125 : chunkBH 125 125 147 = true := chunkBH_125_125
theorem chunkBH_full_126 : chunkBH 126 126 147 = true := chunkBH_126_126
theorem chunkBH_full_127 : chunkBH 127 127 147 = true := chunkBH_127_127
theorem chunkBH_full_128 : chunkBH 128 128 147 = true := chunkBH_128_128
theorem chunkBH_full_129 : chunkBH 129 129 147 = true := chunkBH_129_129
theorem chunkBH_full_130 : chunkBH 130 130 147 = true := chunkBH_130_130
theorem chunkBH_full_131 : chunkBH 131 131 147 = true := chunkBH_131_131
theorem chunkBH_full_132 : chunkBH 132 132 147 = true := chunkBH_132_132
theorem chunkBH_full_133 : chunkBH 133 133 147 = true := chunkBH_133_133
theorem chunkBH_full_134 : chunkBH 134 134 147 = true := chunkBH_134_134
theorem chunkBH_full_135 : chunkBH 135 135 147 = true := chunkBH_135_135
theorem chunkBH_full_136 : chunkBH 136 136 147 = true := chunkBH_136_136
theorem chunkBH_full_137 : chunkBH 137 137 147 = true := chunkBH_137_137
theorem chunkBH_full_138 : chunkBH 138 138 147 = true := chunkBH_138_138
theorem chunkBH_full_139 : chunkBH 139 139 147 = true := chunkBH_139_139
theorem chunkBH_full_140 : chunkBH 140 140 147 = true := chunkBH_140_140
theorem chunkBH_full_141 : chunkBH 141 141 147 = true := chunkBH_141_141
theorem chunkBH_full_142 : chunkBH 142 142 147 = true := chunkBH_142_142
theorem chunkBH_full_143 : chunkBH 143 143 147 = true := chunkBH_143_143
theorem chunkBH_full_144 : chunkBH 144 144 147 = true := chunkBH_144_144
theorem chunkBH_full_145 : chunkBH 145 145 147 = true := chunkBH_145_145
theorem chunkBH_full_146 : chunkBH 146 146 147 = true := chunkBH_146_146

theorem chunkBH_all : ∀ i2, i2 < 147 → chunkBH i2 i2 147 = true := by
  intro i2 hi2
  interval_cases i2
  · exact chunkBH_full_0
  · exact chunkBH_full_1
  · exact chunkBH_full_2
  · exact chunkBH_full_3
  · exact chunkBH_full_4
  · exact chunkBH_full_5
  · exact chunkBH_full_6
  · exact chunkBH_full_7
  · exact chunkBH_full_8
  · exact chunkBH_full_9
  · exact chunkBH_full_10
  · exact chunkBH_full_11
  · exact chunkBH_full_12
  · exact chunkBH_full_13
  · exact chunkBH_full_14
  · exact chunkBH_full_15
  · exact chunkBH_full_16
  · exact chunkBH_full_17
  · exact chunkBH_full_18
  · exact chunkBH_full_19
  · exact chunkBH_full_20
  · exact chunkBH_full_21
  · exact chunkBH_full_22
  · exact chunkBH_full_23
  · exact chunkBH_full_24
  · exact chunkBH_full_25
  · exact chunkBH_full_26
  · exact chunkBH_full_27
  · exact chunkBH_full_28
  · exact chunkBH_full_29
  · exact chunkBH_full_30
  · exact chunkBH_full_31
  · exact chunkBH_full_32
  · exact chunkBH_full_33
  · exact chunkBH_full_34
  · exact chunkBH_full_35
  · exact chunkBH_full_36
  · exact chunkBH_full_37
  · exact chunkBH_full_38
  · exact chunkBH_full_39
  · exact chunkBH_full_40
  · exact chunkBH_full_41
  · exact chunkBH_full_42
  · exact chunkBH_full_43
  · exact chunkBH_full_44
  · exact chunkBH_full_45
  · exact chunkBH_full_46
  · exact chunkBH_full_47
  · exact chunkBH_full_48
  · exact chunkBH_full_49
  · exact chunkBH_full_50
  · exact chunkBH_full_51
  · exact chunkBH_full_52
  · exact chunkBH_full_53
  · exact chunkBH_full_54
  · exact chunkBH_full_55
  · exact chunkBH_full_56
  · exact chunkBH_full_57
  · exact chunkBH_full_58
  · exact chunkBH_full_59
  · exact chunkBH_full_60
  · exact chunkBH_full_61
  · exact chunkBH_full_62
  · exact chunkBH_full_63
  · exact chunkBH_full_64
  · exact chunkBH_full_65
  · exact chunkBH_full_66
  · exact chunkBH_full_67
  · exact chunkBH_full_68
  · exact chunkBH_full_69
  · exact chunkBH_full_70
  · exact chunkBH_full_71
  · exact chunkBH_full_72
  · exact chunkBH_full_73
  · exact chunkBH_full_74
  · exact chunkBH_full_75
  · exact chunkBH_full_76
  · exact chunkBH_full_77
  · exact chunkBH_full_78
  · exact chunkBH_full_79
  · exact chunkBH_full_80
  · exact chunkBH_full_81
  · exact chunkBH_full_82
  · exact chunkBH_full_83
  · exact chunkBH_full_84
  · exact chunkBH_full_85
  · exact chunkBH_full_86
  · exact chunkBH_full_87
  · exact chunkBH_full_88
  · exact chunkBH_full_89
  · exact chunkBH_full_90
  · exact chunkBH_full_91
  · exact chunkBH_full_92
  · exact chunkBH_full_93
  · exact chunkBH_full_94
  · exact chunkBH_full_95
  · exact chunkBH_full_96
  · exact chunkBH_full_97
  · exact chunkBH_full_98
  · exact chunkBH_full_99
  · exact chunkBH_full_100
  · exact chunkBH_full_101
  · exact chunkBH_full_102
  · exact chunkBH_full_103
  · exact chunkBH_full_104
  · exact chunkBH_full_105
  · exact chunkBH_full_106
  · exact chunkBH_full_107
  · exact chunkBH_full_108
  · exact chunkBH_full_109
  · exact chunkBH_full_110
  · exact chunkBH_full_111
  · exact chunkBH_full_112
  · exact chunkBH_full_113
  · exact chunkBH_full_114
  · exact chunkBH_full_115
  · exact chunkBH_full_116
  · exact chunkBH_full_117
  · exact chunkBH_full_118
  · exact chunkBH_full_119
  · exact chunkBH_full_120
  · exact chunkBH_full_121
  · exact chunkBH_full_122
  · exact chunkBH_full_123
  · exact chunkBH_full_124
  · exact chunkBH_full_125
  · exact chunkBH_full_126
  · exact chunkBH_full_127
  · exact chunkBH_full_128
  · exact chunkBH_full_129
  · exact chunkBH_full_130
  · exact chunkBH_full_131
  · exact chunkBH_full_132
  · exact chunkBH_full_133
  · exact chunkBH_full_134
  · exact chunkBH_full_135
  · exact chunkBH_full_136
  · exact chunkBH_full_137
  · exact chunkBH_full_138
  · exact chunkBH_full_139
  · exact chunkBH_full_140
  · exact chunkBH_full_141
  · exact chunkBH_full_142
  · exact chunkBH_full_143
  · exact chunkBH_full_144
  · exact chunkBH_full_145
  · exact chunkBH_full_146

end LRC.O7L3
