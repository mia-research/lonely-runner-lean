import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C60N
import LonelyRunner.LRC.Spec.OrderSevenU5C61N
import LonelyRunner.LRC.Spec.OrderSevenU5C62N
import LonelyRunner.LRC.Spec.OrderSevenU5C63N
import LonelyRunner.LRC.Spec.OrderSevenU5C64N
import LonelyRunner.LRC.Spec.OrderSevenU5C65N
import LonelyRunner.LRC.Spec.OrderSevenU5C66N
import LonelyRunner.LRC.Spec.OrderSevenU5C67N
import LonelyRunner.LRC.Spec.OrderSevenU5C68N
import LonelyRunner.LRC.Spec.OrderSevenU5C69N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_3998 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 3998) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_3998_0, decode 300 d_3998_1, decode 300 d_3998_2, decode 300 d_3998_3, decode 300 d_3998_4, decode 300 d_3998_5, decode 300 d_3998_6, decode 142 d_3998_7] (fun x hx => bits_full_and hx) cov_3998 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_3998_0, ch_3998_1, ch_3998_2, ch_3998_3, ch_3998_4, ch_3998_5, ch_3998_6, ch_3998_7])

theorem root_4002 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4002) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4002_0, decode 300 d_4002_1, decode 300 d_4002_2, decode 300 d_4002_3, decode 300 d_4002_4, decode 300 d_4002_5, decode 161 d_4002_6] (fun x hx => bits_full_and hx) cov_4002 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4002_0, ch_4002_1, ch_4002_2, ch_4002_3, ch_4002_4, ch_4002_5, ch_4002_6])

theorem root_4003 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4003) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4003_0, decode 300 d_4003_1, decode 300 d_4003_2, decode 300 d_4003_3, decode 300 d_4003_4, decode 300 d_4003_5, decode 161 d_4003_6] (fun x hx => bits_full_and hx) cov_4003 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4003_0, ch_4003_1, ch_4003_2, ch_4003_3, ch_4003_4, ch_4003_5, ch_4003_6])

theorem root_4004 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4004) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4004_0, decode 300 d_4004_1, decode 300 d_4004_2, decode 300 d_4004_3, decode 300 d_4004_4, decode 300 d_4004_5, decode 105 d_4004_6] (fun x hx => bits_full_and hx) cov_4004 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4004_0, ch_4004_1, ch_4004_2, ch_4004_3, ch_4004_4, ch_4004_5, ch_4004_6])

theorem root_4010 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4010) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4010_0, decode 300 d_4010_1, decode 300 d_4010_2, decode 300 d_4010_3, decode 300 d_4010_4, decode 300 d_4010_5, decode 161 d_4010_6] (fun x hx => bits_full_and hx) cov_4010 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4010_0, ch_4010_1, ch_4010_2, ch_4010_3, ch_4010_4, ch_4010_5, ch_4010_6])

theorem root_4011 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4011) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4011_0, decode 300 d_4011_1, decode 300 d_4011_2, decode 300 d_4011_3, decode 300 d_4011_4, decode 300 d_4011_5, decode 184 d_4011_6] (fun x hx => bits_full_and hx) cov_4011 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4011_0, ch_4011_1, ch_4011_2, ch_4011_3, ch_4011_4, ch_4011_5, ch_4011_6])

theorem root_4013 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4013) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4013_0, decode 300 d_4013_1, decode 300 d_4013_2, decode 300 d_4013_3, decode 300 d_4013_4, decode 300 d_4013_5, decode 300 d_4013_6, decode 141 d_4013_7] (fun x hx => bits_full_and hx) cov_4013 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4013_0, ch_4013_1, ch_4013_2, ch_4013_3, ch_4013_4, ch_4013_5, ch_4013_6, ch_4013_7])

theorem root_4014 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4014) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4014_0, decode 300 d_4014_1, decode 300 d_4014_2, decode 300 d_4014_3, decode 300 d_4014_4, decode 300 d_4014_5, decode 300 d_4014_6, decode 141 d_4014_7] (fun x hx => bits_full_and hx) cov_4014 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4014_0, ch_4014_1, ch_4014_2, ch_4014_3, ch_4014_4, ch_4014_5, ch_4014_6, ch_4014_7])

theorem root_4015 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4015) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4015_0, decode 300 d_4015_1, decode 300 d_4015_2, decode 300 d_4015_3, decode 300 d_4015_4, decode 300 d_4015_5, decode 300 d_4015_6, decode 141 d_4015_7] (fun x hx => bits_full_and hx) cov_4015 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4015_0, ch_4015_1, ch_4015_2, ch_4015_3, ch_4015_4, ch_4015_5, ch_4015_6, ch_4015_7])

theorem root_4016 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4016) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4016_0, decode 300 d_4016_1, decode 300 d_4016_2, decode 300 d_4016_3, decode 300 d_4016_4, decode 300 d_4016_5, decode 300 d_4016_6, decode 141 d_4016_7] (fun x hx => bits_full_and hx) cov_4016 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4016_0, ch_4016_1, ch_4016_2, ch_4016_3, ch_4016_4, ch_4016_5, ch_4016_6, ch_4016_7])

theorem root_4024 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4024) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4024_0, decode 300 d_4024_1, decode 300 d_4024_2, decode 300 d_4024_3, decode 300 d_4024_4, decode 300 d_4024_5, decode 300 d_4024_6, decode 141 d_4024_7] (fun x hx => bits_full_and hx) cov_4024 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4024_0, ch_4024_1, ch_4024_2, ch_4024_3, ch_4024_4, ch_4024_5, ch_4024_6, ch_4024_7])

theorem root_4025 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4025) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4025_0, decode 300 d_4025_1, decode 300 d_4025_2, decode 300 d_4025_3, decode 300 d_4025_4, decode 300 d_4025_5, decode 300 d_4025_6, decode 141 d_4025_7] (fun x hx => bits_full_and hx) cov_4025 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4025_0, ch_4025_1, ch_4025_2, ch_4025_3, ch_4025_4, ch_4025_5, ch_4025_6, ch_4025_7])

theorem root_4033 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4033) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4033_0, decode 300 d_4033_1, decode 300 d_4033_2, decode 300 d_4033_3, decode 300 d_4033_4, decode 300 d_4033_5, decode 300 d_4033_6, decode 141 d_4033_7] (fun x hx => bits_full_and hx) cov_4033 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4033_0, ch_4033_1, ch_4033_2, ch_4033_3, ch_4033_4, ch_4033_5, ch_4033_6, ch_4033_7])

theorem root_4034 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4034) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4034_0, decode 300 d_4034_1, decode 300 d_4034_2, decode 300 d_4034_3, decode 300 d_4034_4, decode 300 d_4034_5, decode 300 d_4034_6, decode 141 d_4034_7] (fun x hx => bits_full_and hx) cov_4034 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4034_0, ch_4034_1, ch_4034_2, ch_4034_3, ch_4034_4, ch_4034_5, ch_4034_6, ch_4034_7])

theorem root_4035 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4035) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4035_0, decode 300 d_4035_1, decode 300 d_4035_2, decode 300 d_4035_3, decode 300 d_4035_4, decode 300 d_4035_5, decode 300 d_4035_6, decode 141 d_4035_7] (fun x hx => bits_full_and hx) cov_4035 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4035_0, ch_4035_1, ch_4035_2, ch_4035_3, ch_4035_4, ch_4035_5, ch_4035_6, ch_4035_7])

theorem root_4043 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4043) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4043_0, decode 300 d_4043_1, decode 300 d_4043_2, decode 300 d_4043_3, decode 300 d_4043_4, decode 300 d_4043_5, decode 300 d_4043_6, decode 141 d_4043_7] (fun x hx => bits_full_and hx) cov_4043 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4043_0, ch_4043_1, ch_4043_2, ch_4043_3, ch_4043_4, ch_4043_5, ch_4043_6, ch_4043_7])

theorem root_4044 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4044) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4044_0, decode 300 d_4044_1, decode 300 d_4044_2, decode 300 d_4044_3, decode 300 d_4044_4, decode 300 d_4044_5, decode 300 d_4044_6, decode 141 d_4044_7] (fun x hx => bits_full_and hx) cov_4044 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4044_0, ch_4044_1, ch_4044_2, ch_4044_3, ch_4044_4, ch_4044_5, ch_4044_6, ch_4044_7])

theorem root_4045 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4045) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4045_0, decode 300 d_4045_1, decode 300 d_4045_2, decode 300 d_4045_3, decode 300 d_4045_4, decode 300 d_4045_5, decode 300 d_4045_6, decode 141 d_4045_7] (fun x hx => bits_full_and hx) cov_4045 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4045_0, ch_4045_1, ch_4045_2, ch_4045_3, ch_4045_4, ch_4045_5, ch_4045_6, ch_4045_7])

theorem root_4046 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4046) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4046_0, decode 300 d_4046_1, decode 300 d_4046_2, decode 300 d_4046_3, decode 300 d_4046_4, decode 300 d_4046_5, decode 300 d_4046_6, decode 141 d_4046_7] (fun x hx => bits_full_and hx) cov_4046 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4046_0, ch_4046_1, ch_4046_2, ch_4046_3, ch_4046_4, ch_4046_5, ch_4046_6, ch_4046_7])

theorem roots_60_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_60, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_60, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_3998 hB hC hCl hCB, root_4002 hB hC hCl hCB, root_4003 hB hC hCl hCB, root_4004 hB hC hCl hCB, root_4010 hB hC hCl hCB, root_4011 hB hC hCl hCB, root_4013 hB hC hCl hCB, root_4014 hB hC hCl hCB, root_4015 hB hC hCl hCB, root_4016 hB hC hCl hCB, root_4024 hB hC hCl hCB, root_4025 hB hC hCl hCB, root_4033 hB hC hCl hCB, root_4034 hB hC hCl hCB, root_4035 hB hC hCl hCB, root_4043 hB hC hCl hCB, root_4044 hB hC hCl hCB, root_4045 hB hC hCl hCB, root_4046 hB hC hCl hCB]

theorem root_4059 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4059) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4059_0, decode 300 d_4059_1, decode 300 d_4059_2, decode 300 d_4059_3, decode 300 d_4059_4, decode 300 d_4059_5, decode 300 d_4059_6, decode 141 d_4059_7] (fun x hx => bits_full_and hx) cov_4059 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4059_0, ch_4059_1, ch_4059_2, ch_4059_3, ch_4059_4, ch_4059_5, ch_4059_6, ch_4059_7])

theorem root_4066 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4066) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4066_0, decode 300 d_4066_1, decode 300 d_4066_2, decode 300 d_4066_3, decode 300 d_4066_4, decode 300 d_4066_5, decode 300 d_4066_6, decode 141 d_4066_7] (fun x hx => bits_full_and hx) cov_4066 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4066_0, ch_4066_1, ch_4066_2, ch_4066_3, ch_4066_4, ch_4066_5, ch_4066_6, ch_4066_7])

theorem root_4073 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4073) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4073_0, decode 300 d_4073_1, decode 300 d_4073_2, decode 300 d_4073_3, decode 300 d_4073_4, decode 300 d_4073_5, decode 89 d_4073_6] (fun x hx => bits_full_and hx) cov_4073 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4073_0, ch_4073_1, ch_4073_2, ch_4073_3, ch_4073_4, ch_4073_5, ch_4073_6])

theorem root_4074 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4074) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4074_0, decode 300 d_4074_1, decode 300 d_4074_2, decode 300 d_4074_3, decode 300 d_4074_4, decode 300 d_4074_5, decode 89 d_4074_6] (fun x hx => bits_full_and hx) cov_4074 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4074_0, ch_4074_1, ch_4074_2, ch_4074_3, ch_4074_4, ch_4074_5, ch_4074_6])

theorem root_4075 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4075) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4075_0, decode 300 d_4075_1, decode 300 d_4075_2, decode 300 d_4075_3, decode 300 d_4075_4, decode 300 d_4075_5, decode 89 d_4075_6] (fun x hx => bits_full_and hx) cov_4075 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4075_0, ch_4075_1, ch_4075_2, ch_4075_3, ch_4075_4, ch_4075_5, ch_4075_6])

theorem root_4079 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4079) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4079_0, decode 300 d_4079_1, decode 300 d_4079_2, decode 300 d_4079_3, decode 300 d_4079_4, decode 300 d_4079_5, decode 129 d_4079_6] (fun x hx => bits_full_and hx) cov_4079 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4079_0, ch_4079_1, ch_4079_2, ch_4079_3, ch_4079_4, ch_4079_5, ch_4079_6])

theorem root_4080 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4080) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4080_0, decode 300 d_4080_1, decode 300 d_4080_2, decode 300 d_4080_3, decode 300 d_4080_4, decode 300 d_4080_5, decode 129 d_4080_6] (fun x hx => bits_full_and hx) cov_4080 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4080_0, ch_4080_1, ch_4080_2, ch_4080_3, ch_4080_4, ch_4080_5, ch_4080_6])

theorem root_4084 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4084) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4084_0, decode 300 d_4084_1, decode 300 d_4084_2, decode 300 d_4084_3, decode 300 d_4084_4, decode 300 d_4084_5, decode 60 d_4084_6] (fun x hx => bits_full_and hx) cov_4084 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4084_0, ch_4084_1, ch_4084_2, ch_4084_3, ch_4084_4, ch_4084_5, ch_4084_6])

theorem root_4085 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4085) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4085_0, decode 300 d_4085_1, decode 300 d_4085_2, decode 300 d_4085_3, decode 300 d_4085_4, decode 300 d_4085_5, decode 23 d_4085_6] (fun x hx => bits_full_and hx) cov_4085 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4085_0, ch_4085_1, ch_4085_2, ch_4085_3, ch_4085_4, ch_4085_5, ch_4085_6])

theorem root_4097 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4097) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4097_0, decode 300 d_4097_1, decode 300 d_4097_2, decode 300 d_4097_3, decode 300 d_4097_4, decode 300 d_4097_5, decode 65 d_4097_6] (fun x hx => bits_full_and hx) cov_4097 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4097_0, ch_4097_1, ch_4097_2, ch_4097_3, ch_4097_4, ch_4097_5, ch_4097_6])

theorem root_4098 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4098) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4098_0, decode 300 d_4098_1, decode 300 d_4098_2, decode 300 d_4098_3, decode 300 d_4098_4, decode 300 d_4098_5, decode 65 d_4098_6] (fun x hx => bits_full_and hx) cov_4098 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4098_0, ch_4098_1, ch_4098_2, ch_4098_3, ch_4098_4, ch_4098_5, ch_4098_6])

theorem root_4106 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4106) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4106_0, decode 300 d_4106_1, decode 300 d_4106_2, decode 300 d_4106_3, decode 300 d_4106_4, decode 300 d_4106_5, decode 300 d_4106_6, decode 158 d_4106_7] (fun x hx => bits_full_and hx) cov_4106 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4106_0, ch_4106_1, ch_4106_2, ch_4106_3, ch_4106_4, ch_4106_5, ch_4106_6, ch_4106_7])

theorem root_4110 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4110) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4110_0, decode 300 d_4110_1, decode 300 d_4110_2, decode 300 d_4110_3, decode 300 d_4110_4, decode 300 d_4110_5, decode 300 d_4110_6, decode 141 d_4110_7] (fun x hx => bits_full_and hx) cov_4110 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4110_0, ch_4110_1, ch_4110_2, ch_4110_3, ch_4110_4, ch_4110_5, ch_4110_6, ch_4110_7])

theorem root_4116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4116_0, decode 300 d_4116_1, decode 300 d_4116_2, decode 300 d_4116_3, decode 300 d_4116_4, decode 300 d_4116_5, decode 300 d_4116_6, decode 158 d_4116_7] (fun x hx => bits_full_and hx) cov_4116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4116_0, ch_4116_1, ch_4116_2, ch_4116_3, ch_4116_4, ch_4116_5, ch_4116_6, ch_4116_7])

theorem root_4118 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4118) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4118_0, decode 300 d_4118_1, decode 300 d_4118_2, decode 300 d_4118_3, decode 300 d_4118_4, decode 300 d_4118_5, decode 300 d_4118_6, decode 141 d_4118_7] (fun x hx => bits_full_and hx) cov_4118 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4118_0, ch_4118_1, ch_4118_2, ch_4118_3, ch_4118_4, ch_4118_5, ch_4118_6, ch_4118_7])

theorem root_4123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4123_0, decode 300 d_4123_1, decode 300 d_4123_2, decode 300 d_4123_3, decode 300 d_4123_4, decode 300 d_4123_5, decode 300 d_4123_6, decode 158 d_4123_7] (fun x hx => bits_full_and hx) cov_4123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4123_0, ch_4123_1, ch_4123_2, ch_4123_3, ch_4123_4, ch_4123_5, ch_4123_6, ch_4123_7])

theorem root_4125 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4125) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4125_0, decode 300 d_4125_1, decode 300 d_4125_2, decode 300 d_4125_3, decode 300 d_4125_4, decode 300 d_4125_5, decode 300 d_4125_6, decode 141 d_4125_7] (fun x hx => bits_full_and hx) cov_4125 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4125_0, ch_4125_1, ch_4125_2, ch_4125_3, ch_4125_4, ch_4125_5, ch_4125_6, ch_4125_7])

theorem root_4137 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4137) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4137_0, decode 300 d_4137_1, decode 300 d_4137_2, decode 300 d_4137_3, decode 300 d_4137_4, decode 300 d_4137_5, decode 300 d_4137_6, decode 141 d_4137_7] (fun x hx => bits_full_and hx) cov_4137 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4137_0, ch_4137_1, ch_4137_2, ch_4137_3, ch_4137_4, ch_4137_5, ch_4137_6, ch_4137_7])

theorem root_4138 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4138) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4138_0, decode 300 d_4138_1, decode 300 d_4138_2, decode 300 d_4138_3, decode 300 d_4138_4, decode 300 d_4138_5, decode 300 d_4138_6, decode 141 d_4138_7] (fun x hx => bits_full_and hx) cov_4138 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4138_0, ch_4138_1, ch_4138_2, ch_4138_3, ch_4138_4, ch_4138_5, ch_4138_6, ch_4138_7])

theorem root_4150 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4150) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4150_0, decode 300 d_4150_1, decode 300 d_4150_2, decode 300 d_4150_3, decode 300 d_4150_4, decode 300 d_4150_5, decode 300 d_4150_6, decode 141 d_4150_7] (fun x hx => bits_full_and hx) cov_4150 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4150_0, ch_4150_1, ch_4150_2, ch_4150_3, ch_4150_4, ch_4150_5, ch_4150_6, ch_4150_7])

theorem roots_61_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_61, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_61, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4059 hB hC hCl hCB, root_4066 hB hC hCl hCB, root_4073 hB hC hCl hCB, root_4074 hB hC hCl hCB, root_4075 hB hC hCl hCB, root_4079 hB hC hCl hCB, root_4080 hB hC hCl hCB, root_4084 hB hC hCl hCB, root_4085 hB hC hCl hCB, root_4097 hB hC hCl hCB, root_4098 hB hC hCl hCB, root_4106 hB hC hCl hCB, root_4110 hB hC hCl hCB, root_4116 hB hC hCl hCB, root_4118 hB hC hCl hCB, root_4123 hB hC hCl hCB, root_4125 hB hC hCl hCB, root_4137 hB hC hCl hCB, root_4138 hB hC hCl hCB, root_4150 hB hC hCl hCB]

theorem root_4167 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4167) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4167_0, decode 300 d_4167_1, decode 300 d_4167_2, decode 300 d_4167_3, decode 300 d_4167_4, decode 300 d_4167_5, decode 300 d_4167_6, decode 141 d_4167_7] (fun x hx => bits_full_and hx) cov_4167 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4167_0, ch_4167_1, ch_4167_2, ch_4167_3, ch_4167_4, ch_4167_5, ch_4167_6, ch_4167_7])

theorem root_4168 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4168) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4168_0, decode 300 d_4168_1, decode 300 d_4168_2, decode 300 d_4168_3, decode 300 d_4168_4, decode 300 d_4168_5, decode 300 d_4168_6, decode 141 d_4168_7] (fun x hx => bits_full_and hx) cov_4168 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4168_0, ch_4168_1, ch_4168_2, ch_4168_3, ch_4168_4, ch_4168_5, ch_4168_6, ch_4168_7])

theorem root_4169 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4169) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4169_0, decode 300 d_4169_1, decode 300 d_4169_2, decode 300 d_4169_3, decode 300 d_4169_4, decode 300 d_4169_5, decode 300 d_4169_6, decode 142 d_4169_7] (fun x hx => bits_full_and hx) cov_4169 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4169_0, ch_4169_1, ch_4169_2, ch_4169_3, ch_4169_4, ch_4169_5, ch_4169_6, ch_4169_7])

theorem root_4174 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4174) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4174_0, decode 300 d_4174_1, decode 300 d_4174_2, decode 300 d_4174_3, decode 300 d_4174_4, decode 275 d_4174_5] (fun x hx => bits_full_and hx) cov_4174 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4174_0, ch_4174_1, ch_4174_2, ch_4174_3, ch_4174_4, ch_4174_5])

theorem root_4180 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4180) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4180_0, decode 300 d_4180_1, decode 300 d_4180_2, decode 300 d_4180_3, decode 300 d_4180_4, decode 300 d_4180_5, decode 161 d_4180_6] (fun x hx => bits_full_and hx) cov_4180 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4180_0, ch_4180_1, ch_4180_2, ch_4180_3, ch_4180_4, ch_4180_5, ch_4180_6])

theorem root_4181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4181_0, decode 300 d_4181_1, decode 300 d_4181_2, decode 300 d_4181_3, decode 300 d_4181_4, decode 300 d_4181_5, decode 161 d_4181_6] (fun x hx => bits_full_and hx) cov_4181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4181_0, ch_4181_1, ch_4181_2, ch_4181_3, ch_4181_4, ch_4181_5, ch_4181_6])

theorem root_4182 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4182) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4182_0, decode 300 d_4182_1, decode 300 d_4182_2, decode 300 d_4182_3, decode 300 d_4182_4, decode 300 d_4182_5, decode 39 d_4182_6] (fun x hx => bits_full_and hx) cov_4182 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4182_0, ch_4182_1, ch_4182_2, ch_4182_3, ch_4182_4, ch_4182_5, ch_4182_6])

theorem root_4190 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4190) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4190_0, decode 300 d_4190_1, decode 300 d_4190_2, decode 300 d_4190_3, decode 300 d_4190_4, decode 300 d_4190_5, decode 161 d_4190_6] (fun x hx => bits_full_and hx) cov_4190 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4190_0, ch_4190_1, ch_4190_2, ch_4190_3, ch_4190_4, ch_4190_5, ch_4190_6])

theorem root_4191 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4191) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4191_0, decode 300 d_4191_1, decode 300 d_4191_2, decode 300 d_4191_3, decode 300 d_4191_4, decode 300 d_4191_5, decode 161 d_4191_6] (fun x hx => bits_full_and hx) cov_4191 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4191_0, ch_4191_1, ch_4191_2, ch_4191_3, ch_4191_4, ch_4191_5, ch_4191_6])

theorem root_4192 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4192) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4192_0, decode 300 d_4192_1, decode 300 d_4192_2, decode 300 d_4192_3, decode 300 d_4192_4, decode 281 d_4192_5] (fun x hx => bits_full_and hx) cov_4192 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4192_0, ch_4192_1, ch_4192_2, ch_4192_3, ch_4192_4, ch_4192_5])

theorem root_4193 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4193) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4193_0, decode 300 d_4193_1, decode 300 d_4193_2, decode 300 d_4193_3, decode 300 d_4193_4, decode 300 d_4193_5, decode 39 d_4193_6] (fun x hx => bits_full_and hx) cov_4193 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4193_0, ch_4193_1, ch_4193_2, ch_4193_3, ch_4193_4, ch_4193_5, ch_4193_6])

theorem root_4200 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4200) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4200_0, decode 300 d_4200_1, decode 300 d_4200_2, decode 300 d_4200_3, decode 300 d_4200_4, decode 300 d_4200_5, decode 161 d_4200_6] (fun x hx => bits_full_and hx) cov_4200 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4200_0, ch_4200_1, ch_4200_2, ch_4200_3, ch_4200_4, ch_4200_5, ch_4200_6])

theorem root_4201 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4201) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4201_0, decode 300 d_4201_1, decode 300 d_4201_2, decode 300 d_4201_3, decode 300 d_4201_4, decode 300 d_4201_5, decode 161 d_4201_6] (fun x hx => bits_full_and hx) cov_4201 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4201_0, ch_4201_1, ch_4201_2, ch_4201_3, ch_4201_4, ch_4201_5, ch_4201_6])

theorem root_4202 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4202) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4202_0, decode 300 d_4202_1, decode 300 d_4202_2, decode 300 d_4202_3, decode 300 d_4202_4, decode 300 d_4202_5, decode 161 d_4202_6] (fun x hx => bits_full_and hx) cov_4202 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4202_0, ch_4202_1, ch_4202_2, ch_4202_3, ch_4202_4, ch_4202_5, ch_4202_6])

theorem root_4203 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4203) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4203_0, decode 300 d_4203_1, decode 300 d_4203_2, decode 300 d_4203_3, decode 300 d_4203_4, decode 281 d_4203_5] (fun x hx => bits_full_and hx) cov_4203 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4203_0, ch_4203_1, ch_4203_2, ch_4203_3, ch_4203_4, ch_4203_5])

theorem root_4210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4210_0, decode 300 d_4210_1, decode 300 d_4210_2, decode 300 d_4210_3, decode 300 d_4210_4, decode 300 d_4210_5, decode 161 d_4210_6] (fun x hx => bits_full_and hx) cov_4210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4210_0, ch_4210_1, ch_4210_2, ch_4210_3, ch_4210_4, ch_4210_5, ch_4210_6])

theorem root_4211 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4211) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4211_0, decode 300 d_4211_1, decode 300 d_4211_2, decode 300 d_4211_3, decode 300 d_4211_4, decode 240 d_4211_5] (fun x hx => bits_full_and hx) cov_4211 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4211_0, ch_4211_1, ch_4211_2, ch_4211_3, ch_4211_4, ch_4211_5])

theorem root_4222 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4222) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4222_0, decode 300 d_4222_1, decode 300 d_4222_2, decode 300 d_4222_3, decode 300 d_4222_4, decode 300 d_4222_5, decode 54 d_4222_6] (fun x hx => bits_full_and hx) cov_4222 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4222_0, ch_4222_1, ch_4222_2, ch_4222_3, ch_4222_4, ch_4222_5, ch_4222_6])

theorem root_4223 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4223) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4223_0, decode 300 d_4223_1, decode 300 d_4223_2, decode 300 d_4223_3, decode 300 d_4223_4, decode 300 d_4223_5, decode 54 d_4223_6] (fun x hx => bits_full_and hx) cov_4223 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4223_0, ch_4223_1, ch_4223_2, ch_4223_3, ch_4223_4, ch_4223_5, ch_4223_6])

theorem root_4224 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4224) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4224_0, decode 300 d_4224_1, decode 300 d_4224_2, decode 300 d_4224_3, decode 300 d_4224_4, decode 300 d_4224_5, decode 300 d_4224_6, decode 141 d_4224_7] (fun x hx => bits_full_and hx) cov_4224 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4224_0, ch_4224_1, ch_4224_2, ch_4224_3, ch_4224_4, ch_4224_5, ch_4224_6, ch_4224_7])

theorem root_4225 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4225) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4225_0, decode 300 d_4225_1, decode 300 d_4225_2, decode 300 d_4225_3, decode 300 d_4225_4, decode 300 d_4225_5, decode 300 d_4225_6, decode 141 d_4225_7] (fun x hx => bits_full_and hx) cov_4225 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4225_0, ch_4225_1, ch_4225_2, ch_4225_3, ch_4225_4, ch_4225_5, ch_4225_6, ch_4225_7])

theorem roots_62_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_62, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_62, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4167 hB hC hCl hCB, root_4168 hB hC hCl hCB, root_4169 hB hC hCl hCB, root_4174 hB hC hCl hCB, root_4180 hB hC hCl hCB, root_4181 hB hC hCl hCB, root_4182 hB hC hCl hCB, root_4190 hB hC hCl hCB, root_4191 hB hC hCl hCB, root_4192 hB hC hCl hCB, root_4193 hB hC hCl hCB, root_4200 hB hC hCl hCB, root_4201 hB hC hCl hCB, root_4202 hB hC hCl hCB, root_4203 hB hC hCl hCB, root_4210 hB hC hCl hCB, root_4211 hB hC hCl hCB, root_4222 hB hC hCl hCB, root_4223 hB hC hCl hCB, root_4224 hB hC hCl hCB, root_4225 hB hC hCl hCB]

theorem root_4226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4226_0, decode 300 d_4226_1, decode 300 d_4226_2, decode 300 d_4226_3, decode 300 d_4226_4, decode 300 d_4226_5, decode 300 d_4226_6, decode 141 d_4226_7] (fun x hx => bits_full_and hx) cov_4226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4226_0, ch_4226_1, ch_4226_2, ch_4226_3, ch_4226_4, ch_4226_5, ch_4226_6, ch_4226_7])

theorem root_4237 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4237) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4237_0, decode 300 d_4237_1, decode 300 d_4237_2, decode 300 d_4237_3, decode 300 d_4237_4, decode 300 d_4237_5, decode 300 d_4237_6, decode 141 d_4237_7] (fun x hx => bits_full_and hx) cov_4237 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4237_0, ch_4237_1, ch_4237_2, ch_4237_3, ch_4237_4, ch_4237_5, ch_4237_6, ch_4237_7])

theorem root_4238 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4238) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4238_0, decode 300 d_4238_1, decode 300 d_4238_2, decode 300 d_4238_3, decode 300 d_4238_4, decode 300 d_4238_5, decode 300 d_4238_6, decode 158 d_4238_7] (fun x hx => bits_full_and hx) cov_4238 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4238_0, ch_4238_1, ch_4238_2, ch_4238_3, ch_4238_4, ch_4238_5, ch_4238_6, ch_4238_7])

theorem root_4239 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4239) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4239_0, decode 300 d_4239_1, decode 300 d_4239_2, decode 300 d_4239_3, decode 300 d_4239_4, decode 300 d_4239_5, decode 300 d_4239_6, decode 158 d_4239_7] (fun x hx => bits_full_and hx) cov_4239 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4239_0, ch_4239_1, ch_4239_2, ch_4239_3, ch_4239_4, ch_4239_5, ch_4239_6, ch_4239_7])

theorem root_4245 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4245) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4245_0, decode 300 d_4245_1, decode 300 d_4245_2, decode 300 d_4245_3, decode 300 d_4245_4, decode 300 d_4245_5, decode 300 d_4245_6, decode 141 d_4245_7] (fun x hx => bits_full_and hx) cov_4245 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4245_0, ch_4245_1, ch_4245_2, ch_4245_3, ch_4245_4, ch_4245_5, ch_4245_6, ch_4245_7])

theorem root_4246 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4246) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4246_0, decode 300 d_4246_1, decode 300 d_4246_2, decode 300 d_4246_3, decode 300 d_4246_4, decode 300 d_4246_5, decode 300 d_4246_6, decode 141 d_4246_7] (fun x hx => bits_full_and hx) cov_4246 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4246_0, ch_4246_1, ch_4246_2, ch_4246_3, ch_4246_4, ch_4246_5, ch_4246_6, ch_4246_7])

theorem root_4247 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4247) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4247_0, decode 300 d_4247_1, decode 300 d_4247_2, decode 300 d_4247_3, decode 300 d_4247_4, decode 300 d_4247_5, decode 300 d_4247_6, decode 158 d_4247_7] (fun x hx => bits_full_and hx) cov_4247 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4247_0, ch_4247_1, ch_4247_2, ch_4247_3, ch_4247_4, ch_4247_5, ch_4247_6, ch_4247_7])

theorem root_4248 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4248) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4248_0, decode 300 d_4248_1, decode 300 d_4248_2, decode 300 d_4248_3, decode 300 d_4248_4, decode 300 d_4248_5, decode 300 d_4248_6, decode 158 d_4248_7] (fun x hx => bits_full_and hx) cov_4248 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4248_0, ch_4248_1, ch_4248_2, ch_4248_3, ch_4248_4, ch_4248_5, ch_4248_6, ch_4248_7])

theorem root_4253 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4253) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4253_0, decode 300 d_4253_1, decode 300 d_4253_2, decode 300 d_4253_3, decode 300 d_4253_4, decode 300 d_4253_5, decode 300 d_4253_6, decode 141 d_4253_7] (fun x hx => bits_full_and hx) cov_4253 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4253_0, ch_4253_1, ch_4253_2, ch_4253_3, ch_4253_4, ch_4253_5, ch_4253_6, ch_4253_7])

theorem root_4254 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4254) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4254_0, decode 300 d_4254_1, decode 300 d_4254_2, decode 300 d_4254_3, decode 300 d_4254_4, decode 300 d_4254_5, decode 300 d_4254_6, decode 158 d_4254_7] (fun x hx => bits_full_and hx) cov_4254 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4254_0, ch_4254_1, ch_4254_2, ch_4254_3, ch_4254_4, ch_4254_5, ch_4254_6, ch_4254_7])

theorem root_4255 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4255) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4255_0, decode 300 d_4255_1, decode 300 d_4255_2, decode 300 d_4255_3, decode 300 d_4255_4, decode 300 d_4255_5, decode 300 d_4255_6, decode 158 d_4255_7] (fun x hx => bits_full_and hx) cov_4255 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4255_0, ch_4255_1, ch_4255_2, ch_4255_3, ch_4255_4, ch_4255_5, ch_4255_6, ch_4255_7])

theorem root_4259 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4259) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4259_0, decode 300 d_4259_1, decode 300 d_4259_2, decode 300 d_4259_3, decode 300 d_4259_4, decode 300 d_4259_5, decode 300 d_4259_6, decode 141 d_4259_7] (fun x hx => bits_full_and hx) cov_4259 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4259_0, ch_4259_1, ch_4259_2, ch_4259_3, ch_4259_4, ch_4259_5, ch_4259_6, ch_4259_7])

theorem root_4260 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4260) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4260_0, decode 300 d_4260_1, decode 300 d_4260_2, decode 300 d_4260_3, decode 300 d_4260_4, decode 300 d_4260_5, decode 300 d_4260_6, decode 142 d_4260_7] (fun x hx => bits_full_and hx) cov_4260 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4260_0, ch_4260_1, ch_4260_2, ch_4260_3, ch_4260_4, ch_4260_5, ch_4260_6, ch_4260_7])

theorem root_4261 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4261) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4261_0, decode 300 d_4261_1, decode 300 d_4261_2, decode 300 d_4261_3, decode 300 d_4261_4, decode 300 d_4261_5, decode 300 d_4261_6, decode 142 d_4261_7] (fun x hx => bits_full_and hx) cov_4261 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4261_0, ch_4261_1, ch_4261_2, ch_4261_3, ch_4261_4, ch_4261_5, ch_4261_6, ch_4261_7])

theorem root_4262 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4262) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4262_0, decode 300 d_4262_1, decode 300 d_4262_2, decode 300 d_4262_3, decode 300 d_4262_4, decode 300 d_4262_5, decode 300 d_4262_6, decode 142 d_4262_7] (fun x hx => bits_full_and hx) cov_4262 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4262_0, ch_4262_1, ch_4262_2, ch_4262_3, ch_4262_4, ch_4262_5, ch_4262_6, ch_4262_7])

theorem root_4274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4274_0, decode 300 d_4274_1, decode 300 d_4274_2, decode 300 d_4274_3, decode 300 d_4274_4, decode 300 d_4274_5, decode 300 d_4274_6, decode 141 d_4274_7] (fun x hx => bits_full_and hx) cov_4274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4274_0, ch_4274_1, ch_4274_2, ch_4274_3, ch_4274_4, ch_4274_5, ch_4274_6, ch_4274_7])

theorem root_4275 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4275) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4275_0, decode 300 d_4275_1, decode 300 d_4275_2, decode 300 d_4275_3, decode 300 d_4275_4, decode 300 d_4275_5, decode 300 d_4275_6, decode 141 d_4275_7] (fun x hx => bits_full_and hx) cov_4275 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4275_0, ch_4275_1, ch_4275_2, ch_4275_3, ch_4275_4, ch_4275_5, ch_4275_6, ch_4275_7])

theorem root_4276 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4276) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4276_0, decode 300 d_4276_1, decode 300 d_4276_2, decode 300 d_4276_3, decode 300 d_4276_4, decode 300 d_4276_5, decode 300 d_4276_6, decode 141 d_4276_7] (fun x hx => bits_full_and hx) cov_4276 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4276_0, ch_4276_1, ch_4276_2, ch_4276_3, ch_4276_4, ch_4276_5, ch_4276_6, ch_4276_7])

theorem roots_63_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_63, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_63, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4226 hB hC hCl hCB, root_4237 hB hC hCl hCB, root_4238 hB hC hCl hCB, root_4239 hB hC hCl hCB, root_4245 hB hC hCl hCB, root_4246 hB hC hCl hCB, root_4247 hB hC hCl hCB, root_4248 hB hC hCl hCB, root_4253 hB hC hCl hCB, root_4254 hB hC hCl hCB, root_4255 hB hC hCl hCB, root_4259 hB hC hCl hCB, root_4260 hB hC hCl hCB, root_4261 hB hC hCl hCB, root_4262 hB hC hCl hCB, root_4274 hB hC hCl hCB, root_4275 hB hC hCl hCB, root_4276 hB hC hCl hCB]

theorem root_4277 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4277) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4277_0, decode 300 d_4277_1, decode 300 d_4277_2, decode 300 d_4277_3, decode 300 d_4277_4, decode 300 d_4277_5, decode 300 d_4277_6, decode 158 d_4277_7] (fun x hx => bits_full_and hx) cov_4277 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4277_0, ch_4277_1, ch_4277_2, ch_4277_3, ch_4277_4, ch_4277_5, ch_4277_6, ch_4277_7])

theorem root_4278 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4278) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4278_0, decode 300 d_4278_1, decode 300 d_4278_2, decode 300 d_4278_3, decode 300 d_4278_4, decode 300 d_4278_5, decode 300 d_4278_6, decode 158 d_4278_7] (fun x hx => bits_full_and hx) cov_4278 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4278_0, ch_4278_1, ch_4278_2, ch_4278_3, ch_4278_4, ch_4278_5, ch_4278_6, ch_4278_7])

theorem root_4281 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4281) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4281_0, decode 300 d_4281_1, decode 300 d_4281_2, decode 300 d_4281_3, decode 300 d_4281_4, decode 300 d_4281_5, decode 300 d_4281_6, decode 141 d_4281_7] (fun x hx => bits_full_and hx) cov_4281 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4281_0, ch_4281_1, ch_4281_2, ch_4281_3, ch_4281_4, ch_4281_5, ch_4281_6, ch_4281_7])

theorem root_4289 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4289) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4289_0, decode 300 d_4289_1, decode 300 d_4289_2, decode 300 d_4289_3, decode 300 d_4289_4, decode 300 d_4289_5, decode 300 d_4289_6, decode 141 d_4289_7] (fun x hx => bits_full_and hx) cov_4289 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4289_0, ch_4289_1, ch_4289_2, ch_4289_3, ch_4289_4, ch_4289_5, ch_4289_6, ch_4289_7])

theorem root_4291 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4291) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4291_0, decode 300 d_4291_1, decode 300 d_4291_2, decode 300 d_4291_3, decode 300 d_4291_4, decode 300 d_4291_5, decode 300 d_4291_6, decode 141 d_4291_7] (fun x hx => bits_full_and hx) cov_4291 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4291_0, ch_4291_1, ch_4291_2, ch_4291_3, ch_4291_4, ch_4291_5, ch_4291_6, ch_4291_7])

theorem root_4293 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4293) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4293_0, decode 300 d_4293_1, decode 300 d_4293_2, decode 300 d_4293_3, decode 300 d_4293_4, decode 300 d_4293_5, decode 300 d_4293_6, decode 141 d_4293_7] (fun x hx => bits_full_and hx) cov_4293 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4293_0, ch_4293_1, ch_4293_2, ch_4293_3, ch_4293_4, ch_4293_5, ch_4293_6, ch_4293_7])

theorem root_4294 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4294) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4294_0, decode 300 d_4294_1, decode 300 d_4294_2, decode 300 d_4294_3, decode 300 d_4294_4, decode 300 d_4294_5, decode 300 d_4294_6, decode 141 d_4294_7] (fun x hx => bits_full_and hx) cov_4294 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4294_0, ch_4294_1, ch_4294_2, ch_4294_3, ch_4294_4, ch_4294_5, ch_4294_6, ch_4294_7])

theorem root_4302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4302_0, decode 300 d_4302_1, decode 300 d_4302_2, decode 300 d_4302_3, decode 300 d_4302_4, decode 300 d_4302_5, decode 300 d_4302_6, decode 141 d_4302_7] (fun x hx => bits_full_and hx) cov_4302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4302_0, ch_4302_1, ch_4302_2, ch_4302_3, ch_4302_4, ch_4302_5, ch_4302_6, ch_4302_7])

theorem root_4303 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4303) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4303_0, decode 300 d_4303_1, decode 300 d_4303_2, decode 300 d_4303_3, decode 300 d_4303_4, decode 300 d_4303_5, decode 300 d_4303_6, decode 141 d_4303_7] (fun x hx => bits_full_and hx) cov_4303 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4303_0, ch_4303_1, ch_4303_2, ch_4303_3, ch_4303_4, ch_4303_5, ch_4303_6, ch_4303_7])

theorem root_4312 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4312) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4312_0, decode 300 d_4312_1, decode 300 d_4312_2, decode 300 d_4312_3, decode 300 d_4312_4, decode 300 d_4312_5, decode 300 d_4312_6, decode 141 d_4312_7] (fun x hx => bits_full_and hx) cov_4312 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4312_0, ch_4312_1, ch_4312_2, ch_4312_3, ch_4312_4, ch_4312_5, ch_4312_6, ch_4312_7])

theorem root_4314 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4314) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4314_0, decode 300 d_4314_1, decode 300 d_4314_2, decode 300 d_4314_3, decode 300 d_4314_4, decode 300 d_4314_5, decode 300 d_4314_6, decode 141 d_4314_7] (fun x hx => bits_full_and hx) cov_4314 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4314_0, ch_4314_1, ch_4314_2, ch_4314_3, ch_4314_4, ch_4314_5, ch_4314_6, ch_4314_7])

theorem root_4325 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4325) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4325_0, decode 300 d_4325_1, decode 300 d_4325_2, decode 300 d_4325_3, decode 300 d_4325_4, decode 300 d_4325_5, decode 143 d_4325_6] (fun x hx => bits_full_and hx) cov_4325 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4325_0, ch_4325_1, ch_4325_2, ch_4325_3, ch_4325_4, ch_4325_5, ch_4325_6])

theorem root_4326 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4326) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4326_0, decode 300 d_4326_1, decode 300 d_4326_2, decode 300 d_4326_3, decode 300 d_4326_4, decode 300 d_4326_5, decode 37 d_4326_6] (fun x hx => bits_full_and hx) cov_4326 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4326_0, ch_4326_1, ch_4326_2, ch_4326_3, ch_4326_4, ch_4326_5, ch_4326_6])

theorem root_4334 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4334) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4334_0, decode 300 d_4334_1, decode 300 d_4334_2, decode 300 d_4334_3, decode 300 d_4334_4, decode 300 d_4334_5, decode 300 d_4334_6, decode 48 d_4334_7] (fun x hx => bits_full_and hx) cov_4334 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4334_0, ch_4334_1, ch_4334_2, ch_4334_3, ch_4334_4, ch_4334_5, ch_4334_6, ch_4334_7])

theorem root_4335 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4335) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4335_0, decode 300 d_4335_1, decode 300 d_4335_2, decode 300 d_4335_3, decode 300 d_4335_4, decode 300 d_4335_5, decode 75 d_4335_6] (fun x hx => bits_full_and hx) cov_4335 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4335_0, ch_4335_1, ch_4335_2, ch_4335_3, ch_4335_4, ch_4335_5, ch_4335_6])

theorem root_4341 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4341) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4341_0, decode 300 d_4341_1, decode 300 d_4341_2, decode 300 d_4341_3, decode 300 d_4341_4, decode 300 d_4341_5, decode 300 d_4341_6, decode 48 d_4341_7] (fun x hx => bits_full_and hx) cov_4341 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4341_0, ch_4341_1, ch_4341_2, ch_4341_3, ch_4341_4, ch_4341_5, ch_4341_6, ch_4341_7])

theorem root_4342 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4342) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4342_0, decode 300 d_4342_1, decode 300 d_4342_2, decode 300 d_4342_3, decode 300 d_4342_4, decode 300 d_4342_5, decode 300 d_4342_6, decode 141 d_4342_7] (fun x hx => bits_full_and hx) cov_4342 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4342_0, ch_4342_1, ch_4342_2, ch_4342_3, ch_4342_4, ch_4342_5, ch_4342_6, ch_4342_7])

theorem root_4343 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4343) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4343_0, decode 300 d_4343_1, decode 300 d_4343_2, decode 300 d_4343_3, decode 300 d_4343_4, decode 300 d_4343_5, decode 78 d_4343_6] (fun x hx => bits_full_and hx) cov_4343 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4343_0, ch_4343_1, ch_4343_2, ch_4343_3, ch_4343_4, ch_4343_5, ch_4343_6])

theorem root_4350 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4350) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4350_0, decode 300 d_4350_1, decode 300 d_4350_2, decode 300 d_4350_3, decode 300 d_4350_4, decode 300 d_4350_5, decode 199 d_4350_6] (fun x hx => bits_full_and hx) cov_4350 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4350_0, ch_4350_1, ch_4350_2, ch_4350_3, ch_4350_4, ch_4350_5, ch_4350_6])

theorem roots_64_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_64, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_64, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4277 hB hC hCl hCB, root_4278 hB hC hCl hCB, root_4281 hB hC hCl hCB, root_4289 hB hC hCl hCB, root_4291 hB hC hCl hCB, root_4293 hB hC hCl hCB, root_4294 hB hC hCl hCB, root_4302 hB hC hCl hCB, root_4303 hB hC hCl hCB, root_4312 hB hC hCl hCB, root_4314 hB hC hCl hCB, root_4325 hB hC hCl hCB, root_4326 hB hC hCl hCB, root_4334 hB hC hCl hCB, root_4335 hB hC hCl hCB, root_4341 hB hC hCl hCB, root_4342 hB hC hCl hCB, root_4343 hB hC hCl hCB, root_4350 hB hC hCl hCB]

theorem root_4351 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4351) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4351_0, decode 300 d_4351_1, decode 300 d_4351_2, decode 300 d_4351_3, decode 300 d_4351_4, decode 300 d_4351_5, decode 143 d_4351_6] (fun x hx => bits_full_and hx) cov_4351 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4351_0, ch_4351_1, ch_4351_2, ch_4351_3, ch_4351_4, ch_4351_5, ch_4351_6])

theorem root_4352 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4352) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4352_0, decode 300 d_4352_1, decode 300 d_4352_2, decode 300 d_4352_3, decode 300 d_4352_4, decode 300 d_4352_5, decode 37 d_4352_6] (fun x hx => bits_full_and hx) cov_4352 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4352_0, ch_4352_1, ch_4352_2, ch_4352_3, ch_4352_4, ch_4352_5, ch_4352_6])

theorem root_4353 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4353) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4353_0, decode 300 d_4353_1, decode 300 d_4353_2, decode 300 d_4353_3, decode 300 d_4353_4, decode 300 d_4353_5, decode 37 d_4353_6] (fun x hx => bits_full_and hx) cov_4353 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4353_0, ch_4353_1, ch_4353_2, ch_4353_3, ch_4353_4, ch_4353_5, ch_4353_6])

theorem root_4356 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4356) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4356_0, decode 300 d_4356_1, decode 300 d_4356_2, decode 300 d_4356_3, decode 300 d_4356_4, decode 300 d_4356_5, decode 37 d_4356_6] (fun x hx => bits_full_and hx) cov_4356 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4356_0, ch_4356_1, ch_4356_2, ch_4356_3, ch_4356_4, ch_4356_5, ch_4356_6])

theorem root_4357 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4357) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4357_0, decode 300 d_4357_1, decode 300 d_4357_2, decode 300 d_4357_3, decode 300 d_4357_4, decode 300 d_4357_5, decode 37 d_4357_6] (fun x hx => bits_full_and hx) cov_4357 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4357_0, ch_4357_1, ch_4357_2, ch_4357_3, ch_4357_4, ch_4357_5, ch_4357_6])

theorem root_4359 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4359) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4359_0, decode 300 d_4359_1, decode 300 d_4359_2, decode 300 d_4359_3, decode 300 d_4359_4, decode 300 d_4359_5, decode 300 d_4359_6, decode 142 d_4359_7] (fun x hx => bits_full_and hx) cov_4359 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4359_0, ch_4359_1, ch_4359_2, ch_4359_3, ch_4359_4, ch_4359_5, ch_4359_6, ch_4359_7])

theorem root_4372 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4372) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4372_0, decode 300 d_4372_1, decode 300 d_4372_2, decode 300 d_4372_3, decode 300 d_4372_4, decode 300 d_4372_5, decode 57 d_4372_6] (fun x hx => bits_full_and hx) cov_4372 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4372_0, ch_4372_1, ch_4372_2, ch_4372_3, ch_4372_4, ch_4372_5, ch_4372_6])

theorem root_4377 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4377) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4377_0, decode 300 d_4377_1, decode 300 d_4377_2, decode 300 d_4377_3, decode 300 d_4377_4, decode 300 d_4377_5, decode 48 d_4377_6] (fun x hx => bits_full_and hx) cov_4377 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4377_0, ch_4377_1, ch_4377_2, ch_4377_3, ch_4377_4, ch_4377_5, ch_4377_6])

theorem root_4378 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4378) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4378_0, decode 300 d_4378_1, decode 300 d_4378_2, decode 300 d_4378_3, decode 300 d_4378_4, decode 300 d_4378_5, decode 28 d_4378_6] (fun x hx => bits_full_and hx) cov_4378 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4378_0, ch_4378_1, ch_4378_2, ch_4378_3, ch_4378_4, ch_4378_5, ch_4378_6])

theorem root_4379 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4379) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4379_0, decode 300 d_4379_1, decode 300 d_4379_2, decode 300 d_4379_3, decode 300 d_4379_4, decode 286 d_4379_5] (fun x hx => bits_full_and hx) cov_4379 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4379_0, ch_4379_1, ch_4379_2, ch_4379_3, ch_4379_4, ch_4379_5])

theorem root_4385 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4385) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4385_0, decode 300 d_4385_1, decode 300 d_4385_2, decode 300 d_4385_3, decode 300 d_4385_4, decode 300 d_4385_5, decode 300 d_4385_6, decode 141 d_4385_7] (fun x hx => bits_full_and hx) cov_4385 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4385_0, ch_4385_1, ch_4385_2, ch_4385_3, ch_4385_4, ch_4385_5, ch_4385_6, ch_4385_7])

theorem root_4386 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4386) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4386_0, decode 300 d_4386_1, decode 300 d_4386_2, decode 300 d_4386_3, decode 300 d_4386_4, decode 300 d_4386_5, decode 300 d_4386_6, decode 141 d_4386_7] (fun x hx => bits_full_and hx) cov_4386 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4386_0, ch_4386_1, ch_4386_2, ch_4386_3, ch_4386_4, ch_4386_5, ch_4386_6, ch_4386_7])

theorem root_4387 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4387) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4387_0, decode 300 d_4387_1, decode 300 d_4387_2, decode 300 d_4387_3, decode 300 d_4387_4, decode 300 d_4387_5, decode 300 d_4387_6, decode 141 d_4387_7] (fun x hx => bits_full_and hx) cov_4387 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4387_0, ch_4387_1, ch_4387_2, ch_4387_3, ch_4387_4, ch_4387_5, ch_4387_6, ch_4387_7])

theorem root_4396 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4396) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4396_0, decode 300 d_4396_1, decode 300 d_4396_2, decode 300 d_4396_3, decode 300 d_4396_4, decode 300 d_4396_5, decode 300 d_4396_6, decode 142 d_4396_7] (fun x hx => bits_full_and hx) cov_4396 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4396_0, ch_4396_1, ch_4396_2, ch_4396_3, ch_4396_4, ch_4396_5, ch_4396_6, ch_4396_7])

theorem root_4398 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4398) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4398_0, decode 300 d_4398_1, decode 300 d_4398_2, decode 300 d_4398_3, decode 300 d_4398_4, decode 300 d_4398_5, decode 300 d_4398_6, decode 142 d_4398_7] (fun x hx => bits_full_and hx) cov_4398 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4398_0, ch_4398_1, ch_4398_2, ch_4398_3, ch_4398_4, ch_4398_5, ch_4398_6, ch_4398_7])

theorem root_4399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4399_0, decode 300 d_4399_1, decode 300 d_4399_2, decode 300 d_4399_3, decode 300 d_4399_4, decode 300 d_4399_5, decode 300 d_4399_6, decode 142 d_4399_7] (fun x hx => bits_full_and hx) cov_4399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4399_0, ch_4399_1, ch_4399_2, ch_4399_3, ch_4399_4, ch_4399_5, ch_4399_6, ch_4399_7])

theorem root_4401 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4401) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4401_0, decode 300 d_4401_1, decode 300 d_4401_2, decode 300 d_4401_3, decode 300 d_4401_4, decode 300 d_4401_5, decode 300 d_4401_6, decode 142 d_4401_7] (fun x hx => bits_full_and hx) cov_4401 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4401_0, ch_4401_1, ch_4401_2, ch_4401_3, ch_4401_4, ch_4401_5, ch_4401_6, ch_4401_7])

theorem root_4413 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4413) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4413_0, decode 300 d_4413_1, decode 300 d_4413_2, decode 300 d_4413_3, decode 300 d_4413_4, decode 300 d_4413_5, decode 48 d_4413_6] (fun x hx => bits_full_and hx) cov_4413 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4413_0, ch_4413_1, ch_4413_2, ch_4413_3, ch_4413_4, ch_4413_5, ch_4413_6])

theorem root_4414 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4414) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4414_0, decode 300 d_4414_1, decode 300 d_4414_2, decode 300 d_4414_3, decode 300 d_4414_4, decode 300 d_4414_5, decode 48 d_4414_6] (fun x hx => bits_full_and hx) cov_4414 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4414_0, ch_4414_1, ch_4414_2, ch_4414_3, ch_4414_4, ch_4414_5, ch_4414_6])

theorem root_4415 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4415) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4415_0, decode 300 d_4415_1, decode 300 d_4415_2, decode 300 d_4415_3, decode 300 d_4415_4, decode 300 d_4415_5, decode 43 d_4415_6] (fun x hx => bits_full_and hx) cov_4415 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4415_0, ch_4415_1, ch_4415_2, ch_4415_3, ch_4415_4, ch_4415_5, ch_4415_6])

theorem roots_65_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_65, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_65, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4351 hB hC hCl hCB, root_4352 hB hC hCl hCB, root_4353 hB hC hCl hCB, root_4356 hB hC hCl hCB, root_4357 hB hC hCl hCB, root_4359 hB hC hCl hCB, root_4372 hB hC hCl hCB, root_4377 hB hC hCl hCB, root_4378 hB hC hCl hCB, root_4379 hB hC hCl hCB, root_4385 hB hC hCl hCB, root_4386 hB hC hCl hCB, root_4387 hB hC hCl hCB, root_4396 hB hC hCl hCB, root_4398 hB hC hCl hCB, root_4399 hB hC hCl hCB, root_4401 hB hC hCl hCB, root_4413 hB hC hCl hCB, root_4414 hB hC hCl hCB, root_4415 hB hC hCl hCB]

theorem root_4419 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4419) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4419_0, decode 300 d_4419_1, decode 300 d_4419_2, decode 300 d_4419_3, decode 300 d_4419_4, decode 300 d_4419_5, decode 48 d_4419_6] (fun x hx => bits_full_and hx) cov_4419 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4419_0, ch_4419_1, ch_4419_2, ch_4419_3, ch_4419_4, ch_4419_5, ch_4419_6])

theorem root_4420 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4420) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4420_0, decode 300 d_4420_1, decode 300 d_4420_2, decode 300 d_4420_3, decode 300 d_4420_4, decode 300 d_4420_5, decode 48 d_4420_6] (fun x hx => bits_full_and hx) cov_4420 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4420_0, ch_4420_1, ch_4420_2, ch_4420_3, ch_4420_4, ch_4420_5, ch_4420_6])

theorem root_4421 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4421) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4421_0, decode 300 d_4421_1, decode 300 d_4421_2, decode 300 d_4421_3, decode 300 d_4421_4, decode 286 d_4421_5] (fun x hx => bits_full_and hx) cov_4421 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4421_0, ch_4421_1, ch_4421_2, ch_4421_3, ch_4421_4, ch_4421_5])

theorem root_4427 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4427) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4427_0, decode 300 d_4427_1, decode 300 d_4427_2, decode 300 d_4427_3, decode 300 d_4427_4, decode 300 d_4427_5, decode 300 d_4427_6, decode 142 d_4427_7] (fun x hx => bits_full_and hx) cov_4427 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4427_0, ch_4427_1, ch_4427_2, ch_4427_3, ch_4427_4, ch_4427_5, ch_4427_6, ch_4427_7])

theorem root_4438 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4438) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4438_0, decode 300 d_4438_1, decode 300 d_4438_2, decode 300 d_4438_3, decode 300 d_4438_4, decode 300 d_4438_5, decode 300 d_4438_6, decode 141 d_4438_7] (fun x hx => bits_full_and hx) cov_4438 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4438_0, ch_4438_1, ch_4438_2, ch_4438_3, ch_4438_4, ch_4438_5, ch_4438_6, ch_4438_7])

theorem root_4439 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4439) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4439_0, decode 300 d_4439_1, decode 300 d_4439_2, decode 300 d_4439_3, decode 300 d_4439_4, decode 300 d_4439_5, decode 300 d_4439_6, decode 142 d_4439_7] (fun x hx => bits_full_and hx) cov_4439 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4439_0, ch_4439_1, ch_4439_2, ch_4439_3, ch_4439_4, ch_4439_5, ch_4439_6, ch_4439_7])

theorem root_4447 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4447) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4447_0, decode 300 d_4447_1, decode 300 d_4447_2, decode 300 d_4447_3, decode 300 d_4447_4, decode 300 d_4447_5, decode 300 d_4447_6, decode 141 d_4447_7] (fun x hx => bits_full_and hx) cov_4447 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4447_0, ch_4447_1, ch_4447_2, ch_4447_3, ch_4447_4, ch_4447_5, ch_4447_6, ch_4447_7])

theorem root_4448 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4448) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4448_0, decode 300 d_4448_1, decode 300 d_4448_2, decode 300 d_4448_3, decode 300 d_4448_4, decode 300 d_4448_5, decode 300 d_4448_6, decode 141 d_4448_7] (fun x hx => bits_full_and hx) cov_4448 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4448_0, ch_4448_1, ch_4448_2, ch_4448_3, ch_4448_4, ch_4448_5, ch_4448_6, ch_4448_7])

theorem root_4449 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4449) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4449_0, decode 300 d_4449_1, decode 300 d_4449_2, decode 300 d_4449_3, decode 300 d_4449_4, decode 300 d_4449_5, decode 300 d_4449_6, decode 141 d_4449_7] (fun x hx => bits_full_and hx) cov_4449 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4449_0, ch_4449_1, ch_4449_2, ch_4449_3, ch_4449_4, ch_4449_5, ch_4449_6, ch_4449_7])

theorem root_4450 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4450) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4450_0, decode 300 d_4450_1, decode 300 d_4450_2, decode 300 d_4450_3, decode 300 d_4450_4, decode 300 d_4450_5, decode 300 d_4450_6, decode 163 d_4450_7] (fun x hx => bits_full_and hx) cov_4450 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4450_0, ch_4450_1, ch_4450_2, ch_4450_3, ch_4450_4, ch_4450_5, ch_4450_6, ch_4450_7])

theorem root_4456 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4456) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4456_0, decode 300 d_4456_1, decode 300 d_4456_2, decode 300 d_4456_3, decode 300 d_4456_4, decode 300 d_4456_5, decode 300 d_4456_6, decode 141 d_4456_7] (fun x hx => bits_full_and hx) cov_4456 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4456_0, ch_4456_1, ch_4456_2, ch_4456_3, ch_4456_4, ch_4456_5, ch_4456_6, ch_4456_7])

theorem root_4457 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4457) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4457_0, decode 300 d_4457_1, decode 300 d_4457_2, decode 300 d_4457_3, decode 300 d_4457_4, decode 300 d_4457_5, decode 300 d_4457_6, decode 163 d_4457_7] (fun x hx => bits_full_and hx) cov_4457 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4457_0, ch_4457_1, ch_4457_2, ch_4457_3, ch_4457_4, ch_4457_5, ch_4457_6, ch_4457_7])

theorem root_4465 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4465) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4465_0, decode 300 d_4465_1, decode 300 d_4465_2, decode 300 d_4465_3, decode 300 d_4465_4, decode 300 d_4465_5, decode 300 d_4465_6, decode 163 d_4465_7] (fun x hx => bits_full_and hx) cov_4465 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4465_0, ch_4465_1, ch_4465_2, ch_4465_3, ch_4465_4, ch_4465_5, ch_4465_6, ch_4465_7])

theorem root_4471 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4471) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4471_0, decode 300 d_4471_1, decode 300 d_4471_2, decode 300 d_4471_3, decode 300 d_4471_4, decode 300 d_4471_5, decode 300 d_4471_6, decode 141 d_4471_7] (fun x hx => bits_full_and hx) cov_4471 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4471_0, ch_4471_1, ch_4471_2, ch_4471_3, ch_4471_4, ch_4471_5, ch_4471_6, ch_4471_7])

theorem root_4472 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4472) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4472_0, decode 300 d_4472_1, decode 300 d_4472_2, decode 300 d_4472_3, decode 300 d_4472_4, decode 300 d_4472_5, decode 300 d_4472_6, decode 141 d_4472_7] (fun x hx => bits_full_and hx) cov_4472 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4472_0, ch_4472_1, ch_4472_2, ch_4472_3, ch_4472_4, ch_4472_5, ch_4472_6, ch_4472_7])

theorem root_4478 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4478) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4478_0, decode 300 d_4478_1, decode 300 d_4478_2, decode 300 d_4478_3, decode 300 d_4478_4, decode 300 d_4478_5, decode 300 d_4478_6, decode 141 d_4478_7] (fun x hx => bits_full_and hx) cov_4478 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4478_0, ch_4478_1, ch_4478_2, ch_4478_3, ch_4478_4, ch_4478_5, ch_4478_6, ch_4478_7])

theorem root_4479 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4479) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4479_0, decode 300 d_4479_1, decode 300 d_4479_2, decode 300 d_4479_3, decode 300 d_4479_4, decode 300 d_4479_5, decode 300 d_4479_6, decode 141 d_4479_7] (fun x hx => bits_full_and hx) cov_4479 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4479_0, ch_4479_1, ch_4479_2, ch_4479_3, ch_4479_4, ch_4479_5, ch_4479_6, ch_4479_7])

theorem root_4480 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4480) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4480_0, decode 300 d_4480_1, decode 300 d_4480_2, decode 300 d_4480_3, decode 300 d_4480_4, decode 300 d_4480_5, decode 300 d_4480_6, decode 141 d_4480_7] (fun x hx => bits_full_and hx) cov_4480 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4480_0, ch_4480_1, ch_4480_2, ch_4480_3, ch_4480_4, ch_4480_5, ch_4480_6, ch_4480_7])

theorem root_4487 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4487) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4487_0, decode 300 d_4487_1, decode 300 d_4487_2, decode 300 d_4487_3, decode 300 d_4487_4, decode 300 d_4487_5, decode 300 d_4487_6, decode 141 d_4487_7] (fun x hx => bits_full_and hx) cov_4487 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4487_0, ch_4487_1, ch_4487_2, ch_4487_3, ch_4487_4, ch_4487_5, ch_4487_6, ch_4487_7])

theorem roots_66_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_66, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_66, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4419 hB hC hCl hCB, root_4420 hB hC hCl hCB, root_4421 hB hC hCl hCB, root_4427 hB hC hCl hCB, root_4438 hB hC hCl hCB, root_4439 hB hC hCl hCB, root_4447 hB hC hCl hCB, root_4448 hB hC hCl hCB, root_4449 hB hC hCl hCB, root_4450 hB hC hCl hCB, root_4456 hB hC hCl hCB, root_4457 hB hC hCl hCB, root_4465 hB hC hCl hCB, root_4471 hB hC hCl hCB, root_4472 hB hC hCl hCB, root_4478 hB hC hCl hCB, root_4479 hB hC hCl hCB, root_4480 hB hC hCl hCB, root_4487 hB hC hCl hCB]

theorem root_4488 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4488) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4488_0, decode 300 d_4488_1, decode 300 d_4488_2, decode 300 d_4488_3, decode 300 d_4488_4, decode 300 d_4488_5, decode 300 d_4488_6, decode 141 d_4488_7] (fun x hx => bits_full_and hx) cov_4488 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4488_0, ch_4488_1, ch_4488_2, ch_4488_3, ch_4488_4, ch_4488_5, ch_4488_6, ch_4488_7])

theorem root_4490 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4490) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4490_0, decode 300 d_4490_1, decode 300 d_4490_2, decode 300 d_4490_3, decode 300 d_4490_4, decode 300 d_4490_5, decode 300 d_4490_6, decode 141 d_4490_7] (fun x hx => bits_full_and hx) cov_4490 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4490_0, ch_4490_1, ch_4490_2, ch_4490_3, ch_4490_4, ch_4490_5, ch_4490_6, ch_4490_7])

theorem root_4491 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4491) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4491_0, decode 300 d_4491_1, decode 300 d_4491_2, decode 300 d_4491_3, decode 300 d_4491_4, decode 300 d_4491_5, decode 300 d_4491_6, decode 141 d_4491_7] (fun x hx => bits_full_and hx) cov_4491 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4491_0, ch_4491_1, ch_4491_2, ch_4491_3, ch_4491_4, ch_4491_5, ch_4491_6, ch_4491_7])

theorem root_4497 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4497) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4497_0, decode 300 d_4497_1, decode 300 d_4497_2, decode 300 d_4497_3, decode 300 d_4497_4, decode 300 d_4497_5, decode 300 d_4497_6, decode 141 d_4497_7] (fun x hx => bits_full_and hx) cov_4497 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4497_0, ch_4497_1, ch_4497_2, ch_4497_3, ch_4497_4, ch_4497_5, ch_4497_6, ch_4497_7])

theorem root_4498 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4498) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4498_0, decode 300 d_4498_1, decode 300 d_4498_2, decode 300 d_4498_3, decode 300 d_4498_4, decode 300 d_4498_5, decode 300 d_4498_6, decode 141 d_4498_7] (fun x hx => bits_full_and hx) cov_4498 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4498_0, ch_4498_1, ch_4498_2, ch_4498_3, ch_4498_4, ch_4498_5, ch_4498_6, ch_4498_7])

theorem root_4500 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4500) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4500_0, decode 300 d_4500_1, decode 300 d_4500_2, decode 300 d_4500_3, decode 300 d_4500_4, decode 300 d_4500_5, decode 300 d_4500_6, decode 141 d_4500_7] (fun x hx => bits_full_and hx) cov_4500 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4500_0, ch_4500_1, ch_4500_2, ch_4500_3, ch_4500_4, ch_4500_5, ch_4500_6, ch_4500_7])

theorem root_4505 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4505) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4505_0, decode 300 d_4505_1, decode 300 d_4505_2, decode 300 d_4505_3, decode 300 d_4505_4, decode 300 d_4505_5, decode 300 d_4505_6, decode 141 d_4505_7] (fun x hx => bits_full_and hx) cov_4505 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4505_0, ch_4505_1, ch_4505_2, ch_4505_3, ch_4505_4, ch_4505_5, ch_4505_6, ch_4505_7])

theorem root_4508 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4508) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4508_0, decode 300 d_4508_1, decode 300 d_4508_2, decode 300 d_4508_3, decode 300 d_4508_4, decode 300 d_4508_5, decode 300 d_4508_6, decode 141 d_4508_7] (fun x hx => bits_full_and hx) cov_4508 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4508_0, ch_4508_1, ch_4508_2, ch_4508_3, ch_4508_4, ch_4508_5, ch_4508_6, ch_4508_7])

theorem root_4517 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4517) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4517_0, decode 300 d_4517_1, decode 300 d_4517_2, decode 300 d_4517_3, decode 300 d_4517_4, decode 300 d_4517_5, decode 300 d_4517_6, decode 141 d_4517_7] (fun x hx => bits_full_and hx) cov_4517 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4517_0, ch_4517_1, ch_4517_2, ch_4517_3, ch_4517_4, ch_4517_5, ch_4517_6, ch_4517_7])

theorem root_4518 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4518) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4518_0, decode 300 d_4518_1, decode 300 d_4518_2, decode 300 d_4518_3, decode 300 d_4518_4, decode 300 d_4518_5, decode 300 d_4518_6, decode 141 d_4518_7] (fun x hx => bits_full_and hx) cov_4518 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4518_0, ch_4518_1, ch_4518_2, ch_4518_3, ch_4518_4, ch_4518_5, ch_4518_6, ch_4518_7])

theorem root_4519 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4519) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4519_0, decode 300 d_4519_1, decode 300 d_4519_2, decode 300 d_4519_3, decode 300 d_4519_4, decode 300 d_4519_5, decode 300 d_4519_6, decode 141 d_4519_7] (fun x hx => bits_full_and hx) cov_4519 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4519_0, ch_4519_1, ch_4519_2, ch_4519_3, ch_4519_4, ch_4519_5, ch_4519_6, ch_4519_7])

theorem root_4520 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4520) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4520_0, decode 300 d_4520_1, decode 300 d_4520_2, decode 300 d_4520_3, decode 300 d_4520_4, decode 300 d_4520_5, decode 300 d_4520_6, decode 141 d_4520_7] (fun x hx => bits_full_and hx) cov_4520 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4520_0, ch_4520_1, ch_4520_2, ch_4520_3, ch_4520_4, ch_4520_5, ch_4520_6, ch_4520_7])

theorem root_4527 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4527) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4527_0, decode 300 d_4527_1, decode 300 d_4527_2, decode 300 d_4527_3, decode 300 d_4527_4, decode 300 d_4527_5, decode 300 d_4527_6, decode 141 d_4527_7] (fun x hx => bits_full_and hx) cov_4527 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4527_0, ch_4527_1, ch_4527_2, ch_4527_3, ch_4527_4, ch_4527_5, ch_4527_6, ch_4527_7])

theorem root_4528 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4528) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4528_0, decode 300 d_4528_1, decode 300 d_4528_2, decode 300 d_4528_3, decode 300 d_4528_4, decode 300 d_4528_5, decode 300 d_4528_6, decode 141 d_4528_7] (fun x hx => bits_full_and hx) cov_4528 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4528_0, ch_4528_1, ch_4528_2, ch_4528_3, ch_4528_4, ch_4528_5, ch_4528_6, ch_4528_7])

theorem root_4539 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4539) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4539_0, decode 300 d_4539_1, decode 300 d_4539_2, decode 300 d_4539_3, decode 300 d_4539_4, decode 300 d_4539_5, decode 300 d_4539_6, decode 141 d_4539_7] (fun x hx => bits_full_and hx) cov_4539 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4539_0, ch_4539_1, ch_4539_2, ch_4539_3, ch_4539_4, ch_4539_5, ch_4539_6, ch_4539_7])

theorem root_4547 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4547) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4547_0, decode 300 d_4547_1, decode 300 d_4547_2, decode 300 d_4547_3, decode 300 d_4547_4, decode 300 d_4547_5, decode 300 d_4547_6, decode 141 d_4547_7] (fun x hx => bits_full_and hx) cov_4547 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4547_0, ch_4547_1, ch_4547_2, ch_4547_3, ch_4547_4, ch_4547_5, ch_4547_6, ch_4547_7])

theorem root_4552 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4552) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4552_0, decode 300 d_4552_1, decode 300 d_4552_2, decode 300 d_4552_3, decode 300 d_4552_4, decode 300 d_4552_5, decode 107 d_4552_6] (fun x hx => bits_full_and hx) cov_4552 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4552_0, ch_4552_1, ch_4552_2, ch_4552_3, ch_4552_4, ch_4552_5, ch_4552_6])

theorem root_4553 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4553) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4553_0, decode 300 d_4553_1, decode 300 d_4553_2, decode 300 d_4553_3, decode 300 d_4553_4, decode 300 d_4553_5, decode 300 d_4553_6, decode 141 d_4553_7] (fun x hx => bits_full_and hx) cov_4553 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4553_0, ch_4553_1, ch_4553_2, ch_4553_3, ch_4553_4, ch_4553_5, ch_4553_6, ch_4553_7])

theorem roots_67_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_67, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_67, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4488 hB hC hCl hCB, root_4490 hB hC hCl hCB, root_4491 hB hC hCl hCB, root_4497 hB hC hCl hCB, root_4498 hB hC hCl hCB, root_4500 hB hC hCl hCB, root_4505 hB hC hCl hCB, root_4508 hB hC hCl hCB, root_4517 hB hC hCl hCB, root_4518 hB hC hCl hCB, root_4519 hB hC hCl hCB, root_4520 hB hC hCl hCB, root_4527 hB hC hCl hCB, root_4528 hB hC hCl hCB, root_4539 hB hC hCl hCB, root_4547 hB hC hCl hCB, root_4552 hB hC hCl hCB, root_4553 hB hC hCl hCB]

theorem root_4554 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4554) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4554_0, decode 300 d_4554_1, decode 300 d_4554_2, decode 300 d_4554_3, decode 300 d_4554_4, decode 300 d_4554_5, decode 300 d_4554_6, decode 141 d_4554_7] (fun x hx => bits_full_and hx) cov_4554 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4554_0, ch_4554_1, ch_4554_2, ch_4554_3, ch_4554_4, ch_4554_5, ch_4554_6, ch_4554_7])

theorem root_4560 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4560) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4560_0, decode 300 d_4560_1, decode 300 d_4560_2, decode 300 d_4560_3, decode 300 d_4560_4, decode 300 d_4560_5, decode 22 d_4560_6] (fun x hx => bits_full_and hx) cov_4560 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4560_0, ch_4560_1, ch_4560_2, ch_4560_3, ch_4560_4, ch_4560_5, ch_4560_6])

theorem root_4567 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4567) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4567_0, decode 300 d_4567_1, decode 300 d_4567_2, decode 300 d_4567_3, decode 300 d_4567_4, decode 300 d_4567_5, decode 300 d_4567_6, decode 141 d_4567_7] (fun x hx => bits_full_and hx) cov_4567 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4567_0, ch_4567_1, ch_4567_2, ch_4567_3, ch_4567_4, ch_4567_5, ch_4567_6, ch_4567_7])

theorem root_4568 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4568) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4568_0, decode 300 d_4568_1, decode 300 d_4568_2, decode 300 d_4568_3, decode 300 d_4568_4, decode 300 d_4568_5, decode 300 d_4568_6, decode 141 d_4568_7] (fun x hx => bits_full_and hx) cov_4568 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4568_0, ch_4568_1, ch_4568_2, ch_4568_3, ch_4568_4, ch_4568_5, ch_4568_6, ch_4568_7])

theorem root_4569 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4569) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4569_0, decode 300 d_4569_1, decode 300 d_4569_2, decode 300 d_4569_3, decode 300 d_4569_4, decode 300 d_4569_5, decode 300 d_4569_6, decode 142 d_4569_7] (fun x hx => bits_full_and hx) cov_4569 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4569_0, ch_4569_1, ch_4569_2, ch_4569_3, ch_4569_4, ch_4569_5, ch_4569_6, ch_4569_7])

theorem root_4570 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4570) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4570_0, decode 300 d_4570_1, decode 300 d_4570_2, decode 300 d_4570_3, decode 300 d_4570_4, decode 300 d_4570_5, decode 300 d_4570_6, decode 142 d_4570_7] (fun x hx => bits_full_and hx) cov_4570 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4570_0, ch_4570_1, ch_4570_2, ch_4570_3, ch_4570_4, ch_4570_5, ch_4570_6, ch_4570_7])

theorem root_4575 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4575) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4575_0, decode 300 d_4575_1, decode 300 d_4575_2, decode 300 d_4575_3, decode 300 d_4575_4, decode 300 d_4575_5, decode 300 d_4575_6, decode 141 d_4575_7] (fun x hx => bits_full_and hx) cov_4575 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4575_0, ch_4575_1, ch_4575_2, ch_4575_3, ch_4575_4, ch_4575_5, ch_4575_6, ch_4575_7])

theorem root_4577 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4577) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4577_0, decode 300 d_4577_1, decode 300 d_4577_2, decode 300 d_4577_3, decode 300 d_4577_4, decode 300 d_4577_5, decode 300 d_4577_6, decode 141 d_4577_7] (fun x hx => bits_full_and hx) cov_4577 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4577_0, ch_4577_1, ch_4577_2, ch_4577_3, ch_4577_4, ch_4577_5, ch_4577_6, ch_4577_7])

theorem root_4581 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4581) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4581_0, decode 300 d_4581_1, decode 300 d_4581_2, decode 300 d_4581_3, decode 300 d_4581_4, decode 300 d_4581_5, decode 300 d_4581_6, decode 141 d_4581_7] (fun x hx => bits_full_and hx) cov_4581 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4581_0, ch_4581_1, ch_4581_2, ch_4581_3, ch_4581_4, ch_4581_5, ch_4581_6, ch_4581_7])

theorem root_4584 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4584) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4584_0, decode 300 d_4584_1, decode 300 d_4584_2, decode 300 d_4584_3, decode 300 d_4584_4, decode 300 d_4584_5, decode 300 d_4584_6, decode 141 d_4584_7] (fun x hx => bits_full_and hx) cov_4584 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4584_0, ch_4584_1, ch_4584_2, ch_4584_3, ch_4584_4, ch_4584_5, ch_4584_6, ch_4584_7])

theorem root_4585 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4585) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4585_0, decode 300 d_4585_1, decode 300 d_4585_2, decode 300 d_4585_3, decode 300 d_4585_4, decode 300 d_4585_5, decode 300 d_4585_6, decode 141 d_4585_7] (fun x hx => bits_full_and hx) cov_4585 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4585_0, ch_4585_1, ch_4585_2, ch_4585_3, ch_4585_4, ch_4585_5, ch_4585_6, ch_4585_7])

theorem root_4597 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4597) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4597_0, decode 300 d_4597_1, decode 300 d_4597_2, decode 300 d_4597_3, decode 300 d_4597_4, decode 300 d_4597_5, decode 266 d_4597_6] (fun x hx => bits_full_and hx) cov_4597 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4597_0, ch_4597_1, ch_4597_2, ch_4597_3, ch_4597_4, ch_4597_5, ch_4597_6])

theorem root_4599 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4599) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4599_0, decode 300 d_4599_1, decode 300 d_4599_2, decode 300 d_4599_3, decode 300 d_4599_4, decode 286 d_4599_5] (fun x hx => bits_full_and hx) cov_4599 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4599_0, ch_4599_1, ch_4599_2, ch_4599_3, ch_4599_4, ch_4599_5])

theorem root_4600 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4600) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4600_0, decode 300 d_4600_1, decode 300 d_4600_2, decode 300 d_4600_3, decode 300 d_4600_4, decode 300 d_4600_5, decode 266 d_4600_6] (fun x hx => bits_full_and hx) cov_4600 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4600_0, ch_4600_1, ch_4600_2, ch_4600_3, ch_4600_4, ch_4600_5, ch_4600_6])

theorem root_4603 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4603) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4603_0, decode 300 d_4603_1, decode 300 d_4603_2, decode 300 d_4603_3, decode 300 d_4603_4, decode 300 d_4603_5, decode 190 d_4603_6] (fun x hx => bits_full_and hx) cov_4603 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4603_0, ch_4603_1, ch_4603_2, ch_4603_3, ch_4603_4, ch_4603_5, ch_4603_6])

theorem root_4605 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4605) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4605_0, decode 300 d_4605_1, decode 300 d_4605_2, decode 300 d_4605_3, decode 300 d_4605_4, decode 286 d_4605_5] (fun x hx => bits_full_and hx) cov_4605 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4605_0, ch_4605_1, ch_4605_2, ch_4605_3, ch_4605_4, ch_4605_5])

theorem root_4606 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4606) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4606_0, decode 300 d_4606_1, decode 300 d_4606_2, decode 300 d_4606_3, decode 300 d_4606_4, decode 286 d_4606_5] (fun x hx => bits_full_and hx) cov_4606 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4606_0, ch_4606_1, ch_4606_2, ch_4606_3, ch_4606_4, ch_4606_5])

theorem root_4610 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4610) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4610_0, decode 300 d_4610_1, decode 300 d_4610_2, decode 300 d_4610_3, decode 300 d_4610_4, decode 300 d_4610_5, decode 190 d_4610_6] (fun x hx => bits_full_and hx) cov_4610 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4610_0, ch_4610_1, ch_4610_2, ch_4610_3, ch_4610_4, ch_4610_5, ch_4610_6])

theorem root_4613 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4613) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4613_0, decode 300 d_4613_1, decode 300 d_4613_2, decode 300 d_4613_3, decode 300 d_4613_4, decode 300 d_4613_5, decode 100 d_4613_6] (fun x hx => bits_full_and hx) cov_4613 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4613_0, ch_4613_1, ch_4613_2, ch_4613_3, ch_4613_4, ch_4613_5, ch_4613_6])

theorem root_4620 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4620) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4620_0, decode 300 d_4620_1, decode 300 d_4620_2, decode 300 d_4620_3, decode 300 d_4620_4, decode 300 d_4620_5, decode 300 d_4620_6, decode 142 d_4620_7] (fun x hx => bits_full_and hx) cov_4620 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4620_0, ch_4620_1, ch_4620_2, ch_4620_3, ch_4620_4, ch_4620_5, ch_4620_6, ch_4620_7])

theorem roots_68_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_68, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_68, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4554 hB hC hCl hCB, root_4560 hB hC hCl hCB, root_4567 hB hC hCl hCB, root_4568 hB hC hCl hCB, root_4569 hB hC hCl hCB, root_4570 hB hC hCl hCB, root_4575 hB hC hCl hCB, root_4577 hB hC hCl hCB, root_4581 hB hC hCl hCB, root_4584 hB hC hCl hCB, root_4585 hB hC hCl hCB, root_4597 hB hC hCl hCB, root_4599 hB hC hCl hCB, root_4600 hB hC hCl hCB, root_4603 hB hC hCl hCB, root_4605 hB hC hCl hCB, root_4606 hB hC hCl hCB, root_4610 hB hC hCl hCB, root_4613 hB hC hCl hCB, root_4620 hB hC hCl hCB]

theorem root_4622 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4622) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4622_0, decode 300 d_4622_1, decode 300 d_4622_2, decode 300 d_4622_3, decode 300 d_4622_4, decode 300 d_4622_5, decode 300 d_4622_6, decode 142 d_4622_7] (fun x hx => bits_full_and hx) cov_4622 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4622_0, ch_4622_1, ch_4622_2, ch_4622_3, ch_4622_4, ch_4622_5, ch_4622_6, ch_4622_7])

theorem root_4623 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4623) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4623_0, decode 300 d_4623_1, decode 300 d_4623_2, decode 300 d_4623_3, decode 300 d_4623_4, decode 300 d_4623_5, decode 300 d_4623_6, decode 141 d_4623_7] (fun x hx => bits_full_and hx) cov_4623 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4623_0, ch_4623_1, ch_4623_2, ch_4623_3, ch_4623_4, ch_4623_5, ch_4623_6, ch_4623_7])

theorem root_4633 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4633) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4633_0, decode 300 d_4633_1, decode 300 d_4633_2, decode 300 d_4633_3, decode 300 d_4633_4, decode 300 d_4633_5, decode 300 d_4633_6, decode 141 d_4633_7] (fun x hx => bits_full_and hx) cov_4633 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4633_0, ch_4633_1, ch_4633_2, ch_4633_3, ch_4633_4, ch_4633_5, ch_4633_6, ch_4633_7])

theorem root_4634 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4634) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4634_0, decode 300 d_4634_1, decode 300 d_4634_2, decode 300 d_4634_3, decode 300 d_4634_4, decode 300 d_4634_5, decode 300 d_4634_6, decode 141 d_4634_7] (fun x hx => bits_full_and hx) cov_4634 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4634_0, ch_4634_1, ch_4634_2, ch_4634_3, ch_4634_4, ch_4634_5, ch_4634_6, ch_4634_7])

theorem root_4635 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4635) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4635_0, decode 300 d_4635_1, decode 300 d_4635_2, decode 300 d_4635_3, decode 300 d_4635_4, decode 300 d_4635_5, decode 300 d_4635_6, decode 141 d_4635_7] (fun x hx => bits_full_and hx) cov_4635 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4635_0, ch_4635_1, ch_4635_2, ch_4635_3, ch_4635_4, ch_4635_5, ch_4635_6, ch_4635_7])

theorem root_4636 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4636) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4636_0, decode 300 d_4636_1, decode 300 d_4636_2, decode 300 d_4636_3, decode 300 d_4636_4, decode 300 d_4636_5, decode 300 d_4636_6, decode 142 d_4636_7] (fun x hx => bits_full_and hx) cov_4636 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4636_0, ch_4636_1, ch_4636_2, ch_4636_3, ch_4636_4, ch_4636_5, ch_4636_6, ch_4636_7])

theorem root_4645 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4645) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4645_0, decode 300 d_4645_1, decode 300 d_4645_2, decode 300 d_4645_3, decode 300 d_4645_4, decode 300 d_4645_5, decode 300 d_4645_6, decode 141 d_4645_7] (fun x hx => bits_full_and hx) cov_4645 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4645_0, ch_4645_1, ch_4645_2, ch_4645_3, ch_4645_4, ch_4645_5, ch_4645_6, ch_4645_7])

theorem root_4646 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4646) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4646_0, decode 300 d_4646_1, decode 300 d_4646_2, decode 300 d_4646_3, decode 300 d_4646_4, decode 300 d_4646_5, decode 300 d_4646_6, decode 142 d_4646_7] (fun x hx => bits_full_and hx) cov_4646 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4646_0, ch_4646_1, ch_4646_2, ch_4646_3, ch_4646_4, ch_4646_5, ch_4646_6, ch_4646_7])

theorem root_4647 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4647) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4647_0, decode 300 d_4647_1, decode 300 d_4647_2, decode 300 d_4647_3, decode 300 d_4647_4, decode 300 d_4647_5, decode 300 d_4647_6, decode 142 d_4647_7] (fun x hx => bits_full_and hx) cov_4647 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4647_0, ch_4647_1, ch_4647_2, ch_4647_3, ch_4647_4, ch_4647_5, ch_4647_6, ch_4647_7])

theorem root_4651 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4651) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4651_0, decode 300 d_4651_1, decode 300 d_4651_2, decode 300 d_4651_3, decode 300 d_4651_4, decode 300 d_4651_5, decode 300 d_4651_6, decode 141 d_4651_7] (fun x hx => bits_full_and hx) cov_4651 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4651_0, ch_4651_1, ch_4651_2, ch_4651_3, ch_4651_4, ch_4651_5, ch_4651_6, ch_4651_7])

theorem root_4652 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4652) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4652_0, decode 300 d_4652_1, decode 300 d_4652_2, decode 300 d_4652_3, decode 300 d_4652_4, decode 300 d_4652_5, decode 300 d_4652_6, decode 141 d_4652_7] (fun x hx => bits_full_and hx) cov_4652 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4652_0, ch_4652_1, ch_4652_2, ch_4652_3, ch_4652_4, ch_4652_5, ch_4652_6, ch_4652_7])

theorem root_4655 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4655) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4655_0, decode 300 d_4655_1, decode 300 d_4655_2, decode 300 d_4655_3, decode 300 d_4655_4, decode 300 d_4655_5, decode 300 d_4655_6, decode 141 d_4655_7] (fun x hx => bits_full_and hx) cov_4655 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4655_0, ch_4655_1, ch_4655_2, ch_4655_3, ch_4655_4, ch_4655_5, ch_4655_6, ch_4655_7])

theorem root_4656 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4656) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4656_0, decode 300 d_4656_1, decode 300 d_4656_2, decode 300 d_4656_3, decode 300 d_4656_4, decode 300 d_4656_5, decode 300 d_4656_6, decode 141 d_4656_7] (fun x hx => bits_full_and hx) cov_4656 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4656_0, ch_4656_1, ch_4656_2, ch_4656_3, ch_4656_4, ch_4656_5, ch_4656_6, ch_4656_7])

theorem root_4663 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4663) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4663_0, decode 300 d_4663_1, decode 300 d_4663_2, decode 300 d_4663_3, decode 300 d_4663_4, decode 300 d_4663_5, decode 22 d_4663_6] (fun x hx => bits_full_and hx) cov_4663 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4663_0, ch_4663_1, ch_4663_2, ch_4663_3, ch_4663_4, ch_4663_5, ch_4663_6])

theorem root_4668 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4668) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4668_0, decode 300 d_4668_1, decode 300 d_4668_2, decode 300 d_4668_3, decode 300 d_4668_4, decode 300 d_4668_5, decode 93 d_4668_6] (fun x hx => bits_full_and hx) cov_4668 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4668_0, ch_4668_1, ch_4668_2, ch_4668_3, ch_4668_4, ch_4668_5, ch_4668_6])

theorem root_4670 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4670) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4670_0, decode 300 d_4670_1, decode 300 d_4670_2, decode 300 d_4670_3, decode 300 d_4670_4, decode 300 d_4670_5, decode 12 d_4670_6] (fun x hx => bits_full_and hx) cov_4670 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4670_0, ch_4670_1, ch_4670_2, ch_4670_3, ch_4670_4, ch_4670_5, ch_4670_6])

theorem root_4675 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4675) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4675_0, decode 300 d_4675_1, decode 300 d_4675_2, decode 300 d_4675_3, decode 300 d_4675_4, decode 300 d_4675_5, decode 80 d_4675_6] (fun x hx => bits_full_and hx) cov_4675 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4675_0, ch_4675_1, ch_4675_2, ch_4675_3, ch_4675_4, ch_4675_5, ch_4675_6])

theorem root_4682 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4682) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4682_0, decode 300 d_4682_1, decode 300 d_4682_2, decode 300 d_4682_3, decode 300 d_4682_4, decode 300 d_4682_5, decode 93 d_4682_6] (fun x hx => bits_full_and hx) cov_4682 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4682_0, ch_4682_1, ch_4682_2, ch_4682_3, ch_4682_4, ch_4682_5, ch_4682_6])

theorem root_4683 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4683) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4683_0, decode 300 d_4683_1, decode 300 d_4683_2, decode 300 d_4683_3, decode 300 d_4683_4, decode 300 d_4683_5, decode 93 d_4683_6] (fun x hx => bits_full_and hx) cov_4683 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4683_0, ch_4683_1, ch_4683_2, ch_4683_3, ch_4683_4, ch_4683_5, ch_4683_6])

theorem roots_69_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_69, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_69, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4622 hB hC hCl hCB, root_4623 hB hC hCl hCB, root_4633 hB hC hCl hCB, root_4634 hB hC hCl hCB, root_4635 hB hC hCl hCB, root_4636 hB hC hCl hCB, root_4645 hB hC hCl hCB, root_4646 hB hC hCl hCB, root_4647 hB hC hCl hCB, root_4651 hB hC hCl hCB, root_4652 hB hC hCl hCB, root_4655 hB hC hCl hCB, root_4656 hB hC hCl hCB, root_4663 hB hC hCl hCB, root_4668 hB hC hCl hCB, root_4670 hB hC hCl hCB, root_4675 hB hC hCl hCB, root_4682 hB hC hCl hCB, root_4683 hB hC hCl hCB]

end LRC.O7U5
