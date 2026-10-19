import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C90N
import LonelyRunner.LRC.Spec.OrderSevenU5C91N
import LonelyRunner.LRC.Spec.OrderSevenU5C92N
import LonelyRunner.LRC.Spec.OrderSevenU5C93N
import LonelyRunner.LRC.Spec.OrderSevenU5C94N
import LonelyRunner.LRC.Spec.OrderSevenU5C95N
import LonelyRunner.LRC.Spec.OrderSevenU5C96N
import LonelyRunner.LRC.Spec.OrderSevenU5C97N
import LonelyRunner.LRC.Spec.OrderSevenU5C98N
import LonelyRunner.LRC.Spec.OrderSevenU5C99N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_5936 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5936) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5936_0, decode 300 d_5936_1, decode 300 d_5936_2, decode 300 d_5936_3, decode 300 d_5936_4, decode 300 d_5936_5, decode 24 d_5936_6] (fun x hx => bits_full_and hx) cov_5936 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5936_0, ch_5936_1, ch_5936_2, ch_5936_3, ch_5936_4, ch_5936_5, ch_5936_6])

theorem root_5939 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5939) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5939_0, decode 300 d_5939_1, decode 300 d_5939_2, decode 300 d_5939_3, decode 300 d_5939_4, decode 300 d_5939_5, decode 1 d_5939_6] (fun x hx => bits_full_and hx) cov_5939 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5939_0, ch_5939_1, ch_5939_2, ch_5939_3, ch_5939_4, ch_5939_5, ch_5939_6])

theorem root_5940 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5940) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5940_0, decode 300 d_5940_1, decode 300 d_5940_2, decode 300 d_5940_3, decode 300 d_5940_4, decode 300 d_5940_5, decode 24 d_5940_6] (fun x hx => bits_full_and hx) cov_5940 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5940_0, ch_5940_1, ch_5940_2, ch_5940_3, ch_5940_4, ch_5940_5, ch_5940_6])

theorem root_5950 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5950) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5950_0, decode 300 d_5950_1, decode 300 d_5950_2, decode 300 d_5950_3, decode 300 d_5950_4, decode 300 d_5950_5, decode 12 d_5950_6] (fun x hx => bits_full_and hx) cov_5950 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5950_0, ch_5950_1, ch_5950_2, ch_5950_3, ch_5950_4, ch_5950_5, ch_5950_6])

theorem root_5957 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5957) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5957_0, decode 300 d_5957_1, decode 300 d_5957_2, decode 300 d_5957_3, decode 300 d_5957_4, decode 300 d_5957_5, decode 300 d_5957_6, decode 141 d_5957_7] (fun x hx => bits_full_and hx) cov_5957 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5957_0, ch_5957_1, ch_5957_2, ch_5957_3, ch_5957_4, ch_5957_5, ch_5957_6, ch_5957_7])

theorem root_5959 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5959) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5959_0, decode 300 d_5959_1, decode 300 d_5959_2, decode 300 d_5959_3, decode 300 d_5959_4, decode 300 d_5959_5, decode 300 d_5959_6, decode 141 d_5959_7] (fun x hx => bits_full_and hx) cov_5959 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5959_0, ch_5959_1, ch_5959_2, ch_5959_3, ch_5959_4, ch_5959_5, ch_5959_6, ch_5959_7])

theorem root_5964 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5964) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5964_0, decode 300 d_5964_1, decode 300 d_5964_2, decode 300 d_5964_3, decode 300 d_5964_4, decode 300 d_5964_5, decode 300 d_5964_6, decode 141 d_5964_7] (fun x hx => bits_full_and hx) cov_5964 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5964_0, ch_5964_1, ch_5964_2, ch_5964_3, ch_5964_4, ch_5964_5, ch_5964_6, ch_5964_7])

theorem root_5968 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5968) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5968_0, decode 300 d_5968_1, decode 300 d_5968_2, decode 300 d_5968_3, decode 300 d_5968_4, decode 300 d_5968_5, decode 46 d_5968_6] (fun x hx => bits_full_and hx) cov_5968 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5968_0, ch_5968_1, ch_5968_2, ch_5968_3, ch_5968_4, ch_5968_5, ch_5968_6])

theorem root_5969 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5969) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5969_0, decode 300 d_5969_1, decode 300 d_5969_2, decode 300 d_5969_3, decode 300 d_5969_4, decode 300 d_5969_5, decode 46 d_5969_6] (fun x hx => bits_full_and hx) cov_5969 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5969_0, ch_5969_1, ch_5969_2, ch_5969_3, ch_5969_4, ch_5969_5, ch_5969_6])

theorem root_5970 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5970) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5970_0, decode 300 d_5970_1, decode 300 d_5970_2, decode 300 d_5970_3, decode 300 d_5970_4, decode 300 d_5970_5, decode 30 d_5970_6] (fun x hx => bits_full_and hx) cov_5970 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5970_0, ch_5970_1, ch_5970_2, ch_5970_3, ch_5970_4, ch_5970_5, ch_5970_6])

theorem root_5971 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5971) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5971_0, decode 300 d_5971_1, decode 300 d_5971_2, decode 300 d_5971_3, decode 300 d_5971_4, decode 300 d_5971_5, decode 30 d_5971_6] (fun x hx => bits_full_and hx) cov_5971 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5971_0, ch_5971_1, ch_5971_2, ch_5971_3, ch_5971_4, ch_5971_5, ch_5971_6])

theorem root_5980 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5980) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5980_0, decode 300 d_5980_1, decode 300 d_5980_2, decode 300 d_5980_3, decode 300 d_5980_4, decode 300 d_5980_5, decode 9 d_5980_6] (fun x hx => bits_full_and hx) cov_5980 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5980_0, ch_5980_1, ch_5980_2, ch_5980_3, ch_5980_4, ch_5980_5, ch_5980_6])

theorem root_5989 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5989) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5989_0, decode 300 d_5989_1, decode 300 d_5989_2, decode 300 d_5989_3, decode 300 d_5989_4, decode 300 d_5989_5, decode 46 d_5989_6] (fun x hx => bits_full_and hx) cov_5989 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5989_0, ch_5989_1, ch_5989_2, ch_5989_3, ch_5989_4, ch_5989_5, ch_5989_6])

theorem root_5990 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5990) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5990_0, decode 300 d_5990_1, decode 300 d_5990_2, decode 300 d_5990_3, decode 300 d_5990_4, decode 300 d_5990_5, decode 30 d_5990_6] (fun x hx => bits_full_and hx) cov_5990 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5990_0, ch_5990_1, ch_5990_2, ch_5990_3, ch_5990_4, ch_5990_5, ch_5990_6])

theorem root_6003 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6003) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6003_0, decode 300 d_6003_1, decode 300 d_6003_2, decode 300 d_6003_3, decode 300 d_6003_4, decode 300 d_6003_5, decode 300 d_6003_6, decode 141 d_6003_7] (fun x hx => bits_full_and hx) cov_6003 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6003_0, ch_6003_1, ch_6003_2, ch_6003_3, ch_6003_4, ch_6003_5, ch_6003_6, ch_6003_7])

theorem root_6019 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6019) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6019_0, decode 300 d_6019_1, decode 300 d_6019_2, decode 300 d_6019_3, decode 300 d_6019_4, decode 300 d_6019_5, decode 300 d_6019_6, decode 142 d_6019_7] (fun x hx => bits_full_and hx) cov_6019 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6019_0, ch_6019_1, ch_6019_2, ch_6019_3, ch_6019_4, ch_6019_5, ch_6019_6, ch_6019_7])

theorem root_6025 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6025) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6025_0, decode 300 d_6025_1, decode 300 d_6025_2, decode 300 d_6025_3, decode 300 d_6025_4, decode 300 d_6025_5, decode 300 d_6025_6, decode 141 d_6025_7] (fun x hx => bits_full_and hx) cov_6025 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6025_0, ch_6025_1, ch_6025_2, ch_6025_3, ch_6025_4, ch_6025_5, ch_6025_6, ch_6025_7])

theorem root_6026 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6026) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6026_0, decode 300 d_6026_1, decode 300 d_6026_2, decode 300 d_6026_3, decode 300 d_6026_4, decode 300 d_6026_5, decode 300 d_6026_6, decode 141 d_6026_7] (fun x hx => bits_full_and hx) cov_6026 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6026_0, ch_6026_1, ch_6026_2, ch_6026_3, ch_6026_4, ch_6026_5, ch_6026_6, ch_6026_7])

theorem root_6027 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6027) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6027_0, decode 300 d_6027_1, decode 300 d_6027_2, decode 300 d_6027_3, decode 300 d_6027_4, decode 300 d_6027_5, decode 300 d_6027_6, decode 141 d_6027_7] (fun x hx => bits_full_and hx) cov_6027 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6027_0, ch_6027_1, ch_6027_2, ch_6027_3, ch_6027_4, ch_6027_5, ch_6027_6, ch_6027_7])

theorem root_6033 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6033) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6033_0, decode 300 d_6033_1, decode 300 d_6033_2, decode 300 d_6033_3, decode 300 d_6033_4, decode 300 d_6033_5, decode 46 d_6033_6] (fun x hx => bits_full_and hx) cov_6033 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6033_0, ch_6033_1, ch_6033_2, ch_6033_3, ch_6033_4, ch_6033_5, ch_6033_6])

theorem root_6034 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6034) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6034_0, decode 300 d_6034_1, decode 300 d_6034_2, decode 300 d_6034_3, decode 300 d_6034_4, decode 300 d_6034_5, decode 46 d_6034_6] (fun x hx => bits_full_and hx) cov_6034 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6034_0, ch_6034_1, ch_6034_2, ch_6034_3, ch_6034_4, ch_6034_5, ch_6034_6])

theorem roots_90_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_90, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_90, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5936 hB hC hCl hCB, root_5939 hB hC hCl hCB, root_5940 hB hC hCl hCB, root_5950 hB hC hCl hCB, root_5957 hB hC hCl hCB, root_5959 hB hC hCl hCB, root_5964 hB hC hCl hCB, root_5968 hB hC hCl hCB, root_5969 hB hC hCl hCB, root_5970 hB hC hCl hCB, root_5971 hB hC hCl hCB, root_5980 hB hC hCl hCB, root_5989 hB hC hCl hCB, root_5990 hB hC hCl hCB, root_6003 hB hC hCl hCB, root_6019 hB hC hCl hCB, root_6025 hB hC hCl hCB, root_6026 hB hC hCl hCB, root_6027 hB hC hCl hCB, root_6033 hB hC hCl hCB, root_6034 hB hC hCl hCB]

theorem root_6035 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6035) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6035_0, decode 300 d_6035_1, decode 300 d_6035_2, decode 300 d_6035_3, decode 300 d_6035_4, decode 300 d_6035_5, decode 30 d_6035_6] (fun x hx => bits_full_and hx) cov_6035 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6035_0, ch_6035_1, ch_6035_2, ch_6035_3, ch_6035_4, ch_6035_5, ch_6035_6])

theorem root_6037 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6037) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6037_0, decode 300 d_6037_1, decode 300 d_6037_2, decode 300 d_6037_3, decode 300 d_6037_4, decode 300 d_6037_5, decode 77 d_6037_6] (fun x hx => bits_full_and hx) cov_6037 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6037_0, ch_6037_1, ch_6037_2, ch_6037_3, ch_6037_4, ch_6037_5, ch_6037_6])

theorem root_6041 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6041) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6041_0, decode 300 d_6041_1, decode 300 d_6041_2, decode 300 d_6041_3, decode 300 d_6041_4, decode 300 d_6041_5, decode 46 d_6041_6] (fun x hx => bits_full_and hx) cov_6041 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6041_0, ch_6041_1, ch_6041_2, ch_6041_3, ch_6041_4, ch_6041_5, ch_6041_6])

theorem root_6042 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6042) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6042_0, decode 300 d_6042_1, decode 300 d_6042_2, decode 300 d_6042_3, decode 300 d_6042_4, decode 300 d_6042_5, decode 46 d_6042_6] (fun x hx => bits_full_and hx) cov_6042 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6042_0, ch_6042_1, ch_6042_2, ch_6042_3, ch_6042_4, ch_6042_5, ch_6042_6])

theorem root_6045 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6045) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6045_0, decode 300 d_6045_1, decode 300 d_6045_2, decode 300 d_6045_3, decode 300 d_6045_4, decode 300 d_6045_5, decode 32 d_6045_6] (fun x hx => bits_full_and hx) cov_6045 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6045_0, ch_6045_1, ch_6045_2, ch_6045_3, ch_6045_4, ch_6045_5, ch_6045_6])

theorem root_6050 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6050) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6050_0, decode 300 d_6050_1, decode 300 d_6050_2, decode 300 d_6050_3, decode 300 d_6050_4, decode 300 d_6050_5, decode 300 d_6050_6, decode 142 d_6050_7] (fun x hx => bits_full_and hx) cov_6050 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6050_0, ch_6050_1, ch_6050_2, ch_6050_3, ch_6050_4, ch_6050_5, ch_6050_6, ch_6050_7])

theorem root_6051 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6051) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6051_0, decode 300 d_6051_1, decode 300 d_6051_2, decode 300 d_6051_3, decode 300 d_6051_4, decode 300 d_6051_5, decode 300 d_6051_6, decode 142 d_6051_7] (fun x hx => bits_full_and hx) cov_6051 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6051_0, ch_6051_1, ch_6051_2, ch_6051_3, ch_6051_4, ch_6051_5, ch_6051_6, ch_6051_7])

theorem root_6060 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6060) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6060_0, decode 300 d_6060_1, decode 300 d_6060_2, decode 300 d_6060_3, decode 300 d_6060_4, decode 300 d_6060_5, decode 300 d_6060_6, decode 142 d_6060_7] (fun x hx => bits_full_and hx) cov_6060 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6060_0, ch_6060_1, ch_6060_2, ch_6060_3, ch_6060_4, ch_6060_5, ch_6060_6, ch_6060_7])

theorem root_6061 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6061) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6061_0, decode 300 d_6061_1, decode 300 d_6061_2, decode 300 d_6061_3, decode 300 d_6061_4, decode 300 d_6061_5, decode 300 d_6061_6, decode 142 d_6061_7] (fun x hx => bits_full_and hx) cov_6061 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6061_0, ch_6061_1, ch_6061_2, ch_6061_3, ch_6061_4, ch_6061_5, ch_6061_6, ch_6061_7])

theorem root_6070 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6070) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6070_0, decode 300 d_6070_1, decode 300 d_6070_2, decode 300 d_6070_3, decode 300 d_6070_4, decode 300 d_6070_5, decode 300 d_6070_6, decode 142 d_6070_7] (fun x hx => bits_full_and hx) cov_6070 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6070_0, ch_6070_1, ch_6070_2, ch_6070_3, ch_6070_4, ch_6070_5, ch_6070_6, ch_6070_7])

theorem root_6071 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6071) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6071_0, decode 300 d_6071_1, decode 300 d_6071_2, decode 300 d_6071_3, decode 300 d_6071_4, decode 300 d_6071_5, decode 300 d_6071_6, decode 142 d_6071_7] (fun x hx => bits_full_and hx) cov_6071 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6071_0, ch_6071_1, ch_6071_2, ch_6071_3, ch_6071_4, ch_6071_5, ch_6071_6, ch_6071_7])

theorem root_6076 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6076) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6076_0, decode 300 d_6076_1, decode 300 d_6076_2, decode 300 d_6076_3, decode 300 d_6076_4, decode 300 d_6076_5, decode 300 d_6076_6, decode 142 d_6076_7] (fun x hx => bits_full_and hx) cov_6076 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6076_0, ch_6076_1, ch_6076_2, ch_6076_3, ch_6076_4, ch_6076_5, ch_6076_6, ch_6076_7])

theorem root_6077 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6077) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6077_0, decode 300 d_6077_1, decode 300 d_6077_2, decode 300 d_6077_3, decode 300 d_6077_4, decode 300 d_6077_5, decode 300 d_6077_6, decode 142 d_6077_7] (fun x hx => bits_full_and hx) cov_6077 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6077_0, ch_6077_1, ch_6077_2, ch_6077_3, ch_6077_4, ch_6077_5, ch_6077_6, ch_6077_7])

theorem root_6078 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6078) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6078_0, decode 300 d_6078_1, decode 300 d_6078_2, decode 300 d_6078_3, decode 300 d_6078_4, decode 300 d_6078_5, decode 300 d_6078_6, decode 142 d_6078_7] (fun x hx => bits_full_and hx) cov_6078 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6078_0, ch_6078_1, ch_6078_2, ch_6078_3, ch_6078_4, ch_6078_5, ch_6078_6, ch_6078_7])

theorem root_6096 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6096) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6096_0, decode 300 d_6096_1, decode 300 d_6096_2, decode 300 d_6096_3, decode 300 d_6096_4, decode 300 d_6096_5, decode 300 d_6096_6, decode 141 d_6096_7] (fun x hx => bits_full_and hx) cov_6096 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6096_0, ch_6096_1, ch_6096_2, ch_6096_3, ch_6096_4, ch_6096_5, ch_6096_6, ch_6096_7])

theorem root_6097 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6097) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6097_0, decode 300 d_6097_1, decode 300 d_6097_2, decode 300 d_6097_3, decode 300 d_6097_4, decode 300 d_6097_5, decode 300 d_6097_6, decode 142 d_6097_7] (fun x hx => bits_full_and hx) cov_6097 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6097_0, ch_6097_1, ch_6097_2, ch_6097_3, ch_6097_4, ch_6097_5, ch_6097_6, ch_6097_7])

theorem root_6098 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6098) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6098_0, decode 300 d_6098_1, decode 300 d_6098_2, decode 300 d_6098_3, decode 300 d_6098_4, decode 300 d_6098_5, decode 300 d_6098_6, decode 142 d_6098_7] (fun x hx => bits_full_and hx) cov_6098 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6098_0, ch_6098_1, ch_6098_2, ch_6098_3, ch_6098_4, ch_6098_5, ch_6098_6, ch_6098_7])

theorem root_6099 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6099) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6099_0, decode 300 d_6099_1, decode 300 d_6099_2, decode 300 d_6099_3, decode 300 d_6099_4, decode 300 d_6099_5, decode 300 d_6099_6, decode 142 d_6099_7] (fun x hx => bits_full_and hx) cov_6099 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6099_0, ch_6099_1, ch_6099_2, ch_6099_3, ch_6099_4, ch_6099_5, ch_6099_6, ch_6099_7])

theorem root_6116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6116_0, decode 300 d_6116_1, decode 300 d_6116_2, decode 300 d_6116_3, decode 300 d_6116_4, decode 300 d_6116_5, decode 300 d_6116_6, decode 141 d_6116_7] (fun x hx => bits_full_and hx) cov_6116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6116_0, ch_6116_1, ch_6116_2, ch_6116_3, ch_6116_4, ch_6116_5, ch_6116_6, ch_6116_7])

theorem roots_91_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_91, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_91, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6035 hB hC hCl hCB, root_6037 hB hC hCl hCB, root_6041 hB hC hCl hCB, root_6042 hB hC hCl hCB, root_6045 hB hC hCl hCB, root_6050 hB hC hCl hCB, root_6051 hB hC hCl hCB, root_6060 hB hC hCl hCB, root_6061 hB hC hCl hCB, root_6070 hB hC hCl hCB, root_6071 hB hC hCl hCB, root_6076 hB hC hCl hCB, root_6077 hB hC hCl hCB, root_6078 hB hC hCl hCB, root_6096 hB hC hCl hCB, root_6097 hB hC hCl hCB, root_6098 hB hC hCl hCB, root_6099 hB hC hCl hCB, root_6116 hB hC hCl hCB]

theorem root_6117 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6117) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6117_0, decode 300 d_6117_1, decode 300 d_6117_2, decode 300 d_6117_3, decode 300 d_6117_4, decode 300 d_6117_5, decode 300 d_6117_6, decode 141 d_6117_7] (fun x hx => bits_full_and hx) cov_6117 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6117_0, ch_6117_1, ch_6117_2, ch_6117_3, ch_6117_4, ch_6117_5, ch_6117_6, ch_6117_7])

theorem root_6118 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6118) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6118_0, decode 300 d_6118_1, decode 300 d_6118_2, decode 300 d_6118_3, decode 300 d_6118_4, decode 300 d_6118_5, decode 300 d_6118_6, decode 158 d_6118_7] (fun x hx => bits_full_and hx) cov_6118 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6118_0, ch_6118_1, ch_6118_2, ch_6118_3, ch_6118_4, ch_6118_5, ch_6118_6, ch_6118_7])

theorem root_6122 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6122) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6122_0, decode 300 d_6122_1, decode 300 d_6122_2, decode 300 d_6122_3, decode 300 d_6122_4, decode 300 d_6122_5, decode 300 d_6122_6, decode 141 d_6122_7] (fun x hx => bits_full_and hx) cov_6122 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6122_0, ch_6122_1, ch_6122_2, ch_6122_3, ch_6122_4, ch_6122_5, ch_6122_6, ch_6122_7])

theorem root_6123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6123_0, decode 300 d_6123_1, decode 300 d_6123_2, decode 300 d_6123_3, decode 300 d_6123_4, decode 300 d_6123_5, decode 300 d_6123_6, decode 158 d_6123_7] (fun x hx => bits_full_and hx) cov_6123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6123_0, ch_6123_1, ch_6123_2, ch_6123_3, ch_6123_4, ch_6123_5, ch_6123_6, ch_6123_7])

theorem root_6130 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6130) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6130_0, decode 300 d_6130_1, decode 300 d_6130_2, decode 300 d_6130_3, decode 300 d_6130_4, decode 300 d_6130_5, decode 70 d_6130_6] (fun x hx => bits_full_and hx) cov_6130 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6130_0, ch_6130_1, ch_6130_2, ch_6130_3, ch_6130_4, ch_6130_5, ch_6130_6])

theorem root_6131 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6131) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6131_0, decode 300 d_6131_1, decode 300 d_6131_2, decode 300 d_6131_3, decode 300 d_6131_4, decode 300 d_6131_5, decode 63 d_6131_6] (fun x hx => bits_full_and hx) cov_6131 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6131_0, ch_6131_1, ch_6131_2, ch_6131_3, ch_6131_4, ch_6131_5, ch_6131_6])

theorem root_6135 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6135) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6135_0, decode 300 d_6135_1, decode 300 d_6135_2, decode 300 d_6135_3, decode 300 d_6135_4, decode 300 d_6135_5, decode 300 d_6135_6, decode 142 d_6135_7] (fun x hx => bits_full_and hx) cov_6135 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6135_0, ch_6135_1, ch_6135_2, ch_6135_3, ch_6135_4, ch_6135_5, ch_6135_6, ch_6135_7])

theorem root_6136 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6136) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6136_0, decode 300 d_6136_1, decode 300 d_6136_2, decode 300 d_6136_3, decode 300 d_6136_4, decode 300 d_6136_5, decode 300 d_6136_6, decode 141 d_6136_7] (fun x hx => bits_full_and hx) cov_6136 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6136_0, ch_6136_1, ch_6136_2, ch_6136_3, ch_6136_4, ch_6136_5, ch_6136_6, ch_6136_7])

theorem root_6139 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6139) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6139_0, decode 300 d_6139_1, decode 300 d_6139_2, decode 300 d_6139_3, decode 300 d_6139_4, decode 300 d_6139_5, decode 300 d_6139_6, decode 142 d_6139_7] (fun x hx => bits_full_and hx) cov_6139 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6139_0, ch_6139_1, ch_6139_2, ch_6139_3, ch_6139_4, ch_6139_5, ch_6139_6, ch_6139_7])

theorem root_6145 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6145) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6145_0, decode 300 d_6145_1, decode 300 d_6145_2, decode 300 d_6145_3, decode 300 d_6145_4, decode 300 d_6145_5, decode 300 d_6145_6, decode 142 d_6145_7] (fun x hx => bits_full_and hx) cov_6145 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6145_0, ch_6145_1, ch_6145_2, ch_6145_3, ch_6145_4, ch_6145_5, ch_6145_6, ch_6145_7])

theorem root_6146 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6146) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6146_0, decode 300 d_6146_1, decode 300 d_6146_2, decode 300 d_6146_3, decode 300 d_6146_4, decode 300 d_6146_5, decode 300 d_6146_6, decode 141 d_6146_7] (fun x hx => bits_full_and hx) cov_6146 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6146_0, ch_6146_1, ch_6146_2, ch_6146_3, ch_6146_4, ch_6146_5, ch_6146_6, ch_6146_7])

theorem root_6147 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6147) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6147_0, decode 300 d_6147_1, decode 300 d_6147_2, decode 300 d_6147_3, decode 300 d_6147_4, decode 300 d_6147_5, decode 300 d_6147_6, decode 141 d_6147_7] (fun x hx => bits_full_and hx) cov_6147 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6147_0, ch_6147_1, ch_6147_2, ch_6147_3, ch_6147_4, ch_6147_5, ch_6147_6, ch_6147_7])

theorem root_6148 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6148) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6148_0, decode 300 d_6148_1, decode 300 d_6148_2, decode 300 d_6148_3, decode 300 d_6148_4, decode 300 d_6148_5, decode 300 d_6148_6, decode 142 d_6148_7] (fun x hx => bits_full_and hx) cov_6148 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6148_0, ch_6148_1, ch_6148_2, ch_6148_3, ch_6148_4, ch_6148_5, ch_6148_6, ch_6148_7])

theorem root_6152 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6152) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6152_0, decode 300 d_6152_1, decode 300 d_6152_2, decode 300 d_6152_3, decode 300 d_6152_4, decode 300 d_6152_5, decode 300 d_6152_6, decode 141 d_6152_7] (fun x hx => bits_full_and hx) cov_6152 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6152_0, ch_6152_1, ch_6152_2, ch_6152_3, ch_6152_4, ch_6152_5, ch_6152_6, ch_6152_7])

theorem root_6153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6153_0, decode 300 d_6153_1, decode 300 d_6153_2, decode 300 d_6153_3, decode 300 d_6153_4, decode 300 d_6153_5, decode 300 d_6153_6, decode 141 d_6153_7] (fun x hx => bits_full_and hx) cov_6153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6153_0, ch_6153_1, ch_6153_2, ch_6153_3, ch_6153_4, ch_6153_5, ch_6153_6, ch_6153_7])

theorem root_6161 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6161) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6161_0, decode 300 d_6161_1, decode 300 d_6161_2, decode 300 d_6161_3, decode 300 d_6161_4, decode 300 d_6161_5, decode 300 d_6161_6, decode 141 d_6161_7] (fun x hx => bits_full_and hx) cov_6161 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6161_0, ch_6161_1, ch_6161_2, ch_6161_3, ch_6161_4, ch_6161_5, ch_6161_6, ch_6161_7])

theorem root_6171 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6171) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6171_0, decode 300 d_6171_1, decode 300 d_6171_2, decode 300 d_6171_3, decode 300 d_6171_4, decode 300 d_6171_5, decode 300 d_6171_6, decode 141 d_6171_7] (fun x hx => bits_full_and hx) cov_6171 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6171_0, ch_6171_1, ch_6171_2, ch_6171_3, ch_6171_4, ch_6171_5, ch_6171_6, ch_6171_7])

theorem root_6177 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6177) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6177_0, decode 300 d_6177_1, decode 300 d_6177_2, decode 300 d_6177_3, decode 300 d_6177_4, decode 300 d_6177_5, decode 300 d_6177_6, decode 141 d_6177_7] (fun x hx => bits_full_and hx) cov_6177 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6177_0, ch_6177_1, ch_6177_2, ch_6177_3, ch_6177_4, ch_6177_5, ch_6177_6, ch_6177_7])

theorem root_6180 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6180) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6180_0, decode 300 d_6180_1, decode 300 d_6180_2, decode 300 d_6180_3, decode 300 d_6180_4, decode 300 d_6180_5, decode 54 d_6180_6] (fun x hx => bits_full_and hx) cov_6180 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6180_0, ch_6180_1, ch_6180_2, ch_6180_3, ch_6180_4, ch_6180_5, ch_6180_6])

theorem roots_92_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_92, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_92, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6117 hB hC hCl hCB, root_6118 hB hC hCl hCB, root_6122 hB hC hCl hCB, root_6123 hB hC hCl hCB, root_6130 hB hC hCl hCB, root_6131 hB hC hCl hCB, root_6135 hB hC hCl hCB, root_6136 hB hC hCl hCB, root_6139 hB hC hCl hCB, root_6145 hB hC hCl hCB, root_6146 hB hC hCl hCB, root_6147 hB hC hCl hCB, root_6148 hB hC hCl hCB, root_6152 hB hC hCl hCB, root_6153 hB hC hCl hCB, root_6161 hB hC hCl hCB, root_6171 hB hC hCl hCB, root_6177 hB hC hCl hCB, root_6180 hB hC hCl hCB]

theorem root_6181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6181_0, decode 300 d_6181_1, decode 300 d_6181_2, decode 300 d_6181_3, decode 300 d_6181_4, decode 300 d_6181_5, decode 300 d_6181_6, decode 141 d_6181_7] (fun x hx => bits_full_and hx) cov_6181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6181_0, ch_6181_1, ch_6181_2, ch_6181_3, ch_6181_4, ch_6181_5, ch_6181_6, ch_6181_7])

theorem root_6188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6188_0, decode 300 d_6188_1, decode 300 d_6188_2, decode 300 d_6188_3, decode 300 d_6188_4, decode 300 d_6188_5, decode 54 d_6188_6] (fun x hx => bits_full_and hx) cov_6188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6188_0, ch_6188_1, ch_6188_2, ch_6188_3, ch_6188_4, ch_6188_5, ch_6188_6])

theorem root_6193 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6193) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6193_0, decode 300 d_6193_1, decode 300 d_6193_2, decode 300 d_6193_3, decode 300 d_6193_4, decode 268 d_6193_5] (fun x hx => bits_full_and hx) cov_6193 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6193_0, ch_6193_1, ch_6193_2, ch_6193_3, ch_6193_4, ch_6193_5])

theorem root_6194 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6194) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6194_0, decode 300 d_6194_1, decode 300 d_6194_2, decode 300 d_6194_3, decode 300 d_6194_4, decode 268 d_6194_5] (fun x hx => bits_full_and hx) cov_6194 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6194_0, ch_6194_1, ch_6194_2, ch_6194_3, ch_6194_4, ch_6194_5])

theorem root_6195 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6195) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6195_0, decode 300 d_6195_1, decode 300 d_6195_2, decode 300 d_6195_3, decode 300 d_6195_4, decode 300 d_6195_5, decode 300 d_6195_6, decode 141 d_6195_7] (fun x hx => bits_full_and hx) cov_6195 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6195_0, ch_6195_1, ch_6195_2, ch_6195_3, ch_6195_4, ch_6195_5, ch_6195_6, ch_6195_7])

theorem root_6200 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6200) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6200_0, decode 300 d_6200_1, decode 300 d_6200_2, decode 300 d_6200_3, decode 300 d_6200_4, decode 248 d_6200_5] (fun x hx => bits_full_and hx) cov_6200 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6200_0, ch_6200_1, ch_6200_2, ch_6200_3, ch_6200_4, ch_6200_5])

theorem root_6201 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6201) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6201_0, decode 300 d_6201_1, decode 300 d_6201_2, decode 300 d_6201_3, decode 300 d_6201_4, decode 300 d_6201_5, decode 300 d_6201_6, decode 141 d_6201_7] (fun x hx => bits_full_and hx) cov_6201 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6201_0, ch_6201_1, ch_6201_2, ch_6201_3, ch_6201_4, ch_6201_5, ch_6201_6, ch_6201_7])

theorem root_6202 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6202) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6202_0, decode 300 d_6202_1, decode 300 d_6202_2, decode 300 d_6202_3, decode 300 d_6202_4, decode 300 d_6202_5, decode 300 d_6202_6, decode 141 d_6202_7] (fun x hx => bits_full_and hx) cov_6202 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6202_0, ch_6202_1, ch_6202_2, ch_6202_3, ch_6202_4, ch_6202_5, ch_6202_6, ch_6202_7])

theorem root_6206 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6206) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6206_0, decode 300 d_6206_1, decode 300 d_6206_2, decode 300 d_6206_3, decode 300 d_6206_4, decode 300 d_6206_5, decode 300 d_6206_6, decode 51 d_6206_7] (fun x hx => bits_full_and hx) cov_6206 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6206_0, ch_6206_1, ch_6206_2, ch_6206_3, ch_6206_4, ch_6206_5, ch_6206_6, ch_6206_7])

theorem root_6213 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6213) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6213_0, decode 300 d_6213_1, decode 300 d_6213_2, decode 300 d_6213_3, decode 300 d_6213_4, decode 300 d_6213_5, decode 300 d_6213_6, decode 141 d_6213_7] (fun x hx => bits_full_and hx) cov_6213 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6213_0, ch_6213_1, ch_6213_2, ch_6213_3, ch_6213_4, ch_6213_5, ch_6213_6, ch_6213_7])

theorem root_6214 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6214) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6214_0, decode 300 d_6214_1, decode 300 d_6214_2, decode 300 d_6214_3, decode 300 d_6214_4, decode 300 d_6214_5, decode 300 d_6214_6, decode 141 d_6214_7] (fun x hx => bits_full_and hx) cov_6214 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6214_0, ch_6214_1, ch_6214_2, ch_6214_3, ch_6214_4, ch_6214_5, ch_6214_6, ch_6214_7])

theorem root_6218 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6218) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6218_0, decode 300 d_6218_1, decode 300 d_6218_2, decode 300 d_6218_3, decode 300 d_6218_4, decode 300 d_6218_5, decode 300 d_6218_6, decode 141 d_6218_7] (fun x hx => bits_full_and hx) cov_6218 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6218_0, ch_6218_1, ch_6218_2, ch_6218_3, ch_6218_4, ch_6218_5, ch_6218_6, ch_6218_7])

theorem root_6225 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6225) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6225_0, decode 300 d_6225_1, decode 300 d_6225_2, decode 300 d_6225_3, decode 300 d_6225_4, decode 300 d_6225_5, decode 300 d_6225_6, decode 141 d_6225_7] (fun x hx => bits_full_and hx) cov_6225 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6225_0, ch_6225_1, ch_6225_2, ch_6225_3, ch_6225_4, ch_6225_5, ch_6225_6, ch_6225_7])

theorem root_6226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6226_0, decode 300 d_6226_1, decode 300 d_6226_2, decode 300 d_6226_3, decode 300 d_6226_4, decode 300 d_6226_5, decode 300 d_6226_6, decode 141 d_6226_7] (fun x hx => bits_full_and hx) cov_6226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6226_0, ch_6226_1, ch_6226_2, ch_6226_3, ch_6226_4, ch_6226_5, ch_6226_6, ch_6226_7])

theorem root_6227 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6227) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6227_0, decode 300 d_6227_1, decode 300 d_6227_2, decode 300 d_6227_3, decode 300 d_6227_4, decode 300 d_6227_5, decode 300 d_6227_6, decode 141 d_6227_7] (fun x hx => bits_full_and hx) cov_6227 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6227_0, ch_6227_1, ch_6227_2, ch_6227_3, ch_6227_4, ch_6227_5, ch_6227_6, ch_6227_7])

theorem root_6228 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6228) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6228_0, decode 300 d_6228_1, decode 300 d_6228_2, decode 300 d_6228_3, decode 300 d_6228_4, decode 300 d_6228_5, decode 300 d_6228_6, decode 141 d_6228_7] (fun x hx => bits_full_and hx) cov_6228 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6228_0, ch_6228_1, ch_6228_2, ch_6228_3, ch_6228_4, ch_6228_5, ch_6228_6, ch_6228_7])

theorem root_6233 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6233) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6233_0, decode 300 d_6233_1, decode 300 d_6233_2, decode 300 d_6233_3, decode 300 d_6233_4, decode 292 d_6233_5] (fun x hx => bits_full_and hx) cov_6233 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6233_0, ch_6233_1, ch_6233_2, ch_6233_3, ch_6233_4, ch_6233_5])

theorem root_6243 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6243) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6243_0, decode 300 d_6243_1, decode 300 d_6243_2, decode 300 d_6243_3, decode 300 d_6243_4, decode 300 d_6243_5, decode 271 d_6243_6] (fun x hx => bits_full_and hx) cov_6243 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6243_0, ch_6243_1, ch_6243_2, ch_6243_3, ch_6243_4, ch_6243_5, ch_6243_6])

theorem root_6255 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6255) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6255_0, decode 300 d_6255_1, decode 300 d_6255_2, decode 300 d_6255_3, decode 300 d_6255_4, decode 300 d_6255_5, decode 2 d_6255_6] (fun x hx => bits_full_and hx) cov_6255 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6255_0, ch_6255_1, ch_6255_2, ch_6255_3, ch_6255_4, ch_6255_5, ch_6255_6])

theorem root_6261 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6261) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6261_0, decode 300 d_6261_1, decode 300 d_6261_2, decode 300 d_6261_3, decode 300 d_6261_4, decode 257 d_6261_5] (fun x hx => bits_full_and hx) cov_6261 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6261_0, ch_6261_1, ch_6261_2, ch_6261_3, ch_6261_4, ch_6261_5])

theorem roots_93_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_93, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_93, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6181 hB hC hCl hCB, root_6188 hB hC hCl hCB, root_6193 hB hC hCl hCB, root_6194 hB hC hCl hCB, root_6195 hB hC hCl hCB, root_6200 hB hC hCl hCB, root_6201 hB hC hCl hCB, root_6202 hB hC hCl hCB, root_6206 hB hC hCl hCB, root_6213 hB hC hCl hCB, root_6214 hB hC hCl hCB, root_6218 hB hC hCl hCB, root_6225 hB hC hCl hCB, root_6226 hB hC hCl hCB, root_6227 hB hC hCl hCB, root_6228 hB hC hCl hCB, root_6233 hB hC hCl hCB, root_6243 hB hC hCl hCB, root_6255 hB hC hCl hCB, root_6261 hB hC hCl hCB]

theorem root_6268 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6268) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6268_0, decode 300 d_6268_1, decode 300 d_6268_2, decode 300 d_6268_3, decode 300 d_6268_4, decode 298 d_6268_5] (fun x hx => bits_full_and hx) cov_6268 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6268_0, ch_6268_1, ch_6268_2, ch_6268_3, ch_6268_4, ch_6268_5])

theorem root_6272 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6272) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6272_0, decode 300 d_6272_1, decode 300 d_6272_2, decode 300 d_6272_3, decode 300 d_6272_4, decode 300 d_6272_5, decode 59 d_6272_6] (fun x hx => bits_full_and hx) cov_6272 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6272_0, ch_6272_1, ch_6272_2, ch_6272_3, ch_6272_4, ch_6272_5, ch_6272_6])

theorem root_6274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6274_0, decode 300 d_6274_1, decode 300 d_6274_2, decode 300 d_6274_3, decode 300 d_6274_4, decode 300 d_6274_5, decode 116 d_6274_6] (fun x hx => bits_full_and hx) cov_6274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6274_0, ch_6274_1, ch_6274_2, ch_6274_3, ch_6274_4, ch_6274_5, ch_6274_6])

theorem root_6281 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6281) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6281_0, decode 300 d_6281_1, decode 300 d_6281_2, decode 300 d_6281_3, decode 300 d_6281_4, decode 300 d_6281_5, decode 300 d_6281_6, decode 141 d_6281_7] (fun x hx => bits_full_and hx) cov_6281 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6281_0, ch_6281_1, ch_6281_2, ch_6281_3, ch_6281_4, ch_6281_5, ch_6281_6, ch_6281_7])

theorem root_6287 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6287) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6287_0, decode 300 d_6287_1, decode 300 d_6287_2, decode 300 d_6287_3, decode 300 d_6287_4, decode 300 d_6287_5, decode 300 d_6287_6, decode 142 d_6287_7] (fun x hx => bits_full_and hx) cov_6287 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6287_0, ch_6287_1, ch_6287_2, ch_6287_3, ch_6287_4, ch_6287_5, ch_6287_6, ch_6287_7])

theorem root_6291 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6291) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6291_0, decode 300 d_6291_1, decode 300 d_6291_2, decode 300 d_6291_3, decode 300 d_6291_4, decode 300 d_6291_5, decode 300 d_6291_6, decode 142 d_6291_7] (fun x hx => bits_full_and hx) cov_6291 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6291_0, ch_6291_1, ch_6291_2, ch_6291_3, ch_6291_4, ch_6291_5, ch_6291_6, ch_6291_7])

theorem root_6293 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6293) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6293_0, decode 300 d_6293_1, decode 300 d_6293_2, decode 300 d_6293_3, decode 300 d_6293_4, decode 300 d_6293_5, decode 300 d_6293_6, decode 141 d_6293_7] (fun x hx => bits_full_and hx) cov_6293 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6293_0, ch_6293_1, ch_6293_2, ch_6293_3, ch_6293_4, ch_6293_5, ch_6293_6, ch_6293_7])

theorem root_6294 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6294) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6294_0, decode 300 d_6294_1, decode 300 d_6294_2, decode 300 d_6294_3, decode 300 d_6294_4, decode 300 d_6294_5, decode 300 d_6294_6, decode 141 d_6294_7] (fun x hx => bits_full_and hx) cov_6294 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6294_0, ch_6294_1, ch_6294_2, ch_6294_3, ch_6294_4, ch_6294_5, ch_6294_6, ch_6294_7])

theorem root_6295 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6295) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6295_0, decode 300 d_6295_1, decode 300 d_6295_2, decode 300 d_6295_3, decode 300 d_6295_4, decode 300 d_6295_5, decode 300 d_6295_6, decode 141 d_6295_7] (fun x hx => bits_full_and hx) cov_6295 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6295_0, ch_6295_1, ch_6295_2, ch_6295_3, ch_6295_4, ch_6295_5, ch_6295_6, ch_6295_7])

theorem root_6299 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6299) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6299_0, decode 300 d_6299_1, decode 300 d_6299_2, decode 300 d_6299_3, decode 300 d_6299_4, decode 300 d_6299_5, decode 300 d_6299_6, decode 142 d_6299_7] (fun x hx => bits_full_and hx) cov_6299 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6299_0, ch_6299_1, ch_6299_2, ch_6299_3, ch_6299_4, ch_6299_5, ch_6299_6, ch_6299_7])

theorem root_6300 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6300) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6300_0, decode 300 d_6300_1, decode 300 d_6300_2, decode 300 d_6300_3, decode 300 d_6300_4, decode 300 d_6300_5, decode 300 d_6300_6, decode 141 d_6300_7] (fun x hx => bits_full_and hx) cov_6300 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6300_0, ch_6300_1, ch_6300_2, ch_6300_3, ch_6300_4, ch_6300_5, ch_6300_6, ch_6300_7])

theorem root_6302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6302_0, decode 300 d_6302_1, decode 300 d_6302_2, decode 300 d_6302_3, decode 300 d_6302_4, decode 300 d_6302_5, decode 300 d_6302_6, decode 141 d_6302_7] (fun x hx => bits_full_and hx) cov_6302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6302_0, ch_6302_1, ch_6302_2, ch_6302_3, ch_6302_4, ch_6302_5, ch_6302_6, ch_6302_7])

theorem root_6312 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6312) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6312_0, decode 300 d_6312_1, decode 300 d_6312_2, decode 300 d_6312_3, decode 300 d_6312_4, decode 300 d_6312_5, decode 300 d_6312_6, decode 141 d_6312_7] (fun x hx => bits_full_and hx) cov_6312 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6312_0, ch_6312_1, ch_6312_2, ch_6312_3, ch_6312_4, ch_6312_5, ch_6312_6, ch_6312_7])

theorem root_6313 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6313) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6313_0, decode 300 d_6313_1, decode 300 d_6313_2, decode 300 d_6313_3, decode 300 d_6313_4, decode 300 d_6313_5, decode 300 d_6313_6, decode 141 d_6313_7] (fun x hx => bits_full_and hx) cov_6313 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6313_0, ch_6313_1, ch_6313_2, ch_6313_3, ch_6313_4, ch_6313_5, ch_6313_6, ch_6313_7])

theorem root_6320 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6320) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6320_0, decode 300 d_6320_1, decode 300 d_6320_2, decode 300 d_6320_3, decode 300 d_6320_4, decode 300 d_6320_5, decode 300 d_6320_6, decode 142 d_6320_7] (fun x hx => bits_full_and hx) cov_6320 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6320_0, ch_6320_1, ch_6320_2, ch_6320_3, ch_6320_4, ch_6320_5, ch_6320_6, ch_6320_7])

theorem root_6323 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6323) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6323_0, decode 300 d_6323_1, decode 300 d_6323_2, decode 300 d_6323_3, decode 300 d_6323_4, decode 300 d_6323_5, decode 300 d_6323_6, decode 141 d_6323_7] (fun x hx => bits_full_and hx) cov_6323 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6323_0, ch_6323_1, ch_6323_2, ch_6323_3, ch_6323_4, ch_6323_5, ch_6323_6, ch_6323_7])

theorem root_6329 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6329) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6329_0, decode 300 d_6329_1, decode 300 d_6329_2, decode 300 d_6329_3, decode 300 d_6329_4, decode 300 d_6329_5, decode 300 d_6329_6, decode 142 d_6329_7] (fun x hx => bits_full_and hx) cov_6329 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6329_0, ch_6329_1, ch_6329_2, ch_6329_3, ch_6329_4, ch_6329_5, ch_6329_6, ch_6329_7])

theorem root_6330 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6330) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6330_0, decode 300 d_6330_1, decode 300 d_6330_2, decode 300 d_6330_3, decode 300 d_6330_4, decode 300 d_6330_5, decode 300 d_6330_6, decode 142 d_6330_7] (fun x hx => bits_full_and hx) cov_6330 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6330_0, ch_6330_1, ch_6330_2, ch_6330_3, ch_6330_4, ch_6330_5, ch_6330_6, ch_6330_7])

theorem root_6332 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6332) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6332_0, decode 300 d_6332_1, decode 300 d_6332_2, decode 300 d_6332_3, decode 300 d_6332_4, decode 300 d_6332_5, decode 300 d_6332_6, decode 141 d_6332_7] (fun x hx => bits_full_and hx) cov_6332 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6332_0, ch_6332_1, ch_6332_2, ch_6332_3, ch_6332_4, ch_6332_5, ch_6332_6, ch_6332_7])

theorem roots_94_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_94, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_94, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6268 hB hC hCl hCB, root_6272 hB hC hCl hCB, root_6274 hB hC hCl hCB, root_6281 hB hC hCl hCB, root_6287 hB hC hCl hCB, root_6291 hB hC hCl hCB, root_6293 hB hC hCl hCB, root_6294 hB hC hCl hCB, root_6295 hB hC hCl hCB, root_6299 hB hC hCl hCB, root_6300 hB hC hCl hCB, root_6302 hB hC hCl hCB, root_6312 hB hC hCl hCB, root_6313 hB hC hCl hCB, root_6320 hB hC hCl hCB, root_6323 hB hC hCl hCB, root_6329 hB hC hCl hCB, root_6330 hB hC hCl hCB, root_6332 hB hC hCl hCB]

theorem root_6333 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6333) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6333_0, decode 300 d_6333_1, decode 300 d_6333_2, decode 300 d_6333_3, decode 300 d_6333_4, decode 300 d_6333_5, decode 300 d_6333_6, decode 141 d_6333_7] (fun x hx => bits_full_and hx) cov_6333 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6333_0, ch_6333_1, ch_6333_2, ch_6333_3, ch_6333_4, ch_6333_5, ch_6333_6, ch_6333_7])

theorem root_6338 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6338) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6338_0, decode 300 d_6338_1, decode 300 d_6338_2, decode 300 d_6338_3, decode 300 d_6338_4, decode 300 d_6338_5, decode 300 d_6338_6, decode 142 d_6338_7] (fun x hx => bits_full_and hx) cov_6338 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6338_0, ch_6338_1, ch_6338_2, ch_6338_3, ch_6338_4, ch_6338_5, ch_6338_6, ch_6338_7])

theorem root_6339 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6339) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6339_0, decode 300 d_6339_1, decode 300 d_6339_2, decode 300 d_6339_3, decode 300 d_6339_4, decode 300 d_6339_5, decode 300 d_6339_6, decode 142 d_6339_7] (fun x hx => bits_full_and hx) cov_6339 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6339_0, ch_6339_1, ch_6339_2, ch_6339_3, ch_6339_4, ch_6339_5, ch_6339_6, ch_6339_7])

theorem root_6340 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6340) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6340_0, decode 300 d_6340_1, decode 300 d_6340_2, decode 300 d_6340_3, decode 300 d_6340_4, decode 300 d_6340_5, decode 300 d_6340_6, decode 142 d_6340_7] (fun x hx => bits_full_and hx) cov_6340 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6340_0, ch_6340_1, ch_6340_2, ch_6340_3, ch_6340_4, ch_6340_5, ch_6340_6, ch_6340_7])

theorem root_6345 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6345) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6345_0, decode 300 d_6345_1, decode 300 d_6345_2, decode 300 d_6345_3, decode 300 d_6345_4, decode 300 d_6345_5, decode 300 d_6345_6, decode 142 d_6345_7] (fun x hx => bits_full_and hx) cov_6345 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6345_0, ch_6345_1, ch_6345_2, ch_6345_3, ch_6345_4, ch_6345_5, ch_6345_6, ch_6345_7])

theorem root_6346 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6346) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6346_0, decode 300 d_6346_1, decode 300 d_6346_2, decode 300 d_6346_3, decode 300 d_6346_4, decode 300 d_6346_5, decode 300 d_6346_6, decode 141 d_6346_7] (fun x hx => bits_full_and hx) cov_6346 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6346_0, ch_6346_1, ch_6346_2, ch_6346_3, ch_6346_4, ch_6346_5, ch_6346_6, ch_6346_7])

theorem root_6347 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6347) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6347_0, decode 300 d_6347_1, decode 300 d_6347_2, decode 300 d_6347_3, decode 300 d_6347_4, decode 300 d_6347_5, decode 300 d_6347_6, decode 141 d_6347_7] (fun x hx => bits_full_and hx) cov_6347 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6347_0, ch_6347_1, ch_6347_2, ch_6347_3, ch_6347_4, ch_6347_5, ch_6347_6, ch_6347_7])

theorem root_6352 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6352) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6352_0, decode 300 d_6352_1, decode 300 d_6352_2, decode 300 d_6352_3, decode 300 d_6352_4, decode 300 d_6352_5, decode 300 d_6352_6, decode 141 d_6352_7] (fun x hx => bits_full_and hx) cov_6352 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6352_0, ch_6352_1, ch_6352_2, ch_6352_3, ch_6352_4, ch_6352_5, ch_6352_6, ch_6352_7])

theorem root_6360 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6360) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6360_0, decode 300 d_6360_1, decode 300 d_6360_2, decode 300 d_6360_3, decode 300 d_6360_4, decode 300 d_6360_5, decode 300 d_6360_6, decode 141 d_6360_7] (fun x hx => bits_full_and hx) cov_6360 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6360_0, ch_6360_1, ch_6360_2, ch_6360_3, ch_6360_4, ch_6360_5, ch_6360_6, ch_6360_7])

theorem root_6364 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6364) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6364_0, decode 300 d_6364_1, decode 300 d_6364_2, decode 300 d_6364_3, decode 300 d_6364_4, decode 300 d_6364_5, decode 300 d_6364_6, decode 141 d_6364_7] (fun x hx => bits_full_and hx) cov_6364 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6364_0, ch_6364_1, ch_6364_2, ch_6364_3, ch_6364_4, ch_6364_5, ch_6364_6, ch_6364_7])

theorem root_6365 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6365) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6365_0, decode 300 d_6365_1, decode 300 d_6365_2, decode 300 d_6365_3, decode 300 d_6365_4, decode 300 d_6365_5, decode 300 d_6365_6, decode 141 d_6365_7] (fun x hx => bits_full_and hx) cov_6365 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6365_0, ch_6365_1, ch_6365_2, ch_6365_3, ch_6365_4, ch_6365_5, ch_6365_6, ch_6365_7])

theorem root_6366 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6366) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6366_0, decode 300 d_6366_1, decode 300 d_6366_2, decode 300 d_6366_3, decode 300 d_6366_4, decode 300 d_6366_5, decode 300 d_6366_6, decode 141 d_6366_7] (fun x hx => bits_full_and hx) cov_6366 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6366_0, ch_6366_1, ch_6366_2, ch_6366_3, ch_6366_4, ch_6366_5, ch_6366_6, ch_6366_7])

theorem root_6372 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6372) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6372_0, decode 300 d_6372_1, decode 300 d_6372_2, decode 300 d_6372_3, decode 300 d_6372_4, decode 300 d_6372_5, decode 300 d_6372_6, decode 141 d_6372_7] (fun x hx => bits_full_and hx) cov_6372 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6372_0, ch_6372_1, ch_6372_2, ch_6372_3, ch_6372_4, ch_6372_5, ch_6372_6, ch_6372_7])

theorem root_6376 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6376) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6376_0, decode 300 d_6376_1, decode 300 d_6376_2, decode 300 d_6376_3, decode 300 d_6376_4, decode 300 d_6376_5, decode 300 d_6376_6, decode 141 d_6376_7] (fun x hx => bits_full_and hx) cov_6376 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6376_0, ch_6376_1, ch_6376_2, ch_6376_3, ch_6376_4, ch_6376_5, ch_6376_6, ch_6376_7])

theorem root_6377 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6377) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6377_0, decode 300 d_6377_1, decode 300 d_6377_2, decode 300 d_6377_3, decode 300 d_6377_4, decode 300 d_6377_5, decode 300 d_6377_6, decode 141 d_6377_7] (fun x hx => bits_full_and hx) cov_6377 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6377_0, ch_6377_1, ch_6377_2, ch_6377_3, ch_6377_4, ch_6377_5, ch_6377_6, ch_6377_7])

theorem root_6378 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6378) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6378_0, decode 300 d_6378_1, decode 300 d_6378_2, decode 300 d_6378_3, decode 300 d_6378_4, decode 300 d_6378_5, decode 300 d_6378_6, decode 141 d_6378_7] (fun x hx => bits_full_and hx) cov_6378 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6378_0, ch_6378_1, ch_6378_2, ch_6378_3, ch_6378_4, ch_6378_5, ch_6378_6, ch_6378_7])

theorem root_6384 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6384) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6384_0, decode 300 d_6384_1, decode 300 d_6384_2, decode 300 d_6384_3, decode 300 d_6384_4, decode 300 d_6384_5, decode 300 d_6384_6, decode 141 d_6384_7] (fun x hx => bits_full_and hx) cov_6384 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6384_0, ch_6384_1, ch_6384_2, ch_6384_3, ch_6384_4, ch_6384_5, ch_6384_6, ch_6384_7])

theorem root_6392 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6392) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6392_0, decode 300 d_6392_1, decode 300 d_6392_2, decode 300 d_6392_3, decode 300 d_6392_4, decode 300 d_6392_5, decode 300 d_6392_6, decode 141 d_6392_7] (fun x hx => bits_full_and hx) cov_6392 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6392_0, ch_6392_1, ch_6392_2, ch_6392_3, ch_6392_4, ch_6392_5, ch_6392_6, ch_6392_7])

theorem roots_95_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_95, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_95, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6333 hB hC hCl hCB, root_6338 hB hC hCl hCB, root_6339 hB hC hCl hCB, root_6340 hB hC hCl hCB, root_6345 hB hC hCl hCB, root_6346 hB hC hCl hCB, root_6347 hB hC hCl hCB, root_6352 hB hC hCl hCB, root_6360 hB hC hCl hCB, root_6364 hB hC hCl hCB, root_6365 hB hC hCl hCB, root_6366 hB hC hCl hCB, root_6372 hB hC hCl hCB, root_6376 hB hC hCl hCB, root_6377 hB hC hCl hCB, root_6378 hB hC hCl hCB, root_6384 hB hC hCl hCB, root_6392 hB hC hCl hCB]

theorem root_6399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6399_0, decode 300 d_6399_1, decode 300 d_6399_2, decode 300 d_6399_3, decode 300 d_6399_4, decode 300 d_6399_5, decode 300 d_6399_6, decode 141 d_6399_7] (fun x hx => bits_full_and hx) cov_6399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6399_0, ch_6399_1, ch_6399_2, ch_6399_3, ch_6399_4, ch_6399_5, ch_6399_6, ch_6399_7])

theorem root_6414 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6414) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6414_0, decode 300 d_6414_1, decode 300 d_6414_2, decode 300 d_6414_3, decode 300 d_6414_4, decode 300 d_6414_5, decode 300 d_6414_6, decode 142 d_6414_7] (fun x hx => bits_full_and hx) cov_6414 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6414_0, ch_6414_1, ch_6414_2, ch_6414_3, ch_6414_4, ch_6414_5, ch_6414_6, ch_6414_7])

theorem root_6424 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6424) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6424_0, decode 300 d_6424_1, decode 300 d_6424_2, decode 300 d_6424_3, decode 300 d_6424_4, decode 300 d_6424_5, decode 81 d_6424_6] (fun x hx => bits_full_and hx) cov_6424 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6424_0, ch_6424_1, ch_6424_2, ch_6424_3, ch_6424_4, ch_6424_5, ch_6424_6])

theorem root_6425 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6425) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6425_0, decode 300 d_6425_1, decode 300 d_6425_2, decode 300 d_6425_3, decode 300 d_6425_4, decode 300 d_6425_5, decode 102 d_6425_6] (fun x hx => bits_full_and hx) cov_6425 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6425_0, ch_6425_1, ch_6425_2, ch_6425_3, ch_6425_4, ch_6425_5, ch_6425_6])

theorem root_6432 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6432) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6432_0, decode 300 d_6432_1, decode 300 d_6432_2, decode 300 d_6432_3, decode 300 d_6432_4, decode 300 d_6432_5, decode 81 d_6432_6] (fun x hx => bits_full_and hx) cov_6432 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6432_0, ch_6432_1, ch_6432_2, ch_6432_3, ch_6432_4, ch_6432_5, ch_6432_6])

theorem root_6433 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6433) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6433_0, decode 300 d_6433_1, decode 300 d_6433_2, decode 300 d_6433_3, decode 300 d_6433_4, decode 300 d_6433_5, decode 81 d_6433_6] (fun x hx => bits_full_and hx) cov_6433 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6433_0, ch_6433_1, ch_6433_2, ch_6433_3, ch_6433_4, ch_6433_5, ch_6433_6])

theorem root_6434 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6434) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6434_0, decode 300 d_6434_1, decode 300 d_6434_2, decode 300 d_6434_3, decode 300 d_6434_4, decode 300 d_6434_5, decode 47 d_6434_6] (fun x hx => bits_full_and hx) cov_6434 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6434_0, ch_6434_1, ch_6434_2, ch_6434_3, ch_6434_4, ch_6434_5, ch_6434_6])

theorem root_6439 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6439) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6439_0, decode 300 d_6439_1, decode 300 d_6439_2, decode 300 d_6439_3, decode 300 d_6439_4, decode 300 d_6439_5, decode 71 d_6439_6] (fun x hx => bits_full_and hx) cov_6439 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6439_0, ch_6439_1, ch_6439_2, ch_6439_3, ch_6439_4, ch_6439_5, ch_6439_6])

theorem root_6440 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6440) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6440_0, decode 300 d_6440_1, decode 300 d_6440_2, decode 300 d_6440_3, decode 300 d_6440_4, decode 300 d_6440_5, decode 73 d_6440_6] (fun x hx => bits_full_and hx) cov_6440 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6440_0, ch_6440_1, ch_6440_2, ch_6440_3, ch_6440_4, ch_6440_5, ch_6440_6])

theorem root_6442 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6442) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6442_0, decode 300 d_6442_1, decode 300 d_6442_2, decode 300 d_6442_3, decode 300 d_6442_4, decode 300 d_6442_5, decode 73 d_6442_6] (fun x hx => bits_full_and hx) cov_6442 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6442_0, ch_6442_1, ch_6442_2, ch_6442_3, ch_6442_4, ch_6442_5, ch_6442_6])

theorem root_6448 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6448) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6448_0, decode 300 d_6448_1, decode 300 d_6448_2, decode 300 d_6448_3, decode 300 d_6448_4, decode 300 d_6448_5, decode 40 d_6448_6] (fun x hx => bits_full_and hx) cov_6448 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6448_0, ch_6448_1, ch_6448_2, ch_6448_3, ch_6448_4, ch_6448_5, ch_6448_6])

theorem root_6449 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6449) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6449_0, decode 300 d_6449_1, decode 300 d_6449_2, decode 300 d_6449_3, decode 300 d_6449_4, decode 300 d_6449_5, decode 73 d_6449_6] (fun x hx => bits_full_and hx) cov_6449 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6449_0, ch_6449_1, ch_6449_2, ch_6449_3, ch_6449_4, ch_6449_5, ch_6449_6])

theorem root_6450 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6450) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6450_0, decode 300 d_6450_1, decode 300 d_6450_2, decode 300 d_6450_3, decode 300 d_6450_4, decode 300 d_6450_5, decode 73 d_6450_6] (fun x hx => bits_full_and hx) cov_6450 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6450_0, ch_6450_1, ch_6450_2, ch_6450_3, ch_6450_4, ch_6450_5, ch_6450_6])

theorem root_6458 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6458) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6458_0, decode 300 d_6458_1, decode 300 d_6458_2, decode 300 d_6458_3, decode 300 d_6458_4, decode 300 d_6458_5, decode 300 d_6458_6, decode 141 d_6458_7] (fun x hx => bits_full_and hx) cov_6458 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6458_0, ch_6458_1, ch_6458_2, ch_6458_3, ch_6458_4, ch_6458_5, ch_6458_6, ch_6458_7])

theorem root_6463 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6463) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6463_0, decode 300 d_6463_1, decode 300 d_6463_2, decode 300 d_6463_3, decode 300 d_6463_4, decode 300 d_6463_5, decode 300 d_6463_6, decode 141 d_6463_7] (fun x hx => bits_full_and hx) cov_6463 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6463_0, ch_6463_1, ch_6463_2, ch_6463_3, ch_6463_4, ch_6463_5, ch_6463_6, ch_6463_7])

theorem root_6468 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6468) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6468_0, decode 300 d_6468_1, decode 300 d_6468_2, decode 300 d_6468_3, decode 300 d_6468_4, decode 300 d_6468_5, decode 300 d_6468_6, decode 141 d_6468_7] (fun x hx => bits_full_and hx) cov_6468 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6468_0, ch_6468_1, ch_6468_2, ch_6468_3, ch_6468_4, ch_6468_5, ch_6468_6, ch_6468_7])

theorem root_6472 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6472) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6472_0, decode 300 d_6472_1, decode 300 d_6472_2, decode 300 d_6472_3, decode 300 d_6472_4, decode 300 d_6472_5, decode 300 d_6472_6, decode 141 d_6472_7] (fun x hx => bits_full_and hx) cov_6472 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6472_0, ch_6472_1, ch_6472_2, ch_6472_3, ch_6472_4, ch_6472_5, ch_6472_6, ch_6472_7])

theorem root_6473 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6473) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6473_0, decode 300 d_6473_1, decode 300 d_6473_2, decode 300 d_6473_3, decode 300 d_6473_4, decode 300 d_6473_5, decode 300 d_6473_6, decode 141 d_6473_7] (fun x hx => bits_full_and hx) cov_6473 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6473_0, ch_6473_1, ch_6473_2, ch_6473_3, ch_6473_4, ch_6473_5, ch_6473_6, ch_6473_7])

theorem root_6474 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6474) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6474_0, decode 300 d_6474_1, decode 300 d_6474_2, decode 300 d_6474_3, decode 300 d_6474_4, decode 300 d_6474_5, decode 300 d_6474_6, decode 141 d_6474_7] (fun x hx => bits_full_and hx) cov_6474 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6474_0, ch_6474_1, ch_6474_2, ch_6474_3, ch_6474_4, ch_6474_5, ch_6474_6, ch_6474_7])

theorem root_6478 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6478) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6478_0, decode 300 d_6478_1, decode 300 d_6478_2, decode 300 d_6478_3, decode 300 d_6478_4, decode 300 d_6478_5, decode 300 d_6478_6, decode 141 d_6478_7] (fun x hx => bits_full_and hx) cov_6478 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6478_0, ch_6478_1, ch_6478_2, ch_6478_3, ch_6478_4, ch_6478_5, ch_6478_6, ch_6478_7])

theorem roots_96_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_96, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_96, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6399 hB hC hCl hCB, root_6414 hB hC hCl hCB, root_6424 hB hC hCl hCB, root_6425 hB hC hCl hCB, root_6432 hB hC hCl hCB, root_6433 hB hC hCl hCB, root_6434 hB hC hCl hCB, root_6439 hB hC hCl hCB, root_6440 hB hC hCl hCB, root_6442 hB hC hCl hCB, root_6448 hB hC hCl hCB, root_6449 hB hC hCl hCB, root_6450 hB hC hCl hCB, root_6458 hB hC hCl hCB, root_6463 hB hC hCl hCB, root_6468 hB hC hCl hCB, root_6472 hB hC hCl hCB, root_6473 hB hC hCl hCB, root_6474 hB hC hCl hCB, root_6478 hB hC hCl hCB]

theorem root_6479 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6479) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6479_0, decode 300 d_6479_1, decode 300 d_6479_2, decode 300 d_6479_3, decode 300 d_6479_4, decode 300 d_6479_5, decode 300 d_6479_6, decode 141 d_6479_7] (fun x hx => bits_full_and hx) cov_6479 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6479_0, ch_6479_1, ch_6479_2, ch_6479_3, ch_6479_4, ch_6479_5, ch_6479_6, ch_6479_7])

theorem root_6480 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6480) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6480_0, decode 300 d_6480_1, decode 300 d_6480_2, decode 300 d_6480_3, decode 300 d_6480_4, decode 300 d_6480_5, decode 300 d_6480_6, decode 141 d_6480_7] (fun x hx => bits_full_and hx) cov_6480 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6480_0, ch_6480_1, ch_6480_2, ch_6480_3, ch_6480_4, ch_6480_5, ch_6480_6, ch_6480_7])

theorem root_6482 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6482) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6482_0, decode 300 d_6482_1, decode 300 d_6482_2, decode 300 d_6482_3, decode 300 d_6482_4, decode 300 d_6482_5, decode 300 d_6482_6, decode 141 d_6482_7] (fun x hx => bits_full_and hx) cov_6482 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6482_0, ch_6482_1, ch_6482_2, ch_6482_3, ch_6482_4, ch_6482_5, ch_6482_6, ch_6482_7])

theorem root_6483 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6483) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6483_0, decode 300 d_6483_1, decode 300 d_6483_2, decode 300 d_6483_3, decode 300 d_6483_4, decode 300 d_6483_5, decode 300 d_6483_6, decode 141 d_6483_7] (fun x hx => bits_full_and hx) cov_6483 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6483_0, ch_6483_1, ch_6483_2, ch_6483_3, ch_6483_4, ch_6483_5, ch_6483_6, ch_6483_7])

theorem root_6488 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6488) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6488_0, decode 300 d_6488_1, decode 300 d_6488_2, decode 300 d_6488_3, decode 300 d_6488_4, decode 300 d_6488_5, decode 300 d_6488_6, decode 141 d_6488_7] (fun x hx => bits_full_and hx) cov_6488 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6488_0, ch_6488_1, ch_6488_2, ch_6488_3, ch_6488_4, ch_6488_5, ch_6488_6, ch_6488_7])

theorem root_6489 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6489) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6489_0, decode 300 d_6489_1, decode 300 d_6489_2, decode 300 d_6489_3, decode 300 d_6489_4, decode 300 d_6489_5, decode 300 d_6489_6, decode 141 d_6489_7] (fun x hx => bits_full_and hx) cov_6489 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6489_0, ch_6489_1, ch_6489_2, ch_6489_3, ch_6489_4, ch_6489_5, ch_6489_6, ch_6489_7])

theorem root_6492 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6492) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6492_0, decode 300 d_6492_1, decode 300 d_6492_2, decode 300 d_6492_3, decode 300 d_6492_4, decode 300 d_6492_5, decode 300 d_6492_6, decode 141 d_6492_7] (fun x hx => bits_full_and hx) cov_6492 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6492_0, ch_6492_1, ch_6492_2, ch_6492_3, ch_6492_4, ch_6492_5, ch_6492_6, ch_6492_7])

theorem root_6497 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6497) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6497_0, decode 300 d_6497_1, decode 300 d_6497_2, decode 300 d_6497_3, decode 300 d_6497_4, decode 300 d_6497_5, decode 251 d_6497_6] (fun x hx => bits_full_and hx) cov_6497 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6497_0, ch_6497_1, ch_6497_2, ch_6497_3, ch_6497_4, ch_6497_5, ch_6497_6])

theorem root_6498 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6498) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6498_0, decode 300 d_6498_1, decode 300 d_6498_2, decode 300 d_6498_3, decode 300 d_6498_4, decode 300 d_6498_5, decode 251 d_6498_6] (fun x hx => bits_full_and hx) cov_6498 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6498_0, ch_6498_1, ch_6498_2, ch_6498_3, ch_6498_4, ch_6498_5, ch_6498_6])

theorem root_6499 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6499) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6499_0, decode 300 d_6499_1, decode 300 d_6499_2, decode 300 d_6499_3, decode 300 d_6499_4, decode 300 d_6499_5, decode 251 d_6499_6] (fun x hx => bits_full_and hx) cov_6499 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6499_0, ch_6499_1, ch_6499_2, ch_6499_3, ch_6499_4, ch_6499_5, ch_6499_6])

theorem root_6500 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6500) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6500_0, decode 300 d_6500_1, decode 300 d_6500_2, decode 300 d_6500_3, decode 300 d_6500_4, decode 300 d_6500_5, decode 30 d_6500_6] (fun x hx => bits_full_and hx) cov_6500 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6500_0, ch_6500_1, ch_6500_2, ch_6500_3, ch_6500_4, ch_6500_5, ch_6500_6])

theorem root_6503 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6503) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6503_0, decode 300 d_6503_1, decode 300 d_6503_2, decode 300 d_6503_3, decode 300 d_6503_4, decode 300 d_6503_5, decode 65 d_6503_6] (fun x hx => bits_full_and hx) cov_6503 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6503_0, ch_6503_1, ch_6503_2, ch_6503_3, ch_6503_4, ch_6503_5, ch_6503_6])

theorem root_6509 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6509) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6509_0, decode 300 d_6509_1, decode 300 d_6509_2, decode 300 d_6509_3, decode 300 d_6509_4, decode 283 d_6509_5] (fun x hx => bits_full_and hx) cov_6509 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6509_0, ch_6509_1, ch_6509_2, ch_6509_3, ch_6509_4, ch_6509_5])

theorem root_6513 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6513) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6513_0, decode 300 d_6513_1, decode 300 d_6513_2, decode 300 d_6513_3, decode 300 d_6513_4, decode 300 d_6513_5, decode 251 d_6513_6] (fun x hx => bits_full_and hx) cov_6513 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6513_0, ch_6513_1, ch_6513_2, ch_6513_3, ch_6513_4, ch_6513_5, ch_6513_6])

theorem root_6514 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6514) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6514_0, decode 300 d_6514_1, decode 300 d_6514_2, decode 300 d_6514_3, decode 300 d_6514_4, decode 300 d_6514_5, decode 30 d_6514_6] (fun x hx => bits_full_and hx) cov_6514 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6514_0, ch_6514_1, ch_6514_2, ch_6514_3, ch_6514_4, ch_6514_5, ch_6514_6])

theorem root_6517 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6517) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6517_0, decode 300 d_6517_1, decode 300 d_6517_2, decode 300 d_6517_3, decode 300 d_6517_4, decode 300 d_6517_5, decode 30 d_6517_6] (fun x hx => bits_full_and hx) cov_6517 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6517_0, ch_6517_1, ch_6517_2, ch_6517_3, ch_6517_4, ch_6517_5, ch_6517_6])

theorem root_6527 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6527) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6527_0, decode 300 d_6527_1, decode 300 d_6527_2, decode 300 d_6527_3, decode 300 d_6527_4, decode 300 d_6527_5, decode 300 d_6527_6, decode 142 d_6527_7] (fun x hx => bits_full_and hx) cov_6527 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6527_0, ch_6527_1, ch_6527_2, ch_6527_3, ch_6527_4, ch_6527_5, ch_6527_6, ch_6527_7])

theorem root_6535 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6535) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6535_0, decode 300 d_6535_1, decode 300 d_6535_2, decode 300 d_6535_3, decode 300 d_6535_4, decode 300 d_6535_5, decode 300 d_6535_6, decode 142 d_6535_7] (fun x hx => bits_full_and hx) cov_6535 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6535_0, ch_6535_1, ch_6535_2, ch_6535_3, ch_6535_4, ch_6535_5, ch_6535_6, ch_6535_7])

theorem root_6544 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6544) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6544_0, decode 300 d_6544_1, decode 300 d_6544_2, decode 300 d_6544_3, decode 300 d_6544_4, decode 300 d_6544_5, decode 300 d_6544_6, decode 142 d_6544_7] (fun x hx => bits_full_and hx) cov_6544 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6544_0, ch_6544_1, ch_6544_2, ch_6544_3, ch_6544_4, ch_6544_5, ch_6544_6, ch_6544_7])

theorem root_6546 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6546) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6546_0, decode 300 d_6546_1, decode 300 d_6546_2, decode 300 d_6546_3, decode 300 d_6546_4, decode 300 d_6546_5, decode 300 d_6546_6, decode 142 d_6546_7] (fun x hx => bits_full_and hx) cov_6546 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6546_0, ch_6546_1, ch_6546_2, ch_6546_3, ch_6546_4, ch_6546_5, ch_6546_6, ch_6546_7])

theorem roots_97_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_97, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_97, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6479 hB hC hCl hCB, root_6480 hB hC hCl hCB, root_6482 hB hC hCl hCB, root_6483 hB hC hCl hCB, root_6488 hB hC hCl hCB, root_6489 hB hC hCl hCB, root_6492 hB hC hCl hCB, root_6497 hB hC hCl hCB, root_6498 hB hC hCl hCB, root_6499 hB hC hCl hCB, root_6500 hB hC hCl hCB, root_6503 hB hC hCl hCB, root_6509 hB hC hCl hCB, root_6513 hB hC hCl hCB, root_6514 hB hC hCl hCB, root_6517 hB hC hCl hCB, root_6527 hB hC hCl hCB, root_6535 hB hC hCl hCB, root_6544 hB hC hCl hCB, root_6546 hB hC hCl hCB]

theorem root_6552 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6552) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6552_0, decode 300 d_6552_1, decode 300 d_6552_2, decode 300 d_6552_3, decode 300 d_6552_4, decode 300 d_6552_5, decode 300 d_6552_6, decode 142 d_6552_7] (fun x hx => bits_full_and hx) cov_6552 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6552_0, ch_6552_1, ch_6552_2, ch_6552_3, ch_6552_4, ch_6552_5, ch_6552_6, ch_6552_7])

theorem root_6553 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6553) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6553_0, decode 300 d_6553_1, decode 300 d_6553_2, decode 300 d_6553_3, decode 300 d_6553_4, decode 300 d_6553_5, decode 300 d_6553_6, decode 142 d_6553_7] (fun x hx => bits_full_and hx) cov_6553 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6553_0, ch_6553_1, ch_6553_2, ch_6553_3, ch_6553_4, ch_6553_5, ch_6553_6, ch_6553_7])

theorem root_6560 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6560) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6560_0, decode 300 d_6560_1, decode 300 d_6560_2, decode 300 d_6560_3, decode 300 d_6560_4, decode 300 d_6560_5, decode 300 d_6560_6, decode 142 d_6560_7] (fun x hx => bits_full_and hx) cov_6560 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6560_0, ch_6560_1, ch_6560_2, ch_6560_3, ch_6560_4, ch_6560_5, ch_6560_6, ch_6560_7])

theorem root_6561 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6561) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6561_0, decode 300 d_6561_1, decode 300 d_6561_2, decode 300 d_6561_3, decode 300 d_6561_4, decode 300 d_6561_5, decode 300 d_6561_6, decode 142 d_6561_7] (fun x hx => bits_full_and hx) cov_6561 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6561_0, ch_6561_1, ch_6561_2, ch_6561_3, ch_6561_4, ch_6561_5, ch_6561_6, ch_6561_7])

theorem root_6562 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6562) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6562_0, decode 300 d_6562_1, decode 300 d_6562_2, decode 300 d_6562_3, decode 300 d_6562_4, decode 300 d_6562_5, decode 300 d_6562_6, decode 142 d_6562_7] (fun x hx => bits_full_and hx) cov_6562 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6562_0, ch_6562_1, ch_6562_2, ch_6562_3, ch_6562_4, ch_6562_5, ch_6562_6, ch_6562_7])

theorem root_6565 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6565) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6565_0, decode 300 d_6565_1, decode 300 d_6565_2, decode 300 d_6565_3, decode 300 d_6565_4, decode 300 d_6565_5, decode 300 d_6565_6, decode 141 d_6565_7] (fun x hx => bits_full_and hx) cov_6565 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6565_0, ch_6565_1, ch_6565_2, ch_6565_3, ch_6565_4, ch_6565_5, ch_6565_6, ch_6565_7])

theorem root_6574 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6574) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6574_0, decode 300 d_6574_1, decode 300 d_6574_2, decode 300 d_6574_3, decode 300 d_6574_4, decode 300 d_6574_5, decode 300 d_6574_6, decode 141 d_6574_7] (fun x hx => bits_full_and hx) cov_6574 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6574_0, ch_6574_1, ch_6574_2, ch_6574_3, ch_6574_4, ch_6574_5, ch_6574_6, ch_6574_7])

theorem root_6580 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6580) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6580_0, decode 300 d_6580_1, decode 300 d_6580_2, decode 300 d_6580_3, decode 300 d_6580_4, decode 300 d_6580_5, decode 300 d_6580_6, decode 141 d_6580_7] (fun x hx => bits_full_and hx) cov_6580 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6580_0, ch_6580_1, ch_6580_2, ch_6580_3, ch_6580_4, ch_6580_5, ch_6580_6, ch_6580_7])

theorem root_6581 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6581) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6581_0, decode 300 d_6581_1, decode 300 d_6581_2, decode 300 d_6581_3, decode 300 d_6581_4, decode 300 d_6581_5, decode 78 d_6581_6] (fun x hx => bits_full_and hx) cov_6581 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6581_0, ch_6581_1, ch_6581_2, ch_6581_3, ch_6581_4, ch_6581_5, ch_6581_6])

theorem root_6582 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6582) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6582_0, decode 300 d_6582_1, decode 300 d_6582_2, decode 300 d_6582_3, decode 300 d_6582_4, decode 300 d_6582_5, decode 78 d_6582_6] (fun x hx => bits_full_and hx) cov_6582 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6582_0, ch_6582_1, ch_6582_2, ch_6582_3, ch_6582_4, ch_6582_5, ch_6582_6])

theorem root_6586 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6586) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6586_0, decode 300 d_6586_1, decode 300 d_6586_2, decode 300 d_6586_3, decode 300 d_6586_4, decode 300 d_6586_5, decode 251 d_6586_6] (fun x hx => bits_full_and hx) cov_6586 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6586_0, ch_6586_1, ch_6586_2, ch_6586_3, ch_6586_4, ch_6586_5, ch_6586_6])

theorem root_6587 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6587) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6587_0, decode 300 d_6587_1, decode 300 d_6587_2, decode 300 d_6587_3, decode 300 d_6587_4, decode 300 d_6587_5, decode 251 d_6587_6] (fun x hx => bits_full_and hx) cov_6587 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6587_0, ch_6587_1, ch_6587_2, ch_6587_3, ch_6587_4, ch_6587_5, ch_6587_6])

theorem root_6588 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6588) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6588_0, decode 300 d_6588_1, decode 300 d_6588_2, decode 300 d_6588_3, decode 300 d_6588_4, decode 300 d_6588_5, decode 300 d_6588_6, decode 141 d_6588_7] (fun x hx => bits_full_and hx) cov_6588 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6588_0, ch_6588_1, ch_6588_2, ch_6588_3, ch_6588_4, ch_6588_5, ch_6588_6, ch_6588_7])

theorem root_6594 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6594) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6594_0, decode 300 d_6594_1, decode 300 d_6594_2, decode 300 d_6594_3, decode 300 d_6594_4, decode 300 d_6594_5, decode 300 d_6594_6, decode 141 d_6594_7] (fun x hx => bits_full_and hx) cov_6594 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6594_0, ch_6594_1, ch_6594_2, ch_6594_3, ch_6594_4, ch_6594_5, ch_6594_6, ch_6594_7])

theorem root_6598 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6598) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6598_0, decode 300 d_6598_1, decode 300 d_6598_2, decode 300 d_6598_3, decode 300 d_6598_4, decode 300 d_6598_5, decode 300 d_6598_6, decode 141 d_6598_7] (fun x hx => bits_full_and hx) cov_6598 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6598_0, ch_6598_1, ch_6598_2, ch_6598_3, ch_6598_4, ch_6598_5, ch_6598_6, ch_6598_7])

theorem root_6603 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6603) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6603_0, decode 300 d_6603_1, decode 300 d_6603_2, decode 300 d_6603_3, decode 300 d_6603_4, decode 300 d_6603_5, decode 300 d_6603_6, decode 141 d_6603_7] (fun x hx => bits_full_and hx) cov_6603 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6603_0, ch_6603_1, ch_6603_2, ch_6603_3, ch_6603_4, ch_6603_5, ch_6603_6, ch_6603_7])

theorem root_6605 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6605) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6605_0, decode 300 d_6605_1, decode 300 d_6605_2, decode 300 d_6605_3, decode 300 d_6605_4, decode 300 d_6605_5, decode 300 d_6605_6, decode 141 d_6605_7] (fun x hx => bits_full_and hx) cov_6605 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6605_0, ch_6605_1, ch_6605_2, ch_6605_3, ch_6605_4, ch_6605_5, ch_6605_6, ch_6605_7])

theorem root_6613 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6613) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6613_0, decode 300 d_6613_1, decode 300 d_6613_2, decode 300 d_6613_3, decode 300 d_6613_4, decode 300 d_6613_5, decode 300 d_6613_6, decode 141 d_6613_7] (fun x hx => bits_full_and hx) cov_6613 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6613_0, ch_6613_1, ch_6613_2, ch_6613_3, ch_6613_4, ch_6613_5, ch_6613_6, ch_6613_7])

theorem root_6614 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6614) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6614_0, decode 300 d_6614_1, decode 300 d_6614_2, decode 300 d_6614_3, decode 300 d_6614_4, decode 300 d_6614_5, decode 300 d_6614_6, decode 142 d_6614_7] (fun x hx => bits_full_and hx) cov_6614 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6614_0, ch_6614_1, ch_6614_2, ch_6614_3, ch_6614_4, ch_6614_5, ch_6614_6, ch_6614_7])

theorem roots_98_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_98, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_98, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6552 hB hC hCl hCB, root_6553 hB hC hCl hCB, root_6560 hB hC hCl hCB, root_6561 hB hC hCl hCB, root_6562 hB hC hCl hCB, root_6565 hB hC hCl hCB, root_6574 hB hC hCl hCB, root_6580 hB hC hCl hCB, root_6581 hB hC hCl hCB, root_6582 hB hC hCl hCB, root_6586 hB hC hCl hCB, root_6587 hB hC hCl hCB, root_6588 hB hC hCl hCB, root_6594 hB hC hCl hCB, root_6598 hB hC hCl hCB, root_6603 hB hC hCl hCB, root_6605 hB hC hCl hCB, root_6613 hB hC hCl hCB, root_6614 hB hC hCl hCB]

theorem root_6615 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6615) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6615_0, decode 300 d_6615_1, decode 300 d_6615_2, decode 300 d_6615_3, decode 300 d_6615_4, decode 300 d_6615_5, decode 300 d_6615_6, decode 142 d_6615_7] (fun x hx => bits_full_and hx) cov_6615 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6615_0, ch_6615_1, ch_6615_2, ch_6615_3, ch_6615_4, ch_6615_5, ch_6615_6, ch_6615_7])

theorem root_6626 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6626) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6626_0, decode 300 d_6626_1, decode 300 d_6626_2, decode 300 d_6626_3, decode 300 d_6626_4, decode 300 d_6626_5, decode 300 d_6626_6, decode 141 d_6626_7] (fun x hx => bits_full_and hx) cov_6626 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6626_0, ch_6626_1, ch_6626_2, ch_6626_3, ch_6626_4, ch_6626_5, ch_6626_6, ch_6626_7])

theorem root_6635 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6635) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6635_0, decode 300 d_6635_1, decode 300 d_6635_2, decode 300 d_6635_3, decode 300 d_6635_4, decode 300 d_6635_5, decode 300 d_6635_6, decode 141 d_6635_7] (fun x hx => bits_full_and hx) cov_6635 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6635_0, ch_6635_1, ch_6635_2, ch_6635_3, ch_6635_4, ch_6635_5, ch_6635_6, ch_6635_7])

theorem root_6642 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6642) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6642_0, decode 300 d_6642_1, decode 300 d_6642_2, decode 300 d_6642_3, decode 300 d_6642_4, decode 300 d_6642_5, decode 300 d_6642_6, decode 141 d_6642_7] (fun x hx => bits_full_and hx) cov_6642 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6642_0, ch_6642_1, ch_6642_2, ch_6642_3, ch_6642_4, ch_6642_5, ch_6642_6, ch_6642_7])

theorem root_6643 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6643) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6643_0, decode 300 d_6643_1, decode 300 d_6643_2, decode 300 d_6643_3, decode 300 d_6643_4, decode 300 d_6643_5, decode 300 d_6643_6, decode 142 d_6643_7] (fun x hx => bits_full_and hx) cov_6643 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6643_0, ch_6643_1, ch_6643_2, ch_6643_3, ch_6643_4, ch_6643_5, ch_6643_6, ch_6643_7])

theorem root_6644 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6644) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6644_0, decode 300 d_6644_1, decode 300 d_6644_2, decode 300 d_6644_3, decode 300 d_6644_4, decode 300 d_6644_5, decode 34 d_6644_6] (fun x hx => bits_full_and hx) cov_6644 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6644_0, ch_6644_1, ch_6644_2, ch_6644_3, ch_6644_4, ch_6644_5, ch_6644_6])

theorem root_6649 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6649) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6649_0, decode 300 d_6649_1, decode 300 d_6649_2, decode 300 d_6649_3, decode 300 d_6649_4, decode 300 d_6649_5, decode 28 d_6649_6] (fun x hx => bits_full_and hx) cov_6649 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6649_0, ch_6649_1, ch_6649_2, ch_6649_3, ch_6649_4, ch_6649_5, ch_6649_6])

theorem root_6673 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6673) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6673_0, decode 300 d_6673_1, decode 300 d_6673_2, decode 300 d_6673_3, decode 300 d_6673_4, decode 300 d_6673_5, decode 300 d_6673_6, decode 141 d_6673_7] (fun x hx => bits_full_and hx) cov_6673 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6673_0, ch_6673_1, ch_6673_2, ch_6673_3, ch_6673_4, ch_6673_5, ch_6673_6, ch_6673_7])

theorem root_6674 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6674) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6674_0, decode 300 d_6674_1, decode 300 d_6674_2, decode 300 d_6674_3, decode 300 d_6674_4, decode 300 d_6674_5, decode 300 d_6674_6, decode 142 d_6674_7] (fun x hx => bits_full_and hx) cov_6674 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6674_0, ch_6674_1, ch_6674_2, ch_6674_3, ch_6674_4, ch_6674_5, ch_6674_6, ch_6674_7])

theorem root_6675 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6675) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6675_0, decode 300 d_6675_1, decode 300 d_6675_2, decode 300 d_6675_3, decode 300 d_6675_4, decode 300 d_6675_5, decode 300 d_6675_6, decode 142 d_6675_7] (fun x hx => bits_full_and hx) cov_6675 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6675_0, ch_6675_1, ch_6675_2, ch_6675_3, ch_6675_4, ch_6675_5, ch_6675_6, ch_6675_7])

theorem root_6684 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6684) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6684_0, decode 300 d_6684_1, decode 300 d_6684_2, decode 300 d_6684_3, decode 300 d_6684_4, decode 300 d_6684_5, decode 11 d_6684_6] (fun x hx => bits_full_and hx) cov_6684 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6684_0, ch_6684_1, ch_6684_2, ch_6684_3, ch_6684_4, ch_6684_5, ch_6684_6])

theorem root_6685 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6685) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6685_0, decode 300 d_6685_1, decode 300 d_6685_2, decode 300 d_6685_3, decode 300 d_6685_4, decode 294 d_6685_5] (fun x hx => bits_full_and hx) cov_6685 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6685_0, ch_6685_1, ch_6685_2, ch_6685_3, ch_6685_4, ch_6685_5])

theorem root_6686 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6686) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6686_0, decode 300 d_6686_1, decode 300 d_6686_2, decode 300 d_6686_3, decode 300 d_6686_4, decode 294 d_6686_5] (fun x hx => bits_full_and hx) cov_6686 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6686_0, ch_6686_1, ch_6686_2, ch_6686_3, ch_6686_4, ch_6686_5])

theorem root_6688 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6688) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6688_0, decode 300 d_6688_1, decode 300 d_6688_2, decode 300 d_6688_3, decode 300 d_6688_4, decode 300 d_6688_5, decode 63 d_6688_6] (fun x hx => bits_full_and hx) cov_6688 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6688_0, ch_6688_1, ch_6688_2, ch_6688_3, ch_6688_4, ch_6688_5, ch_6688_6])

theorem root_6693 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6693) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6693_0, decode 300 d_6693_1, decode 300 d_6693_2, decode 300 d_6693_3, decode 300 d_6693_4, decode 300 d_6693_5, decode 35 d_6693_6] (fun x hx => bits_full_and hx) cov_6693 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6693_0, ch_6693_1, ch_6693_2, ch_6693_3, ch_6693_4, ch_6693_5, ch_6693_6])

theorem root_6696 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6696) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6696_0, decode 300 d_6696_1, decode 300 d_6696_2, decode 300 d_6696_3, decode 300 d_6696_4, decode 300 d_6696_5, decode 63 d_6696_6] (fun x hx => bits_full_and hx) cov_6696 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6696_0, ch_6696_1, ch_6696_2, ch_6696_3, ch_6696_4, ch_6696_5, ch_6696_6])

theorem root_6697 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6697) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6697_0, decode 300 d_6697_1, decode 300 d_6697_2, decode 300 d_6697_3, decode 300 d_6697_4, decode 300 d_6697_5, decode 35 d_6697_6] (fun x hx => bits_full_and hx) cov_6697 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6697_0, ch_6697_1, ch_6697_2, ch_6697_3, ch_6697_4, ch_6697_5, ch_6697_6])

theorem root_6701 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6701) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6701_0, decode 300 d_6701_1, decode 300 d_6701_2, decode 300 d_6701_3, decode 300 d_6701_4, decode 300 d_6701_5, decode 300 d_6701_6, decode 141 d_6701_7] (fun x hx => bits_full_and hx) cov_6701 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6701_0, ch_6701_1, ch_6701_2, ch_6701_3, ch_6701_4, ch_6701_5, ch_6701_6, ch_6701_7])

theorem root_6702 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6702) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6702_0, decode 300 d_6702_1, decode 300 d_6702_2, decode 300 d_6702_3, decode 300 d_6702_4, decode 300 d_6702_5, decode 300 d_6702_6, decode 142 d_6702_7] (fun x hx => bits_full_and hx) cov_6702 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6702_0, ch_6702_1, ch_6702_2, ch_6702_3, ch_6702_4, ch_6702_5, ch_6702_6, ch_6702_7])

theorem root_6703 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6703) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6703_0, decode 300 d_6703_1, decode 300 d_6703_2, decode 300 d_6703_3, decode 300 d_6703_4, decode 300 d_6703_5, decode 300 d_6703_6, decode 142 d_6703_7] (fun x hx => bits_full_and hx) cov_6703 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6703_0, ch_6703_1, ch_6703_2, ch_6703_3, ch_6703_4, ch_6703_5, ch_6703_6, ch_6703_7])

theorem roots_99_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_99, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_99, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6615 hB hC hCl hCB, root_6626 hB hC hCl hCB, root_6635 hB hC hCl hCB, root_6642 hB hC hCl hCB, root_6643 hB hC hCl hCB, root_6644 hB hC hCl hCB, root_6649 hB hC hCl hCB, root_6673 hB hC hCl hCB, root_6674 hB hC hCl hCB, root_6675 hB hC hCl hCB, root_6684 hB hC hCl hCB, root_6685 hB hC hCl hCB, root_6686 hB hC hCl hCB, root_6688 hB hC hCl hCB, root_6693 hB hC hCl hCB, root_6696 hB hC hCl hCB, root_6697 hB hC hCl hCB, root_6701 hB hC hCl hCB, root_6702 hB hC hCl hCB, root_6703 hB hC hCl hCB]

end LRC.O7U5
