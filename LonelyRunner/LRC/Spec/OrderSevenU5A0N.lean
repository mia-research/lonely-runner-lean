import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C0N
import LonelyRunner.LRC.Spec.OrderSevenU5C1N
import LonelyRunner.LRC.Spec.OrderSevenU5C2N
import LonelyRunner.LRC.Spec.OrderSevenU5C3N
import LonelyRunner.LRC.Spec.OrderSevenU5C4N
import LonelyRunner.LRC.Spec.OrderSevenU5C5N
import LonelyRunner.LRC.Spec.OrderSevenU5C6N
import LonelyRunner.LRC.Spec.OrderSevenU5C7N
import LonelyRunner.LRC.Spec.OrderSevenU5C8N
import LonelyRunner.LRC.Spec.OrderSevenU5C9N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_6 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6_0, decode 300 d_6_1, decode 300 d_6_2, decode 300 d_6_3, decode 300 d_6_4, decode 300 d_6_5, decode 37 d_6_6] (fun x hx => bits_full_and hx) cov_6 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6_0, ch_6_1, ch_6_2, ch_6_3, ch_6_4, ch_6_5, ch_6_6])

theorem root_7 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7_0, decode 300 d_7_1, decode 300 d_7_2, decode 300 d_7_3, decode 300 d_7_4, decode 300 d_7_5, decode 36 d_7_6] (fun x hx => bits_full_and hx) cov_7 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7_0, ch_7_1, ch_7_2, ch_7_3, ch_7_4, ch_7_5, ch_7_6])

theorem root_11 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 11) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_11_0, decode 300 d_11_1, decode 300 d_11_2, decode 300 d_11_3, decode 300 d_11_4, decode 270 d_11_5] (fun x hx => bits_full_and hx) cov_11 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_11_0, ch_11_1, ch_11_2, ch_11_3, ch_11_4, ch_11_5])

theorem root_12 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 12) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_12_0, decode 300 d_12_1, decode 300 d_12_2, decode 300 d_12_3, decode 300 d_12_4, decode 287 d_12_5] (fun x hx => bits_full_and hx) cov_12 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_12_0, ch_12_1, ch_12_2, ch_12_3, ch_12_4, ch_12_5])

theorem root_13 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 13) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_13_0, decode 300 d_13_1, decode 300 d_13_2, decode 300 d_13_3, decode 300 d_13_4, decode 287 d_13_5] (fun x hx => bits_full_and hx) cov_13 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_13_0, ch_13_1, ch_13_2, ch_13_3, ch_13_4, ch_13_5])

theorem root_21 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 21) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_21_0, decode 300 d_21_1, decode 300 d_21_2, decode 300 d_21_3, decode 300 d_21_4, decode 270 d_21_5] (fun x hx => bits_full_and hx) cov_21 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_21_0, ch_21_1, ch_21_2, ch_21_3, ch_21_4, ch_21_5])

theorem root_22 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 22) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_22_0, decode 300 d_22_1, decode 300 d_22_2, decode 300 d_22_3, decode 300 d_22_4, decode 270 d_22_5] (fun x hx => bits_full_and hx) cov_22 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_22_0, ch_22_1, ch_22_2, ch_22_3, ch_22_4, ch_22_5])

theorem root_23 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 23) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_23_0, decode 300 d_23_1, decode 300 d_23_2, decode 300 d_23_3, decode 300 d_23_4, decode 270 d_23_5] (fun x hx => bits_full_and hx) cov_23 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_23_0, ch_23_1, ch_23_2, ch_23_3, ch_23_4, ch_23_5])

theorem root_33 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 33) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_33_0, decode 300 d_33_1, decode 300 d_33_2, decode 300 d_33_3, decode 300 d_33_4, decode 300 d_33_5, decode 42 d_33_6] (fun x hx => bits_full_and hx) cov_33 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_33_0, ch_33_1, ch_33_2, ch_33_3, ch_33_4, ch_33_5, ch_33_6])

theorem root_42 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 42) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_42_0, decode 300 d_42_1, decode 300 d_42_2, decode 300 d_42_3, decode 300 d_42_4, decode 300 d_42_5, decode 24 d_42_6] (fun x hx => bits_full_and hx) cov_42 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_42_0, ch_42_1, ch_42_2, ch_42_3, ch_42_4, ch_42_5, ch_42_6])

theorem root_43 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 43) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_43_0, decode 300 d_43_1, decode 300 d_43_2, decode 300 d_43_3, decode 300 d_43_4, decode 300 d_43_5, decode 42 d_43_6] (fun x hx => bits_full_and hx) cov_43 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_43_0, ch_43_1, ch_43_2, ch_43_3, ch_43_4, ch_43_5, ch_43_6])

theorem root_44 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 44) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_44_0, decode 300 d_44_1, decode 300 d_44_2, decode 300 d_44_3, decode 300 d_44_4, decode 300 d_44_5, decode 42 d_44_6] (fun x hx => bits_full_and hx) cov_44 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_44_0, ch_44_1, ch_44_2, ch_44_3, ch_44_4, ch_44_5, ch_44_6])

theorem root_45 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 45) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_45_0, decode 300 d_45_1, decode 300 d_45_2, decode 300 d_45_3, decode 300 d_45_4, decode 300 d_45_5, decode 42 d_45_6] (fun x hx => bits_full_and hx) cov_45 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_45_0, ch_45_1, ch_45_2, ch_45_3, ch_45_4, ch_45_5, ch_45_6])

theorem root_51 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 51) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_51_0, decode 300 d_51_1, decode 300 d_51_2, decode 300 d_51_3, decode 300 d_51_4, decode 300 d_51_5, decode 42 d_51_6] (fun x hx => bits_full_and hx) cov_51 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_51_0, ch_51_1, ch_51_2, ch_51_3, ch_51_4, ch_51_5, ch_51_6])

theorem root_52 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 52) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_52_0, decode 300 d_52_1, decode 300 d_52_2, decode 300 d_52_3, decode 300 d_52_4, decode 300 d_52_5, decode 24 d_52_6] (fun x hx => bits_full_and hx) cov_52 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_52_0, ch_52_1, ch_52_2, ch_52_3, ch_52_4, ch_52_5, ch_52_6])

theorem root_53 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 53) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_53_0, decode 300 d_53_1, decode 300 d_53_2, decode 300 d_53_3, decode 300 d_53_4, decode 300 d_53_5, decode 24 d_53_6] (fun x hx => bits_full_and hx) cov_53 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_53_0, ch_53_1, ch_53_2, ch_53_3, ch_53_4, ch_53_5, ch_53_6])

theorem root_55 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 55) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_55_0, decode 300 d_55_1, decode 300 d_55_2, decode 300 d_55_3, decode 300 d_55_4, decode 300 d_55_5, decode 42 d_55_6] (fun x hx => bits_full_and hx) cov_55 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_55_0, ch_55_1, ch_55_2, ch_55_3, ch_55_4, ch_55_5, ch_55_6])

theorem root_56 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 56) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_56_0, decode 300 d_56_1, decode 300 d_56_2, decode 300 d_56_3, decode 300 d_56_4, decode 300 d_56_5, decode 300 d_56_6, decode 142 d_56_7] (fun x hx => bits_full_and hx) cov_56 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_56_0, ch_56_1, ch_56_2, ch_56_3, ch_56_4, ch_56_5, ch_56_6, ch_56_7])

theorem root_57 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 57) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_57_0, decode 300 d_57_1, decode 300 d_57_2, decode 300 d_57_3, decode 300 d_57_4, decode 300 d_57_5, decode 300 d_57_6, decode 142 d_57_7] (fun x hx => bits_full_and hx) cov_57 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_57_0, ch_57_1, ch_57_2, ch_57_3, ch_57_4, ch_57_5, ch_57_6, ch_57_7])

theorem root_61 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 61) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_61_0, decode 300 d_61_1, decode 300 d_61_2, decode 300 d_61_3, decode 300 d_61_4, decode 300 d_61_5, decode 300 d_61_6, decode 141 d_61_7] (fun x hx => bits_full_and hx) cov_61 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_61_0, ch_61_1, ch_61_2, ch_61_3, ch_61_4, ch_61_5, ch_61_6, ch_61_7])

theorem root_62 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 62) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_62_0, decode 300 d_62_1, decode 300 d_62_2, decode 300 d_62_3, decode 300 d_62_4, decode 300 d_62_5, decode 300 d_62_6, decode 141 d_62_7] (fun x hx => bits_full_and hx) cov_62 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_62_0, ch_62_1, ch_62_2, ch_62_3, ch_62_4, ch_62_5, ch_62_6, ch_62_7])

theorem root_66 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 66) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_66_0, decode 300 d_66_1, decode 300 d_66_2, decode 300 d_66_3, decode 300 d_66_4, decode 300 d_66_5, decode 300 d_66_6, decode 141 d_66_7] (fun x hx => bits_full_and hx) cov_66 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_66_0, ch_66_1, ch_66_2, ch_66_3, ch_66_4, ch_66_5, ch_66_6, ch_66_7])

theorem roots_0_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_0, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_0, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6 hB hC hCl hCB, root_7 hB hC hCl hCB, root_11 hB hC hCl hCB, root_12 hB hC hCl hCB, root_13 hB hC hCl hCB, root_21 hB hC hCl hCB, root_22 hB hC hCl hCB, root_23 hB hC hCl hCB, root_33 hB hC hCl hCB, root_42 hB hC hCl hCB, root_43 hB hC hCl hCB, root_44 hB hC hCl hCB, root_45 hB hC hCl hCB, root_51 hB hC hCl hCB, root_52 hB hC hCl hCB, root_53 hB hC hCl hCB, root_55 hB hC hCl hCB, root_56 hB hC hCl hCB, root_57 hB hC hCl hCB, root_61 hB hC hCl hCB, root_62 hB hC hCl hCB, root_66 hB hC hCl hCB]

theorem root_67 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 67) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_67_0, decode 300 d_67_1, decode 300 d_67_2, decode 300 d_67_3, decode 300 d_67_4, decode 300 d_67_5, decode 300 d_67_6, decode 141 d_67_7] (fun x hx => bits_full_and hx) cov_67 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_67_0, ch_67_1, ch_67_2, ch_67_3, ch_67_4, ch_67_5, ch_67_6, ch_67_7])

theorem root_68 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 68) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_68_0, decode 300 d_68_1, decode 300 d_68_2, decode 300 d_68_3, decode 300 d_68_4, decode 300 d_68_5, decode 300 d_68_6, decode 141 d_68_7] (fun x hx => bits_full_and hx) cov_68 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_68_0, ch_68_1, ch_68_2, ch_68_3, ch_68_4, ch_68_5, ch_68_6, ch_68_7])

theorem root_72 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 72) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_72_0, decode 300 d_72_1, decode 300 d_72_2, decode 300 d_72_3, decode 300 d_72_4, decode 300 d_72_5, decode 300 d_72_6, decode 141 d_72_7] (fun x hx => bits_full_and hx) cov_72 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_72_0, ch_72_1, ch_72_2, ch_72_3, ch_72_4, ch_72_5, ch_72_6, ch_72_7])

theorem root_76 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 76) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_76_0, decode 300 d_76_1, decode 300 d_76_2, decode 300 d_76_3, decode 300 d_76_4, decode 300 d_76_5, decode 300 d_76_6, decode 142 d_76_7] (fun x hx => bits_full_and hx) cov_76 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_76_0, ch_76_1, ch_76_2, ch_76_3, ch_76_4, ch_76_5, ch_76_6, ch_76_7])

theorem root_85 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 85) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_85_0, decode 300 d_85_1, decode 300 d_85_2, decode 300 d_85_3, decode 300 d_85_4, decode 300 d_85_5, decode 300 d_85_6, decode 160 d_85_7] (fun x hx => bits_full_and hx) cov_85 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_85_0, ch_85_1, ch_85_2, ch_85_3, ch_85_4, ch_85_5, ch_85_6, ch_85_7])

theorem root_86 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 86) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_86_0, decode 300 d_86_1, decode 300 d_86_2, decode 300 d_86_3, decode 300 d_86_4, decode 300 d_86_5, decode 300 d_86_6, decode 141 d_86_7] (fun x hx => bits_full_and hx) cov_86 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_86_0, ch_86_1, ch_86_2, ch_86_3, ch_86_4, ch_86_5, ch_86_6, ch_86_7])

theorem root_90 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 90) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_90_0, decode 300 d_90_1, decode 300 d_90_2, decode 300 d_90_3, decode 300 d_90_4, decode 300 d_90_5, decode 300 d_90_6, decode 141 d_90_7] (fun x hx => bits_full_and hx) cov_90 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_90_0, ch_90_1, ch_90_2, ch_90_3, ch_90_4, ch_90_5, ch_90_6, ch_90_7])

theorem root_93 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 93) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_93_0, decode 300 d_93_1, decode 300 d_93_2, decode 300 d_93_3, decode 300 d_93_4, decode 300 d_93_5, decode 300 d_93_6, decode 141 d_93_7] (fun x hx => bits_full_and hx) cov_93 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_93_0, ch_93_1, ch_93_2, ch_93_3, ch_93_4, ch_93_5, ch_93_6, ch_93_7])

theorem root_94 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 94) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_94_0, decode 300 d_94_1, decode 300 d_94_2, decode 300 d_94_3, decode 300 d_94_4, decode 300 d_94_5, decode 300 d_94_6, decode 141 d_94_7] (fun x hx => bits_full_and hx) cov_94 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_94_0, ch_94_1, ch_94_2, ch_94_3, ch_94_4, ch_94_5, ch_94_6, ch_94_7])

theorem root_100 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 100) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_100_0, decode 300 d_100_1, decode 300 d_100_2, decode 300 d_100_3, decode 300 d_100_4, decode 300 d_100_5, decode 300 d_100_6, decode 141 d_100_7] (fun x hx => bits_full_and hx) cov_100 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_100_0, ch_100_1, ch_100_2, ch_100_3, ch_100_4, ch_100_5, ch_100_6, ch_100_7])

theorem root_103 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 103) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_103_0, decode 300 d_103_1, decode 300 d_103_2, decode 300 d_103_3, decode 300 d_103_4, decode 300 d_103_5, decode 300 d_103_6, decode 141 d_103_7] (fun x hx => bits_full_and hx) cov_103 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_103_0, ch_103_1, ch_103_2, ch_103_3, ch_103_4, ch_103_5, ch_103_6, ch_103_7])

theorem root_106 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 106) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_106_0, decode 300 d_106_1, decode 300 d_106_2, decode 300 d_106_3, decode 300 d_106_4, decode 300 d_106_5, decode 300 d_106_6, decode 142 d_106_7] (fun x hx => bits_full_and hx) cov_106 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_106_0, ch_106_1, ch_106_2, ch_106_3, ch_106_4, ch_106_5, ch_106_6, ch_106_7])

theorem root_109 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 109) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_109_0, decode 300 d_109_1, decode 300 d_109_2, decode 300 d_109_3, decode 300 d_109_4, decode 300 d_109_5, decode 300 d_109_6, decode 141 d_109_7] (fun x hx => bits_full_and hx) cov_109 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_109_0, ch_109_1, ch_109_2, ch_109_3, ch_109_4, ch_109_5, ch_109_6, ch_109_7])

theorem root_110 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 110) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_110_0, decode 300 d_110_1, decode 300 d_110_2, decode 300 d_110_3, decode 300 d_110_4, decode 300 d_110_5, decode 300 d_110_6, decode 141 d_110_7] (fun x hx => bits_full_and hx) cov_110 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_110_0, ch_110_1, ch_110_2, ch_110_3, ch_110_4, ch_110_5, ch_110_6, ch_110_7])

theorem root_111 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 111) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_111_0, decode 300 d_111_1, decode 300 d_111_2, decode 300 d_111_3, decode 300 d_111_4, decode 300 d_111_5, decode 300 d_111_6, decode 141 d_111_7] (fun x hx => bits_full_and hx) cov_111 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_111_0, ch_111_1, ch_111_2, ch_111_3, ch_111_4, ch_111_5, ch_111_6, ch_111_7])

theorem root_114 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 114) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_114_0, decode 300 d_114_1, decode 300 d_114_2, decode 300 d_114_3, decode 300 d_114_4, decode 300 d_114_5, decode 300 d_114_6, decode 142 d_114_7] (fun x hx => bits_full_and hx) cov_114 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_114_0, ch_114_1, ch_114_2, ch_114_3, ch_114_4, ch_114_5, ch_114_6, ch_114_7])

theorem root_115 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 115) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_115_0, decode 300 d_115_1, decode 300 d_115_2, decode 300 d_115_3, decode 300 d_115_4, decode 300 d_115_5, decode 300 d_115_6, decode 142 d_115_7] (fun x hx => bits_full_and hx) cov_115 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_115_0, ch_115_1, ch_115_2, ch_115_3, ch_115_4, ch_115_5, ch_115_6, ch_115_7])

theorem root_116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_116_0, decode 300 d_116_1, decode 300 d_116_2, decode 300 d_116_3, decode 300 d_116_4, decode 300 d_116_5, decode 300 d_116_6, decode 142 d_116_7] (fun x hx => bits_full_and hx) cov_116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_116_0, ch_116_1, ch_116_2, ch_116_3, ch_116_4, ch_116_5, ch_116_6, ch_116_7])

theorem roots_1_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_1, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_1, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_67 hB hC hCl hCB, root_68 hB hC hCl hCB, root_72 hB hC hCl hCB, root_76 hB hC hCl hCB, root_85 hB hC hCl hCB, root_86 hB hC hCl hCB, root_90 hB hC hCl hCB, root_93 hB hC hCl hCB, root_94 hB hC hCl hCB, root_100 hB hC hCl hCB, root_103 hB hC hCl hCB, root_106 hB hC hCl hCB, root_109 hB hC hCl hCB, root_110 hB hC hCl hCB, root_111 hB hC hCl hCB, root_114 hB hC hCl hCB, root_115 hB hC hCl hCB, root_116 hB hC hCl hCB]

theorem root_123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_123_0, decode 300 d_123_1, decode 300 d_123_2, decode 300 d_123_3, decode 300 d_123_4, decode 300 d_123_5, decode 300 d_123_6, decode 141 d_123_7] (fun x hx => bits_full_and hx) cov_123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_123_0, ch_123_1, ch_123_2, ch_123_3, ch_123_4, ch_123_5, ch_123_6, ch_123_7])

theorem root_128 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 128) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_128_0, decode 300 d_128_1, decode 300 d_128_2, decode 300 d_128_3, decode 300 d_128_4, decode 300 d_128_5, decode 300 d_128_6, decode 141 d_128_7] (fun x hx => bits_full_and hx) cov_128 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_128_0, ch_128_1, ch_128_2, ch_128_3, ch_128_4, ch_128_5, ch_128_6, ch_128_7])

theorem root_129 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 129) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_129_0, decode 300 d_129_1, decode 300 d_129_2, decode 300 d_129_3, decode 300 d_129_4, decode 300 d_129_5, decode 300 d_129_6, decode 141 d_129_7] (fun x hx => bits_full_and hx) cov_129 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_129_0, ch_129_1, ch_129_2, ch_129_3, ch_129_4, ch_129_5, ch_129_6, ch_129_7])

theorem root_139 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 139) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_139_0, decode 300 d_139_1, decode 300 d_139_2, decode 300 d_139_3, decode 300 d_139_4, decode 300 d_139_5, decode 300 d_139_6, decode 141 d_139_7] (fun x hx => bits_full_and hx) cov_139 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_139_0, ch_139_1, ch_139_2, ch_139_3, ch_139_4, ch_139_5, ch_139_6, ch_139_7])

theorem root_142 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 142) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_142_0, decode 300 d_142_1, decode 300 d_142_2, decode 300 d_142_3, decode 300 d_142_4, decode 300 d_142_5, decode 300 d_142_6, decode 141 d_142_7] (fun x hx => bits_full_and hx) cov_142 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_142_0, ch_142_1, ch_142_2, ch_142_3, ch_142_4, ch_142_5, ch_142_6, ch_142_7])

theorem root_146 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 146) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_146_0, decode 300 d_146_1, decode 300 d_146_2, decode 300 d_146_3, decode 300 d_146_4, decode 300 d_146_5, decode 300 d_146_6, decode 141 d_146_7] (fun x hx => bits_full_and hx) cov_146 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_146_0, ch_146_1, ch_146_2, ch_146_3, ch_146_4, ch_146_5, ch_146_6, ch_146_7])

theorem root_151 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 151) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_151_0, decode 300 d_151_1, decode 300 d_151_2, decode 300 d_151_3, decode 300 d_151_4, decode 300 d_151_5, decode 300 d_151_6, decode 141 d_151_7] (fun x hx => bits_full_and hx) cov_151 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_151_0, ch_151_1, ch_151_2, ch_151_3, ch_151_4, ch_151_5, ch_151_6, ch_151_7])

theorem root_153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_153_0, decode 300 d_153_1, decode 300 d_153_2, decode 300 d_153_3, decode 300 d_153_4, decode 300 d_153_5, decode 300 d_153_6, decode 141 d_153_7] (fun x hx => bits_full_and hx) cov_153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_153_0, ch_153_1, ch_153_2, ch_153_3, ch_153_4, ch_153_5, ch_153_6, ch_153_7])

theorem root_154 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 154) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_154_0, decode 300 d_154_1, decode 300 d_154_2, decode 300 d_154_3, decode 300 d_154_4, decode 300 d_154_5, decode 300 d_154_6, decode 141 d_154_7] (fun x hx => bits_full_and hx) cov_154 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_154_0, ch_154_1, ch_154_2, ch_154_3, ch_154_4, ch_154_5, ch_154_6, ch_154_7])

theorem root_155 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 155) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_155_0, decode 300 d_155_1, decode 300 d_155_2, decode 300 d_155_3, decode 300 d_155_4, decode 300 d_155_5, decode 300 d_155_6, decode 141 d_155_7] (fun x hx => bits_full_and hx) cov_155 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_155_0, ch_155_1, ch_155_2, ch_155_3, ch_155_4, ch_155_5, ch_155_6, ch_155_7])

theorem root_163 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 163) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_163_0, decode 300 d_163_1, decode 300 d_163_2, decode 300 d_163_3, decode 300 d_163_4, decode 300 d_163_5, decode 300 d_163_6, decode 141 d_163_7] (fun x hx => bits_full_and hx) cov_163 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_163_0, ch_163_1, ch_163_2, ch_163_3, ch_163_4, ch_163_5, ch_163_6, ch_163_7])

theorem root_164 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 164) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_164_0, decode 300 d_164_1, decode 300 d_164_2, decode 300 d_164_3, decode 300 d_164_4, decode 300 d_164_5, decode 300 d_164_6, decode 141 d_164_7] (fun x hx => bits_full_and hx) cov_164 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_164_0, ch_164_1, ch_164_2, ch_164_3, ch_164_4, ch_164_5, ch_164_6, ch_164_7])

theorem root_172 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 172) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_172_0, decode 300 d_172_1, decode 300 d_172_2, decode 300 d_172_3, decode 300 d_172_4, decode 300 d_172_5, decode 300 d_172_6, decode 141 d_172_7] (fun x hx => bits_full_and hx) cov_172 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_172_0, ch_172_1, ch_172_2, ch_172_3, ch_172_4, ch_172_5, ch_172_6, ch_172_7])

theorem root_176 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 176) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_176_0, decode 300 d_176_1, decode 300 d_176_2, decode 300 d_176_3, decode 300 d_176_4, decode 300 d_176_5, decode 300 d_176_6, decode 30 d_176_7] (fun x hx => bits_full_and hx) cov_176 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_176_0, ch_176_1, ch_176_2, ch_176_3, ch_176_4, ch_176_5, ch_176_6, ch_176_7])

theorem root_177 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 177) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_177_0, decode 300 d_177_1, decode 300 d_177_2, decode 300 d_177_3, decode 300 d_177_4, decode 300 d_177_5, decode 300 d_177_6, decode 30 d_177_7] (fun x hx => bits_full_and hx) cov_177 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_177_0, ch_177_1, ch_177_2, ch_177_3, ch_177_4, ch_177_5, ch_177_6, ch_177_7])

theorem root_178 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 178) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_178_0, decode 300 d_178_1, decode 300 d_178_2, decode 300 d_178_3, decode 300 d_178_4, decode 300 d_178_5, decode 300 d_178_6, decode 30 d_178_7] (fun x hx => bits_full_and hx) cov_178 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_178_0, ch_178_1, ch_178_2, ch_178_3, ch_178_4, ch_178_5, ch_178_6, ch_178_7])

theorem root_179 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 179) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_179_0, decode 300 d_179_1, decode 300 d_179_2, decode 300 d_179_3, decode 300 d_179_4, decode 300 d_179_5, decode 254 d_179_6] (fun x hx => bits_full_and hx) cov_179 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_179_0, ch_179_1, ch_179_2, ch_179_3, ch_179_4, ch_179_5, ch_179_6])

theorem root_180 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 180) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_180_0, decode 300 d_180_1, decode 300 d_180_2, decode 300 d_180_3, decode 300 d_180_4, decode 300 d_180_5, decode 254 d_180_6] (fun x hx => bits_full_and hx) cov_180 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_180_0, ch_180_1, ch_180_2, ch_180_3, ch_180_4, ch_180_5, ch_180_6])

theorem root_186 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 186) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_186_0, decode 300 d_186_1, decode 300 d_186_2, decode 300 d_186_3, decode 300 d_186_4, decode 300 d_186_5, decode 300 d_186_6, decode 30 d_186_7] (fun x hx => bits_full_and hx) cov_186 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_186_0, ch_186_1, ch_186_2, ch_186_3, ch_186_4, ch_186_5, ch_186_6, ch_186_7])

theorem roots_2_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_2, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_2, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_123 hB hC hCl hCB, root_128 hB hC hCl hCB, root_129 hB hC hCl hCB, root_139 hB hC hCl hCB, root_142 hB hC hCl hCB, root_146 hB hC hCl hCB, root_151 hB hC hCl hCB, root_153 hB hC hCl hCB, root_154 hB hC hCl hCB, root_155 hB hC hCl hCB, root_163 hB hC hCl hCB, root_164 hB hC hCl hCB, root_172 hB hC hCl hCB, root_176 hB hC hCl hCB, root_177 hB hC hCl hCB, root_178 hB hC hCl hCB, root_179 hB hC hCl hCB, root_180 hB hC hCl hCB, root_186 hB hC hCl hCB]

theorem root_187 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 187) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_187_0, decode 300 d_187_1, decode 300 d_187_2, decode 300 d_187_3, decode 300 d_187_4, decode 300 d_187_5, decode 254 d_187_6] (fun x hx => bits_full_and hx) cov_187 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_187_0, ch_187_1, ch_187_2, ch_187_3, ch_187_4, ch_187_5, ch_187_6])

theorem root_188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_188_0, decode 300 d_188_1, decode 300 d_188_2, decode 300 d_188_3, decode 300 d_188_4, decode 300 d_188_5, decode 182 d_188_6] (fun x hx => bits_full_and hx) cov_188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_188_0, ch_188_1, ch_188_2, ch_188_3, ch_188_4, ch_188_5, ch_188_6])

theorem root_195 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 195) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_195_0, decode 300 d_195_1, decode 300 d_195_2, decode 300 d_195_3, decode 300 d_195_4, decode 300 d_195_5, decode 300 d_195_6, decode 141 d_195_7] (fun x hx => bits_full_and hx) cov_195 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_195_0, ch_195_1, ch_195_2, ch_195_3, ch_195_4, ch_195_5, ch_195_6, ch_195_7])

theorem root_203 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 203) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_203_0, decode 300 d_203_1, decode 300 d_203_2, decode 300 d_203_3, decode 300 d_203_4, decode 300 d_203_5, decode 300 d_203_6, decode 141 d_203_7] (fun x hx => bits_full_and hx) cov_203 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_203_0, ch_203_1, ch_203_2, ch_203_3, ch_203_4, ch_203_5, ch_203_6, ch_203_7])

theorem root_204 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 204) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_204_0, decode 300 d_204_1, decode 300 d_204_2, decode 300 d_204_3, decode 300 d_204_4, decode 300 d_204_5, decode 300 d_204_6, decode 141 d_204_7] (fun x hx => bits_full_and hx) cov_204 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_204_0, ch_204_1, ch_204_2, ch_204_3, ch_204_4, ch_204_5, ch_204_6, ch_204_7])

theorem root_210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_210_0, decode 300 d_210_1, decode 300 d_210_2, decode 300 d_210_3, decode 300 d_210_4, decode 300 d_210_5, decode 300 d_210_6, decode 141 d_210_7] (fun x hx => bits_full_and hx) cov_210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_210_0, ch_210_1, ch_210_2, ch_210_3, ch_210_4, ch_210_5, ch_210_6, ch_210_7])

theorem root_220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_220_0, decode 300 d_220_1, decode 300 d_220_2, decode 300 d_220_3, decode 300 d_220_4, decode 300 d_220_5, decode 300 d_220_6, decode 141 d_220_7] (fun x hx => bits_full_and hx) cov_220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_220_0, ch_220_1, ch_220_2, ch_220_3, ch_220_4, ch_220_5, ch_220_6, ch_220_7])

theorem root_226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_226_0, decode 300 d_226_1, decode 300 d_226_2, decode 300 d_226_3, decode 300 d_226_4, decode 300 d_226_5, decode 300 d_226_6, decode 141 d_226_7] (fun x hx => bits_full_and hx) cov_226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_226_0, ch_226_1, ch_226_2, ch_226_3, ch_226_4, ch_226_5, ch_226_6, ch_226_7])

theorem root_232 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 232) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_232_0, decode 300 d_232_1, decode 300 d_232_2, decode 300 d_232_3, decode 300 d_232_4, decode 300 d_232_5, decode 300 d_232_6, decode 141 d_232_7] (fun x hx => bits_full_and hx) cov_232 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_232_0, ch_232_1, ch_232_2, ch_232_3, ch_232_4, ch_232_5, ch_232_6, ch_232_7])

theorem root_233 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 233) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_233_0, decode 300 d_233_1, decode 300 d_233_2, decode 300 d_233_3, decode 300 d_233_4, decode 300 d_233_5, decode 300 d_233_6, decode 141 d_233_7] (fun x hx => bits_full_and hx) cov_233 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_233_0, ch_233_1, ch_233_2, ch_233_3, ch_233_4, ch_233_5, ch_233_6, ch_233_7])

theorem root_240 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 240) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_240_0, decode 300 d_240_1, decode 300 d_240_2, decode 300 d_240_3, decode 300 d_240_4, decode 300 d_240_5, decode 300 d_240_6, decode 141 d_240_7] (fun x hx => bits_full_and hx) cov_240 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_240_0, ch_240_1, ch_240_2, ch_240_3, ch_240_4, ch_240_5, ch_240_6, ch_240_7])

theorem root_241 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 241) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_241_0, decode 300 d_241_1, decode 300 d_241_2, decode 300 d_241_3, decode 300 d_241_4, decode 300 d_241_5, decode 300 d_241_6, decode 141 d_241_7] (fun x hx => bits_full_and hx) cov_241 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_241_0, ch_241_1, ch_241_2, ch_241_3, ch_241_4, ch_241_5, ch_241_6, ch_241_7])

theorem root_242 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 242) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_242_0, decode 300 d_242_1, decode 300 d_242_2, decode 300 d_242_3, decode 300 d_242_4, decode 300 d_242_5, decode 300 d_242_6, decode 141 d_242_7] (fun x hx => bits_full_and hx) cov_242 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_242_0, ch_242_1, ch_242_2, ch_242_3, ch_242_4, ch_242_5, ch_242_6, ch_242_7])

theorem root_246 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 246) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_246_0, decode 300 d_246_1, decode 300 d_246_2, decode 300 d_246_3, decode 300 d_246_4, decode 300 d_246_5, decode 300 d_246_6, decode 141 d_246_7] (fun x hx => bits_full_and hx) cov_246 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_246_0, ch_246_1, ch_246_2, ch_246_3, ch_246_4, ch_246_5, ch_246_6, ch_246_7])

theorem root_247 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 247) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_247_0, decode 300 d_247_1, decode 300 d_247_2, decode 300 d_247_3, decode 300 d_247_4, decode 300 d_247_5, decode 300 d_247_6, decode 141 d_247_7] (fun x hx => bits_full_and hx) cov_247 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_247_0, ch_247_1, ch_247_2, ch_247_3, ch_247_4, ch_247_5, ch_247_6, ch_247_7])

theorem root_249 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 249) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_249_0, decode 300 d_249_1, decode 300 d_249_2, decode 300 d_249_3, decode 300 d_249_4, decode 300 d_249_5, decode 300 d_249_6, decode 141 d_249_7] (fun x hx => bits_full_and hx) cov_249 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_249_0, ch_249_1, ch_249_2, ch_249_3, ch_249_4, ch_249_5, ch_249_6, ch_249_7])

theorem root_251 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 251) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_251_0, decode 300 d_251_1, decode 300 d_251_2, decode 300 d_251_3, decode 300 d_251_4, decode 300 d_251_5, decode 300 d_251_6, decode 141 d_251_7] (fun x hx => bits_full_and hx) cov_251 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_251_0, ch_251_1, ch_251_2, ch_251_3, ch_251_4, ch_251_5, ch_251_6, ch_251_7])

theorem root_253 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 253) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_253_0, decode 300 d_253_1, decode 300 d_253_2, decode 300 d_253_3, decode 300 d_253_4, decode 300 d_253_5, decode 300 d_253_6, decode 141 d_253_7] (fun x hx => bits_full_and hx) cov_253 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_253_0, ch_253_1, ch_253_2, ch_253_3, ch_253_4, ch_253_5, ch_253_6, ch_253_7])

theorem root_256 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 256) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_256_0, decode 300 d_256_1, decode 300 d_256_2, decode 300 d_256_3, decode 300 d_256_4, decode 300 d_256_5, decode 300 d_256_6, decode 141 d_256_7] (fun x hx => bits_full_and hx) cov_256 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_256_0, ch_256_1, ch_256_2, ch_256_3, ch_256_4, ch_256_5, ch_256_6, ch_256_7])

theorem roots_3_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_3, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_3, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_187 hB hC hCl hCB, root_188 hB hC hCl hCB, root_195 hB hC hCl hCB, root_203 hB hC hCl hCB, root_204 hB hC hCl hCB, root_210 hB hC hCl hCB, root_220 hB hC hCl hCB, root_226 hB hC hCl hCB, root_232 hB hC hCl hCB, root_233 hB hC hCl hCB, root_240 hB hC hCl hCB, root_241 hB hC hCl hCB, root_242 hB hC hCl hCB, root_246 hB hC hCl hCB, root_247 hB hC hCl hCB, root_249 hB hC hCl hCB, root_251 hB hC hCl hCB, root_253 hB hC hCl hCB, root_256 hB hC hCl hCB]

theorem root_257 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 257) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_257_0, decode 300 d_257_1, decode 300 d_257_2, decode 300 d_257_3, decode 300 d_257_4, decode 300 d_257_5, decode 300 d_257_6, decode 141 d_257_7] (fun x hx => bits_full_and hx) cov_257 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_257_0, ch_257_1, ch_257_2, ch_257_3, ch_257_4, ch_257_5, ch_257_6, ch_257_7])

theorem root_258 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 258) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_258_0, decode 300 d_258_1, decode 300 d_258_2, decode 300 d_258_3, decode 300 d_258_4, decode 300 d_258_5, decode 300 d_258_6, decode 141 d_258_7] (fun x hx => bits_full_and hx) cov_258 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_258_0, ch_258_1, ch_258_2, ch_258_3, ch_258_4, ch_258_5, ch_258_6, ch_258_7])

theorem root_266 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 266) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_266_0, decode 300 d_266_1, decode 300 d_266_2, decode 300 d_266_3, decode 300 d_266_4, decode 300 d_266_5, decode 300 d_266_6, decode 141 d_266_7] (fun x hx => bits_full_and hx) cov_266 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_266_0, ch_266_1, ch_266_2, ch_266_3, ch_266_4, ch_266_5, ch_266_6, ch_266_7])

theorem root_267 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 267) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_267_0, decode 300 d_267_1, decode 300 d_267_2, decode 300 d_267_3, decode 300 d_267_4, decode 300 d_267_5, decode 300 d_267_6, decode 141 d_267_7] (fun x hx => bits_full_and hx) cov_267 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_267_0, ch_267_1, ch_267_2, ch_267_3, ch_267_4, ch_267_5, ch_267_6, ch_267_7])

theorem root_268 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 268) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_268_0, decode 300 d_268_1, decode 300 d_268_2, decode 300 d_268_3, decode 300 d_268_4, decode 300 d_268_5, decode 300 d_268_6, decode 141 d_268_7] (fun x hx => bits_full_and hx) cov_268 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_268_0, ch_268_1, ch_268_2, ch_268_3, ch_268_4, ch_268_5, ch_268_6, ch_268_7])

theorem root_271 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 271) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_271_0, decode 300 d_271_1, decode 300 d_271_2, decode 300 d_271_3, decode 300 d_271_4, decode 300 d_271_5, decode 300 d_271_6, decode 141 d_271_7] (fun x hx => bits_full_and hx) cov_271 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_271_0, ch_271_1, ch_271_2, ch_271_3, ch_271_4, ch_271_5, ch_271_6, ch_271_7])

theorem root_272 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 272) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_272_0, decode 300 d_272_1, decode 300 d_272_2, decode 300 d_272_3, decode 300 d_272_4, decode 300 d_272_5, decode 300 d_272_6, decode 141 d_272_7] (fun x hx => bits_full_and hx) cov_272 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_272_0, ch_272_1, ch_272_2, ch_272_3, ch_272_4, ch_272_5, ch_272_6, ch_272_7])

theorem root_273 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 273) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_273_0, decode 300 d_273_1, decode 300 d_273_2, decode 300 d_273_3, decode 300 d_273_4, decode 300 d_273_5, decode 300 d_273_6, decode 141 d_273_7] (fun x hx => bits_full_and hx) cov_273 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_273_0, ch_273_1, ch_273_2, ch_273_3, ch_273_4, ch_273_5, ch_273_6, ch_273_7])

theorem root_281 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 281) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_281_0, decode 300 d_281_1, decode 300 d_281_2, decode 300 d_281_3, decode 300 d_281_4, decode 300 d_281_5, decode 300 d_281_6, decode 141 d_281_7] (fun x hx => bits_full_and hx) cov_281 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_281_0, ch_281_1, ch_281_2, ch_281_3, ch_281_4, ch_281_5, ch_281_6, ch_281_7])

theorem root_282 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 282) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_282_0, decode 300 d_282_1, decode 300 d_282_2, decode 300 d_282_3, decode 300 d_282_4, decode 300 d_282_5, decode 300 d_282_6, decode 141 d_282_7] (fun x hx => bits_full_and hx) cov_282 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_282_0, ch_282_1, ch_282_2, ch_282_3, ch_282_4, ch_282_5, ch_282_6, ch_282_7])

theorem root_283 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 283) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_283_0, decode 300 d_283_1, decode 300 d_283_2, decode 300 d_283_3, decode 300 d_283_4, decode 300 d_283_5, decode 300 d_283_6, decode 141 d_283_7] (fun x hx => bits_full_and hx) cov_283 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_283_0, ch_283_1, ch_283_2, ch_283_3, ch_283_4, ch_283_5, ch_283_6, ch_283_7])

theorem root_284 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 284) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_284_0, decode 300 d_284_1, decode 300 d_284_2, decode 300 d_284_3, decode 300 d_284_4, decode 300 d_284_5, decode 300 d_284_6, decode 141 d_284_7] (fun x hx => bits_full_and hx) cov_284 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_284_0, ch_284_1, ch_284_2, ch_284_3, ch_284_4, ch_284_5, ch_284_6, ch_284_7])

theorem root_296 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 296) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_296_0, decode 300 d_296_1, decode 300 d_296_2, decode 300 d_296_3, decode 300 d_296_4, decode 300 d_296_5, decode 300 d_296_6, decode 141 d_296_7] (fun x hx => bits_full_and hx) cov_296 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_296_0, ch_296_1, ch_296_2, ch_296_3, ch_296_4, ch_296_5, ch_296_6, ch_296_7])

theorem root_297 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 297) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_297_0, decode 300 d_297_1, decode 300 d_297_2, decode 300 d_297_3, decode 300 d_297_4, decode 300 d_297_5, decode 300 d_297_6, decode 141 d_297_7] (fun x hx => bits_full_and hx) cov_297 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_297_0, ch_297_1, ch_297_2, ch_297_3, ch_297_4, ch_297_5, ch_297_6, ch_297_7])

theorem root_299 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 299) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_299_0, decode 300 d_299_1, decode 300 d_299_2, decode 300 d_299_3, decode 300 d_299_4, decode 300 d_299_5, decode 300 d_299_6, decode 141 d_299_7] (fun x hx => bits_full_and hx) cov_299 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_299_0, ch_299_1, ch_299_2, ch_299_3, ch_299_4, ch_299_5, ch_299_6, ch_299_7])

theorem root_300 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 300) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_300_0, decode 300 d_300_1, decode 300 d_300_2, decode 300 d_300_3, decode 300 d_300_4, decode 300 d_300_5, decode 300 d_300_6, decode 141 d_300_7] (fun x hx => bits_full_and hx) cov_300 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_300_0, ch_300_1, ch_300_2, ch_300_3, ch_300_4, ch_300_5, ch_300_6, ch_300_7])

theorem root_302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_302_0, decode 300 d_302_1, decode 300 d_302_2, decode 300 d_302_3, decode 300 d_302_4, decode 300 d_302_5, decode 43 d_302_6] (fun x hx => bits_full_and hx) cov_302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_302_0, ch_302_1, ch_302_2, ch_302_3, ch_302_4, ch_302_5, ch_302_6])

theorem root_303 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 303) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_303_0, decode 300 d_303_1, decode 300 d_303_2, decode 300 d_303_3, decode 300 d_303_4, decode 300 d_303_5, decode 142 d_303_6] (fun x hx => bits_full_and hx) cov_303 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_303_0, ch_303_1, ch_303_2, ch_303_3, ch_303_4, ch_303_5, ch_303_6])

theorem root_304 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 304) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_304_0, decode 300 d_304_1, decode 300 d_304_2, decode 300 d_304_3, decode 300 d_304_4, decode 300 d_304_5, decode 142 d_304_6] (fun x hx => bits_full_and hx) cov_304 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_304_0, ch_304_1, ch_304_2, ch_304_3, ch_304_4, ch_304_5, ch_304_6])

theorem roots_4_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_4, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_4, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_257 hB hC hCl hCB, root_258 hB hC hCl hCB, root_266 hB hC hCl hCB, root_267 hB hC hCl hCB, root_268 hB hC hCl hCB, root_271 hB hC hCl hCB, root_272 hB hC hCl hCB, root_273 hB hC hCl hCB, root_281 hB hC hCl hCB, root_282 hB hC hCl hCB, root_283 hB hC hCl hCB, root_284 hB hC hCl hCB, root_296 hB hC hCl hCB, root_297 hB hC hCl hCB, root_299 hB hC hCl hCB, root_300 hB hC hCl hCB, root_302 hB hC hCl hCB, root_303 hB hC hCl hCB, root_304 hB hC hCl hCB]

theorem root_310 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 310) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_310_0, decode 300 d_310_1, decode 300 d_310_2, decode 300 d_310_3, decode 300 d_310_4, decode 300 d_310_5, decode 300 d_310_6, decode 141 d_310_7] (fun x hx => bits_full_and hx) cov_310 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_310_0, ch_310_1, ch_310_2, ch_310_3, ch_310_4, ch_310_5, ch_310_6, ch_310_7])

theorem root_311 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 311) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_311_0, decode 300 d_311_1, decode 300 d_311_2, decode 300 d_311_3, decode 300 d_311_4, decode 300 d_311_5, decode 300 d_311_6, decode 141 d_311_7] (fun x hx => bits_full_and hx) cov_311 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_311_0, ch_311_1, ch_311_2, ch_311_3, ch_311_4, ch_311_5, ch_311_6, ch_311_7])

theorem root_312 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 312) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_312_0, decode 300 d_312_1, decode 300 d_312_2, decode 300 d_312_3, decode 300 d_312_4, decode 300 d_312_5, decode 300 d_312_6, decode 141 d_312_7] (fun x hx => bits_full_and hx) cov_312 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_312_0, ch_312_1, ch_312_2, ch_312_3, ch_312_4, ch_312_5, ch_312_6, ch_312_7])

theorem root_313 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 313) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_313_0, decode 300 d_313_1, decode 300 d_313_2, decode 300 d_313_3, decode 300 d_313_4, decode 300 d_313_5, decode 300 d_313_6, decode 141 d_313_7] (fun x hx => bits_full_and hx) cov_313 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_313_0, ch_313_1, ch_313_2, ch_313_3, ch_313_4, ch_313_5, ch_313_6, ch_313_7])

theorem root_330 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 330) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_330_0, decode 300 d_330_1, decode 300 d_330_2, decode 300 d_330_3, decode 300 d_330_4, decode 300 d_330_5, decode 300 d_330_6, decode 141 d_330_7] (fun x hx => bits_full_and hx) cov_330 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_330_0, ch_330_1, ch_330_2, ch_330_3, ch_330_4, ch_330_5, ch_330_6, ch_330_7])

theorem root_331 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 331) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_331_0, decode 300 d_331_1, decode 300 d_331_2, decode 300 d_331_3, decode 300 d_331_4, decode 300 d_331_5, decode 300 d_331_6, decode 141 d_331_7] (fun x hx => bits_full_and hx) cov_331 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_331_0, ch_331_1, ch_331_2, ch_331_3, ch_331_4, ch_331_5, ch_331_6, ch_331_7])

theorem root_332 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 332) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_332_0, decode 300 d_332_1, decode 300 d_332_2, decode 300 d_332_3, decode 300 d_332_4, decode 300 d_332_5, decode 300 d_332_6, decode 141 d_332_7] (fun x hx => bits_full_and hx) cov_332 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_332_0, ch_332_1, ch_332_2, ch_332_3, ch_332_4, ch_332_5, ch_332_6, ch_332_7])

theorem root_335 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 335) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_335_0, decode 300 d_335_1, decode 300 d_335_2, decode 300 d_335_3, decode 300 d_335_4, decode 300 d_335_5, decode 300 d_335_6, decode 141 d_335_7] (fun x hx => bits_full_and hx) cov_335 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_335_0, ch_335_1, ch_335_2, ch_335_3, ch_335_4, ch_335_5, ch_335_6, ch_335_7])

theorem root_347 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 347) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_347_0, decode 300 d_347_1, decode 300 d_347_2, decode 300 d_347_3, decode 300 d_347_4, decode 300 d_347_5, decode 300 d_347_6, decode 141 d_347_7] (fun x hx => bits_full_and hx) cov_347 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_347_0, ch_347_1, ch_347_2, ch_347_3, ch_347_4, ch_347_5, ch_347_6, ch_347_7])

theorem root_355 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 355) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_355_0, decode 300 d_355_1, decode 300 d_355_2, decode 300 d_355_3, decode 300 d_355_4, decode 300 d_355_5, decode 300 d_355_6, decode 141 d_355_7] (fun x hx => bits_full_and hx) cov_355 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_355_0, ch_355_1, ch_355_2, ch_355_3, ch_355_4, ch_355_5, ch_355_6, ch_355_7])

theorem root_356 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 356) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_356_0, decode 300 d_356_1, decode 300 d_356_2, decode 300 d_356_3, decode 300 d_356_4, decode 300 d_356_5, decode 300 d_356_6, decode 141 d_356_7] (fun x hx => bits_full_and hx) cov_356 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_356_0, ch_356_1, ch_356_2, ch_356_3, ch_356_4, ch_356_5, ch_356_6, ch_356_7])

theorem root_364 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 364) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_364_0, decode 300 d_364_1, decode 300 d_364_2, decode 300 d_364_3, decode 300 d_364_4, decode 300 d_364_5, decode 300 d_364_6, decode 141 d_364_7] (fun x hx => bits_full_and hx) cov_364 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_364_0, ch_364_1, ch_364_2, ch_364_3, ch_364_4, ch_364_5, ch_364_6, ch_364_7])

theorem root_371 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 371) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_371_0, decode 300 d_371_1, decode 300 d_371_2, decode 300 d_371_3, decode 300 d_371_4, decode 300 d_371_5, decode 300 d_371_6, decode 141 d_371_7] (fun x hx => bits_full_and hx) cov_371 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_371_0, ch_371_1, ch_371_2, ch_371_3, ch_371_4, ch_371_5, ch_371_6, ch_371_7])

theorem root_372 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 372) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_372_0, decode 300 d_372_1, decode 300 d_372_2, decode 300 d_372_3, decode 300 d_372_4, decode 300 d_372_5, decode 300 d_372_6, decode 141 d_372_7] (fun x hx => bits_full_and hx) cov_372 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_372_0, ch_372_1, ch_372_2, ch_372_3, ch_372_4, ch_372_5, ch_372_6, ch_372_7])

theorem root_376 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 376) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_376_0, decode 300 d_376_1, decode 300 d_376_2, decode 300 d_376_3, decode 300 d_376_4, decode 300 d_376_5, decode 300 d_376_6, decode 141 d_376_7] (fun x hx => bits_full_and hx) cov_376 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_376_0, ch_376_1, ch_376_2, ch_376_3, ch_376_4, ch_376_5, ch_376_6, ch_376_7])

theorem root_377 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 377) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_377_0, decode 300 d_377_1, decode 300 d_377_2, decode 300 d_377_3, decode 300 d_377_4, decode 300 d_377_5, decode 300 d_377_6, decode 141 d_377_7] (fun x hx => bits_full_and hx) cov_377 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_377_0, ch_377_1, ch_377_2, ch_377_3, ch_377_4, ch_377_5, ch_377_6, ch_377_7])

theorem root_380 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 380) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_380_0, decode 300 d_380_1, decode 300 d_380_2, decode 300 d_380_3, decode 300 d_380_4, decode 300 d_380_5, decode 300 d_380_6, decode 142 d_380_7] (fun x hx => bits_full_and hx) cov_380 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_380_0, ch_380_1, ch_380_2, ch_380_3, ch_380_4, ch_380_5, ch_380_6, ch_380_7])

theorem root_386 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 386) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_386_0, decode 300 d_386_1, decode 300 d_386_2, decode 300 d_386_3, decode 300 d_386_4, decode 300 d_386_5, decode 300 d_386_6, decode 30 d_386_7] (fun x hx => bits_full_and hx) cov_386 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_386_0, ch_386_1, ch_386_2, ch_386_3, ch_386_4, ch_386_5, ch_386_6, ch_386_7])

theorem roots_5_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_5, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_5, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_310 hB hC hCl hCB, root_311 hB hC hCl hCB, root_312 hB hC hCl hCB, root_313 hB hC hCl hCB, root_330 hB hC hCl hCB, root_331 hB hC hCl hCB, root_332 hB hC hCl hCB, root_335 hB hC hCl hCB, root_347 hB hC hCl hCB, root_355 hB hC hCl hCB, root_356 hB hC hCl hCB, root_364 hB hC hCl hCB, root_371 hB hC hCl hCB, root_372 hB hC hCl hCB, root_376 hB hC hCl hCB, root_377 hB hC hCl hCB, root_380 hB hC hCl hCB, root_386 hB hC hCl hCB]

theorem root_387 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 387) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_387_0, decode 300 d_387_1, decode 300 d_387_2, decode 300 d_387_3, decode 300 d_387_4, decode 300 d_387_5, decode 300 d_387_6, decode 30 d_387_7] (fun x hx => bits_full_and hx) cov_387 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_387_0, ch_387_1, ch_387_2, ch_387_3, ch_387_4, ch_387_5, ch_387_6, ch_387_7])

theorem root_388 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 388) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_388_0, decode 300 d_388_1, decode 300 d_388_2, decode 300 d_388_3, decode 300 d_388_4, decode 300 d_388_5, decode 300 d_388_6, decode 32 d_388_7] (fun x hx => bits_full_and hx) cov_388 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_388_0, ch_388_1, ch_388_2, ch_388_3, ch_388_4, ch_388_5, ch_388_6, ch_388_7])

theorem root_389 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 389) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_389_0, decode 300 d_389_1, decode 300 d_389_2, decode 300 d_389_3, decode 300 d_389_4, decode 300 d_389_5, decode 300 d_389_6, decode 32 d_389_7] (fun x hx => bits_full_and hx) cov_389 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_389_0, ch_389_1, ch_389_2, ch_389_3, ch_389_4, ch_389_5, ch_389_6, ch_389_7])

theorem root_396 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 396) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_396_0, decode 300 d_396_1, decode 300 d_396_2, decode 300 d_396_3, decode 300 d_396_4, decode 300 d_396_5, decode 300 d_396_6, decode 30 d_396_7] (fun x hx => bits_full_and hx) cov_396 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_396_0, ch_396_1, ch_396_2, ch_396_3, ch_396_4, ch_396_5, ch_396_6, ch_396_7])

theorem root_397 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 397) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_397_0, decode 300 d_397_1, decode 300 d_397_2, decode 300 d_397_3, decode 300 d_397_4, decode 300 d_397_5, decode 300 d_397_6, decode 30 d_397_7] (fun x hx => bits_full_and hx) cov_397 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_397_0, ch_397_1, ch_397_2, ch_397_3, ch_397_4, ch_397_5, ch_397_6, ch_397_7])

theorem root_398 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 398) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_398_0, decode 300 d_398_1, decode 300 d_398_2, decode 300 d_398_3, decode 300 d_398_4, decode 300 d_398_5, decode 300 d_398_6, decode 141 d_398_7] (fun x hx => bits_full_and hx) cov_398 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_398_0, ch_398_1, ch_398_2, ch_398_3, ch_398_4, ch_398_5, ch_398_6, ch_398_7])

theorem root_399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_399_0, decode 300 d_399_1, decode 300 d_399_2, decode 300 d_399_3, decode 300 d_399_4, decode 300 d_399_5, decode 300 d_399_6, decode 141 d_399_7] (fun x hx => bits_full_and hx) cov_399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_399_0, ch_399_1, ch_399_2, ch_399_3, ch_399_4, ch_399_5, ch_399_6, ch_399_7])

theorem root_404 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 404) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_404_0, decode 300 d_404_1, decode 300 d_404_2, decode 300 d_404_3, decode 300 d_404_4, decode 300 d_404_5, decode 300 d_404_6, decode 30 d_404_7] (fun x hx => bits_full_and hx) cov_404 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_404_0, ch_404_1, ch_404_2, ch_404_3, ch_404_4, ch_404_5, ch_404_6, ch_404_7])

theorem root_405 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 405) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_405_0, decode 300 d_405_1, decode 300 d_405_2, decode 300 d_405_3, decode 300 d_405_4, decode 300 d_405_5, decode 300 d_405_6, decode 30 d_405_7] (fun x hx => bits_full_and hx) cov_405 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_405_0, ch_405_1, ch_405_2, ch_405_3, ch_405_4, ch_405_5, ch_405_6, ch_405_7])

theorem root_406 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 406) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_406_0, decode 300 d_406_1, decode 300 d_406_2, decode 300 d_406_3, decode 300 d_406_4, decode 300 d_406_5, decode 300 d_406_6, decode 30 d_406_7] (fun x hx => bits_full_and hx) cov_406 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_406_0, ch_406_1, ch_406_2, ch_406_3, ch_406_4, ch_406_5, ch_406_6, ch_406_7])

theorem root_407 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 407) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_407_0, decode 300 d_407_1, decode 300 d_407_2, decode 300 d_407_3, decode 300 d_407_4, decode 300 d_407_5, decode 300 d_407_6, decode 141 d_407_7] (fun x hx => bits_full_and hx) cov_407 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_407_0, ch_407_1, ch_407_2, ch_407_3, ch_407_4, ch_407_5, ch_407_6, ch_407_7])

theorem root_415 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 415) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_415_0, decode 300 d_415_1, decode 300 d_415_2, decode 300 d_415_3, decode 300 d_415_4, decode 300 d_415_5, decode 300 d_415_6, decode 142 d_415_7] (fun x hx => bits_full_and hx) cov_415 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_415_0, ch_415_1, ch_415_2, ch_415_3, ch_415_4, ch_415_5, ch_415_6, ch_415_7])

theorem root_421 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 421) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_421_0, decode 300 d_421_1, decode 300 d_421_2, decode 300 d_421_3, decode 300 d_421_4, decode 300 d_421_5, decode 300 d_421_6, decode 142 d_421_7] (fun x hx => bits_full_and hx) cov_421 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_421_0, ch_421_1, ch_421_2, ch_421_3, ch_421_4, ch_421_5, ch_421_6, ch_421_7])

theorem root_422 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 422) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_422_0, decode 300 d_422_1, decode 300 d_422_2, decode 300 d_422_3, decode 300 d_422_4, decode 300 d_422_5, decode 300 d_422_6, decode 142 d_422_7] (fun x hx => bits_full_and hx) cov_422 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_422_0, ch_422_1, ch_422_2, ch_422_3, ch_422_4, ch_422_5, ch_422_6, ch_422_7])

theorem root_429 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 429) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_429_0, decode 300 d_429_1, decode 300 d_429_2, decode 300 d_429_3, decode 300 d_429_4, decode 300 d_429_5, decode 300 d_429_6, decode 141 d_429_7] (fun x hx => bits_full_and hx) cov_429 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_429_0, ch_429_1, ch_429_2, ch_429_3, ch_429_4, ch_429_5, ch_429_6, ch_429_7])

theorem root_430 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 430) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_430_0, decode 300 d_430_1, decode 300 d_430_2, decode 300 d_430_3, decode 300 d_430_4, decode 300 d_430_5, decode 300 d_430_6, decode 141 d_430_7] (fun x hx => bits_full_and hx) cov_430 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_430_0, ch_430_1, ch_430_2, ch_430_3, ch_430_4, ch_430_5, ch_430_6, ch_430_7])

theorem root_431 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 431) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_431_0, decode 300 d_431_1, decode 300 d_431_2, decode 300 d_431_3, decode 300 d_431_4, decode 300 d_431_5, decode 300 d_431_6, decode 141 d_431_7] (fun x hx => bits_full_and hx) cov_431 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_431_0, ch_431_1, ch_431_2, ch_431_3, ch_431_4, ch_431_5, ch_431_6, ch_431_7])

theorem root_439 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 439) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_439_0, decode 300 d_439_1, decode 300 d_439_2, decode 300 d_439_3, decode 300 d_439_4, decode 300 d_439_5, decode 300 d_439_6, decode 141 d_439_7] (fun x hx => bits_full_and hx) cov_439 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_439_0, ch_439_1, ch_439_2, ch_439_3, ch_439_4, ch_439_5, ch_439_6, ch_439_7])

theorem root_440 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 440) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_440_0, decode 300 d_440_1, decode 300 d_440_2, decode 300 d_440_3, decode 300 d_440_4, decode 300 d_440_5, decode 300 d_440_6, decode 141 d_440_7] (fun x hx => bits_full_and hx) cov_440 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_440_0, ch_440_1, ch_440_2, ch_440_3, ch_440_4, ch_440_5, ch_440_6, ch_440_7])

theorem roots_6_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_6, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_6, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_387 hB hC hCl hCB, root_388 hB hC hCl hCB, root_389 hB hC hCl hCB, root_396 hB hC hCl hCB, root_397 hB hC hCl hCB, root_398 hB hC hCl hCB, root_399 hB hC hCl hCB, root_404 hB hC hCl hCB, root_405 hB hC hCl hCB, root_406 hB hC hCl hCB, root_407 hB hC hCl hCB, root_415 hB hC hCl hCB, root_421 hB hC hCl hCB, root_422 hB hC hCl hCB, root_429 hB hC hCl hCB, root_430 hB hC hCl hCB, root_431 hB hC hCl hCB, root_439 hB hC hCl hCB, root_440 hB hC hCl hCB]

theorem root_441 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 441) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_441_0, decode 300 d_441_1, decode 300 d_441_2, decode 300 d_441_3, decode 300 d_441_4, decode 300 d_441_5, decode 300 d_441_6, decode 141 d_441_7] (fun x hx => bits_full_and hx) cov_441 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_441_0, ch_441_1, ch_441_2, ch_441_3, ch_441_4, ch_441_5, ch_441_6, ch_441_7])

theorem root_450 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 450) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_450_0, decode 300 d_450_1, decode 300 d_450_2, decode 300 d_450_3, decode 300 d_450_4, decode 300 d_450_5, decode 300 d_450_6, decode 158 d_450_7] (fun x hx => bits_full_and hx) cov_450 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_450_0, ch_450_1, ch_450_2, ch_450_3, ch_450_4, ch_450_5, ch_450_6, ch_450_7])

theorem root_451 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 451) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_451_0, decode 300 d_451_1, decode 300 d_451_2, decode 300 d_451_3, decode 300 d_451_4, decode 300 d_451_5, decode 300 d_451_6, decode 158 d_451_7] (fun x hx => bits_full_and hx) cov_451 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_451_0, ch_451_1, ch_451_2, ch_451_3, ch_451_4, ch_451_5, ch_451_6, ch_451_7])

theorem root_463 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 463) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_463_0, decode 300 d_463_1, decode 300 d_463_2, decode 300 d_463_3, decode 300 d_463_4, decode 300 d_463_5, decode 300 d_463_6, decode 158 d_463_7] (fun x hx => bits_full_and hx) cov_463 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_463_0, ch_463_1, ch_463_2, ch_463_3, ch_463_4, ch_463_5, ch_463_6, ch_463_7])

theorem root_468 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 468) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_468_0, decode 300 d_468_1, decode 300 d_468_2, decode 300 d_468_3, decode 300 d_468_4, decode 300 d_468_5, decode 300 d_468_6, decode 141 d_468_7] (fun x hx => bits_full_and hx) cov_468 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_468_0, ch_468_1, ch_468_2, ch_468_3, ch_468_4, ch_468_5, ch_468_6, ch_468_7])

theorem root_469 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 469) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_469_0, decode 300 d_469_1, decode 300 d_469_2, decode 300 d_469_3, decode 300 d_469_4, decode 300 d_469_5, decode 300 d_469_6, decode 141 d_469_7] (fun x hx => bits_full_and hx) cov_469 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_469_0, ch_469_1, ch_469_2, ch_469_3, ch_469_4, ch_469_5, ch_469_6, ch_469_7])

theorem root_470 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 470) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_470_0, decode 300 d_470_1, decode 300 d_470_2, decode 300 d_470_3, decode 300 d_470_4, decode 300 d_470_5, decode 300 d_470_6, decode 141 d_470_7] (fun x hx => bits_full_and hx) cov_470 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_470_0, ch_470_1, ch_470_2, ch_470_3, ch_470_4, ch_470_5, ch_470_6, ch_470_7])

theorem root_476 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 476) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_476_0, decode 300 d_476_1, decode 300 d_476_2, decode 300 d_476_3, decode 300 d_476_4, decode 300 d_476_5, decode 300 d_476_6, decode 141 d_476_7] (fun x hx => bits_full_and hx) cov_476 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_476_0, ch_476_1, ch_476_2, ch_476_3, ch_476_4, ch_476_5, ch_476_6, ch_476_7])

theorem root_483 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 483) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_483_0, decode 300 d_483_1, decode 300 d_483_2, decode 300 d_483_3, decode 300 d_483_4, decode 300 d_483_5, decode 300 d_483_6, decode 141 d_483_7] (fun x hx => bits_full_and hx) cov_483 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_483_0, ch_483_1, ch_483_2, ch_483_3, ch_483_4, ch_483_5, ch_483_6, ch_483_7])

theorem root_484 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 484) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_484_0, decode 300 d_484_1, decode 300 d_484_2, decode 300 d_484_3, decode 300 d_484_4, decode 300 d_484_5, decode 300 d_484_6, decode 141 d_484_7] (fun x hx => bits_full_and hx) cov_484 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_484_0, ch_484_1, ch_484_2, ch_484_3, ch_484_4, ch_484_5, ch_484_6, ch_484_7])

theorem root_490 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 490) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_490_0, decode 300 d_490_1, decode 300 d_490_2, decode 300 d_490_3, decode 300 d_490_4, decode 300 d_490_5, decode 300 d_490_6, decode 141 d_490_7] (fun x hx => bits_full_and hx) cov_490 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_490_0, ch_490_1, ch_490_2, ch_490_3, ch_490_4, ch_490_5, ch_490_6, ch_490_7])

theorem root_493 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 493) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_493_0, decode 300 d_493_1, decode 300 d_493_2, decode 300 d_493_3, decode 300 d_493_4, decode 300 d_493_5, decode 300 d_493_6, decode 141 d_493_7] (fun x hx => bits_full_and hx) cov_493 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_493_0, ch_493_1, ch_493_2, ch_493_3, ch_493_4, ch_493_5, ch_493_6, ch_493_7])

theorem root_496 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 496) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_496_0, decode 300 d_496_1, decode 300 d_496_2, decode 300 d_496_3, decode 300 d_496_4, decode 300 d_496_5, decode 300 d_496_6, decode 142 d_496_7] (fun x hx => bits_full_and hx) cov_496 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_496_0, ch_496_1, ch_496_2, ch_496_3, ch_496_4, ch_496_5, ch_496_6, ch_496_7])

theorem root_505 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 505) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_505_0, decode 300 d_505_1, decode 300 d_505_2, decode 300 d_505_3, decode 300 d_505_4, decode 300 d_505_5, decode 300 d_505_6, decode 142 d_505_7] (fun x hx => bits_full_and hx) cov_505 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_505_0, ch_505_1, ch_505_2, ch_505_3, ch_505_4, ch_505_5, ch_505_6, ch_505_7])

theorem root_509 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 509) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_509_0, decode 300 d_509_1, decode 300 d_509_2, decode 300 d_509_3, decode 300 d_509_4, decode 300 d_509_5, decode 300 d_509_6, decode 141 d_509_7] (fun x hx => bits_full_and hx) cov_509 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_509_0, ch_509_1, ch_509_2, ch_509_3, ch_509_4, ch_509_5, ch_509_6, ch_509_7])

theorem root_510 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 510) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_510_0, decode 300 d_510_1, decode 300 d_510_2, decode 300 d_510_3, decode 300 d_510_4, decode 300 d_510_5, decode 300 d_510_6, decode 141 d_510_7] (fun x hx => bits_full_and hx) cov_510 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_510_0, ch_510_1, ch_510_2, ch_510_3, ch_510_4, ch_510_5, ch_510_6, ch_510_7])

theorem root_511 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 511) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_511_0, decode 300 d_511_1, decode 300 d_511_2, decode 300 d_511_3, decode 300 d_511_4, decode 300 d_511_5, decode 300 d_511_6, decode 141 d_511_7] (fun x hx => bits_full_and hx) cov_511 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_511_0, ch_511_1, ch_511_2, ch_511_3, ch_511_4, ch_511_5, ch_511_6, ch_511_7])

theorem root_514 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 514) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_514_0, decode 300 d_514_1, decode 300 d_514_2, decode 300 d_514_3, decode 300 d_514_4, decode 300 d_514_5, decode 300 d_514_6, decode 142 d_514_7] (fun x hx => bits_full_and hx) cov_514 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_514_0, ch_514_1, ch_514_2, ch_514_3, ch_514_4, ch_514_5, ch_514_6, ch_514_7])

theorem roots_7_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_7, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_7, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_441 hB hC hCl hCB, root_450 hB hC hCl hCB, root_451 hB hC hCl hCB, root_463 hB hC hCl hCB, root_468 hB hC hCl hCB, root_469 hB hC hCl hCB, root_470 hB hC hCl hCB, root_476 hB hC hCl hCB, root_483 hB hC hCl hCB, root_484 hB hC hCl hCB, root_490 hB hC hCl hCB, root_493 hB hC hCl hCB, root_496 hB hC hCl hCB, root_505 hB hC hCl hCB, root_509 hB hC hCl hCB, root_510 hB hC hCl hCB, root_511 hB hC hCl hCB, root_514 hB hC hCl hCB]

theorem root_522 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 522) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_522_0, decode 300 d_522_1, decode 300 d_522_2, decode 300 d_522_3, decode 300 d_522_4, decode 300 d_522_5, decode 300 d_522_6, decode 142 d_522_7] (fun x hx => bits_full_and hx) cov_522 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_522_0, ch_522_1, ch_522_2, ch_522_3, ch_522_4, ch_522_5, ch_522_6, ch_522_7])

theorem root_523 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 523) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_523_0, decode 300 d_523_1, decode 300 d_523_2, decode 300 d_523_3, decode 300 d_523_4, decode 300 d_523_5, decode 300 d_523_6, decode 142 d_523_7] (fun x hx => bits_full_and hx) cov_523 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_523_0, ch_523_1, ch_523_2, ch_523_3, ch_523_4, ch_523_5, ch_523_6, ch_523_7])

theorem root_524 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 524) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_524_0, decode 300 d_524_1, decode 300 d_524_2, decode 300 d_524_3, decode 300 d_524_4, decode 300 d_524_5, decode 300 d_524_6, decode 142 d_524_7] (fun x hx => bits_full_and hx) cov_524 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_524_0, ch_524_1, ch_524_2, ch_524_3, ch_524_4, ch_524_5, ch_524_6, ch_524_7])

theorem root_531 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 531) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_531_0, decode 300 d_531_1, decode 300 d_531_2, decode 300 d_531_3, decode 300 d_531_4, decode 300 d_531_5, decode 125 d_531_6] (fun x hx => bits_full_and hx) cov_531 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_531_0, ch_531_1, ch_531_2, ch_531_3, ch_531_4, ch_531_5, ch_531_6])

theorem root_533 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 533) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_533_0, decode 300 d_533_1, decode 300 d_533_2, decode 300 d_533_3, decode 300 d_533_4, decode 300 d_533_5, decode 109 d_533_6] (fun x hx => bits_full_and hx) cov_533 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_533_0, ch_533_1, ch_533_2, ch_533_3, ch_533_4, ch_533_5, ch_533_6])

theorem root_540 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 540) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_540_0, decode 300 d_540_1, decode 300 d_540_2, decode 300 d_540_3, decode 300 d_540_4, decode 300 d_540_5, decode 81 d_540_6] (fun x hx => bits_full_and hx) cov_540 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_540_0, ch_540_1, ch_540_2, ch_540_3, ch_540_4, ch_540_5, ch_540_6])

theorem root_547 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 547) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_547_0, decode 300 d_547_1, decode 300 d_547_2, decode 300 d_547_3, decode 300 d_547_4, decode 300 d_547_5, decode 87 d_547_6] (fun x hx => bits_full_and hx) cov_547 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_547_0, ch_547_1, ch_547_2, ch_547_3, ch_547_4, ch_547_5, ch_547_6])

theorem root_551 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 551) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_551_0, decode 300 d_551_1, decode 300 d_551_2, decode 300 d_551_3, decode 300 d_551_4, decode 300 d_551_5, decode 87 d_551_6] (fun x hx => bits_full_and hx) cov_551 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_551_0, ch_551_1, ch_551_2, ch_551_3, ch_551_4, ch_551_5, ch_551_6])

theorem root_552 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 552) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_552_0, decode 300 d_552_1, decode 300 d_552_2, decode 300 d_552_3, decode 300 d_552_4, decode 300 d_552_5, decode 87 d_552_6] (fun x hx => bits_full_and hx) cov_552 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_552_0, ch_552_1, ch_552_2, ch_552_3, ch_552_4, ch_552_5, ch_552_6])

theorem root_556 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 556) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_556_0, decode 300 d_556_1, decode 300 d_556_2, decode 300 d_556_3, decode 300 d_556_4, decode 250 d_556_5] (fun x hx => bits_full_and hx) cov_556 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_556_0, ch_556_1, ch_556_2, ch_556_3, ch_556_4, ch_556_5])

theorem root_557 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 557) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_557_0, decode 300 d_557_1, decode 300 d_557_2, decode 300 d_557_3, decode 300 d_557_4, decode 250 d_557_5] (fun x hx => bits_full_and hx) cov_557 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_557_0, ch_557_1, ch_557_2, ch_557_3, ch_557_4, ch_557_5])

theorem root_561 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 561) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_561_0, decode 300 d_561_1, decode 300 d_561_2, decode 300 d_561_3, decode 300 d_561_4, decode 300 d_561_5, decode 300 d_561_6, decode 141 d_561_7] (fun x hx => bits_full_and hx) cov_561 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_561_0, ch_561_1, ch_561_2, ch_561_3, ch_561_4, ch_561_5, ch_561_6, ch_561_7])

theorem root_562 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 562) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_562_0, decode 300 d_562_1, decode 300 d_562_2, decode 300 d_562_3, decode 300 d_562_4, decode 300 d_562_5, decode 300 d_562_6, decode 141 d_562_7] (fun x hx => bits_full_and hx) cov_562 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_562_0, ch_562_1, ch_562_2, ch_562_3, ch_562_4, ch_562_5, ch_562_6, ch_562_7])

theorem root_563 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 563) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_563_0, decode 300 d_563_1, decode 300 d_563_2, decode 300 d_563_3, decode 300 d_563_4, decode 300 d_563_5, decode 300 d_563_6, decode 141 d_563_7] (fun x hx => bits_full_and hx) cov_563 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_563_0, ch_563_1, ch_563_2, ch_563_3, ch_563_4, ch_563_5, ch_563_6, ch_563_7])

theorem root_569 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 569) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_569_0, decode 300 d_569_1, decode 300 d_569_2, decode 300 d_569_3, decode 300 d_569_4, decode 300 d_569_5, decode 209 d_569_6] (fun x hx => bits_full_and hx) cov_569 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_569_0, ch_569_1, ch_569_2, ch_569_3, ch_569_4, ch_569_5, ch_569_6])

theorem root_571 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 571) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_571_0, decode 300 d_571_1, decode 300 d_571_2, decode 300 d_571_3, decode 300 d_571_4, decode 250 d_571_5] (fun x hx => bits_full_and hx) cov_571 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_571_0, ch_571_1, ch_571_2, ch_571_3, ch_571_4, ch_571_5])

theorem root_576 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 576) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_576_0, decode 300 d_576_1, decode 300 d_576_2, decode 300 d_576_3, decode 300 d_576_4, decode 250 d_576_5] (fun x hx => bits_full_and hx) cov_576 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_576_0, ch_576_1, ch_576_2, ch_576_3, ch_576_4, ch_576_5])

theorem root_577 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 577) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_577_0, decode 300 d_577_1, decode 300 d_577_2, decode 300 d_577_3, decode 300 d_577_4, decode 250 d_577_5] (fun x hx => bits_full_and hx) cov_577 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_577_0, ch_577_1, ch_577_2, ch_577_3, ch_577_4, ch_577_5])

theorem root_580 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 580) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_580_0, decode 300 d_580_1, decode 300 d_580_2, decode 300 d_580_3, decode 300 d_580_4, decode 300 d_580_5, decode 300 d_580_6, decode 141 d_580_7] (fun x hx => bits_full_and hx) cov_580 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_580_0, ch_580_1, ch_580_2, ch_580_3, ch_580_4, ch_580_5, ch_580_6, ch_580_7])

theorem root_581 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 581) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_581_0, decode 300 d_581_1, decode 300 d_581_2, decode 300 d_581_3, decode 300 d_581_4, decode 300 d_581_5, decode 300 d_581_6, decode 141 d_581_7] (fun x hx => bits_full_and hx) cov_581 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_581_0, ch_581_1, ch_581_2, ch_581_3, ch_581_4, ch_581_5, ch_581_6, ch_581_7])

theorem roots_8_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_8, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_8, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_522 hB hC hCl hCB, root_523 hB hC hCl hCB, root_524 hB hC hCl hCB, root_531 hB hC hCl hCB, root_533 hB hC hCl hCB, root_540 hB hC hCl hCB, root_547 hB hC hCl hCB, root_551 hB hC hCl hCB, root_552 hB hC hCl hCB, root_556 hB hC hCl hCB, root_557 hB hC hCl hCB, root_561 hB hC hCl hCB, root_562 hB hC hCl hCB, root_563 hB hC hCl hCB, root_569 hB hC hCl hCB, root_571 hB hC hCl hCB, root_576 hB hC hCl hCB, root_577 hB hC hCl hCB, root_580 hB hC hCl hCB, root_581 hB hC hCl hCB]

theorem root_582 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 582) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_582_0, decode 300 d_582_1, decode 300 d_582_2, decode 300 d_582_3, decode 300 d_582_4, decode 300 d_582_5, decode 300 d_582_6, decode 141 d_582_7] (fun x hx => bits_full_and hx) cov_582 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_582_0, ch_582_1, ch_582_2, ch_582_3, ch_582_4, ch_582_5, ch_582_6, ch_582_7])

theorem root_590 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 590) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_590_0, decode 300 d_590_1, decode 300 d_590_2, decode 300 d_590_3, decode 300 d_590_4, decode 300 d_590_5, decode 300 d_590_6, decode 141 d_590_7] (fun x hx => bits_full_and hx) cov_590 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_590_0, ch_590_1, ch_590_2, ch_590_3, ch_590_4, ch_590_5, ch_590_6, ch_590_7])

theorem root_594 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 594) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_594_0, decode 300 d_594_1, decode 300 d_594_2, decode 300 d_594_3, decode 300 d_594_4, decode 300 d_594_5, decode 300 d_594_6, decode 141 d_594_7] (fun x hx => bits_full_and hx) cov_594 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_594_0, ch_594_1, ch_594_2, ch_594_3, ch_594_4, ch_594_5, ch_594_6, ch_594_7])

theorem root_595 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 595) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_595_0, decode 300 d_595_1, decode 300 d_595_2, decode 300 d_595_3, decode 300 d_595_4, decode 300 d_595_5, decode 300 d_595_6, decode 141 d_595_7] (fun x hx => bits_full_and hx) cov_595 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_595_0, ch_595_1, ch_595_2, ch_595_3, ch_595_4, ch_595_5, ch_595_6, ch_595_7])

theorem root_596 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 596) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_596_0, decode 300 d_596_1, decode 300 d_596_2, decode 300 d_596_3, decode 300 d_596_4, decode 300 d_596_5, decode 300 d_596_6, decode 141 d_596_7] (fun x hx => bits_full_and hx) cov_596 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_596_0, ch_596_1, ch_596_2, ch_596_3, ch_596_4, ch_596_5, ch_596_6, ch_596_7])

theorem root_597 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 597) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_597_0, decode 300 d_597_1, decode 300 d_597_2, decode 300 d_597_3, decode 300 d_597_4, decode 300 d_597_5, decode 300 d_597_6, decode 141 d_597_7] (fun x hx => bits_full_and hx) cov_597 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_597_0, ch_597_1, ch_597_2, ch_597_3, ch_597_4, ch_597_5, ch_597_6, ch_597_7])

theorem root_604 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 604) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_604_0, decode 300 d_604_1, decode 300 d_604_2, decode 300 d_604_3, decode 300 d_604_4, decode 300 d_604_5, decode 300 d_604_6, decode 141 d_604_7] (fun x hx => bits_full_and hx) cov_604 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_604_0, ch_604_1, ch_604_2, ch_604_3, ch_604_4, ch_604_5, ch_604_6, ch_604_7])

theorem root_605 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 605) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_605_0, decode 300 d_605_1, decode 300 d_605_2, decode 300 d_605_3, decode 300 d_605_4, decode 300 d_605_5, decode 300 d_605_6, decode 141 d_605_7] (fun x hx => bits_full_and hx) cov_605 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_605_0, ch_605_1, ch_605_2, ch_605_3, ch_605_4, ch_605_5, ch_605_6, ch_605_7])

theorem root_606 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 606) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_606_0, decode 300 d_606_1, decode 300 d_606_2, decode 300 d_606_3, decode 300 d_606_4, decode 300 d_606_5, decode 300 d_606_6, decode 141 d_606_7] (fun x hx => bits_full_and hx) cov_606 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_606_0, ch_606_1, ch_606_2, ch_606_3, ch_606_4, ch_606_5, ch_606_6, ch_606_7])

theorem root_607 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 607) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_607_0, decode 300 d_607_1, decode 300 d_607_2, decode 300 d_607_3, decode 300 d_607_4, decode 300 d_607_5, decode 300 d_607_6, decode 141 d_607_7] (fun x hx => bits_full_and hx) cov_607 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_607_0, ch_607_1, ch_607_2, ch_607_3, ch_607_4, ch_607_5, ch_607_6, ch_607_7])

theorem root_619 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 619) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_619_0, decode 300 d_619_1, decode 300 d_619_2, decode 300 d_619_3, decode 300 d_619_4, decode 300 d_619_5, decode 19 d_619_6] (fun x hx => bits_full_and hx) cov_619 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_619_0, ch_619_1, ch_619_2, ch_619_3, ch_619_4, ch_619_5, ch_619_6])

theorem root_620 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 620) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_620_0, decode 300 d_620_1, decode 300 d_620_2, decode 300 d_620_3, decode 300 d_620_4, decode 300 d_620_5, decode 19 d_620_6] (fun x hx => bits_full_and hx) cov_620 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_620_0, ch_620_1, ch_620_2, ch_620_3, ch_620_4, ch_620_5, ch_620_6])

theorem root_629 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 629) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_629_0, decode 300 d_629_1, decode 300 d_629_2, decode 300 d_629_3, decode 300 d_629_4, decode 300 d_629_5, decode 300 d_629_6, decode 141 d_629_7] (fun x hx => bits_full_and hx) cov_629 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_629_0, ch_629_1, ch_629_2, ch_629_3, ch_629_4, ch_629_5, ch_629_6, ch_629_7])

theorem root_632 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 632) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_632_0, decode 300 d_632_1, decode 300 d_632_2, decode 300 d_632_3, decode 300 d_632_4, decode 300 d_632_5, decode 300 d_632_6, decode 141 d_632_7] (fun x hx => bits_full_and hx) cov_632 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_632_0, ch_632_1, ch_632_2, ch_632_3, ch_632_4, ch_632_5, ch_632_6, ch_632_7])

theorem root_635 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 635) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_635_0, decode 300 d_635_1, decode 300 d_635_2, decode 300 d_635_3, decode 300 d_635_4, decode 300 d_635_5, decode 300 d_635_6, decode 141 d_635_7] (fun x hx => bits_full_and hx) cov_635 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_635_0, ch_635_1, ch_635_2, ch_635_3, ch_635_4, ch_635_5, ch_635_6, ch_635_7])

theorem root_638 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 638) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_638_0, decode 300 d_638_1, decode 300 d_638_2, decode 300 d_638_3, decode 300 d_638_4, decode 300 d_638_5, decode 300 d_638_6, decode 141 d_638_7] (fun x hx => bits_full_and hx) cov_638 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_638_0, ch_638_1, ch_638_2, ch_638_3, ch_638_4, ch_638_5, ch_638_6, ch_638_7])

theorem root_639 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 639) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_639_0, decode 300 d_639_1, decode 300 d_639_2, decode 300 d_639_3, decode 300 d_639_4, decode 300 d_639_5, decode 300 d_639_6, decode 141 d_639_7] (fun x hx => bits_full_and hx) cov_639 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_639_0, ch_639_1, ch_639_2, ch_639_3, ch_639_4, ch_639_5, ch_639_6, ch_639_7])

theorem root_641 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 641) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_641_0, decode 300 d_641_1, decode 300 d_641_2, decode 300 d_641_3, decode 300 d_641_4, decode 300 d_641_5, decode 300 d_641_6, decode 141 d_641_7] (fun x hx => bits_full_and hx) cov_641 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_641_0, ch_641_1, ch_641_2, ch_641_3, ch_641_4, ch_641_5, ch_641_6, ch_641_7])

theorem root_648 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 648) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_648_0, decode 300 d_648_1, decode 300 d_648_2, decode 300 d_648_3, decode 300 d_648_4, decode 300 d_648_5, decode 300 d_648_6, decode 141 d_648_7] (fun x hx => bits_full_and hx) cov_648 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_648_0, ch_648_1, ch_648_2, ch_648_3, ch_648_4, ch_648_5, ch_648_6, ch_648_7])

theorem roots_9_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_9, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_9, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_582 hB hC hCl hCB, root_590 hB hC hCl hCB, root_594 hB hC hCl hCB, root_595 hB hC hCl hCB, root_596 hB hC hCl hCB, root_597 hB hC hCl hCB, root_604 hB hC hCl hCB, root_605 hB hC hCl hCB, root_606 hB hC hCl hCB, root_607 hB hC hCl hCB, root_619 hB hC hCl hCB, root_620 hB hC hCl hCB, root_629 hB hC hCl hCB, root_632 hB hC hCl hCB, root_635 hB hC hCl hCB, root_638 hB hC hCl hCB, root_639 hB hC hCl hCB, root_641 hB hC hCl hCB, root_648 hB hC hCl hCB]

end LRC.O7U5
